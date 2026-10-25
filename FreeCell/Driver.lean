import FreeCell.Verify
import FreeCell.Propose

/-!
# Bounded execution

`solveBounded` first asks the untrusted proposer (`FreeCell.Propose`) for a
winning move list and keeps it only if `checkWin` accepts it. Otherwise it runs
the reference search's own `step` under operational limits. A decided result is
an `Outcome`, which carries its checker proof, so neither the proposer nor the
limits can produce a wrong answer; limits can only produce `unknown`. With the
proposer disabled and no limits it computes exactly `solve` (`runSteps_eq_run`).
-/

namespace FreeCell

structure Limits where
  /-- Stop once more than this many positions have been visited. -/
  maxPositions : Option Nat := none
  /-- Stop after this many milliseconds of search. -/
  timeLimitMs : Option Nat := none
  /-- Stop when this file exists (cooperative cancellation). -/
  cancelFile : Option System.FilePath := none
  /-- Positions the untrusted proposer may expand before the reference search starts; 0 skips it. -/
  proposerBudget : Nat := 2000000

/-- Which search produced a decided result. -/
inductive Engine where
  | proposer
  | reference

def Engine.name : Engine → String
  | .proposer => "proposer"
  | .reference => "reference"

inductive Result (start : State) where
  | decided (o : Outcome start) (engine : Engine) (explored : Nat)
  | unknown (reason : String) (explored : Nat)

/-- Up to `n` further steps, stopping early if the visited set exceeds `maxPositions`. -/
def runChunk {start : State} (hv : start.Valid) (maxPositions : Option Nat) :
    Nat → (σ : Search start) → Outcome start ⊕ { σ' : Search start // σ'.measure ≤ σ.measure }
  | 0, σ => .inr ⟨σ, Nat.le_refl _⟩
  | n + 1, σ =>
    if maxPositions.any (σ.visited.size > ·) then .inr ⟨σ, Nat.le_refl _⟩ else
    match step hv σ with
    | .inl o => .inl o
    | .inr ⟨σ', h⟩ =>
      match runChunk hv maxPositions n σ' with
      | .inl o => .inl o
      | .inr ⟨σ'', h'⟩ => .inr ⟨σ'', Nat.le_trans h' (Nat.le_of_lt h)⟩

def chunkSize : Nat := 1024

/-- Search in chunks, checking the limits between chunks. Each iteration takes at least one
step, so the loop terminates by the same measure as `run`. -/
def searchLoop {start : State} (hv : start.Valid) (lim : Limits) (t0 : Nat) (σ : Search start) :
    IO (Result start) := do
  if lim.maxPositions.any (σ.visited.size > ·) then
    return .unknown "position limit reached" σ.visited.size
  if let some ms := lim.timeLimitMs then
    if (← IO.monoMsNow) - t0 ≥ ms then
      return .unknown "time limit reached" σ.visited.size
  if let some f := lim.cancelFile then
    if ← f.pathExists then
      return .unknown "cancelled" σ.visited.size
  match step hv σ with
  | .inl o => return .decided o .reference (explored o σ)
  | .inr ⟨σ1, h1⟩ =>
    match runChunk hv lim.maxPositions chunkSize σ1 with
    | .inl o => return .decided o .reference (explored o σ1)
    | .inr ⟨σ2, h2⟩ =>
      have : σ2.measure < σ.measure := Nat.lt_of_le_of_lt h2 h1
      searchLoop hv lim t0 σ2
termination_by σ.measure
where
  explored (o : Outcome start) (σ : Search start) : Nat :=
    match o with
    | .lose c _ => c.size
    | .win .. => σ.visited.size

/-- Why a bounded phase stopped early, if it did. -/
def limitReached (lim : Limits) (t0 visited : Nat) : IO (Option String) := do
  if lim.maxPositions.any (visited > ·) then return some "position limit reached"
  if let some ms := lim.timeLimitMs then
    if (← IO.monoMsNow) - t0 ≥ ms then return some "time limit reached"
  if let some f := lim.cancelFile then
    if ← f.pathExists then return some "cancelled"
  return none

inductive ProposerResult where
  | found (moves : List Move) (seen : Nat)
  | stopped (reason : String) (seen : Nat)
  | gaveUp (seen : Nat)

/-- Run the untrusted proposer for at most `lim.proposerBudget` expansions. -/
def runProposer (start : State) (lim : Limits) (t0 : Nat) : IO ProposerResult := do
  match Proposer.init start with
  | .inl ms => return .found ms 1
  | .inr p0 =>
    let rec loop : Nat → Proposer → IO ProposerResult
      | 0, p => return .gaveUp p.seen.size
      | rounds + 1, p => do
        if let some why ← limitReached lim t0 p.seen.size then return .stopped why p.seen.size
        if p.expanded ≥ lim.proposerBudget then return .gaveUp p.seen.size
        match p.run (min chunkSize (lim.proposerBudget - p.expanded)) lim.maxPositions with
        | .found ms n => return .found ms n
        | .exhausted => return .gaveUp p.seen.size
        | .more p' => loop rounds p'
    loop (lim.proposerBudget / chunkSize + 2) p0

/-- `--max-positions` bounds both phases together: the reference search gets what the
proposer left. Each phase can overshoot by at most one position's successors. -/
def solveBounded (start : State) (hv : start.Valid) (lim : Limits) : IO (Result start) := do
  let t0 ← IO.monoMsNow
  match initSearch start with
  | .inl o => return .decided o .reference 1
  | .inr σ0 =>
    let used ← match ← runProposer start lim t0 with
      | .found ms n =>
        if h : checkWin start ms = true then
          return .decided (.win ms h) .proposer n
        IO.eprintln "warning: the untrusted proposer's path failed the checker and was discarded"
        pure n
      | .stopped why n => return .unknown why n
      | .gaveUp n => pure n
    let lim' := { lim with maxPositions := lim.maxPositions.map (· - used) }
    match ← searchLoop hv lim' t0 σ0 with
    | .unknown why n => return .unknown why (used + n)
    | r => return r

end FreeCell
