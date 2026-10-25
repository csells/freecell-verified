import FreeCell.Heuristic
import Std.Data.TreeMap
import Std.Data.HashSet

/-!
# Untrusted win proposer

A best-first search that looks for a winning move list quickly. Nothing about it
is proved: it may miss wins, and its answer is only a proposal. The command line
accepts a proposal only after `checkWin` (proved sound) confirms it, and decides
unwinnability only with the reference search.

After each move it also plays "safe" foundation moves — aces and twos, and any
card whose opposite-colour foundations are at least one rank lower — which keeps
paths short. These are ordinary legal moves recorded in the path, so the checker
sees them like any other.
-/

namespace FreeCell

open Std

/-- A foundation move that can never hurt: no tableau card could still need it as a parent. -/
def safeHome (s : State) (c : Card) : Bool :=
  s.home.getD c.suit 0 + 1 == c.rank &&
    (c.rank ≤ 2 || (List.range 4).all fun su =>
      (su == 1 || su == 2) == c.red || s.home.getD su 0 + 1 ≥ c.rank)

/-- Repeatedly play safe foundation moves, appending them (reversed) to `path`. -/
def autoHome : Nat → State → List Move → State × List Move
  | 0, s, path => (s, path)
  | n + 1, s, path =>
    let fromCols := (colIdx.filterMap fun i => match s.cols.getD i [] with
      | c :: _ => if safeHome s c then some (Move.mk (.col i) .home) else none
      | [] => none)
    let fromCells := s.cells.filterMap fun c =>
      if safeHome s c then some (Move.mk (.cell c) .home) else none
    match (fromCols ++ fromCells).head? with
    | none => (s, path)
    | some m =>
      match applyMove s m with
      | some t => autoHome n t (m :: path)
      | none => (s, path)

/-- How many cards cover the next card each foundation needs. -/
def nextDepth (s : State) (su : Nat) : Nat :=
  let r := s.home.getD su 0 + 1
  if r > 13 then 0 else
  let target : Card := ⟨r, su⟩
  (s.cols.filterMap fun col => col.idxOf? target).headD 0

/-- Proposer priority: cards home first, then uncovering the next foundation cards, then mobility. -/
def proposerScore (s : State) : Nat :=
  let homeN := s.home.foldl (· + ·) 0
  let depth := ((List.range 4).map (nextDepth s)).foldl (· + ·) 0
  let freeCells := 4 - s.cells.length
  let emptyCols := (s.cols.filter (·.isEmpty)).length
  let disorder := (s.cols.map breaks).foldl (· + ·) 0
  100000 + 40 * homeN + 4 * freeCells + 8 * emptyCols - 3 * depth - 2 * disorder

/-- The proposer's resumable state: a best-first queue keyed by packed (score, insertion number). -/
structure Proposer where
  queue : TreeMap Nat (State × List Move) compare
  seen : HashSet State
  counter : Nat
  expanded : Nat

def Proposer.key (sc n : Nat) : Nat := sc * 2 ^ 40 + n

/-- Start proposing from `start`; may already return a winning move list. -/
def Proposer.init (start : State) : List Move ⊕ Proposer :=
  let (s0, p0) := autoHome 52 start []
  if s0.won then .inl p0.reverse
  else .inr ⟨TreeMap.empty.insert (key (proposerScore s0) 0) (s0, p0),
    HashSet.emptyWithCapacity 4096 |>.insert s0, 1, 0⟩

inductive ProposeStep where
  | found (moves : List Move)
  | exhausted
  | more (p : Proposer)

/-- Expand up to `n` positions, best first, stopping early once more than `maxSeen`
positions have been seen. -/
def Proposer.run (n : Nat) (maxSeen : Option Nat) (p : Proposer) : ProposeStep := Id.run do
  let mut queue := p.queue
  let mut seen := p.seen
  let mut counter := p.counter
  let mut expanded := p.expanded
  for _ in [0:n] do
    if maxSeen.any (seen.size > ·) then break
    let some ((k, (s, path))) := queue.maxEntry? | return .exhausted
    queue := queue.erase k
    expanded := expanded + 1
    for (m, t0) in succs s do
      let (t, path') := autoHome 52 t0 (m :: path)
      if t.won then return .found path'.reverse
      unless seen.contains t do
        seen := seen.insert t
        queue := queue.insert (key (proposerScore t) counter) (t, path')
        counter := counter + 1
  return .more ⟨queue, seen, counter, expanded⟩

end FreeCell
