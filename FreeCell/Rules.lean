import FreeCell.State

/-!
# The rules: single-card moves

A move takes the exposed card of a column, or a card from a free cell, and puts
it on its foundation, on an empty column, on an exposed card one rank higher of
the opposite colour, or (from a column only) into a free cell. Cards never leave
a foundation. Multi-card "supermoves" are sequences of these moves; see
`FreeCell.Supermove`.

`Legal` is the declarative relation (trusted specification). `applyMove` and
`moves` are the executable versions; `applyMove_eq_some_iff` and `mem_moves_iff`
prove they agree with `Legal` exactly.
-/

namespace FreeCell

/-- Where a moving card comes from. A free cell is named by the card it holds. -/
inductive Src where
  | col (i : Nat)
  | cell (c : Card)
deriving DecidableEq, Hashable, Repr, Inhabited

/-- Where a moving card goes. A free cell destination is any empty cell. -/
inductive Dst where
  | home
  | col (j : Nat)
  | cell
deriving DecidableEq, Hashable, Repr, Inhabited

structure Move where
  src : Src
  dst : Dst
deriving DecidableEq, Hashable, Repr, Inhabited

/-! ## Declarative rules -/

/-- `Pick s src c u`: card `c` can be lifted from `src`, leaving `u`. -/
inductive Pick : State → Src → Card → State → Prop
  | col {s : State} {i : Nat} {c : Card} {rest : List Card} :
      i < 8 → s.cols[i]? = some (c :: rest) →
      Pick s (.col i) c { s with cols := s.cols.set i rest }
  | cell {s : State} {c : Card} :
      c ∈ s.cells →
      Pick s (.cell c) c { s with cells := s.cells.erase c }

/-- `Put u src c dst t`: card `c`, lifted from `src` leaving `u`, can be put at `dst`, giving `t`. -/
inductive Put : State → Src → Card → Dst → State → Prop
  | home {u : State} {src : Src} {c : Card} {h : Nat} :
      u.home[c.suit]? = some h → h + 1 = c.rank →
      Put u src c .home { u with home := u.home.set c.suit c.rank }
  | empty {u : State} {src : Src} {c : Card} {j : Nat} :
      j < 8 → src ≠ .col j → u.cols[j]? = some [] →
      Put u src c (.col j) { u with cols := u.cols.set j [c] }
  | stack {u : State} {src : Src} {c p : Card} {ps : List Card} {j : Nat} :
      j < 8 → src ≠ .col j → u.cols[j]? = some (p :: ps) →
      p.rank = c.rank + 1 → p.red ≠ c.red →
      Put u src c (.col j) { u with cols := u.cols.set j (c :: p :: ps) }
  | cell {u : State} {i : Nat} {c : Card} :
      u.cells.length < 4 →
      Put u (.col i) c .cell { u with cells := insertSorted c u.cells }

/-- `Legal s m t`: move `m` is legal in `s` and produces `t`. -/
def Legal (s : State) (m : Move) (t : State) : Prop :=
  ∃ c u, Pick s m.src c u ∧ Put u m.src c m.dst t

/-- One single-card move. -/
def Step (s t : State) : Prop := ∃ m, Legal s m t

/-! ## Executable rules -/

def pick (s : State) : Src → Option (Card × State)
  | .col i =>
    if i < 8 then
      match s.cols[i]? with
      | some (c :: rest) => some (c, { s with cols := s.cols.set i rest })
      | _ => none
    else none
  | .cell c => if c ∈ s.cells then some (c, { s with cells := s.cells.erase c }) else none

def put (u : State) (src : Src) (c : Card) : Dst → Option State
  | .home =>
    match u.home[c.suit]? with
    | some h => if h + 1 = c.rank then some { u with home := u.home.set c.suit c.rank } else none
    | none => none
  | .col j =>
    if j < 8 ∧ src ≠ .col j then
      match u.cols[j]? with
      | some [] => some { u with cols := u.cols.set j [c] }
      | some (p :: ps) =>
        if p.rank = c.rank + 1 ∧ p.red ≠ c.red then
          some { u with cols := u.cols.set j (c :: p :: ps) }
        else none
      | none => none
    else none
  | .cell =>
    match src with
    | .col _ => if u.cells.length < 4 then some { u with cells := insertSorted c u.cells } else none
    | .cell _ => none

def applyMove (s : State) (m : Move) : Option State := do
  let (c, u) ← pick s m.src
  put u m.src c m.dst

def colIdx : List Nat := List.range 8

/-- Every move that could be legal in `s`. -/
def candidateMoves (s : State) : List Move :=
  let srcs := colIdx.map Src.col ++ s.cells.map Src.cell
  let dsts := Dst.home :: colIdx.map Dst.col ++ [Dst.cell]
  srcs.flatMap fun src => dsts.map fun dst => ⟨src, dst⟩

/-- The legal moves in `s`, each with its resulting position. -/
def succs (s : State) : List (Move × State) :=
  (candidateMoves s).filterMap fun m => (applyMove s m).map (m, ·)

/-- The positions reachable from `s` in one move. -/
def moves (s : State) : List State := (succs s).map (·.2)

/-! ## Agreement of executable and declarative rules -/

theorem pick_eq_some_iff {s : State} {src : Src} {c : Card} {u : State} :
    pick s src = some (c, u) ↔ Pick s src c u := by
  constructor
  · intro h
    cases src with
    | col i =>
      simp only [pick] at h
      split at h
      · split at h
        · rename_i c' rest hcol
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Pick.col (by assumption) hcol
        · simp at h
      · simp at h
    | cell d =>
      simp only [pick] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Pick.cell (by assumption)
      · simp at h
  · intro h
    cases h with
    | col hi hcol => simp [pick, hi, hcol]
    | cell hc => simp [pick, hc]

theorem put_eq_some_iff {u : State} {src : Src} {c : Card} {dst : Dst} {t : State} :
    put u src c dst = some t ↔ Put u src c dst t := by
  constructor
  · intro h
    cases dst with
    | home =>
      simp only [put] at h
      split at h
      · split at h
        · simp only [Option.some.injEq] at h; subst h
          exact Put.home (by assumption) (by assumption)
        · simp at h
      · simp at h
    | col j =>
      simp only [put] at h
      split at h
      · rename_i hj
        split at h
        · simp only [Option.some.injEq] at h; subst h
          exact Put.empty hj.1 hj.2 (by assumption)
        · split at h
          · rename_i hst
            simp only [Option.some.injEq] at h; subst h
            exact Put.stack hj.1 hj.2 (by assumption) hst.1 hst.2
          · simp at h
        · simp at h
      · simp at h
    | cell =>
      cases src with
      | col i =>
        simp only [put] at h
        split at h
        · simp only [Option.some.injEq] at h; subst h
          exact Put.cell (by assumption)
        · simp at h
      | cell _ => simp [put] at h
  · intro h
    cases h with
    | home hh hr => simp [put, hh, hr]
    | empty hj hs he => simp [put, hj, hs, he]
    | stack hj hs hp hr hc => simp [put, hj, hs, hp, hr, hc]
    | cell hl => simp [put, hl]

theorem applyMove_eq_some_iff {s : State} {m : Move} {t : State} :
    applyMove s m = some t ↔ Legal s m t := by
  simp only [applyMove, Legal, Option.bind_eq_bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨⟨c, u⟩, hp, hq⟩
    exact ⟨c, u, pick_eq_some_iff.mp hp, put_eq_some_iff.mp hq⟩
  · rintro ⟨c, u, hp, hq⟩
    exact ⟨(c, u), pick_eq_some_iff.mpr hp, put_eq_some_iff.mpr hq⟩

theorem Pick.src_mem {s : State} {src : Src} {c : Card} {u : State} (h : Pick s src c u) :
    src ∈ colIdx.map Src.col ++ s.cells.map Src.cell := by
  cases h with
  | col hi _ => simp [colIdx, hi]
  | cell hc => simp [hc]

theorem Put.dst_mem {u : State} {src : Src} {c : Card} {dst : Dst} {t : State}
    (h : Put u src c dst t) : dst ∈ Dst.home :: colIdx.map Dst.col ++ [Dst.cell] := by
  cases h <;> simp_all [colIdx]

theorem Legal.mem_candidateMoves {s : State} {m : Move} {t : State} (h : Legal s m t) :
    m ∈ candidateMoves s := by
  obtain ⟨c, u, hp, hq⟩ := h
  simp only [candidateMoves, List.mem_flatMap, List.mem_map]
  exact ⟨m.src, hp.src_mem, m.dst, hq.dst_mem, rfl⟩

/-- **Enumeration is sound and complete**: `succs s` lists exactly the legal moves with their results. -/
theorem mem_succs_iff {s t : State} {m : Move} : (m, t) ∈ succs s ↔ Legal s m t := by
  simp only [succs, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨m', -, t', hm, rfl, rfl⟩; exact applyMove_eq_some_iff.mp hm
  · intro hm; exact ⟨m, hm.mem_candidateMoves, t, applyMove_eq_some_iff.mpr hm, rfl, rfl⟩

/-- `moves s` lists exactly the one-move successors. -/
theorem mem_moves_iff {s t : State} : t ∈ moves s ↔ Step s t := by
  simp only [moves, List.mem_map, Step]
  constructor
  · rintro ⟨⟨m, t'⟩, hm, rfl⟩; exact ⟨m, mem_succs_iff.mp hm⟩
  · rintro ⟨m, hm⟩; exact ⟨(m, t), mem_succs_iff.mpr hm, rfl⟩

end FreeCell
