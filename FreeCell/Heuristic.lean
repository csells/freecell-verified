import FreeCell.Rules

/-!
# Search-order heuristic

Only the order in which the reference search explores successors depends on
this score; no theorem does. Higher scores are explored first.
-/

namespace FreeCell

/-- Adjacent pairs in a column (exposed card first) that do not form a stack. -/
def breaks : List Card → Nat
  | c :: p :: rest => (if Card.canStack c p then 0 else 1) + breaks (p :: rest)
  | _ => 0

def score (s : State) : Nat :=
  let homeN := s.home.foldl (· + ·) 0
  let freeCells := 4 - s.cells.length
  let emptyCols := (s.cols.filter (·.isEmpty)).length
  let disorder := (s.cols.map breaks).foldl (· + ·) 0
  1000 + 20 * homeN + 6 * freeCells + 12 * emptyCols - 3 * disorder

/-- Successors ordered so that the best-scoring one is last, i.e. pushed last and popped first. -/
def orderedSuccs (s : State) : List (Move × State) :=
  (succs s).mergeSort fun a b => score a.2 ≤ score b.2

theorem mem_orderedSuccs {s : State} {x : Move × State} : x ∈ orderedSuccs s ↔ x ∈ succs s :=
  List.mem_mergeSort

end FreeCell
