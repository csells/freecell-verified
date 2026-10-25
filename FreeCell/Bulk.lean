import FreeCell.Cert
import FreeCell.Deal

/-!
# Checking many deals at once

Winning move lists for many Microsoft deals, stored compactly as text and checked by
`checkWin`. A move is two characters: the source (`1`–`8` for a column, or the letter
of the card in a free cell, `cardLetters` indexed by `Card.code`) and the destination
(`h` foundation, `f` free cell, `1`–`8` column). Decoding is unverified and needs no
proof: whatever moves it produces, `checkWin` decides whether they win.
-/

namespace FreeCell

def cardLetters : List Char := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz".toList

def decodeCol (c : Char) : Option Nat :=
  if '1' ≤ c ∧ c ≤ '8' then some (c.toNat - '1'.toNat) else none

def decodeSrc (c : Char) : Option Src :=
  match decodeCol c with
  | some i => some (.col i)
  | none => (cardLetters.idxOf? c).map fun i => .cell (Card.ofCode i)

def decodeDst : Char → Option Dst
  | 'h' => some .home
  | 'f' => some .cell
  | c => (decodeCol c).map .col

def decodeMoves : List Char → Option (List Move)
  | a :: b :: rest => do return ⟨← decodeSrc a, ← decodeDst b⟩ :: (← decodeMoves rest)
  | [] => some []
  | [_] => none

/-- Does the encoded move list win from `start`? -/
def checkWinCode (start : State) (code : String) : Bool :=
  match decodeMoves code.toList with
  | some ms => checkWin start ms
  | none => false

theorem checkWinCode_sound {start : State} {code : String} (h : checkWinCode start code = true) :
    ∃ t, Reachable start t ∧ t.Won := by
  unfold checkWinCode at h
  split at h
  · exact checkWin_sound h
  · simp at h

/-- `data` holds `count` lines, an encoded winning move list for each of the deals
`lo, lo + 1, …`; the lines for deals in `skip` are not checked. -/
def checkDealChunk (lo count : Nat) (skip : List Nat) (data : String) : Bool :=
  let lines := data.splitOn "\n"
  lines.length == count &&
    (List.range count).all fun k => skip.contains (lo + k) || checkWinCode (msDeal (lo + k)) (lines.getD k "")

theorem checkDealChunk_sound {lo count : Nat} {skip : List Nat} {data : String}
    (h : checkDealChunk lo count skip data = true) :
    ∀ n, lo ≤ n → n < lo + count → n ∉ skip → ∃ t, Reachable (msDeal n) t ∧ t.Won := by
  intro n h1 h2 h3
  simp only [checkDealChunk, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true] at h
  obtain ⟨-, h⟩ := h
  have hk := h (n - lo) (by omega)
  rw [Nat.add_sub_cancel' h1] at hk
  rcases hk with hk | hk
  · exact absurd (List.elem_iff.mp hk) h3
  · exact checkWinCode_sound hk

end FreeCell
