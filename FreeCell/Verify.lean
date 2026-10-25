import FreeCell.Codec

/-!
# Certificates

A certificate names its format, rule set and starting position, then gives
either a winning move list or a closed set of positions:

    freecell-verified certificate v1
    rules: standard-freecell/single-card/4-cells/v1
    start: <compact position>
    winnable: <n>                       or   unwinnable: <n>
    <n move lines>                           <n compact positions>

`verifyCertificate start text` checks a certificate against the position the
caller requested, not the one the file claims. `verifyCertificate_winnable` and
`verifyCertificate_unwinnable` state what an accepted certificate proves.
-/

namespace FreeCell

open Std

def certFormat : String := "freecell-verified certificate v1"
def rulesId : String := "standard-freecell/single-card/4-cells/v1"

inductive Verdict where
  | winnable
  | unwinnable
deriving DecidableEq, Repr

inductive CertBody where
  | win (moves : List Move)
  | lose (positions : List State)

structure Certificate where
  start : State
  body : CertBody

def Outcome.toCertificate {start : State} : Outcome start → Certificate
  | .win ms _ => ⟨start, .win ms⟩
  | .lose c _ => ⟨start, .lose c.toList⟩

def writeCertificate (c : Certificate) : String :=
  let header := [certFormat, s!"rules: {rulesId}", s!"start: {showCompact c.start}"]
  let body := match c.body with
    | .win ms => s!"winnable: {ms.length}" :: ms.map showMove
    | .lose ss => s!"unwinnable: {ss.length}" :: ss.map showCompact
  String.intercalate "\n" (header ++ body) ++ "\n"

def expectLine (expected : String) : Option String → Except String Unit
  | some l => if l = expected then .ok () else .error s!"expected '{expected}', found '{l}'"
  | none => .error s!"missing line '{expected}'"

def parseCertificate (text : String) : Except String Certificate := do
  let lines := (text.split (· == '\n')).toList.map (fun l => l.toString.trimAscii.toString)
    |>.filter (· ≠ "")
  match lines with
  | fmt :: rules :: start :: kind :: rest =>
    expectLine certFormat (some fmt)
    expectLine s!"rules: {rulesId}" (some rules)
    unless start.startsWith "start: " do throw "missing start line"
    let s ← parseCompact (start.drop "start: ".length).toString
    let count (pfx : String) : Except String Nat :=
      match (kind.drop pfx.length).toString.toNat? with
      | some n => if n = rest.length then .ok n else
          .error s!"certificate declares {n} entries but contains {rest.length}"
      | none => .error "malformed entry count"
    if kind.startsWith "winnable: " then
      let _ ← count "winnable: "
      return ⟨s, .win (← rest.mapM parseMove)⟩
    else if kind.startsWith "unwinnable: " then
      let _ ← count "unwinnable: "
      return ⟨s, .lose (← rest.mapM parseCompact)⟩
    else throw "certificate must declare 'winnable:' or 'unwinnable:'"
  | _ => throw "truncated certificate header"

/-- Check certificate evidence against `start` itself. -/
def verifyBody (start : State) : CertBody → Except String Verdict
  | .win ms =>
    if checkWin start ms then .ok .winnable
    else .error "move list is illegal or does not end in a won position"
  | .lose ss =>
    if checkClosed start (HashSet.ofList ss) then .ok .unwinnable
    else .error "position set is not a closed, win-free set containing the start"

def verifyCertificate (start : State) (text : String) : Except String Verdict :=
  match parseCertificate text with
  | .error e => .error e
  | .ok c =>
    if c.start = start then verifyBody start c.body
    else .error "certificate is for a different starting position"

theorem verifyBody_sound {start : State} {b : CertBody} {v : Verdict}
    (h : verifyBody start b = .ok v) :
    (v = .winnable → ∃ t, Reachable start t ∧ t.Won) ∧
      (v = .unwinnable → ¬ ∃ t, Reachable start t ∧ t.Won) := by
  cases b with
  | win ms =>
    simp only [verifyBody] at h
    split at h
    · rename_i hc
      simp only [Except.ok.injEq] at h; subst h
      exact ⟨fun _ => checkWin_sound hc, fun e => (by cases e)⟩
    · cases h
  | lose ss =>
    simp only [verifyBody] at h
    split at h
    · rename_i hc
      simp only [Except.ok.injEq] at h; subst h
      exact ⟨fun e => (by cases e), fun _ => not_winnable_of_checkClosed hc⟩
    · cases h

/-- An accepted winnable certificate proves `start` winnable, whatever the text contained. -/
theorem verifyCertificate_winnable {start : State} {text : String}
    (h : verifyCertificate start text = .ok .winnable) : ∃ t, Reachable start t ∧ t.Won := by
  unfold verifyCertificate at h
  split at h
  · cases h
  · split at h
    · exact (verifyBody_sound h).1 rfl
    · cases h

/-- An accepted unwinnable certificate proves `start` unwinnable, whatever the text contained. -/
theorem verifyCertificate_unwinnable {start : State} {text : String}
    (h : verifyCertificate start text = .ok .unwinnable) : ¬ ∃ t, Reachable start t ∧ t.Won := by
  unfold verifyCertificate at h
  split at h
  · cases h
  · split at h
    · exact (verifyBody_sound h).2 rfl
    · cases h

end FreeCell
