import NSSE.P0DDeadColor
import NSSE.P0ComparisonRecurrence

/-! Turn the actual reader suffix graph into a finite family of decorated
words. Comparing two decorations splits by head (join), then literal letter
(union), and recurses on tails. The representation is proved exact. -/
namespace NSSE.P0SuffixWords
open P0DDeadReader P0DDeadTrace P0CutComparison P0ComparisonRecurrence
variable {Q A H : Type*}

def Rel (endX endY : H) : List (H × A) → List (H × A) → Prop
  | [], [] => endX = endY
  | [], (h,_)::_ => endX = h
  | (h,_)::_, [] => h = endY
  | (h,a)::s, (k,b)::t => h = k ∧ (a = b → Rel endX endY s t)

def decorate (J : Reader Q A H) (w : List A) : List (H × A) :=
  List.ofFn (fun k : Fin w.length => (leftAt J w k,w[k.val]))

@[simp] theorem decorate_length (J : Reader Q A H) (w : List A) :
    (decorate J w).length = w.length := by simp [decorate]

theorem decorate_drop (J : Reader Q A H) (w : List A) (k : Nat) (hk : k < w.length) :
    (decorate J w).drop k = (leftAt J w k,w[k]) :: (decorate J w).drop (k+1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hk)]
  simp only [decorate,List.getElem_ofFn]

theorem proper_heads (J : Reader Q A H) (w : List A) (hc : Complete J w)
    (k : Nat) (hk : k < w.length) : leftAt J w k = rightAt J w k := by
  obtain ⟨q,hq⟩ := trace_proper J w hc k hk
  unfold leftAt rightAt
  rw [hq]

theorem terminal_heads (J : Reader Q A H) (w : List A) (hc : Complete J w) :
    leftAt J w w.length = J.endX ∧ rightAt J w w.length = J.endY := by
  unfold leftAt rightAt
  rw [complete_trace J w hc]
  exact ⟨rfl,rfl⟩

theorem suffix_exact (J : Reader Q A H) (w : List A) (hc : Complete J w)
    (a b : Nat) (ha : a ≤ w.length) (hb : b ≤ w.length) :
    Compatible w (leftAt J w) (rightAt J w) a b ↔
      Rel J.endX J.endY ((decorate J w).drop a) ((decorate J w).drop b) := by
  have hmain : ∀ d a b, w.length-a = d → a ≤ w.length → b ≤ w.length →
      (Compatible w (leftAt J w) (rightAt J w) a b ↔
        Rel J.endX J.endY ((decorate J w).drop a) ((decorate J w).drop b)) := by
    intro d
    induction d with
    | zero =>
      intro a b hd ha hb
      have hea : a = w.length := by omega
      subst a
      rw [end_left w (leftAt J w) (rightAt J w) b hb,(terminal_heads J w hc).1]
      have hdrop : (decorate J w).drop w.length = [] := by
        exact List.drop_eq_nil_of_le (by simp)
      rw [hdrop]
      by_cases heb : b = w.length
      · rw [heb,hdrop,Rel,(terminal_heads J w hc).2]
      · rw [decorate_drop J w b (by omega),Rel,proper_heads J w hc b (by omega)]
    | succ d ih =>
      intro a b hd ha hb
      have hal : a < w.length := by omega
      rw [decorate_drop J w a hal]
      by_cases heb : b = w.length
      · subst b
        have hdrop : (decorate J w).drop w.length = [] := by
          exact List.drop_eq_nil_of_le (by simp)
        rw [hdrop,Rel,end_right w (leftAt J w) (rightAt J w) a ha,(terminal_heads J w hc).2]
      · have hbl : b < w.length := by omega
        rw [decorate_drop J w b hbl,Rel,step_iff w (leftAt J w) (rightAt J w) a b hal hbl,
          ← proper_heads J w hc b hbl,List.getElem?_eq_getElem hal,List.getElem?_eq_getElem hbl,
          Option.some.injEq,ih (a+1) (b+1) (by omega) (by omega) (by omega)]
  exact hmain (w.length-a) a b rfl ha hb

def tailWord (J : Reader Q A H) (w : List A) (k : Fin (w.length+1)) : List (H × A) :=
  (decorate J w).drop k.val

theorem tailWord_injective (J : Reader Q A H) (w : List A) : Function.Injective (tailWord J w) := by
  intro a b he
  have hlen := congrArg List.length he
  simp only [tailWord,List.length_drop,decorate_length] at hlen
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  omega

theorem tailWord_exact (J : Reader Q A H) (w : List A) (hc : Complete J w)
    (a b : Fin (w.length+1)) :
    Compatible w (leftAt J w) (rightAt J w) a b ↔ Rel J.endX J.endY (tailWord J w a) (tailWord J w b) :=
  suffix_exact J w hc a b (by have := a.isLt; omega) (by have := b.isLt; omega)

end NSSE.P0SuffixWords
