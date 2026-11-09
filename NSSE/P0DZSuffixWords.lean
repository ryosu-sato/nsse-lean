import NSSE.P0DZRelations
import NSSE.P0FourRailOrientation

/-! An exact decorated-word presentation of actual D/Z comparisons at
distinct positions, for every rail pair. The full symmetric conflict
graph equals the ordinary suffix graph with the two branch endpoints. -/
namespace NSSE.P0DZSuffixWords
open P0DZBranch P0DZTrace P0DZRelations P0SuffixConflict
open P0SuffixWords P0SuffixCotree P0ComparisonRecurrence
variable {Q Z A H : Type*}

def decorate (J : Branch Q Z A H) (w : List A) : List (MultiConstructorTrees.Label H × A) :=
  List.ofFn (fun k : Fin w.length => (labelAt J w false k,w[k.val]))

@[simp] theorem decorate_length (J : Branch Q Z A H) (w : List A) :
    (decorate J w).length = w.length := by simp [decorate]

theorem decorate_drop (J : Branch Q Z A H) (w : List A) (k : Nat) (hk : k < w.length) :
    (decorate J w).drop k = (labelAt J w false k,w[k]) :: (decorate J w).drop (k+1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hk)]
  simp only [decorate,List.getElem_ofFn]

theorem equality_suffix_exact (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (a b : Nat) (ha : a ≤ w.length) (hb : b ≤ w.length) (s t : Bool) :
    P0CutComparison.Compatible w (labelAt J w s) (labelAt J w t) a b ↔
      Rel (endpoint J s) (endpoint J t) ((decorate J w).drop a) ((decorate J w).drop b) := by
  have hmain : ∀ d a b, w.length-a = d → a ≤ w.length → b ≤ w.length →
      (P0CutComparison.Compatible w (labelAt J w s) (labelAt J w t) a b ↔
        Rel (endpoint J s) (endpoint J t) ((decorate J w).drop a) ((decorate J w).drop b)) := by
    intro d
    induction d with
    | zero =>
      intro a b hd ha hb
      have hea : a = w.length := by omega
      subst a
      rw [end_left w (labelAt J w s) (labelAt J w t) b hb,label_terminal J w hc s]
      have hdrop : (decorate J w).drop w.length = [] := List.drop_eq_nil_of_le (by simp)
      rw [hdrop]
      by_cases heb : b = w.length
      · rw [heb,hdrop,P0SuffixWords.Rel,label_terminal J w hc t]
      · rw [decorate_drop J w b (by omega),P0SuffixWords.Rel,label_rails J w b (by omega) t false]
    | succ d ih =>
      intro a b hd ha hb
      have hal : a < w.length := by omega
      rw [decorate_drop J w a hal]
      by_cases heb : b = w.length
      · subst b
        have hdrop : (decorate J w).drop w.length = [] := List.drop_eq_nil_of_le (by simp)
        rw [hdrop,P0SuffixWords.Rel,end_right w (labelAt J w s) (labelAt J w t) a ha,
          label_terminal J w hc t,label_rails J w a hal s false]
      · have hbl : b < w.length := by omega
        rw [decorate_drop J w b hbl,P0SuffixWords.Rel,
          step_iff w (labelAt J w s) (labelAt J w t) a b hal hbl,
          label_rails J w a hal s false,label_rails J w b hbl t false,
          List.getElem?_eq_getElem hal,List.getElem?_eq_getElem hbl,Option.some.injEq,
          ih (a+1) (b+1) (by omega) (by omega) (by omega)]
  exact hmain (w.length-a) a b rfl ha hb

theorem suffix_exact (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (a b : Nat) (ha : a ≤ w.length) (hb : b ≤ w.length) (hne : a ≠ b) (s t : Bool) :
    Compatible J w a s b t ↔
      Rel (endpoint J s) (endpoint J t) ((decorate J w).drop a) ((decorate J w).drop b) := by
  rw [comparison_eq J w hc a b hne s t,equality_suffix_exact J w hc a b ha hb s t]

def Adjacent (J : Branch Q Z A H) (w : List A) (a b : Nat) : Prop := ¬ AllCompatible J w a b

theorem edge_exact (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (hends : J.endX ≠ J.endY) (a b : Nat) (ha : a ≤ w.length) (hb : b ≤ w.length) :
    Adjacent J w a b ↔ Edge J.endX J.endY ((decorate J w).drop a) ((decorate J w).drop b) := by
  by_cases hab : a = b
  · subst b
    simp only [Adjacent,diagonal_conflict J w hc hends a ha,Edge,
      P0FourRailOrientation.rel_self,hends,not_false_eq_true,or_self]
  · constructor
    · intro hn
      by_contra hne
      apply hn
      intro s t
      exact (suffix_exact J w hc a b ha hb hab s t).mpr
        (P0FourRailOrientation.nonedge_any J.endX J.endY hends _ _ hne (endpoint J s) (endpoint J t))
    · intro he hall
      rcases he with h | h
      · exact h ((suffix_exact J w hc a b ha hb hab false true).mp (hall false true))
      · exact h ((suffix_exact J w hc b a hb ha (Ne.symm hab) false true).mp
          (compatible_symm J w a b true false (hall true false)))

end NSSE.P0DZSuffixWords
