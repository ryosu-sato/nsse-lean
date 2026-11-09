import NSSE.P0SuffixConflict
import NSSE.P0CutComparison

/-! Symmetry and the equality presentation of four-rail comparisons at
distinct origins. The latter uses actual completeness: two distinct
origins cannot both be terminal at a common offset. -/
namespace NSSE.P0DZRelations
open P0DZBranch P0DZTrace P0SuffixConflict P0ProperWords
variable {Q Z A H : Type*}

theorem agree_symm {x y : MultiConstructorTrees.Label H} (h : Agree x y) : Agree y x := by
  cases x <;> cases y <;> simp_all [Agree,eq_comm]

theorem compatible_symm (J : Branch Q Z A H) (w : List A) (a b : Nat) (s t : Bool)
    (h : Compatible J w a s b t) : Compatible J w b t a s := by
  intro l hl hb ha hm
  exact agree_symm (h l hl ha hb (fun k hk => (hm k hk).symm))

theorem all_symm (J : Branch Q Z A H) (w : List A) (a b : Nat)
    (h : AllCompatible J w a b) : AllCompatible J w b a :=
  fun s t => compatible_symm J w a b t s (h t s)

theorem label_rails (J : Branch Q Z A H) (w : List A) (k : Nat) (hk : k < w.length)
    (s t : Bool) : labelAt J w s k = labelAt J w t k := by
  unfold labelAt
  rw [proper_state J w k hk]
  cases properFrom J J.initial (w.take k) <;> rfl

theorem agree_iff_eq (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (a b : Nat) (ha : a ≤ w.length) (hb : b ≤ w.length) (hne : a ≠ b) (s t : Bool) :
    Agree (labelAt J w s a) (labelAt J w t b) ↔ labelAt J w s a = labelAt J w t b := by
  refine ⟨agree_eq,?_⟩
  intro he
  by_cases hap : a < w.length
  · obtain ⟨q,hq⟩ := complete_prefix J w hc a hap
    rw [label_proper J w a hap q hq s] at he ⊢
    rw [← he]
    rfl
  · have hbp : b < w.length := by omega
    obtain ⟨q,hq⟩ := complete_prefix J w hc b hbp
    rw [label_proper J w b hbp q hq t] at he ⊢
    rw [he]
    rfl

theorem comparison_eq (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (a b : Nat) (hne : a ≠ b) (s t : Bool) :
    Compatible J w a s b t ↔
      P0CutComparison.Compatible w (labelAt J w s) (labelAt J w t) a b := by
  constructor
  · intro h l hl ha hb hm
    exact agree_eq (h l hl ha hb hm)
  · intro h l hl ha hb hm
    exact (agree_iff_eq J w hc (a+l) (b+l) ha hb (by omega) s t).mpr (h l hl ha hb hm)

theorem diagonal_conflict (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (hends : J.endX ≠ J.endY) (a : Nat) (ha : a ≤ w.length) : ¬ AllCompatible J w a a := by
  intro h
  have hh := h false true (w.length-a) (by omega) (by omega) (by omega) (fun _ _ => rfl)
  rw [show a+(w.length-a) = w.length by omega,label_terminal J w hc false,
    label_terminal J w hc true] at hh
  exact hends (agree_eq hh)

end NSSE.P0DZRelations
