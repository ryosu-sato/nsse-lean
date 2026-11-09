import NSSE.MultiConstructorSpineMoves
import NSSE.MultiConstructorSpineMembership

/-! The support of the concrete one-sided extension is contained in the
original token/ray certificate. In particular, original-variable support
does not grow. This theorem needs no successful assignment premise. -/
namespace NSSE.MultiConstructorSpineClosure
open MultiConstructorConstraints MultiConstructorSpineInput MultiConstructorSpineInput.Data
open MultiConstructorSpineRelation MultiConstructorSpineBoundary MultiConstructorSpineMoves
open MultiConstructorSpineMembership MultiConstructorInputMap
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

omit [DecidableEq H] in
theorem original_decomp (phi : Constraints arity n) (a b : Bound arity n)
    (ha : a ∈ phi.lower) (hb : b ∈ phi.upper) (hh : a.head = b.head)
    (hr : Support phi a.parent b.parent) (i : Fin (arity a.head)) (j : Fin (arity b.head))
    (he : i.val = j.val) : Support phi (a.children i) (b.children j) := by
  cases a with | mk x h ac =>
    cases b with | mk y k bc =>
      dsimp only at hh hr i j he ⊢
      subst k
      have hij : i = j := Fin.ext he
      subst j
      exact Support.decomp ha hb hr i

theorem decomp (phi : Constraints arity n) (S : Data arity n D) (a b : Bound arity S.size)
    (ha : a ∈ (S.program phi).lower) (hb : b ∈ (S.program phi).upper) (hh : a.head = b.head)
    (hr : relation phi S a.parent b.parent) (i : Fin (arity a.head)) (j : Fin (arity b.head))
    (he : i.val = j.val) : relation phi S (a.children i) (b.children j) := by
  rcases lower_cases phi S a ha with ⟨a,hoa,rfl⟩ | ⟨k,rfl⟩ | ⟨h,_,rfl⟩
  · rcases upper_cases phi S b hb with ⟨b,hob,rfl⟩ | ⟨k,rfl⟩ | ⟨h,_,rfl⟩
    · exact (old_old phi S _ _).mpr
        (original_decomp phi a b hoa hob hh ((old_old phi S _ _).mp hr) i j he)
    · change relation phi S (S.old (a.children i))
        (if j.val = S.word[k.val].val then S.yAt (S.after k) else S.topVar)
      split_ifs with hj
      · exact old_step_y phi S k a hoa i (he.trans hj) hr
      · exact any_top phi S _
    · exact any_top phi S _
  · rcases upper_cases phi S b hb with ⟨b,hob,rfl⟩ | ⟨l,rfl⟩ | ⟨h,_,rfl⟩
    · change relation phi S
        (if i.val = S.word[k.val].val then S.xAt (S.after k) else S.botVar) (S.old (b.children j))
      split_ifs with hi
      · exact x_step_old phi S k b hob j (he.symm.trans hi) hr
      · exact bot_any phi S _
    · change relation phi S
        (if i.val = S.word[k.val].val then S.xAt (S.after k) else S.botVar)
        (if j.val = S.word[l.val].val then S.yAt (S.after l) else S.topVar)
      split_ifs with hi hj hj
      · exact x_step_y phi S k l (Fin.ext (hi.symm.trans (he.trans hj))) hr
      · exact any_top phi S _
      · exact bot_any phi S _
      · exact bot_any phi S _
    · exact any_top phi S _
  · exact bot_any phi S _

theorem support (phi : Constraints arity n) (S : Data arity n D) (a b : Fin S.size)
    (hs : Support (S.program phi) a b) : relation phi S a b := by
  induction hs with
  | refl a => exact MultiConstructorSpineRelation.refl phi S a
  | trans _ _ hab hbc => exact MultiConstructorSpineRelation.trans phi S _ _ _ hab hbc
  | @decomp h x y a b hl hu _ i ih =>
    exact decomp phi S ⟨x,h,a⟩ ⟨y,h,b⟩ hl hu rfl ih i i rfl

theorem old_support (phi : Constraints arity n) (S : Data arity n D) (a b : Fin n)
    (hs : Support (S.program phi) (S.old a) (S.old b)) : Support phi a b :=
  (old_old phi S a b).mp (support phi S _ _ hs)

omit [DecidableEq H] in
theorem lift_support (phi : Constraints arity n) (S : Data arity n D) (a b : Fin n)
    (hs : Support phi a b) : Support (S.program phi) (S.old a) (S.old b) := by
  induction hs with
  | refl a => exact Support.refl _
  | trans _ _ hab hbc => exact Support.trans hab hbc
  | @decomp h x y a b hl hu _ i ih =>
    apply Support.decomp (h := h) (a := fun k => S.old (a k)) (b := fun k => S.old (b k)) ?_ ?_ ih i
    · exact List.mem_append_left _ (List.mem_map_of_mem hl)
    · exact List.mem_append_left _ (List.mem_map_of_mem hu)

theorem old_support_iff (phi : Constraints arity n) (S : Data arity n D) (a b : Fin n) :
    Support (S.program phi) (S.old a) (S.old b) ↔ Support phi a b :=
  ⟨old_support phi S a b,lift_support phi S a b⟩

end NSSE.MultiConstructorSpineClosure
