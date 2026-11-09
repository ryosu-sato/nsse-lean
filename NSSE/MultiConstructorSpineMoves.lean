import NSSE.MultiConstructorSpineBoundary

/-! Child propagation and filler comparisons in the concrete support
certificate. No assignment or satisfiability assumption is needed. -/
namespace NSSE.MultiConstructorSpineMoves
open MultiConstructorConstraints MultiConstructorTokens MultiConstructorRawTrace MultiConstructorUnifiedWords
open MultiConstructorUnifiedPrefix MultiConstructorSpineInput MultiConstructorSpineInput.Data
open MultiConstructorSpineTags MultiConstructorSpineRelation MultiConstructorSpineBoundary GeneralCopyGrid
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

theorem bot_any (phi : Constraints arity n) (S : Data arity n D) (v : Fin S.size) :
    relation phi S S.botVar v := by
  change relationTag phi S (decode S (encode S .bot)) (decode S v)
  rw [decode_encode]
  cases decode S v <;> trivial

theorem any_top (phi : Constraints arity n) (S : Data arity n D) (v : Fin S.size) :
    relation phi S v S.topVar := by
  change relationTag phi S (decode S v) (decode S (encode S .top))
  rw [decode_encode]
  cases decode S v <;> trivial

theorem ray_step (phi : Constraints arity n) (S : Data arity n D) (i j : Fin S.word.length)
    (he : S.word[i.val] = S.word[j.val]) (hr : ray phi S i.val j.val) :
    ray phi S (i.val+1) (j.val+1) := by
  change Active _ _ (j.val+1) (i.val+1)
  refine ⟨by have := i.isLt; omega,Or.inr ⟨i.val,hr,i.isLt,rfl,?_⟩⟩
  change S.word[i.val]? = S.word[j.val]?
  simp only [List.getElem?_eq_getElem i.isLt,List.getElem?_eq_getElem j.isLt,he]

theorem x_step_old (phi : Constraints arity n) (S : Data arity n D) (k : Fin S.word.length)
    (b : Bound arity n) (hb : b ∈ phi.upper) (i : Fin (arity b.head))
    (hi : i.val = S.word[k.val].val) (hr : relation phi S (S.xAt (S.here k)) (S.old b.parent)) :
    relation phi S (S.xAt (S.after k)) (S.old (b.children i)) := by
  apply (x_old phi S _ _).mpr
  change b.children i ∈ (row phi S.left S.right S.word (k.val+1)).1
  rw [row_succ phi S.left S.right S.word k.val k.isLt]
  apply (mem_upperNext phi _ _ _).mpr
  exact ⟨b,hb,⟨b.parent,(x_old phi S _ _).mp hr,.refl _⟩,i,hi,.refl _⟩

theorem old_step_y (phi : Constraints arity n) (S : Data arity n D) (k : Fin S.word.length)
    (a : Bound arity n) (ha : a ∈ phi.lower) (i : Fin (arity a.head))
    (hi : i.val = S.word[k.val].val) (hr : relation phi S (S.old a.parent) (S.yAt (S.here k))) :
    relation phi S (S.old (a.children i)) (S.yAt (S.after k)) := by
  apply (old_y phi S _ _).mpr
  change a.children i ∈ (row phi S.left S.right S.word (k.val+1)).2
  rw [row_succ phi S.left S.right S.word k.val k.isLt]
  apply (mem_lowerNext phi _ _ _).mpr
  exact ⟨a,ha,⟨a.parent,(old_y phi S _ _).mp hr,.refl _⟩,i,hi,.refl _⟩

theorem x_step_y (phi : Constraints arity n) (S : Data arity n D) (i j : Fin S.word.length)
    (he : S.word[i.val] = S.word[j.val])
    (hr : relation phi S (S.xAt (S.here i)) (S.yAt (S.here j))) :
    relation phi S (S.xAt (S.after i)) (S.yAt (S.after j)) :=
  (x_y phi S _ _).mpr (ray_step phi S i j he ((x_y phi S _ _).mp hr))

end NSSE.MultiConstructorSpineMoves
