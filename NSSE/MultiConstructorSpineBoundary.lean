import NSSE.MultiConstructorSpineRelation

/-! Root aliases obey the same token and ray formulas as fresh spine
positions. Boundary comparisons retain all original root births. -/
namespace NSSE.MultiConstructorSpineBoundary
open MultiConstructorConstraints MultiConstructorTokens MultiConstructorRawTrace MultiConstructorUnifiedWords
open MultiConstructorUnifiedPrefix MultiConstructorSpineInput MultiConstructorSpineInput.Data
open MultiConstructorSpineTags MultiConstructorSpineRelation GeneralCopyGrid
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

theorem old_old (phi : Constraints arity n) (S : Data arity n D) (u v : Fin n) :
    relation phi S (S.old u) (S.old v) ↔ Support phi u v := by
  change relation phi S (encode S (.old u)) (encode S (.old v)) ↔ _
  rw [relation_encode]
  rfl

theorem x_old (phi : Constraints arity n) (S : Data arity n D) (i : Fin (S.word.length+1)) (v : Fin n) :
    relation phi S (S.xAt i) (S.old v) ↔ v ∈ (row phi S.left S.right S.word i.val).1 := by
  by_cases hi : i.val = 0
  · have hx : S.xAt i = S.old S.left := by simp [xAt,hi]
    rw [hx,old_old,hi]
    change Support phi S.left v ↔ v ∈ up phi {S.left}
    simp only [mem_up,Finset.mem_singleton,exists_eq_left]
  · let k : Fin S.word.length := ⟨i.val-1,by have := i.isLt; omega⟩
    have hk : S.after k = i := by apply Fin.ext; change i.val-1+1 = i.val; omega
    rw [← hk]
    change relation phi S (encode S (.x k)) (encode S (.old v)) ↔ _
    rw [relation_encode]
    rfl

theorem old_y (phi : Constraints arity n) (S : Data arity n D) (u : Fin n) (j : Fin (S.word.length+1)) :
    relation phi S (S.old u) (S.yAt j) ↔ u ∈ (row phi S.left S.right S.word j.val).2 := by
  by_cases hj : j.val = 0
  · have hy : S.yAt j = S.old S.right := by simp [yAt,hj]
    rw [hy,old_old,hj]
    change Support phi u S.right ↔ u ∈ down phi {S.right}
    simp only [mem_down,Finset.mem_singleton,exists_eq_left]
  · let k : Fin S.word.length := ⟨j.val-1,by have := j.isLt; omega⟩
    have hk : S.after k = j := by apply Fin.ext; change j.val-1+1 = j.val; omega
    rw [← hk]
    change relation phi S (encode S (.old u)) (encode S (.y k)) ↔ _
    rw [relation_encode]
    rfl

theorem ray_left_zero (phi : Constraints arity n) (S : Data arity n D) (j : Nat) :
    ray phi S 0 j ↔ S.left ∈ (row phi S.left S.right S.word j).2 := by
  constructor
  · intro hr
    obtain ⟨_,a,b,l,ha,hb,hborn,_⟩ := (active_iff_ray _ S.word.length j 0).mp hr
    have ha0 : a = 0 := by omega
    have hl0 : l = 0 := by omega
    subst a; subst l
    have hb0 : b = j := by omega
    subst b
    obtain ⟨v,hu,hl⟩ := hborn
    change v ∈ up phi {S.left} at hu
    obtain ⟨u,hu,hrel⟩ := (mem_up phi {S.left} v).mp hu
    have he : u = S.left := Finset.mem_singleton.mp hu
    subst u
    exact (row_closed phi S.left S.right S.word j).2 v hl S.left hrel
  · intro hl
    exact direct phi S 0 j (Nat.zero_le _) S.left
      ((mem_up phi {S.left} S.left).mpr ⟨S.left,Finset.mem_singleton_self _,.refl _⟩) hl

theorem ray_right_zero (phi : Constraints arity n) (S : Data arity n D) (i : Nat) (hi : i ≤ S.word.length) :
    ray phi S i 0 ↔ S.right ∈ (row phi S.left S.right S.word i).1 := by
  constructor
  · intro hr
    obtain ⟨_,a,b,l,ha,hb,hborn,_⟩ := (active_iff_ray _ S.word.length 0 i).mp hr
    have hb0 : b = 0 := by omega
    have hl0 : l = 0 := by omega
    subst b; subst l
    have ha0 : a = i := by omega
    subst a
    obtain ⟨v,hu,hl⟩ := hborn
    change v ∈ down phi {S.right} at hl
    obtain ⟨u,hu',hrel⟩ := (mem_down phi {S.right} v).mp hl
    have he : u = S.right := Finset.mem_singleton.mp hu'
    subst u
    exact (row_closed phi S.left S.right S.word i).1 v hu S.right hrel
  · intro hu
    exact direct phi S i 0 hi S.right hu
      ((mem_down phi {S.right} S.right).mpr ⟨S.right,Finset.mem_singleton_self _,.refl _⟩)

theorem x_y (phi : Constraints arity n) (S : Data arity n D) (i j : Fin (S.word.length+1)) :
    relation phi S (S.xAt i) (S.yAt j) ↔ ray phi S i.val j.val := by
  by_cases hi : i.val = 0
  · have hx : S.xAt i = S.old S.left := by simp [xAt,hi]
    rw [hx,old_y,hi,ray_left_zero]
  · by_cases hj : j.val = 0
    · have hy : S.yAt j = S.old S.right := by simp [yAt,hj]
      rw [hy,x_old,hj,ray_right_zero phi S i.val (by have := i.isLt; omega)]
    · let a : Fin S.word.length := ⟨i.val-1,by have := i.isLt; omega⟩
      let b : Fin S.word.length := ⟨j.val-1,by have := j.isLt; omega⟩
      have ha : S.after a = i := by apply Fin.ext; change i.val-1+1 = i.val; omega
      have hb : S.after b = j := by apply Fin.ext; change j.val-1+1 = j.val; omega
      rw [← ha,← hb]
      change relation phi S (encode S (.x a)) (encode S (.y b)) ↔ _
      rw [relation_encode]
      rfl

end NSSE.MultiConstructorSpineBoundary
