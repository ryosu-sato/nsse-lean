import NSSE.MultiConstructorUnifiedBranch

/-! Exact restriction of original token rows, proper heads and literal
factor matches to a finite prefix. Terminal choices are handled separately. -/
namespace NSSE.MultiConstructorUnifiedPrefix
open MultiConstructorConstraints MultiConstructorTokens MultiConstructorRawTrace
open MultiConstructorUnifiedWords P0ProperWords
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

theorem row_prefix (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (m k : Nat) (hk : k ≤ m) : row phi x y (w.take m) k = row phi x y w k := by
  simp only [row,List.take_take,Nat.min_eq_left hk]

theorem row_succ (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (k : Nat) (hk : k < w.length) :
    row phi x y w (k+1) = step phi (row phi x y w k) w[k].val := by
  simp only [row,List.take_succ_eq_append_getElem hk,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem fold_closed (phi : Constraints arity n) (s : Row n) (w : List (Fin D))
    (hs : UpperClosed phi s.1 ∧ LowerClosed phi s.2) :
    let t := w.foldl (fun s i => step phi s i.val) s
    UpperClosed phi t.1 ∧ LowerClosed phi t.2 := by
  induction w generalizing s with
  | nil => exact hs
  | cons a w ih => exact ih (step phi s a.val) ⟨upperNext_closed _ _ _,lowerNext_closed _ _ _⟩

theorem row_closed (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D)) (k : Nat) :
    UpperClosed phi (row phi x y w k).1 ∧ LowerClosed phi (row phi x y w k).2 :=
  fold_closed phi (initial phi x y) (w.take k) ⟨up_closed _ _,down_closed _ _⟩

theorem match_prefix (w : List (Fin D)) (m a b l : Nat) (ha : a+l ≤ m) (hb : b+l ≤ m) :
    WordMatch (w.take m) a b l ↔ WordMatch w a b l := by
  unfold WordMatch
  have he (i : Nat) (hi : i < l) :
      (w.take m)[a+i]? = w[a+i]? ∧ (w.take m)[b+i]? = w[b+i]? :=
    ⟨List.getElem?_take_of_lt (by omega),List.getElem?_take_of_lt (by omega)⟩
  exact ⟨fun h i hi => by simpa only [(he i hi).1,(he i hi).2] using h i hi,
    fun h i hi => by simpa only [(he i hi).1,(he i hi).2] using h i hi⟩

def restrictHeads (w : List (Fin D)) (heads : Fin w.length → H) (m : Nat)
    (k : Fin (w.take m).length) : H :=
  heads ⟨k.val,by have := k.isLt; simp only [List.length_take] at this; omega⟩

theorem local_restrict (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (m : Nat) (hl : Local phi x y w heads) :
    Local phi x y (w.take m) (restrictHeads w heads m) := by
  intro k
  have hkm : k.val < m := by have := k.isLt; simp only [List.length_take] at this; omega
  have hkn : k.val < w.length := by have := k.isLt; simp only [List.length_take] at this; omega
  have h := hl ⟨k.val,hkn⟩
  rw [row_prefix phi x y w m k.val (by omega)]
  simpa only [restrictHeads,List.getElem_take] using h

omit [DecidableEq H] in
theorem value_restrict (w : List (Fin D)) (heads : Fin w.length → H) (m k : Nat)
    (hm : m ≤ w.length) (hk : k < m) (ex ey ex' ey' : MultiConstructorTrees.Label H) (s : Bool) :
    value (w.take m) (restrictHeads w heads m) ex' ey' s k = value w heads ex ey s k := by
  rw [value,dif_pos (by simp only [List.length_take,Nat.min_eq_left hm]; exact hk),
    value,dif_pos (by omega)]
  rfl

theorem born_prefix (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (m a b : Nat) (ha : a ≤ m) (hb : b ≤ m) :
    Born phi x y (w.take m) a b ↔ Born phi x y w a b := by
  simp only [Born,row_prefix phi x y w m a ha,row_prefix phi x y w m b hb]

end NSSE.MultiConstructorUnifiedPrefix
