import NSSE.MultiConstructorUnifiedWords

/-! Every actual compiled branch assignment yields the selector-independent
unified witness with its computed finite proper-head array. -/
namespace NSSE.MultiConstructorUnifiedBranch
open MultiConstructorConstraints MultiConstructorTokens MultiConstructorRawTrace
open MultiConstructorBranch MultiConstructorBranchTrace MultiConstructorBranchLocal
open MultiConstructorUnifiedWords
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

theorem walk_raw (C : Parameters arity n) (s : State n) (w : List (Fin D)) :
    (walk C s w).1 = rawWord C s.1 w := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => exact ih (successor C s a.val)

def selectedHeads (C : Parameters arity n) (w : List (Fin D)) (k : Fin w.length) : H :=
  output C (walk C (branch C D).initial (w.take k.val))

theorem value_eq (C : Parameters arity n) (w : List (Fin D)) (s : Bool) (k : Nat) :
    value w (selectedHeads C w) C.endX C.endY s k = MultiConstructorBranchAssignment.value C w s k := by
  by_cases hk : k < w.length
  · rw [value,dif_pos hk,MultiConstructorBranchAssignment.value,if_pos hk]
    rfl
  · rw [value,dif_neg hk,MultiConstructorBranchAssignment.value,if_neg hk]

theorem assignment_sound (C : Parameters arity n) (w : List (Fin D))
    (ha : MultiConstructorBranchAssignment.Assignment C w) :
    Assignment C.input C.left C.right w (selectedHeads C w) C.endX C.endY := by
  refine ⟨?_,?_,?_⟩
  · intro k
    have hg := local_guard C w (branch C D).initial ha.1 k.val k.isLt
    have he : (walk C (branch C D).initial (w.take k.val)).1 =
        row C.input C.left C.right w k.val := walk_raw C _ _
    refine ⟨?_,?_,hg.2⟩
    · rw [← he]
      exact hg.1.1
    · rw [← he]
      exact hg.1.2.2
  · change EndValid C (rawWord C (initial C.input C.left C.right) (w.take w.length))
    rw [List.take_length]
    exact local_end C w (branch C D).initial ha.1
  · intro a b l hb hal hbl hm
    rw [value_eq,value_eq]
    exact ha.2 a.val (by have := a.isLt; omega) b.val (by have := b.isLt; omega) hb
      l.val (by have := l.isLt; omega) hal hbl hm

theorem accepted_witness (C : Parameters arity n) (w : List (Fin D))
    (ha : P0DZBranch.Accepted (branch C D) w) : Witness C.input C.left C.right w :=
  ⟨selectedHeads C w,C.endX,C.endY,
    assignment_sound C w ((MultiConstructorBranchAssignment.accepted_iff C w).mp ha)⟩

theorem no_diagonal (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (ex ey : MultiConstructorTrees.Label H)
    (ha : Assignment phi x y w heads ex ey) (a : Nat) (han : a ≤ w.length) :
    ¬Born phi x y w a a := by
  intro hb
  have hh := ha.2.2 ⟨a,by omega⟩ ⟨a,by omega⟩ ⟨w.length-a,by omega⟩ hb
    (by simp; omega) (by simp; omega) (fun _ _ => rfl)
  have he : P0DZBranch.Agree ex ey := by
    simpa only [show a+(w.length-a) = w.length by omega,value,lt_self_iff_false,dif_neg,if_true,if_false]
      using hh
  exact ha.2.1.2.2.2 (P0DZTrace.agree_eq he)

theorem self_query_no_witness (phi : Constraints arity n) (x : Fin n) (w : List (Fin D)) :
    ¬Witness phi x x w := by
  rintro ⟨heads,ex,ey,ha⟩
  apply no_diagonal phi x x w heads ex ey ha 0 (by omega)
  change ∃ u ∈ up phi {x}, ∃ v ∈ down phi {x}, Support phi u v
  exact ⟨x,(mem_up phi {x} x).mpr ⟨x,Finset.mem_singleton_self _,.refl x⟩,
    x,(mem_down phi {x} x).mpr ⟨x,Finset.mem_singleton_self _,.refl x⟩,.refl x⟩

end NSSE.MultiConstructorUnifiedBranch
