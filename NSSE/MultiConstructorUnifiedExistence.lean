import NSSE.MultiConstructorUnifiedBound
import NSSE.P0BoundedWords

/-! Total original U-word existence by a proved input-only finite bound.
This is the token/word theorem; original model correspondence is separate. -/
namespace NSSE.MultiConstructorUnifiedExistence
open MultiConstructorConstraints MultiConstructorUnifiedWords MultiConstructorUnifiedBound
variable {H : Type*} [DecidableEq H] [Fintype H] {arity : H → Nat} {n : Nat}

def candidates (phi : Constraints arity n) (x y : Fin n) (D : Nat) : Finset (List (Fin D)) :=
  (P0BoundedWords.words Finset.univ (bound n D)).filter (fun w => inspect phi x y w = true)

theorem mem_candidates (phi : Constraints arity n) (x y : Fin n) (D : Nat) (w : List (Fin D)) :
    w ∈ candidates phi x y D ↔ Witness phi x y w ∧ w.length ≤ bound n D := by
  simp only [candidates,Finset.mem_filter,P0BoundedWords.mem_words,Finset.mem_univ,
    implies_true,forall_const,and_true,inspect_correct]
  exact and_comm

def decideExists (phi : Constraints arity n) (x y : Fin n) (D : Nat) : Bool :=
  decide (candidates phi x y D).Nonempty

theorem decideExists_correct (phi : Constraints arity n) (x y : Fin n) (D : Nat) :
    decideExists phi x y D = true ↔ ∃ w : List (Fin D), Witness phi x y w := by
  simp only [decideExists,decide_eq_true_eq,Finset.Nonempty,mem_candidates]
  exact (bounded_iff phi x y).symm

def existenceDecision (phi : Constraints arity n) (x y : Fin n) (D : Nat) :
    Decidable (∃ w : List (Fin D), Witness phi x y w) :=
  decidable_of_iff (decideExists phi x y D = true) (decideExists_correct phi x y D)

theorem decideExists_false (phi : Constraints arity n) (x y : Fin n) (D : Nat) :
    decideExists phi x y D = false ↔ ∀ w : List (Fin D), ¬Witness phi x y w := by
  rw [← Bool.not_eq_true,decideExists_correct,not_exists]

theorem positive_witness (phi : Constraints arity n) (x y : Fin n) (D : Nat)
    (hp : decideExists phi x y D = true) :
    ∃ w : List (Fin D), Witness phi x y w ∧ w.length ≤ bound n D :=
  exists_short phi x y ((decideExists_correct phi x y D).mp hp)

end NSSE.MultiConstructorUnifiedExistence
