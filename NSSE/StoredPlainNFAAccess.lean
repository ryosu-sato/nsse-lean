import NSSE.StoredMarkedNFAAccess
import NSSE.StoredSeedNFABuild

namespace NSSE.StoredPlainNFAAccess
open StoredForwardLookup
variable {d : Nat}

def start (A : StoredRightIdealNFABuild.Data) (q : Fin A.count) : Bool × Nat := get false A.start q.val
def final (A : StoredRightIdealNFABuild.Data) (q : Fin A.count) : Bool × Nat := get false A.final q.val
def step (A : StoredRightIdealNFABuild.Data) (q r : Fin A.count) (i : Fin d) : Bool × Nat :=
  three A.step q.val i.val r.val

theorem start_bound (A : StoredRightIdealNFABuild.Data) (q : Fin A.count) : (start A q).2 ≤ A.count :=
  (get_bound false A.start q.val).trans q.isLt
theorem final_bound (A : StoredRightIdealNFABuild.Data) (q : Fin A.count) : (final A q).2 ≤ A.count :=
  (get_bound false A.final q.val).trans q.isLt
theorem step_bound (A : StoredRightIdealNFABuild.Data) (q r : Fin A.count) (i : Fin d) :
    (step A q r i).2 ≤ 2*A.count+d+2 := StoredForwardLookup.move_bound A.step q i r

def input (A : StoredRightIdealNFABuild.Data) : NSSE.NFA (Fin d) (Fin A.count) where
  start q := (start A q).1 = true
  accept q := (final A q).1 = true
  step q i r := (step A q r i).1 = true
instance (A : StoredRightIdealNFABuild.Data) : DecidablePred (input (d := d) A).start := fun _ => inferInstanceAs (Decidable (_ = true))
instance (A : StoredRightIdealNFABuild.Data) : DecidablePred (input (d := d) A).accept := fun _ => inferInstanceAs (Decidable (_ = true))
instance (A : StoredRightIdealNFABuild.Data) : ∀ q i r, Decidable ((input (d := d) A).step q i r) := fun _ _ _ => inferInstanceAs (Decidable (_ = true))

variable {n : Nat} (T : NSSE.NFA (Fin d) (Fin n)) [DecidablePred T.start]
  [DecidablePred T.accept] [∀ q i r, Decidable (T.step q i r)]

theorem start_value (q : Fin n) : (start (StoredRightIdealNFABuild.snapshot T) q).1 = true ↔ T.start q := by
  simp only [start,StoredRightIdealNFABuild.snapshot,get_ofFn,decide_eq_true_eq]
theorem final_value (q : Fin n) : (final (StoredRightIdealNFABuild.snapshot T) q).1 = true ↔ T.accept q := by
  simp only [final,StoredRightIdealNFABuild.snapshot,get_ofFn,decide_eq_true_eq]
theorem step_value (q r : Fin n) (i : Fin d) : (step (StoredRightIdealNFABuild.snapshot T) q r i).1 = true ↔ T.step q i r := by
  simp only [step,StoredRightIdealNFABuild.snapshot,three_ofFn,decide_eq_true_eq]
theorem input_snapshot : input (d := d) (StoredRightIdealNFABuild.snapshot T) = T := by
  unfold input
  congr 1
  · funext q; exact propext (start_value T q)
  · funext q i r; exact propext (step_value T q r i)
  · funext q; exact propext (final_value T q)
end NSSE.StoredPlainNFAAccess
