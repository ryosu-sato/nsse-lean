import NSSE.StoredCapRowNFABuild

namespace NSSE.StoredMarkedNFAAccess
open StoredForwardLookup
variable {d : Nat}

def start (A : StoredCapRowNFABuild.Data) (q : Fin A.count) : Bool × Nat := get false A.start q.val
def final (A : StoredCapRowNFABuild.Data) (q : Fin A.count) : Bool × Nat := get false A.final q.val

def step (A : StoredCapRowNFABuild.Data) (q r : Fin A.count) : (Fin d ⊕ Bool) → Bool × Nat
  | .inl i => let t := three A.step q.val i.val r.val; (t.1,1+t.2)
  | .inr false => let t := two A.left q.val r.val; (t.1,1+t.2)
  | .inr true => let t := two A.right q.val r.val; (t.1,1+t.2)

theorem start_bound (A : StoredCapRowNFABuild.Data) (q : Fin A.count) : (start A q).2 ≤ A.count :=
  (get_bound false A.start q.val).trans q.isLt

theorem final_bound (A : StoredCapRowNFABuild.Data) (q : Fin A.count) : (final A q).2 ≤ A.count :=
  (get_bound false A.final q.val).trans q.isLt

theorem step_bound (A : StoredCapRowNFABuild.Data) (q r : Fin A.count) (x : Fin d ⊕ Bool) :
    (step A q r x).2 ≤ 2*A.count+d+3 := by
  have hq := q.isLt
  have hr := r.isLt
  cases x with
  | inl i =>
    have h := three_bound A.step q.val i.val r.val
    have hi := i.isLt
    simp only [step]; omega
  | inr b =>
    cases b
    · have h := two_bound A.left q.val r.val; simp only [step]; omega
    · have h := two_bound A.right q.val r.val; simp only [step]; omega

-- Semantic view: downstream consumers must charge the read counters above.
def input (A : StoredCapRowNFABuild.Data) : NSSE.NFA (Fin d ⊕ Bool) (Fin A.count) where
  start q := (start A q).1 = true
  accept q := (final A q).1 = true
  step q x r := (step A q r x).1 = true

instance (A : StoredCapRowNFABuild.Data) : DecidablePred (input (d := d) A).start := fun _ => inferInstanceAs (Decidable (_ = true))
instance (A : StoredCapRowNFABuild.Data) : DecidablePred (input (d := d) A).accept := fun _ => inferInstanceAs (Decidable (_ = true))
instance (A : StoredCapRowNFABuild.Data) : ∀ q x r, Decidable ((input (d := d) A).step q x r) := fun _ _ _ => inferInstanceAs (Decidable (_ = true))

variable {n : Nat} (T : NSSE.NFA (Fin d ⊕ Bool) (Fin n)) [DecidablePred T.start]
  [DecidablePred T.accept] [∀ q x r, Decidable (T.step q x r)]

theorem start_value (q : Fin n) :
    (start (StoredCapRowNFABuild.snapshot T) q).1 = true ↔ T.start q := by
  simp only [start,StoredCapRowNFABuild.snapshot,get_ofFn,decide_eq_true_eq]

theorem final_value (q : Fin n) :
    (final (StoredCapRowNFABuild.snapshot T) q).1 = true ↔ T.accept q := by
  simp only [final,StoredCapRowNFABuild.snapshot,get_ofFn,decide_eq_true_eq]

theorem step_value (q r : Fin n) (x : Fin d ⊕ Bool) :
    (step (StoredCapRowNFABuild.snapshot T) q r x).1 = true ↔ T.step q x r := by
  cases x with
  | inl i => simp only [step,StoredCapRowNFABuild.snapshot,three_ofFn,decide_eq_true_eq]
  | inr b => cases b <;> simp only [step,StoredCapRowNFABuild.snapshot,two_ofFn,decide_eq_true_eq]

theorem input_snapshot : input (d := d) (StoredCapRowNFABuild.snapshot T) = T := by
  unfold input
  congr 1
  · funext q; exact propext (start_value T q)
  · funext q x r; exact propext (step_value T q r x)
  · funext q; exact propext (final_value T q)
end NSSE.StoredMarkedNFAAccess
