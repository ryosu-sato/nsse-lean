import NSSE.MultiConstructorFlatEntailment
import Mathlib.Logic.Encodable.Pi

/-! Executable selection of bounded successful assignment data. The
constructor encoding is representation data; finite numbered signatures
provide it automatically. Search termination follows from the proved
negative decision and global witness bound. -/
namespace NSSE.MultiConstructorWitnessCode
open MultiConstructorTrees MultiConstructorConstraints MultiConstructorUnifiedWords
open MultiConstructorSpineInput MultiConstructorSpineInput.Data MultiConstructorFirstPath
variable {H : Type*} {arity : H → Nat} {n D : Nat}

def labelEquiv : Label H ≃ Option (Option H) where
  toFun | .bot => none | .top => some none | .node h => some (some h)
  invFun | none => .bot | some none => .top | some (some h) => .node h
  left_inv e := by cases e <;> rfl
  right_inv e := by cases e with | none => rfl | some e => cases e <;> rfl

instance labelEncodable [Encodable H] : Encodable (Label H) := Encodable.ofEquiv _ labelEquiv

abbrev Payload (H : Type*) (D : Nat) := Σ w : List (Fin D), (Fin w.length → H) × Label H × Label H

def data (Q : Query arity n) (p : Payload H D) : Data arity n D :=
  ⟨Q.left,Q.right,p.1,p.2.1,p.2.2.1,p.2.2.2⟩

variable [DecidableEq H]

def Good (Q : Query arity n) (p : Payload H D) : Prop :=
  Assignment Q.constraints Q.left Q.right p.1 p.2.1 p.2.2.1 p.2.2.2 ∧
    p.1.length ≤ MultiConstructorUnifiedBound.bound n D

def goodDecision (Q : Query arity n) : DecidablePred (Good (D := D) Q) := by
  intro p
  letI := assignmentDecision Q.constraints Q.left Q.right p.1 p.2.1 p.2.2.1 p.2.2.2
  unfold Good
  infer_instance

theorem exists_good (Q : Query arity n) (hD : ∀ h, arity h ≤ D) (hn : ¬Entails allAlgebra Q) :
    ∃ p : Payload H D, Good Q p := by
  have hw := ((MultiConstructorSpineRealization.countermodel_iff Q hD).mp hn).2
  obtain ⟨w,⟨heads,ex,ey,ha⟩,hb⟩ := MultiConstructorUnifiedBound.exists_short Q.constraints Q.left Q.right hw
  exact ⟨⟨w,heads,ex,ey⟩,ha,hb⟩

variable [Fintype H] [Encodable H]

def select (Q : Query arity n) (hn : MultiConstructorFlatEntailment.inspect Q = false) :
    {p : Payload H (alphabetSize arity) // Good Q p} :=
  @Encodable.chooseX _ (Good Q) inferInstance (goodDecision Q)
    (exists_good Q arity_le_alphabet ((MultiConstructorFlatEntailment.inspect_false Q).mp hn))

theorem selected_assignment (Q : Query arity n) (hn : MultiConstructorFlatEntailment.inspect Q = false) :
    let S := data Q (select Q hn).val
    Assignment Q.constraints S.left S.right S.word S.heads S.endX S.endY :=
  (select Q hn).property.1

theorem selected_bound (Q : Query arity n) (hn : MultiConstructorFlatEntailment.inspect Q = false) :
    (data Q (select Q hn).val).word.length ≤ MultiConstructorUnifiedBound.bound n (alphabetSize arity) :=
  (select Q hn).property.2

end NSSE.MultiConstructorWitnessCode
