import NSSE.StoredRowNonempty

/-! Actual row package compilation, existential closure and finite evaluation.
These counters do not include construction/encoding of the input Row or a
machine simulation of its functional field representation. -/
namespace NSSE.StoredRowDecision
open FirstOrder FirstOrder.Language ExplicitUnaryTableLanguage ExactReachabilitySize
open SymbolicGuardedBlocks ArrayAtomExistentialPackages ExistentialFormulaPackage FiniteValuationLookup
variable {d m n : Nat}

def evaluationBudget (d m S : Nat) :=
  4+11*S+(d+1)^2+StoredQuantifiedEvaluation.weight d m S d*(S*(d+1)^S)

theorem evaluation_bound (A : Package language (Fin m)) (ps : Values d m) (S : Nat)
    (hs : nodes A.toFormula ≤ S) : (ConstructedPackageEvaluation.decide A ps).2 ≤ evaluationBudget d m S := by
  obtain ⟨hb,hv⟩ := StoredPackageElimination.parts A S hs
  have hz : ConstructedPackageEvaluation.size A ≤ S := by
    rw [← ConstructedPackageEvaluation.size_value]; exact hs
  apply (ConstructedPackageEvaluation.bound A ps).trans
  unfold ConstructedPackageEvaluation.budget evaluationBudget StoredQuantifiedEvaluation.weight
  calc
    _ ≤ 4+5*S+6*S+(d+1)^2+(2*(m+S)+d+3*d+3)*(S*(d+1)^S) := by gcongr; omega
    _ = _ := by ring

def seed (R : Row language (Fin m) n) (h : RowQF R) (ps : Values d m) : Bool × Nat :=
  let a := StoredRowNonempty.seed R h
  let b := ConstructedPackageEvaluation.decide a.1 ps
  (b.1,1+a.2+b.2)
def nonempty (R : Row language (Fin m) n) (h : RowQF R) (ps : Values d m) : Bool × Nat :=
  let a := StoredRowNonempty.nonempty R h
  let b := ConstructedPackageEvaluation.decide a.1 ps
  (b.1,1+a.2+b.2)

theorem seed_correct [Nonempty (Fin d)] (R : Row language (Fin m) n) (h : RowQF R) (ps : Values d m) :
    (seed R h ps).1 = true ↔ ∃ x, (R.dataNFA ps.meaning).Accepts [x] := by
  simp only [seed,StoredRowNonempty.seed_value,ConstructedPackageEvaluation.correct]
  exact ExistentialRowNonempty.seedOnly_correct R h ps.meaning

theorem nonempty_correct [Nonempty (Fin d)] (R : Row language (Fin m) n) (h : RowQF R) (ps : Values d m) :
    (nonempty R h ps).1 = true ↔ ∃ xs, (R.dataNFA ps.meaning).Accepts xs := by
  simp only [nonempty,StoredRowNonempty.nonempty_value,ConstructedPackageEvaluation.correct]
  exact ExistentialRowNonempty.nonempty_correct R h ps.meaning

def seedBudget (d m n B : Nat) := 1+StoredRowNonempty.seedBudget n B+
  evaluationBudget d m (ExistentialRowNonemptySize.seedBound n B)
def nonemptyBudget (d m n B : Nat) := 1+StoredRowNonempty.nonemptyBudget n B+
  evaluationBudget d m (ExistentialRowNonemptySize.nonemptyBound n B)

theorem seed_bound (R : Row language (Fin m) n) (h : RowQF R) (ps : Values d m) (B : Nat)
    (hf : DirectRowBooleanSize.Fields R B) : (seed R h ps).2 ≤ seedBudget d m n B := by
  have ha := StoredRowNonempty.seed_bound R h B hf
  have hb := evaluation_bound (ExistentialRowNonempty.seedOnly R h) ps _
    (ExistentialRowNonemptySize.seed_le R h hf)
  simp only [seed,StoredRowNonempty.seed_value,seedBudget]
  omega

theorem nonempty_bound (R : Row language (Fin m) n) (h : RowQF R) (ps : Values d m) (B : Nat)
    (hf : DirectRowBooleanSize.Fields R B) : (nonempty R h ps).2 ≤ nonemptyBudget d m n B := by
  have ha := StoredRowNonempty.nonempty_bound R h B hf
  have hb := evaluation_bound (ExistentialRowNonempty.nonempty R h) ps _
    (ExistentialRowNonemptySize.nonempty_le R h hf)
  simp only [nonempty,StoredRowNonempty.nonempty_value,nonemptyBudget]
  omega
end NSSE.StoredRowDecision
