import NSSE.StoredScalarPackage

/-! Actual distinct-tag package and existential tag wrapping. -/
namespace NSSE.StoredFreshTags
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow
variable {R : Nat → Type} {P : Type}
abbrev Names (P : Type) := P ⊕ Fin 2

def distinct : Data R (Names P) 0 := .imp (.equal (.inl (.inr 0)) (.inl (.inr 1))) .falsum
theorem distinct_value : denote (distinct (R := R) (P := P)) = FreshTagScalarLowering.distinct := rfl
def tagPackage : StoredRelationalClosure.Package R (Names P) × Nat :=
  let a := StoredRelationalPackages.atom distinct (by rw [distinct_value]; exact FreshTagScalarLowering.distinct_qf)
  (a.1,3+a.2)
theorem tag_shape : (tagPackage (R := R) (P := P)).2 ≤ 19 ∧
    StoredRelationalElimination.size (tagPackage (R := R) (P := P)).1 = 3 ∧
    arity (tagPackage (R := R) (P := P)).1.body = 0 := by
  have hs := StoredRelationalPackages.atom_shape (distinct (R := R) (P := P)) (by rw [distinct_value]; exact FreshTagScalarLowering.distinct_qf)
  have hc := StoredRelationalPackages.atom_bound (distinct (R := R) (P := P)) (by rw [distinct_value]; exact FreshTagScalarLowering.distinct_qf) 0 (by simp only [distinct,arity,Nat.max_self]; exact le_rfl)
  simp only [distinct,nodes,arity,weight] at hs hc
  simp only [tagPackage,StoredRelationalElimination.size,distinct]
  omega

def wrap (A : StoredRelationalClosure.Package R (Names P)) : StoredRelationalClosure.Package R P × Nat :=
  let t := tagPackage
  let j := StoredRelationalPackages.conj t.1 A
  let b := StoredRelationalPackages.bind 2 j.1
  (b.1,3+t.2+j.2+b.2)
theorem shape (A : StoredRelationalClosure.Package R (Names P)) :
    StoredRelationalElimination.size (wrap A).1 = StoredRelationalElimination.size A+18 ∧
    arity (wrap A).1.body = arity A.body := by
  have ht := tag_shape (R := R) (P := P)
  have hj := StoredRelationalPackages.conj_shape (tagPackage (R := R) (P := P)).1 A
  have hb := StoredRelationalPackages.bind_shape 2 (StoredRelationalPackages.conj (tagPackage (R := R) (P := P)).1 A).1
  constructor
  · simp only [wrap,StoredRelationalElimination.size] at *
    rw [hb.2.1,hj.2.1]
    omega
  · simp only [wrap,hb.2.2,hj.2.2,ht.2.2,Nat.zero_max]
def budget (S K : Nat) := 26+StoredRelationalElimination.joinBudget (S+3) K+weight K 6*(S+8)
theorem bound (A : StoredRelationalClosure.Package R (Names P)) (S K : Nat)
    (hs : StoredRelationalElimination.size A ≤ S) (hk : arity A.body ≤ K) :
    (wrap A).2 ≤ budget S K := by
  have ht := tag_shape (R := R) (P := P)
  have hj := StoredRelationalPackages.conj_shape (tagPackage (R := R) (P := P)).1 A
  have cj := StoredRelationalElimination.conj_bound (tagPackage (R := R) (P := P)).1 A (S+3) K
    (by rw [ht.2.1]; omega) (by omega) (by rw [ht.2.2]; omega) hk
  have cb := StoredRelationalPackages.bind_bound 2 (StoredRelationalPackages.conj (tagPackage (R := R) (P := P)).1 A).1 K
    (by rw [hj.2.2,ht.2.2]; exact max_le (Nat.zero_le _) hk)
  norm_num at cb
  have hn : nodes (StoredRelationalPackages.conj (tagPackage (R := R) (P := P)).1 A).1.body ≤ S+8 := by
    rw [hj.2.1]
    simp only [StoredRelationalElimination.size] at hs ht
    omega
  have hm := Nat.mul_le_mul_left (weight K 6) hn
  simp only [wrap,budget] at *
  omega

theorem correct (A : StoredRelationalClosure.Package R (Names P)) {D : Type}
    [(UniformWordLowering.wordLanguage R).Structure D] [Nonempty D] (p : P → D) :
    Formula.Realize (wrap A).1.original.toFormula p ↔
      ∃ tags : Fin 2 → D, tags 0 ≠ tags 1 ∧ Formula.Realize A.original.toFormula (Sum.elim p tags) := by
  simp only [wrap,StoredRelationalPackages.bind_original,StoredRelationalPackages.conj_original,
    ExistentialFormulaPackage.Package.bind_correct,ExistentialFormulaPackage.Package.conj_correct,
    tagPackage,StoredRelationalPackages.atom_original,ExistentialFormulaPackage.Package.atom_correct,
    distinct_value,FreshTagScalarLowering.distinct_correct]
end NSSE.StoredFreshTags
