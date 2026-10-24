import NSSE.StoredFormulaMaterialization

/-! Signed QF skeleton for stored scalar lowering. Atomic compilation costs
are explicit; no claim yet instantiates the array atom compilers. -/
namespace NSSE.StoredSignedLowering
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalClosure StoredRelationalElimination
variable {R S : Nat → Type} {P X : Type} {n : Nat}
structure Atoms (R S : Nat → Type) (X P : Type) (n : Nat) where
  falsum : Bool → Package S P × Nat
  equal : (X ⊕ Fin n) → (X ⊕ Fin n) → Bool → Package S P × Nat
  rel : (k : Nat) → R k → StoredRelationTuple.Data (X ⊕ Fin n) k → Bool → Package S P × Nat

def build (a : Atoms R S X P n) : (φ : Data R X n) → (denote φ).IsQF → Bool → Package S P × Nat
  | .falsum,_,p => a.falsum p
  | .equal x y,_,p => a.equal x y p
  | .rel r xs,_,p => a.rel _ r xs p
  | .imp φ ψ,h,p =>
    let x := build a φ (by cases h with | imp hφ _ => exact hφ | of_isAtomic ha => cases ha) (!p)
    let y := build a ψ (by cases h with | imp _ hψ => exact hψ | of_isAtomic ha => cases ha) p
    let z := if p then StoredRelationalPackages.disj x.1 y.1 else StoredRelationalPackages.conj x.1 y.1
    (z.1,4+x.2+y.2+z.2)
  | .all φ,h,_ => False.elim (BoundedFormula.not_all_isQF (denote φ) h)

structure Bounds (a : Atoms R S X P n) (c B K : Nat) : Prop where
  falsum : ∀ p, (a.falsum p).2 ≤ c ∧ size (a.falsum p).1 ≤ B ∧ arity (a.falsum p).1.body ≤ K
  equal : ∀ x y p, (a.equal x y p).2 ≤ c ∧ size (a.equal x y p).1 ≤ B ∧ arity (a.equal x y p).1.body ≤ K
  rel : ∀ k r xs p, (a.rel k r xs p).2 ≤ c ∧ size (a.rel k r xs p).1 ≤ B ∧ arity (a.rel k r xs p).1.body ≤ K

theorem shape (a : Atoms R S X P n) (c B K : Nat) (ha : Bounds a c B K)
    (φ : Data R X n) (h : (denote φ).IsQF) (p : Bool) :
    size (build a φ h p).1+5 ≤ (B+5)*nodes φ ∧ arity (build a φ h p).1.body ≤ K := by
  cases φ with
  | falsum => have h := ha.falsum p; simp only [build,nodes,Nat.mul_one]; constructor <;> omega
  | equal x y => have h := ha.equal x y p; simp only [build,nodes,Nat.mul_one]; constructor <;> omega
  | rel r xs => have h := ha.rel _ r xs p; simp only [build,nodes,Nat.mul_one]; constructor <;> omega
  | imp φ ψ =>
    have hl : (denote φ).IsQF := by cases h with | imp hp _ => exact hp | of_isAtomic hat => cases hat
    have hr : (denote ψ).IsQF := by cases h with | imp _ hp => exact hp | of_isAtomic hat => cases hat
    have hx := shape a c B K ha φ hl (!p)
    have hy := shape a c B K ha ψ hr p
    have hkc : arity (StoredRelationalPackages.conj (build a φ hl (!p)).1 (build a ψ hr p).1).1.body ≤ K := by
      rw [(StoredRelationalPackages.conj_shape _ _).2.2]; exact max_le hx.2 hy.2
    have hkd : arity (StoredRelationalPackages.disj (build a φ hl (!p)).1 (build a ψ hr p).1).1.body ≤ K := by
      rw [(StoredRelationalPackages.disj_shape _ _).2.2]; exact max_le hx.2 hy.2
    cases p <;> simp only [build,Bool.not_false,Bool.not_true,Bool.false_eq_true,↓reduceIte,nodes] at *
    all_goals
      constructor
      · rw [size_value]
        simp only [StoredRelationalPackages.conj_original,StoredRelationalPackages.disj_original,
          ExistentialFormulaPackage.Package.nodes_conj,ExistentialFormulaPackage.Package.nodes_disj,← size_value]
        nlinarith [hx.1,hy.1]
      · first | exact hkc | exact hkd
  | all φ => exact False.elim (BoundedFormula.not_all_isQF (denote φ) h)

theorem bound (a : Atoms R S X P n) (c B K N : Nat) (ha : Bounds a c B K)
    (φ : Data R X n) (h : (denote φ).IsQF) (p : Bool) (hn : nodes φ ≤ N) :
    (build a φ h p).2 ≤ (c+4+joinBudget ((B+5)*N) K)*nodes φ := by
  cases φ with
  | falsum => have h := (ha.falsum p).1; simp only [build,nodes,Nat.mul_one]; omega
  | equal x y => have h := (ha.equal x y p).1; simp only [build,nodes,Nat.mul_one]; omega
  | rel r xs => have h := (ha.rel _ r xs p).1; simp only [build,nodes,Nat.mul_one]; omega
  | imp φ ψ =>
    have hl : (denote φ).IsQF := by cases h with | imp hp _ => exact hp | of_isAtomic hat => cases hat
    have hr : (denote ψ).IsQF := by cases h with | imp _ hp => exact hp | of_isAtomic hat => cases hat
    have hnφ : nodes φ ≤ N := by simp only [nodes] at hn; omega
    have hnψ : nodes ψ ≤ N := by simp only [nodes] at hn; omega
    have hx := shape a c B K ha φ hl (!p)
    have hy := shape a c B K ha ψ hr p
    have hsx : size (build a φ hl (!p)).1 ≤ (B+5)*N := by
      have hm := Nat.mul_le_mul_left (B+5) hnφ; omega
    have hsy : size (build a ψ hr p).1 ≤ (B+5)*N := by
      have hm := Nat.mul_le_mul_left (B+5) hnψ; omega
    have hc₁ := bound a c B K N ha φ hl (!p) hnφ
    have hc₂ := bound a c B K N ha ψ hr p hnψ
    have hj₁ := StoredRelationalElimination.conj_bound _ _ _ K hsx hsy hx.2 hy.2
    have hj₂ := StoredRelationalElimination.disj_bound _ _ _ K hsx hsy hx.2 hy.2
    cases p <;> simp only [build,Bool.not_false,Bool.not_true,Bool.false_eq_true,↓reduceIte,nodes] at * <;> nlinarith
  | all φ => exact False.elim (BoundedFormula.not_all_isQF (denote φ) h)
theorem correct (a : Atoms R S X P n) {D E : Type}
    [(UniformWordLowering.wordLanguage R).Structure D] [(UniformWordLowering.wordLanguage S).Structure E]
    [Nonempty E] (v : X → D) (vs : Fin n → D) (w : P → E)
    (hf : ∀ p, (a.falsum p).1.original.toFormula.Realize w ↔ (False ↔ p=true))
    (he : ∀ x y p, (a.equal x y p).1.original.toFormula.Realize w ↔
      (Sum.elim v vs x = Sum.elim v vs y ↔ p=true))
    (hr : ∀ k r xs p, (a.rel k r xs p).1.original.toFormula.Realize w ↔
      (Structure.RelMap (L := UniformWordLowering.wordLanguage R) r
        (fun i => Sum.elim v vs (StoredRelationTuple.read xs i).1) ↔ p=true))
    (φ : Data R X n) (h : (denote φ).IsQF) (p : Bool) :
    (build a φ h p).1.original.toFormula.Realize w ↔ ((denote φ).Realize v vs ↔ p=true) := by
  cases φ with
  | falsum => exact hf p
  | equal x y => exact he x y p
  | rel r xs => exact hr _ r xs p
  | imp φ ψ =>
    have hl : (denote φ).IsQF := by cases h with | imp hp _ => exact hp | of_isAtomic hat => cases hat
    have hright : (denote ψ).IsQF := by cases h with | imp _ hp => exact hp | of_isAtomic hat => cases hat
    have hx := correct a v vs w hf he hr φ hl (!p)
    have hy := correct a v vs w hf he hr ψ hright p
    cases p <;>
      simp only [build,Bool.not_false,Bool.not_true,Bool.false_eq_true,↓reduceIte,
        StoredRelationalPackages.conj_original,StoredRelationalPackages.disj_original,
        ExistentialFormulaPackage.Package.conj_correct,ExistentialFormulaPackage.Package.disj_correct,
        denote,BoundedFormula.Realize] at * <;> tauto
  | all φ => exact False.elim (BoundedFormula.not_all_isQF (denote φ) h)
end NSSE.StoredSignedLowering
