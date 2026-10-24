import NSSE.UnifiedModelParameterTransport

/-! # Existential scalar lowering with internally allocated distinct tags -/

namespace NSSE.FreshTagScalarLowering

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks UnifiedBlockPresentation
open ExistentialFormulaPackage ArrayAtomExistentialPackages

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {k c : Nat} {ns : Fin k → Nat}

abbrev Names (P : Type w) := P ⊕ Fin 2

def distinct : L.Formula (Names P) :=
  ((Term.var (.inr 0)).equal (Term.var (.inr 1))).not

theorem distinct_qf : (distinct (L := L) (P := P)).IsQF :=
  (BoundedFormula.IsAtomic.isQF (.equal _ _)).not

theorem distinct_correct {D : Type*} [L.Structure D] (p : P → D) (tags : Fin 2 → D) :
    (distinct (L := L)).Realize (Sum.elim p tags) ↔ tags 0 ≠ tags 1 := by
  simp [distinct]

def lower (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, RowQF (rows i)) (hc : RowQF C) (seed last : P) {q : Nat}
    (φ : (language ns c).BoundedFormula Empty q) : Package L P :=
  Package.bind 2 (Package.conj (Package.atom distinct distinct_qf)
    (ExistentialScalarPrenex.lower
      (fun i => RowParameterTransport.mapRow (Sum.inl : P → Names P) (rows i))
      (RowParameterTransport.mapRow Sum.inl C)
      (fun i => RankCleanedQuantifierFree.parameter_map_qf _ _ (hr i))
      (RankCleanedQuantifierFree.parameter_map_qf _ _ hc)
      (.inl seed) (.inl last) (.inr 0) (.inr 1) φ))

theorem lower_correct (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, RowQF (rows i)) (hc : RowQF C) (seed last : P) {q : Nat}
    (φ : (language ns c).BoundedFormula Empty q) (hφ : φ.IsQF)
    {D : Type*} [L.Structure D] [Nontrivial D] (p : P → D) :
    letI := model rows C seed last p
    φ.exs.Realize (Empty.elim : Empty → List D) ↔ (lower rows C hr hc seed last φ).toFormula.Realize p := by
  have he (tags : Fin 2 → D) (ht : tags 0 ≠ tags 1) :
      letI := model rows C seed last p
      φ.exs.Realize (Empty.elim : Empty → List D) ↔
        (ExistentialScalarPrenex.lower
          (fun i => RowParameterTransport.mapRow (Sum.inl : P → Names P) (rows i))
          (RowParameterTransport.mapRow Sum.inl C)
          (fun i => RankCleanedQuantifierFree.parameter_map_qf _ _ (hr i))
          (RankCleanedQuantifierFree.parameter_map_qf _ _ hc)
          (.inl seed) (.inl last) (.inr 0) (.inr 1) φ).toFormula.Realize (Sum.elim p tags) := by
    have hh := ExistentialScalarPrenex.lower_correct
      (fun i => RowParameterTransport.mapRow (Sum.inl : P → Names P) (rows i))
      (RowParameterTransport.mapRow Sum.inl C)
      (fun i => RankCleanedQuantifierFree.parameter_map_qf _ _ (hr i))
      (RankCleanedQuantifierFree.parameter_map_qf _ _ hc)
      (.inl seed) (.inl last) (.inr 0) (.inr 1) φ hφ (Sum.elim p tags) ht
    rw [UnifiedModelParameterTransport.model_map] at hh
    exact hh
  simp only [lower, Package.bind_correct, Package.conj_correct, Package.atom_correct, distinct_correct]
  constructor
  · intro h
    obtain ⟨z,o,hzo⟩ := exists_pair_ne D
    exact ⟨![z,o], hzo, (he ![z,o] hzo).mp h⟩
  · rintro ⟨tags, ht, h⟩
    exact (he tags ht).mpr h

theorem lower_body_qf (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, RowQF (rows i)) (hc : RowQF C) (seed last : P) {q : Nat}
    (φ : (language ns c).BoundedFormula Empty q) :
    (lower rows C hr hc seed last φ).boundedBody.IsQF := Package.boundedBody_qf _

end NSSE.FreshTagScalarLowering
