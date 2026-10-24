import NSSE.DirectRankStateRecurrence

/-! # Parameter transport for the actual unified word model -/

namespace NSSE.UnifiedModelParameterTransport

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks

universe u v w w'
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {P' : Type w'} {n k c : Nat} {ns : Fin k → Nat}

theorem block_relation_map (f : P → P') (R : Row L P n) (seed last : P)
    {D : Type*} [L.Structure D] (p : P' → D) {a : Nat} (r : BlockRelationPresentation.Rel n a)
    (xs : Fin a → List D) :
    @Structure.RelMap _ _ (BlockRelationPresentation.model (RowParameterTransport.mapRow f R) (f seed) (f last) p) _ r xs ↔
    @Structure.RelMap _ _ (BlockRelationPresentation.model R seed last (p ∘ f)) _ r xs := by
  cases r with
  | block q r =>
    have hx : xs = ![xs 0] := by funext i; fin_cases i; rfl
    rw [hx, BlockRelationPresentation.block_interpret, BlockRelationPresentation.block_interpret,
      RowParameterTransport.dataNFA_map]
    rfl
  | guarded e first =>
    have hx : xs = ![xs 0, xs 1] := by funext i; fin_cases i <;> rfl
    rw [hx, BlockRelationPresentation.guarded_interpret, BlockRelationPresentation.guarded_interpret]
    exact FiniteArrayHFormula.literalH_map f R e seed last first p _ _
  | initial q =>
    rw [BlockRelationPresentation.initial_interpret, BlockRelationPresentation.initial_interpret,
      RowParameterTransport.dataNFA_map]
    rfl
  | final q =>
    rw [BlockRelationPresentation.final_interpret, BlockRelationPresentation.final_interpret,
      RowParameterTransport.dataNFA_map]

theorem relation_map (f : P → P') (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (seed last : P) {D : Type*} [L.Structure D] (p : P' → D) {a : Nat}
    (r : UnifiedBlockPresentation.Rel ns c a) (xs : Fin a → List D) :
    @Structure.RelMap _ _ (UnifiedBlockPresentation.model (fun i => RowParameterTransport.mapRow f (rows i))
      (RowParameterTransport.mapRow f C) (f seed) (f last) p) _ r xs ↔
    @Structure.RelMap _ _ (UnifiedBlockPresentation.model rows C seed last (p ∘ f)) _ r xs := by
  cases r with
  | row i r => exact block_relation_map f (rows i) seed last p r xs
  | candidate r => exact block_relation_map f C seed last p r xs
  | noA =>
    have hx : xs = ![xs 0] := by funext i; fin_cases i; rfl
    rw [hx, UnifiedBlockPresentation.noA_interpret, UnifiedBlockPresentation.noA_interpret]
    rfl

theorem model_map (f : P → P') (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (seed last : P) {D : Type*} [L.Structure D] (p : P' → D) :
    UnifiedBlockPresentation.model (fun i => RowParameterTransport.mapRow f (rows i))
      (RowParameterTransport.mapRow f C) (f seed) (f last) p =
    UnifiedBlockPresentation.model rows C seed last (p ∘ f) := by
  apply Structure.ext
  · funext a r
    exact nomatch r
  · funext a r xs
    exact propext (relation_map f rows C seed last p r xs)

end NSSE.UnifiedModelParameterTransport
