import NSSE.FiniteWordCoordinates
import NSSE.UnifiedBlockWitnessBound

/-! # Complete finite-coordinate representation of bounded word tuples -/

namespace NSSE.FiniteWordArrayRepresentation

open FirstOrder FirstOrder.Language ConvolutionShapes FiniteWordCoordinates

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {q T : Nat}

noncomputable def words {D : Type*} (p : P → D) (zero one : P) (bs : Fin (count q T) → D) :
    Fin q → List D :=
  fun i => (CanonicalConvolution.decode
    ((DynamicColumnRunFormula.inputWord (Sum.elim p bs) (flags zero q T) (letters zero q T) (.inl one) T).map toDense) i).reverse

def valid (zero one : P) (q T : Nat) : L.Formula (Params P q T) :=
  PrefixArrayValidity.formula (flags zero q T) (.inl one) T

theorem words_length {D : Type*} (p : P → D) (zero one : P) (bs : Fin (count q T) → D) (i : Fin q) :
    (words p zero one bs i).length ≤ T := by
  unfold words CanonicalConvolution.decode
  rw [List.length_reverse]
  calc
    _ ≤ _ := List.length_filterMap_le _ _
    _ = T := by simp [DynamicColumnRunFormula.inputWord]

theorem filterMap_ofFn {α β : Type*} (T : Nat) (f : Fin T → α) (g : α → Option β) :
    (List.ofFn f).filterMap g = (List.ofFn (fun t => g (f t))).filterMap id := by
  induction T with
  | zero => rfl
  | succ T ih => simp only [List.ofFn_succ, List.filterMap_cons]; rw [ih]; rfl

theorem getElem_array {D : Type*} (w : List D) (T : Nat) :
    (List.ofFn (fun t : Fin T => w[t.val]?)).filterMap id = w.take T := by
  induction T generalizing w with
  | zero => simp
  | succ T ih =>
    cases w with
    | nil => simp
    | cons a w => simpa only [List.ofFn_succ, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Fin.val_succ, List.filterMap_cons, id_eq, List.take_succ_cons] using congrArg (a :: ·) (ih w)

theorem words_encoded {D : Type*} (p : P → D) (zero one : P) (h01 : p zero ≠ p one)
    (w : Fin q → List D) (hw : ∀ i, (w i).length ≤ T) :
    words p zero one (encode (T := T) (p zero) (p one) w) = w := by
  have hd : (DynamicColumnRunFormula.inputWord (valuation p zero one w)
      (flags zero q T) (letters zero q T) (.inl one) T).map toDense =
      List.ofFn (fun t : Fin T => fun i : Fin q => (w i).reverse[t.val]?) := by
    unfold DynamicColumnRunFormula.inputWord
    rw [List.map_ofFn]
    congr 1
    funext t i
    exact dense_encoded p zero one h01 w hw t i
  funext i
  change (CanonicalConvolution.decode
    ((DynamicColumnRunFormula.inputWord (valuation p zero one w) _ _ _ T).map toDense) i).reverse = w i
  rw [hd]
  unfold CanonicalConvolution.decode
  rw [filterMap_ofFn, getElem_array,
    List.take_of_length_le (by simpa only [List.length_reverse] using hw i), List.reverse_reverse]

theorem exists_representation {D : Type*} [L.Structure D] (p : P → D) (zero one : P)
    (h01 : p zero ≠ p one) (w : Fin q → List D) (hw : ∀ i, (w i).length ≤ T) :
    ∃ bs : Fin (count q T) → D,
      (valid (L := L) zero one q T).Realize (Sum.elim p bs) ∧ words p zero one bs = w := by
  refine ⟨encode (p zero) (p one) w, ?_, words_encoded p zero one h01 w hw⟩
  exact encoded_valid p zero one h01 w hw

theorem bounded_exists_iff {D : Type*} [L.Structure D] (p : P → D) (zero one : P)
    (h01 : p zero ≠ p one) (Φ : (Fin q → List D) → Prop) :
    (∃ w, (∀ i, (w i).length ≤ T) ∧ Φ w) ↔
      ∃ bs : Fin (count q T) → D,
        (valid (L := L) zero one q T).Realize (Sum.elim p bs) ∧ Φ (words p zero one bs) := by
  constructor
  · rintro ⟨w, hw, hΦ⟩
    obtain ⟨bs, hv, he⟩ := exists_representation (L := L) p zero one h01 w hw
    exact ⟨bs, hv, he.symm ▸ hΦ⟩
  · rintro ⟨bs, _, hΦ⟩
    exact ⟨words p zero one bs, words_length p zero one bs, hΦ⟩

/-- The actual word sentence now has equivalent finite scalar array witnesses.
The remaining matrix translation must replace word-model realization by scalar syntax. -/
theorem exs_arrays_iff {D : Type*} [L.Structure D] {k c : Nat} {ns : Fin k → Nat}
    (rows : (i : Fin k) → SymbolicGuardedBlocks.Row L P (ns i)) (C : SymbolicGuardedBlocks.Row L P c)
    (seed last zero one : P) (p : P → D) (h01 : p zero ≠ p one)
    (φ : (UnifiedBlockPresentation.language ns c).BoundedFormula Empty q) (hφ : φ.IsQF) :
    letI := UnifiedBlockPresentation.model rows C seed last p
    let B := (q*q+1)*2^UnifiedBlockWitnessBound.exponent ns c
    φ.exs.Realize (Empty.elim : Empty → List D) ↔
      ∃ bs : Fin (count q B) → D,
        (valid (L := L) zero one q B).Realize (Sum.elim p bs) ∧
        φ.Realize Empty.elim (words p zero one bs) := by
  letI := UnifiedBlockPresentation.model rows C seed last p
  dsimp only
  rw [UnifiedBlockWitnessBound.exs_explicit_bound rows C seed last p φ hφ]
  exact bounded_exists_iff (L := L) p zero one h01 _

end NSSE.FiniteWordArrayRepresentation
