import NSSE.PrefixArrayValidity

/-! # Explicit finite scalar coordinates for bounded word tuples

Original scalar parameters occupy the left summand. Presence and letter
coordinates use disjoint numbered blocks in the right summand.
-/

namespace NSSE.FiniteWordCoordinates

open FirstOrder FirstOrder.Language ConvolutionShapes

universe u v w
variable {P : Type w} {q T : Nat}

def slots (q T : Nat) := (T+1)*q
def count (q T : Nat) := slots q T + slots q T
abbrev Params (P : Type w) (q T : Nat) := P ⊕ Fin (count q T)

def flags (zero : P) (q T : Nat) (t : Nat) (i : Fin q) : Params P q T :=
  if h : t < T+1 then .inr (Fin.castAdd (slots q T) (finProdFinEquiv (⟨t,h⟩,i))) else .inl zero

def letters (zero : P) (q T : Nat) (t : Nat) (i : Fin q) : Params P q T :=
  if h : t < T+1 then .inr (Fin.natAdd (slots q T) (finProdFinEquiv (⟨t,h⟩,i))) else .inl zero

def encode {D : Type*} (zero one : D) (words : Fin q → List D) : Fin (count q T) → D :=
  Fin.addCases
    (fun j => if (finProdFinEquiv.symm j).1.val < (words (finProdFinEquiv.symm j).2).length then one else zero)
    (fun j => ((words (finProdFinEquiv.symm j).2).reverse[(finProdFinEquiv.symm j).1.val]?).getD zero)

def valuation {D : Type*} (p : P → D) (zero one : P) (words : Fin q → List D) : Params P q T → D :=
  Sum.elim p (encode (T := T) (p zero) (p one) words)

@[simp] theorem valuation_parameter {D : Type*} (p : P → D) (zero one : P)
    (words : Fin q → List D) (x : P) : valuation (T := T) p zero one words (.inl x) = p x := rfl

theorem flags_value {D : Type*} (p : P → D) (zero one : P) (words : Fin q → List D)
    (hw : ∀ i, (words i).length ≤ T) (t : Nat) (i : Fin q) :
    valuation p zero one words (flags zero q T t i) = if t < (words i).length then p one else p zero := by
  unfold flags
  split
  · simp only [valuation, encode, Sum.elim_inr, Fin.addCases_left, Fin.addCases_right, Equiv.symm_apply_apply]
  · have hn : ¬ t < (words i).length := by have hh := hw i; omega
    simp [valuation, hn]

theorem letters_value {D : Type*} (p : P → D) (zero one : P) (words : Fin q → List D)
    (hw : ∀ i, (words i).length ≤ T) (t : Nat) (i : Fin q) :
    valuation p zero one words (letters zero q T t i) = ((words i).reverse[t]?).getD (p zero) := by
  unfold letters
  split
  · simp only [valuation, encode, Sum.elim_inr, Fin.addCases_left, Fin.addCases_right, Equiv.symm_apply_apply]
  · have hn : (words i).reverse.length ≤ t := by simp only [List.length_reverse]; have hh := hw i; omega
    simp [valuation, List.getElem?_eq_none hn]

theorem flags_true {D : Type*} (p : P → D) (zero one : P) (h01 : p zero ≠ p one)
    (words : Fin q → List D) (hw : ∀ i, (words i).length ≤ T) (t : Nat) (i : Fin q) :
    valuation p zero one words (flags zero q T t i) = p one ↔ t < (words i).length := by
  rw [flags_value p zero one words hw]
  split_ifs <;> simp_all

theorem encoded_valid {L : FirstOrder.Language.{u,v}} {D : Type*} [L.Structure D]
    (p : P → D) (zero one : P) (h01 : p zero ≠ p one) (words : Fin q → List D)
    (hw : ∀ i, (words i).length ≤ T) :
    (PrefixArrayValidity.formula (L := L) (flags zero q T) (.inl one) T).Realize
      (valuation p zero one words) := by
  rw [PrefixArrayValidity.realize_formula]
  intro t _ i
  simp only [valuation_parameter, flags_true p zero one h01 words hw]
  omega

theorem dense_encoded {D : Type*} (p : P → D) (zero one : P) (h01 : p zero ≠ p one)
    (words : Fin q → List D) (hw : ∀ i, (words i).length ≤ T) (t : Nat) (i : Fin q) :
    toDense (DynamicColumnSelection.column (valuation p zero one words)
      (flags zero q T t) (letters zero q T t) (.inl one)) i = (words i).reverse[t]? := by
  classical
  rw [DynamicColumnSelection.dense_column, valuation_parameter]
  simp only [flags_true p zero one h01 words hw, letters_value p zero one words hw]
  by_cases ht : t < (words i).length
  · have ht' : t < (words i).reverse.length := by simpa using ht
    simp [ht, List.getElem?_eq_getElem ht']
  · have ht' : (words i).reverse.length ≤ t := by simp only [List.length_reverse]; omega
    simp [ht, List.getElem?_eq_none ht']

theorem count_eq (q T : Nat) : count q T = 2*(T+1)*q := by unfold count slots; ring

end NSSE.FiniteWordCoordinates
