import NSSE.StoredDataLabels

namespace NSSE.StoredClosedLabel

inductive Atom where
  | constant (b : Bool)
  deriving BEq

def make (r : Bool × Nat) : Atom × Nat := (.constant r.1,1+r.2)
def evaluate : Atom → Bool × Nat
  | .constant b => (b,1)
def denote {d : Nat} {P : Type} : Atom → (AlphabetTableRows.language (Fin d)).Formula P
  | .constant b => AlphabetTableRows.truth b

theorem evaluate_correct {d : Nat} {P : Type} (a : Atom) (p : P → Fin d) :
    (evaluate a).1 = true ↔ (denote (d := d) a).Realize p := by
  cases a; simp only [evaluate,denote,AlphabetTableRows.realize_truth]
theorem evaluate_cost (a : Atom) : (evaluate a).2 = 1 := by cases a; rfl

def vector (n : Nat) (f : Fin n → Bool × Nat) :=
  CountedFinEnumeration.tabulate n (fun q => make (f q))
def matrix (n : Nat) (f : Fin n → Fin n → Bool × Nat) :=
  CountedFinEnumeration.tabulate n (fun q => vector n (f q))

theorem vector_value (n : Nat) (f : Fin n → Bool × Nat) :
    (vector n f).1 = List.ofFn (fun q => Atom.constant (f q).1) := by
  simp only [vector,CountedFinEnumeration.tabulate_value,make]
theorem matrix_value (n : Nat) (f : Fin n → Fin n → Bool × Nat) :
    (matrix n f).1 = List.ofFn (fun q => List.ofFn (fun r => Atom.constant (f q r).1)) := by
  simp only [matrix,CountedFinEnumeration.tabulate_value,vector_value]
theorem vector_bound (n c : Nat) (f : Fin n → Bool × Nat) (h : ∀ q, (f q).2 ≤ c) :
    (vector n f).2 ≤ StoredForwardTableBuild.tabBudget n (1+c) :=
  CountedFinEnumeration.tabulate_bound n _ _ (fun q => Nat.add_le_add_left (h q) 1)
theorem matrix_bound (n c : Nat) (f : Fin n → Fin n → Bool × Nat) (h : ∀ q r, (f q r).2 ≤ c) :
    (matrix n f).2 ≤ StoredForwardTableBuild.tabBudget n (StoredForwardTableBuild.tabBudget n (1+c)) :=
  CountedFinEnumeration.tabulate_bound n _ _ (fun q => vector_bound n c (f q) (h q))
end NSSE.StoredClosedLabel
