import NSSE.StoredRowComplementBound

/-! One actual cleanup subtraction: empty-tail recognition followed by direct difference. -/
namespace NSSE.StoredCleanupStep
open FirstOrder FirstOrder.Language StoredRelationalRow
variable {R : Nat → Type} {P : Type} {c n : Nat}

def build (C : Row R P c) (A : Row R P n) (last : P) : (Sigma (Row R P)) × Nat :=
  let a := StoredEmptyTailCompiler.build A last
  let b := StoredRowDifference.build C a.1.row
  (b.1,2+a.2+b.2)
def factor (n : Nat) := 2^(3*n)+1
def increase (n B : Nat) := 5+StoredRowComplementGuards.sizeBudget (3*n) (StoredEmptyTailGuards.sizeBudget n B)
def budget (c n B K : Nat) := 2+StoredEmptyTailCompiler.budget n B K+
  StoredRowDifference.budget c (3*n) (StoredEmptyTailGuards.sizeBudget n B) K

theorem states (C : Row R P c) (A : Row R P n) (last : P) : (build C A last).1.1 = c*factor n := by
  simp only [build,StoredRowDifference.states,StoredEmptyTailStates.count_value,factor]
theorem bound (C : Row R P c) (A : Row R P n) (last : P) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    (build C A last).2 ≤ budget c n B K := by
  have ha := StoredEmptyTailCompiler.bound A last B K h
  have hs := StoredEmptyTailCompiler.shape A last B K h
  have hb := StoredRowDifference.bound C (StoredEmptyTailCompiler.build A last).1.row _ K hs
  conv at hb => rhs; rw [StoredEmptyTailStates.count_value]
  simp only [build,budget]; omega
theorem shape (C : Row R P c) (A : Row R P n) (last : P) (F B K : Nat)
    (hc : StoredRowTransport.Bounds C F K) (ha : StoredRowTransport.Bounds A B K) :
    StoredRowTransport.Bounds (build C A last).1.2 (F+increase n B) K := by
  have hs := StoredRowDifference.shape C (StoredEmptyTailCompiler.build A last).1.row F _ K hc
    (StoredEmptyTailCompiler.shape A last B K ha)
  have he : 5+F+StoredRowComplementGuards.sizeBudget (StoredEmptyTailCompiler.build A last).1.states.count
      (StoredEmptyTailGuards.sizeBudget n B) = F+increase n B := by
    rw [StoredEmptyTailStates.count_value]; unfold increase; omega
  rw [he] at hs
  exact hs

theorem accepts (C : Row R P c) (A : Row R P n) (last : P)
    {D : Type} [(UniformWordLowering.wordLanguage R).Structure D] (p : P → D) (xs : List D) :
    ((build C A last).1.2.original.dataNFA p).Accepts xs ↔
      (C.original.dataNFA p).Accepts xs ∧ ¬ EmptyTailFiring.Witness A.original last p xs := by
  change ((StoredRowDifference.build C (StoredEmptyTailCompiler.build A last).1.row).1.2.original.dataNFA p).Accepts xs ↔ _
  rw [StoredRowDifference.accepts,StoredEmptyTailCompiler.accepts]
end NSSE.StoredCleanupStep
