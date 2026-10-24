import NSSE.StoredCleanupStep

/-! Actual cleanup iteration over stored rows, with exact state and field recurrences. -/
namespace NSSE.StoredCleanupList
open FirstOrder FirstOrder.Language StoredRelationalRow
variable {R : Nat → Type} {P : Type}
abbrev Packed (R : Nat → Type) (P : Type) := Sigma (Row R P)
def original (A : Packed R P) : EmptyTailRemoval.Candidate (UniformWordLowering.wordLanguage R) P := ⟨A.1,A.2.original⟩

def build (C : Packed R P) : List (Packed R P) → P → Packed R P × Nat
  | [],_ => (C,1)
  | A::rows,last =>
    let a := StoredCleanupStep.build C.2 A.2 last
    let b := build a.1 rows last
    (b.1,2+a.2+b.2)
def stateFactor (ns : List Nat) := (ns.map StoredCleanupStep.factor).prod
def fieldIncrease (ns : List Nat) (B : Nat) := (ns.map (fun n => StoredCleanupStep.increase n B)).sum
def budget (c : Nat) : List Nat → Nat → Nat → Nat
  | [],_,_ => 1
  | n::ns,B,K => 2+StoredCleanupStep.budget c n B K+budget (c*StoredCleanupStep.factor n) ns B K

theorem states (C : Packed R P) (rows : List (Packed R P)) (last : P) :
    (build C rows last).1.1 = C.1*stateFactor (rows.map Sigma.fst) := by
  induction rows generalizing C with
  | nil => simp [build,stateFactor]
  | cons A rows ih =>
    simp only [build,ih,StoredCleanupStep.states,List.map_cons,stateFactor,List.prod_cons]
    simp only [List.map_cons,List.prod_cons,Nat.mul_assoc]

theorem bound (C : Packed R P) (rows : List (Packed R P)) (last : P) (B K : Nat)
    (h : ∀ A ∈ rows, StoredRowTransport.Bounds A.2 B K) :
    (build C rows last).2 ≤ budget C.1 (rows.map Sigma.fst) B K := by
  induction rows generalizing C with
  | nil => exact le_rfl
  | cons A rows ih =>
    have ha := StoredCleanupStep.bound C.2 A.2 last B K (h A (by simp))
    have hb := ih (StoredCleanupStep.build C.2 A.2 last).1 (fun A hA => h A (by simp [hA]))
    conv at hb => rhs; rw [StoredCleanupStep.states]
    simp only [build,List.map_cons,budget]; omega

theorem shape (C : Packed R P) (rows : List (Packed R P)) (last : P) (F B K : Nat)
    (hc : StoredRowTransport.Bounds C.2 F K) (h : ∀ A ∈ rows, StoredRowTransport.Bounds A.2 B K) :
    StoredRowTransport.Bounds (build C rows last).1.2 (F+fieldIncrease (rows.map Sigma.fst) B) K := by
  induction rows generalizing C F with
  | nil => simpa only [build,List.map_nil,fieldIncrease,List.sum_nil,Nat.add_zero] using hc
  | cons A rows ih =>
    have ha := StoredCleanupStep.shape C.2 A.2 last F B K hc (h A (by simp))
    have hb := ih (StoredCleanupStep.build C.2 A.2 last).1 (F+StoredCleanupStep.increase A.1 B) ha
      (fun A hA => h A (by simp [hA]))
    simpa only [build,List.map_cons,fieldIncrease,List.sum_cons,Nat.add_assoc] using hb

theorem accepts (C : Packed R P) (rows : List (Packed R P)) (last : P)
    {D : Type} [(UniformWordLowering.wordLanguage R).Structure D] (p : P → D) (xs : List D) :
    ((build C rows last).1.2.original.dataNFA p).Accepts xs ↔
      (C.2.original.dataNFA p).Accepts xs ∧ ∀ A ∈ rows, ¬ EmptyTailFiring.Witness A.2.original last p xs := by
  induction rows generalizing C with
  | nil => simp [build]
  | cons A rows ih =>
    simp only [build,ih,StoredCleanupStep.accepts,List.forall_mem_cons]
    tauto

theorem original_accepts (C : Packed R P) (rows : List (Packed R P)) (last : P)
    {D : Type} [(UniformWordLowering.wordLanguage R).Structure D] (p : P → D) (xs : List D) :
    ((build C rows last).1.2.original.dataNFA p).Accepts xs ↔
      ((DirectEmptyTailRemoval.subtractList (original C) (rows.map original) last).2.dataNFA p).Accepts xs := by
  rw [accepts,DirectEmptyTailRemoval.subtractList_correct]
  simp only [original,List.forall_mem_map]
end NSSE.StoredCleanupList
