import NSSE.SymbolicReachability
import Mathlib.ModelTheory.Complexity
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Exact reachable-state tables as existential first-order syntax

Every table entry is constrained by an equivalence. The same certificate
therefore supports both acceptance and rejection. The constructor reads
guard syntax only; it never decides a semantic guard.
-/

namespace NSSE.ExactReachabilityTable

open FirstOrder FirstOrder.Language SymbolicReachability

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {n T : Nat}

def every (m : Nat) (f : Fin m → L.Formula P) : L.Formula P :=
  ((List.finRange m).map f).foldr (· ⊓ ·) ⊤

@[simp] theorem realize_every {D : Type*} [L.Structure D] (p : P → D)
    (m : Nat) (f : Fin m → L.Formula P) :
    (every m f).Realize p ↔ ∀ i, (f i).Realize p := by
  unfold every Formula.Realize
  simp only [BoundedFormula.realize_foldr_inf, List.mem_map]
  constructor
  · intro h i
    exact h (f i) ⟨i, List.mem_finRange i, rfl⟩
  · rintro h _ ⟨i, _, rfl⟩
    exact h i

def reachable (initial : Fin n → L.Formula P)
    (step : Nat → Fin n → Fin n → L.Formula P)
    {D : Type*} [L.Structure D] (p : P → D) : Nat → Fin n → Prop
  | 0, q => (initial q).Realize p
  | t+1, q => ∃ r, reachable initial step p t r ∧ (step t r q).Realize p

def Consistent (initial : Fin n → L.Formula P)
    (step : Nat → Fin n → Fin n → L.Formula P)
    {D : Type*} [L.Structure D] (p : P → D) (bits : Fin (T+1) → Fin n → Prop) : Prop :=
  (∀ q, bits 0 q ↔ (initial q).Realize p) ∧
    ∀ t : Fin T, ∀ q, bits t.succ q ↔ ∃ r, bits t.castSucc r ∧ (step t r q).Realize p

theorem consistent_exact (initial : Fin n → L.Formula P)
    (step : Nat → Fin n → Fin n → L.Formula P)
    {D : Type*} [L.Structure D] (p : P → D) (bits : Fin (T+1) → Fin n → Prop)
    (h : Consistent initial step p bits) (t : Fin (T+1)) (q : Fin n) :
    bits t q ↔ reachable initial step p t q := by
  obtain ⟨t, ht⟩ := t
  induction t generalizing q with
  | zero => exact h.1 q
  | succ t ih =>
    have ht' : t < T := by omega
    change bits (⟨t, ht'⟩ : Fin T).succ q ↔ _
    rw [h.2 ⟨t, ht'⟩ q]
    exact exists_congr (fun r => and_congr (ih r (by omega)) Iff.rfl)

def bit (one : P) (t : Fin (T+1)) (q : Fin n) : L.Formula (P ⊕ Fin ((T+1)*n)) :=
  (Term.var (.inr (finProdFinEquiv (t,q)))).equal (Term.var (.inl one))

@[simp] theorem realize_bit {D : Type*} [L.Structure D]
    (p : P → D) (bs : Fin ((T+1)*n) → D) (one : P) (t : Fin (T+1)) (q : Fin n) :
    (bit (L := L) one t q).Realize (Sum.elim p bs) ↔ bs (finProdFinEquiv (t,q)) = p one := by
  simp [bit]

def matrix (initial : Fin n → L.Formula P)
    (step : Nat → Fin n → Fin n → L.Formula P) (one : P) (T : Nat) :
    L.Formula (P ⊕ Fin ((T+1)*n)) :=
  every n (fun q => (bit one 0 q).iff ((initial q).relabel Sum.inl)) ⊓
    every T (fun t => every n (fun q =>
      (bit one t.succ q).iff
        (any n (fun r => bit one t.castSucc r ⊓ (step t r q).relabel Sum.inl))))

theorem realize_matrix (initial : Fin n → L.Formula P)
    (step : Nat → Fin n → Fin n → L.Formula P) (one : P)
    {D : Type*} [L.Structure D] (p : P → D) (bs : Fin ((T+1)*n) → D) :
    (matrix initial step one T).Realize (Sum.elim p bs) ↔
      Consistent initial step p (fun t q => bs (finProdFinEquiv (t,q)) = p one) := by
  simp [matrix, Consistent, Formula.realize_iff, Formula.realize_relabel,
    Function.comp_def]

theorem exists_matrix (initial : Fin n → L.Formula P)
    (step : Nat → Fin n → Fin n → L.Formula P) (zero one : P)
    {D : Type*} [L.Structure D] (p : P → D) (h01 : p zero ≠ p one) (T : Nat) :
    ∃ bs : Fin ((T+1)*n) → D, (matrix initial step one T).Realize (Sum.elim p bs) := by
  classical
  let bs : Fin ((T+1)*n) → D := fun i =>
    if reachable initial step p (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
      then p one else p zero
  have hb (t : Fin (T+1)) (q : Fin n) :
      bs (finProdFinEquiv (t,q)) = p one ↔ reachable initial step p t q := by
    simp only [bs, Equiv.symm_apply_apply]
    split_ifs with h <;> simp_all
  refine ⟨bs, (realize_matrix initial step one p bs).mpr ?_⟩
  constructor
  · intro q
    exact hb 0 q
  · intro t q
    simp only [hb, reachable]
    rfl

def output (final : Fin n → L.Formula P) (one : P) (T : Nat) :
    L.Formula (P ⊕ Fin ((T+1)*n)) :=
  any n (fun q => bit one (Fin.last T) q ⊓ (final q).relabel Sum.inl)

theorem matrix_output_exact (initial final : Fin n → L.Formula P)
    (step : Nat → Fin n → Fin n → L.Formula P) (one : P)
    {D : Type*} [L.Structure D] (p : P → D) (bs : Fin ((T+1)*n) → D)
    (h : (matrix initial step one T).Realize (Sum.elim p bs)) :
    (output final one T).Realize (Sum.elim p bs) ↔
      ∃ q, reachable initial step p T q ∧ (final q).Realize p := by
  have hc := (realize_matrix initial step one p bs).mp h
  simp only [output, realize_any, Formula.realize_inf, realize_bit,
    Formula.realize_relabel, Function.comp_def, Sum.elim_inl]
  exact exists_congr (fun q => and_congr
    (consistent_exact initial step p _ hc (Fin.last T) q) Iff.rfl)

def signed (positive : Bool) (f : L.Formula P) : L.Formula P :=
  if positive then f else f.not

@[simp] theorem realize_signed {D : Type*} [L.Structure D]
    (p : P → D) (positive : Bool) (f : L.Formula P) :
    (signed positive f).Realize p ↔ (f.Realize p ↔ positive = true) := by
  cases positive <;> simp [signed]

/-- An executable syntax constructor with exactly (T+1)*n table variables. -/
def compile (initial final : Fin n → L.Formula P)
    (step : Nat → Fin n → Fin n → L.Formula P) (one : P) (T : Nat) (positive : Bool) :
    L.Formula P :=
  closeColumn (matrix initial step one T ⊓ signed positive (output final one T))

theorem compile_correct (initial final : Fin n → L.Formula P)
    (step : Nat → Fin n → Fin n → L.Formula P) (zero one : P) (T : Nat) (positive : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (h01 : p zero ≠ p one) :
    (compile initial final step one T positive).Realize p ↔
      ((∃ q, reachable initial step p T q ∧ (final q).Realize p) ↔ positive = true) := by
  simp only [compile, realize_closeColumn, Formula.realize_inf, realize_signed]
  constructor
  · rintro ⟨bs, hm, hs⟩
    exact (matrix_output_exact initial final step one p bs hm).symm.trans hs
  · intro h
    obtain ⟨bs, hm⟩ := exists_matrix initial step zero one p h01 T
    exact ⟨bs, hm, (matrix_output_exact initial final step one p bs hm).trans h⟩

theorem every_qf (m : Nat) (f : Fin m → L.Formula P) (hf : ∀ i, (f i).IsQF) :
    (every m f).IsQF := by
  have hlist (fs : List (L.Formula P)) (hfs : ∀ f ∈ fs, f.IsQF) :
      (fs.foldr (· ⊓ ·) ⊤).IsQF := by
    induction fs with
    | nil => exact BoundedFormula.IsQF.top
    | cons f fs ih => exact (hfs f (by simp)).inf (ih (fun g hg => hfs g (by simp [hg])))
  apply hlist
  intro g hg
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
  exact hf i

theorem any_qf (m : Nat) (f : Fin m → L.Formula P) (hf : ∀ i, (f i).IsQF) :
    (any m f).IsQF := by
  have hlist (fs : List (L.Formula P)) (hfs : ∀ f ∈ fs, f.IsQF) :
      (fs.foldr (· ⊔ ·) ⊥).IsQF := by
    induction fs with
    | nil => exact BoundedFormula.isQF_bot
    | cons f fs ih => exact (hfs f (by simp)).sup (ih (fun g hg => hfs g (by simp [hg])))
  apply hlist
  intro g hg
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
  exact hf i

theorem relabel_qf {α β : Type*} (f : L.Formula α) (hf : f.IsQF) (g : α → β) :
    (f.relabel g).IsQF := hf.relabel _

theorem bit_qf (one : P) (t : Fin (T+1)) (q : Fin n) : (bit (L := L) one t q).IsQF :=
  BoundedFormula.IsAtomic.isQF (.equal _ _)

theorem iff_qf (f g : L.Formula P) (hf : f.IsQF) (hg : g.IsQF) : (f.iff g).IsQF :=
  (hf.imp hg).inf (hg.imp hf)

theorem matrix_qf (initial : Fin n → L.Formula P)
    (step : Nat → Fin n → Fin n → L.Formula P) (one : P) (T : Nat)
    (hi : ∀ q, (initial q).IsQF) (hs : ∀ t < T, ∀ q r, (step t q r).IsQF) :
    (matrix initial step one T).IsQF := by
  apply BoundedFormula.IsQF.inf
  · apply every_qf
    intro q
    exact iff_qf _ _ (bit_qf _ _ _) (relabel_qf _ (hi q) _)
  · apply every_qf
    intro t
    apply every_qf
    intro q
    apply iff_qf _ _ (bit_qf _ _ _)
    apply any_qf
    intro r
    exact (bit_qf _ _ _).inf (relabel_qf _ (hs t t.isLt r q) _)

theorem output_qf (final : Fin n → L.Formula P) (one : P) (T : Nat)
    (hf : ∀ q, (final q).IsQF) : (output final one T).IsQF := by
  apply any_qf
  intro q
  exact (bit_qf _ _ _).inf (relabel_qf _ (hf q) _)

theorem signed_qf (positive : Bool) (f : L.Formula P) (hf : f.IsQF) :
    (signed positive f).IsQF := by
  cases positive
  · exact hf.not
  · exact hf

/-- The matrix under the newly introduced existential block stays quantifier-free. -/
theorem compile_matrix_qf (initial final : Fin n → L.Formula P)
    (step : Nat → Fin n → Fin n → L.Formula P) (one : P) (T : Nat) (positive : Bool)
    (hi : ∀ q, (initial q).IsQF) (hf : ∀ q, (final q).IsQF)
    (hs : ∀ t < T, ∀ q r, (step t q r).IsQF) :
    (matrix initial step one T ⊓ signed positive (output final one T)).IsQF :=
  (matrix_qf initial step one T hi hs).inf (signed_qf _ _ (output_qf final one T hf))

end NSSE.ExactReachabilityTable
