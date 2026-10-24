import NSSE.StoredDynamicColumn

/-! Dynamic two-tape steps connected to actual stored signed-run certificates. -/
namespace NSSE.StoredDynamicRun
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow StoredDynamicColumn
variable {R : Nat → Type} {P : Type} {n T : Nat}
structure Column (P : Type) where
  flags : Coordinates P
  letters : Coordinates P
abbrev Columns (P : Type) := Nat → Column P × Nat

def flags (C : Columns P) (t : Nat) (i : Fin 2) : P := (StoredRelationTuple.read (C t).1.flags i).1
def letters (C : Columns P) (t : Nat) (i : Fin 2) : P := (StoredRelationTuple.read (C t).1.letters i).1

def transition (A : Automaton R P n) (C : Columns P) (one : P) : StoredRunTable.Step R P n :=
  fun t q r =>
    let a := C t
    let b := StoredDynamicColumn.build A.step a.1.flags a.1.letters one q r
    (⟨b.1,StoredDynamicColumn.qfree A a.1.flags a.1.letters one q r⟩,1+a.2+b.2)
theorem transition_value (A : Automaton R P n) (C : Columns P) (one : P) (t : Nat) (q r : Fin n) :
    denote (transition A C one t q r).1.formula =
      DynamicColumnRunFormula.steps A.original (flags C) (letters C) one t q r := by
  simp only [transition,StoredDynamicColumn.value,DynamicColumnRunFormula.steps,flags,letters]
  rfl

def package (A : Automaton R P n) (C : Columns P) (one : P) (T : Nat) (positive : Bool) :
    StoredRelationalClosure.Package R P × Nat :=
  StoredRunTable.package A.initial A.final (transition A C one) one T positive
theorem package_value (A : Automaton R P n) (C : Columns P) (one : P) (positive : Bool) :
    (package A C one T positive).1.original.toFormula =
      DynamicColumnRunFormula.compile A.original (flags C) (letters C) one T positive := by
  simp only [package,StoredRunTable.package_formula,transition_value,DynamicColumnRunFormula.compile,
    Automaton.original]

def closed (A : Automaton R P n) (C : Columns P) (one : P) (T : Nat) (positive : Bool) : Data R P 0 × Nat :=
  StoredRunTable.closed A.initial A.final (transition A C one) one T positive
theorem closed_value (A : Automaton R P n) (C : Columns P) (one : P) (positive : Bool) :
    denote (closed A C one T positive).1 =
      DynamicColumnRunFormula.compile A.original (flags C) (letters C) one T positive := by
  simp only [closed,StoredRunTable.closed_value,transition_value,DynamicColumnRunFormula.compile,
    Automaton.original]
theorem closed_correct (A : Automaton R P n) (C : Columns P) (zero one : P) (positive : Bool)
    {D : Type*} [(UniformWordLowering.wordLanguage R).Structure D] (p : P → D) (h01 : p zero ≠ p one) :
    Formula.Realize (denote (closed A C one T positive).1) p ↔
      ((A.original.dataInterpret p).Accepts (DynamicColumnRunFormula.inputWord p (flags C) (letters C) one T) ↔ positive = true) := by
  rw [closed_value]
  exact DynamicColumnRunFormula.compile_correct A.original (flags C) (letters C) zero one T positive p h01

def labelCost (c d B K : Nat) := 1+c+d+StoredDynamicColumn.budget c B K
def labelSize (B : Nat) := 109+4*B

theorem label_bounds (A : Automaton R P n) (C : Columns P) (one : P) (c d B K : Nat)
    (h : Bounds A c B K) (hc : ∀ t < T, (C t).2 ≤ d) :
    StoredRunTable.Bounds A.initial A.final (transition A C one) T (labelCost c d B K) (labelSize B) K := by
  constructor
  · intro q
    have hq := h.initial q
    exact ⟨by have hh := hq.cost; unfold labelCost; omega,
      by have hh := hq.nodes; unfold labelSize; omega,hq.arity⟩
  · intro q
    have hq := h.final q
    exact ⟨by have hh := hq.cost; unfold labelCost; omega,
      by have hh := hq.nodes; unfold labelSize; omega,hq.arity⟩
  · intro t ht q r
    have hb := StoredDynamicColumn.bound A (C t).1.flags (C t).1.letters one q r c B K h
    have hn := StoredDynamicColumn.nodes_bound A (C t).1.flags (C t).1.letters one q r c B K h
    have hk := StoredDynamicColumn.arity_bound A (C t).1.flags (C t).1.letters one q r c B K h
    have hd := hc t ht
    refine ⟨?_,hn,hk⟩
    simp only [transition,labelCost]; omega

theorem package_bound (A : Automaton R P n) (C : Columns P) (one : P) (positive : Bool) (c d B K : Nat)
    (h : Bounds A c B K) (hc : ∀ t < T, (C t).2 ≤ d) :
    (package A C one T positive).2 ≤ StoredRunTable.budget n T (labelCost c d B K) (labelSize B) K :=
  StoredRunTable.package_bound _ _ _ one positive _ _ _ (label_bounds A C one c d B K h hc)
theorem package_shape (A : Automaton R P n) (C : Columns P) (one : P) (positive : Bool) (c d B K : Nat)
    (h : Bounds A c B K) (hc : ∀ t < T, (C t).2 ≤ d) :
    StoredRelationalElimination.size (package A C one T positive).1 ≤ StoredRunTable.sizeBudget n T (labelSize B) ∧
    arity (package A C one T positive).1.body ≤ K :=
  ⟨StoredRunTable.package_size _ _ _ one positive _ _ _ (label_bounds A C one c d B K h hc),
   StoredRunTable.package_arity _ _ _ one positive _ _ _ (label_bounds A C one c d B K h hc)⟩
theorem closed_bound (A : Automaton R P n) (C : Columns P) (one : P) (positive : Bool) (c d B K : Nat)
    (h : Bounds A c B K) (hc : ∀ t < T, (C t).2 ≤ d) :
    (closed A C one T positive).2 ≤ 1016*(n+T+labelCost c d B K+labelSize B+K+1)^5 :=
  StoredRunTable.closed_polynomial _ _ _ one positive _ _ _ (label_bounds A C one c d B K h hc)
theorem radius_value (n T c d B K : Nat) :
    n+T+labelCost c d B K+labelSize B+K+1 = 460+n+T+5*c+d+128*B+K+64*K*B := by
  unfold labelCost labelSize StoredDynamicColumn.budget StoredDynamicColumn.cellBudget StoredRunTable.anyBudget
    StoredArrayValidity.everyBudget StoredForwardTableBuild.tabBudget weight
  ring
theorem radius_bound (n T c d B K : Nat) :
    n+T+labelCost c d B K+labelSize B+K+1 ≤ 661*(n+T+c+d+B+K+1)^2 := by
  let u := n+T+c+d+B+K+1
  have hn : n ≤ u := by dsimp [u]; omega
  have ht : T ≤ u := by dsimp [u]; omega
  have hc : c ≤ u := by dsimp [u]; omega
  have hd : d ≤ u := by dsimp [u]; omega
  have hb : B ≤ u := by dsimp [u]; omega
  have hk : K ≤ u := by dsimp [u]; omega
  have hu : 1 ≤ u := by dsimp [u]; omega
  rw [radius_value]
  have hm : 460+n+T+5*c+d+128*B+K+64*K*B ≤ 460+u+u+5*u+u+128*u+u+64*u*u := by gcongr
  change _ ≤ 661*u^2
  nlinarith

theorem closed_polynomial (A : Automaton R P n) (C : Columns P) (one : P) (positive : Bool) (c d B K : Nat)
    (h : Bounds A c B K) (hc : ∀ t < T, (C t).2 ≤ d) :
    (closed A C one T positive).2 ≤ (1016*661^5)*(n+T+c+d+B+K+1)^10 := by
  have hb := closed_bound A C one positive c d B K h hc
  have hp := Nat.mul_le_mul_left 1016 (Nat.pow_le_pow_left (radius_bound n T c d B K) 5)
  refine hb.trans (hp.trans_eq ?_)
  simp only [mul_pow,← pow_mul,Nat.mul_assoc]
end NSSE.StoredDynamicRun
