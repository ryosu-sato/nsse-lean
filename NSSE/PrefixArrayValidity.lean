import NSSE.DynamicColumnRunFormula

/-! # Prefix-valid scalar presence arrays imply canonicality after empty-column erasure -/

namespace NSSE.PrefixArrayValidity

open FirstOrder FirstOrder.Language CanonicalConvolution ConvolutionShapes ExactReachabilityTable
open DynamicColumnSelection

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {k : Nat}

def ValidWithEmpty {D : Type*} (a : Fin k → Bool) : List (CanonicalConvolution.Column D k) → Prop
  | [] => True
  | c::w => (∀ i, active c i = true → a i = true) ∧ ValidWithEmpty (active c) w

theorem canonical_filter {D : Type*} (w : List (CanonicalConvolution.Column D k)) (a : Fin k → Bool)
    (h : ValidWithEmpty a w) : ValidFrom a (w.filter present) := by
  induction w generalizing a with
  | nil => trivial
  | cons c w ih =>
    cases hp : present c
    · simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte]
      exact validFrom_mono (ih (active c) h.2) h.1
    · simp only [List.filter_cons, hp, ↓reduceIte]
      exact ⟨hp, h.1, ih (active c) h.2⟩

theorem ofFn_valid {D : Type*} (cs : Nat → CanonicalConvolution.Column D k) (T : Nat)
    (a : Fin k → Bool) (h0 : ∀ i, active (cs 0) i = true → a i = true)
    (hs : ∀ t < T, ∀ i, active (cs (t+1)) i = true → active (cs t) i = true) :
    ValidWithEmpty a (List.ofFn (fun t : Fin T => cs t)) := by
  induction T generalizing cs a with
  | zero => trivial
  | succ T ih =>
    rw [List.ofFn_succ]
    refine ⟨h0, ?_⟩
    apply ih (fun t => cs (t+1)) (active (cs 0))
    · exact hs 0 (by omega)
    · intro t ht
      exact hs (t+1) (by omega)

/-- The extra edge into slot T is harmless and allows a uniform rectangular
constraint. Witness arrays set all flags beyond their word length to false. -/
def formula (flags : Nat → Fin k → P) (one : P) (T : Nat) : L.Formula P :=
  every T (fun t => every k (fun i => (flag one (flags (t+1) i)).imp (flag one (flags t i))))

@[simp] theorem realize_formula {D : Type*} [L.Structure D] (p : P → D)
    (flags : Nat → Fin k → P) (one : P) (T : Nat) :
    (formula (L := L) flags one T).Realize p ↔
      ∀ t < T, ∀ i, p (flags (t+1) i) = p one → p (flags t i) = p one := by
  simp only [formula, realize_every, Formula.realize_imp, realize_flag]
  exact ⟨fun h t ht => h ⟨t,ht⟩, fun h t => h t t.isLt⟩

theorem canonical_input {D : Type*} [L.Structure D] (p : P → D)
    (flags letters : Nat → Fin k → P) (one : P) (T : Nat)
    (hv : (formula (L := L) flags one T).Realize p) :
    Canonical (((DynamicColumnRunFormula.inputWord p flags letters one T).map toDense).filter present) := by
  apply canonical_filter _ (fun _ => true)
  unfold DynamicColumnRunFormula.inputWord
  rw [List.map_ofFn]
  apply ofFn_valid (fun t => toDense (column p (flags t) (letters t) one)) T
  · intro i _
    rfl
  · intro t ht i
    have h := (realize_formula p flags one T).mp hv t ht i
    classical
    simpa only [active_toDense, column, mask_code, chosenMask, decide_eq_true_eq] using h

theorem formula_qf (flags : Nat → Fin k → P) (one : P) (T : Nat) :
    (formula (L := L) flags one T).IsQF := by
  apply every_qf
  intro t
  apply every_qf
  intro i
  exact (BoundedFormula.IsAtomic.isQF (.equal _ _)).imp
    (BoundedFormula.IsAtomic.isQF (.equal _ _))

theorem nodes_formula (flags : Nat → Fin k → P) (one : P) (T : Nat) :
    ExactReachabilitySize.nodes (formula (L := L) flags one T) = 3+T*(8+8*k) := by
  simp [formula, ExactReachabilitySize.nodes_every, ExactReachabilitySize.nodes, flag,
    Term.equal, Term.bdEqual, Nat.mul_comm]
  omega

theorem compileH_literal {n : Nat} (R : SymbolicGuardedBlocks.Row L P n)
    (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool)
    (flags letters : Nat → Fin 2 → P) (zero one : P) (T : Nat) (positive : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (h01 : p zero ≠ p one)
    (hv : (formula (L := L) flags one T).Realize p) :
    (DynamicColumnRunFormula.compileH R e seed last first flags letters one T positive).Realize p ↔
      (R.LiteralH e seed last first p
        (CanonicalConvolution.decode ((DynamicColumnRunFormula.inputWord p flags letters one T).map toDense) 0).reverse
        (CanonicalConvolution.decode ((DynamicColumnRunFormula.inputWord p flags letters one T).map toDense) 1).reverse ↔
        positive = true) :=
  DynamicColumnRunFormula.compileH_literal R e seed last first flags letters zero one T positive p h01
    (canonical_input p flags letters one T hv)

end NSSE.PrefixArrayValidity
