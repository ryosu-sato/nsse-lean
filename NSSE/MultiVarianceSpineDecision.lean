import NSSE.MultiVarianceOriginalSpine
import NSSE.MultiVarianceSatisfiability

/-! Exact supplied-spine checking and ORIGINAL finite-graph countermodels.
The existence quantifier over spines remains unbounded: this module does
not yet decide arbitrary input entailment or assume the paper witness bound. -/
namespace NSSE.MultiVarianceSpineDecision
open MultiConstructorConstraints (Query)
open MultiVarianceEncoding MultiVarianceTrees MultiVarianceConstraints
open MultiVarianceSpineSeparation MultiVarianceOriginalSpine
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

def validDecision : (s : Spine arity) → Decidable s.Valid
  | .stop a b => inferInstanceAs (Decidable (¬a ≤ b))
  | .step _ _ s => validDecision s

def inspect (Q : Query arity n) (s : Spine arity) : Bool :=
  @decide s.Valid (validDecision s) &&
    MultiVarianceSatisfiability.inspect pol (extension pol Q s)

theorem inspect_correct (Q : Query arity n) (s : Spine arity) :
    inspect pol Q s = true ↔ s.Valid ∧ Satisfiable pol (extension pol Q s) := by
  simp only [inspect, Bool.and_eq_true, decide_eq_true_eq,
    MultiVarianceSatisfiability.inspect_correct]

theorem inspect_original (Q : Query arity n) (s : Spine arity) :
    inspect pol Q s = true ↔ s.Valid ∧
      ∃ rho : Fin n → Tree pol, Satisfies Q.constraints rho ∧
        MultiVarianceFlatSpine.Formula (pol := pol) s (rho Q.left) (rho Q.right) := by
  rw [inspect_correct, satisfiable_extension_iff]

theorem not_entails_iff_exists_no_clash (Q : Query arity n) :
    ¬Entails pol Q ↔ ∃ s : Spine arity, s.Valid ∧ ¬LabelClash pol (extension pol Q s) := by
  rw [not_entails_iff_extension]
  simp only [MultiVarianceCanonicalModel.satisfiable_iff]

theorem not_entails_iff_exists_inspect (Q : Query arity n) :
    ¬Entails pol Q ↔ ∃ s : Spine arity, inspect pol Q s = true := by
  simp only [inspect_correct]
  exact not_entails_iff_extension pol Q

/-- One actual finite graph and root pointers for the ORIGINAL variables.
The graph state count m includes auxiliary variables; the pointer count n does not. -/
structure Code (arity : H → Nat) (n m : Nat) where
  graph : MultiConstructorGraph.Graph arity (MultiVarianceModelTokens.State m)
  roots : Fin n → MultiVarianceModelTokens.State m

def code (Q : Query arity n) (s : Spine arity) : Code arity n (count n s.depth) where
  graph := MultiVarianceCanonicalModel.graph pol (extension pol Q s)
  roots x := MultiVarianceModelTokens.start pol (extension pol Q s) (old s.depth x)

def realize {m : Nat} (C : Code arity n m) (x : Fin n) : Tree pol :=
  MultiVarianceGraph.unfold pol C.graph (C.roots x)

theorem code_spec (Q : Query arity n) (s : Spine arity) (hv : s.Valid)
    (hc : ¬LabelClash pol (extension pol Q s)) :
    Satisfies Q.constraints (realize pol (code pol Q s)) ∧
      ¬realize pol (code pol Q s) Q.left ≤ realize pol (code pol Q s) Q.right :=
  extension_countermodel pol Q s hv
    (MultiVarianceCanonicalModel.model pol (extension pol Q s))
    (MultiVarianceCanonicalModel.satisfies pol (extension pol Q s) hc)

omit [DecidableEq H] in
theorem realize_regular {m : Nat} (C : Code arity n m) (x : Fin n) :
    MultiConstructorRegularTrees.Regular (realize pol C x).raw :=
  ⟨MultiVarianceModelTokens.State m,inferInstance,C.graph,C.roots x,rfl⟩

omit [DecidableEq H] in
theorem state_count (n : Nat) (s : Spine arity) :
    Fintype.card (MultiVarianceModelTokens.State (count n s.depth)) = 4^(n+2*s.depth+2) :=
  MultiVarianceModelTokens.card_states

def extract (Q : Query arity n) (s : Spine arity) : Option (Code arity n (count n s.depth)) :=
  if inspect pol Q s then some (code pol Q s) else none

theorem extract_none (Q : Query arity n) (s : Spine arity) :
    extract pol Q s = none ↔ ¬(s.Valid ∧ Satisfiable pol (extension pol Q s)) := by
  rw [← inspect_correct]
  cases hi : inspect pol Q s <;> simp [extract,hi]

theorem extract_some (Q : Query arity n) (s : Spine arity)
    (C : Code arity n (count n s.depth)) (he : extract pol Q s = some C) :
    s.Valid ∧ Satisfies Q.constraints (realize pol C) ∧
      ¬realize pol C Q.left ≤ realize pol C Q.right := by
  cases hi : inspect pol Q s
  · simp [extract,hi] at he
  · have hc : code pol Q s = C := by simpa [extract,hi] using he
    subst C
    obtain ⟨hv,hs⟩ := (inspect_correct pol Q s).mp hi
    exact ⟨hv, code_spec pol Q s hv
      ((MultiVarianceCanonicalModel.satisfiable_iff pol (extension pol Q s)).mp hs)⟩

def RegularEntails (Q : Query arity n) : Prop :=
  ∀ rho : Fin n → Tree pol, Satisfies Q.constraints rho →
    (∀ x, MultiConstructorRegularTrees.Regular (rho x).raw) → rho Q.left ≤ rho Q.right

/-- A real regular countermodel exists whenever any original countermodel
exists. No depth bound or completion hypothesis is needed for this theorem. -/
theorem regular_entails_iff (Q : Query arity n) : RegularEntails pol Q ↔ Entails pol Q := by
  constructor
  · intro hr
    by_contra hn
    obtain ⟨s,hv,hc⟩ := (not_entails_iff_exists_no_clash pol Q).mp hn
    obtain ⟨hs,hbad⟩ := code_spec pol Q s hv hc
    exact hbad (hr _ hs (realize_regular pol (code pol Q s)))
  · intro he rho hs _
    exact he rho hs

theorem self_inspect_false (Q : Query arity n) (he : Q.left = Q.right) (s : Spine arity) :
    inspect pol Q s = false := by
  cases hi : inspect pol Q s
  · rfl
  · obtain ⟨hv,hs⟩ := (inspect_correct pol Q s).mp hi
    exact False.elim (self_extension_unsatisfiable pol Q he s hv hs)

end NSSE.MultiVarianceSpineDecision
