import NSSE.P0SuffixPatternDFA
import NSSE.P0PeriodicMonitor
import NSSE.P0PeriodicSuffixGood

/-! Exact finite residual filter: a literal suffix, a supplied final-state
predicate, and absence of a permanent comparison. Good is checked separately. -/
namespace NSSE.P0ResidualDFA
open P0ProperMachine P0ProperWords P0PeriodicDriver P0PeriodicInspectionDecision
variable {Q A H : Type*} [Fintype Q] [DecidableEq Q] [DecidableEq A] {r : Nat}

abbrev State (Q : Type*) (m r : Nat) :=
  P0SuffixPatternDFA.State m × P0PeriodicMonitor.State Q r

instance stateDecision (m r : Nat) : DecidableEq (State Q m r) :=
  @instDecidableEqProd (P0SuffixPatternDFA.State m) (P0PeriodicMonitor.State Q r)
    inferInstance inferInstance

theorem card_state (m r : Nat) :
    Fintype.card (State Q m r) = 2^(m+1) * (Fintype.card Q * 2^(Fintype.card Q*r^2+r+1)) := by
  change Fintype.card (P0SuffixPatternDFA.State m × P0PeriodicMonitor.State Q r) = _
  rw [Fintype.card_prod,P0SuffixPatternDFA.card_state,P0PeriodicMonitor.card_state]

def automaton (M : Machine Q A H) (bd : DecidableRel M.birth)
    (hr : 0 < r) (cycle : Fin r → A) (p : List A) (final : Q → Prop) : DFA A (State Q p.length r) where
  start := (P0SuffixPatternDFA.start p.length,P0PeriodicMonitor.start M bd)
  step s a := (P0SuffixPatternDFA.step p s.1 a,P0PeriodicMonitor.step M bd hr cycle s.2 a)
  accept s := s.1 ⟨p.length,by omega⟩ = true ∧ final s.2.1 ∧ P0PeriodicMonitor.accepts hr s.2 = false

def acceptDecision (M : Machine Q A H) (bd : DecidableRel M.birth)
    (hr : 0 < r) (cycle : Fin r → A) (p : List A) (final : Q → Prop) (fd : DecidablePred final) :
    DecidablePred (automaton M bd hr cycle p final).accept := by
  letI := fd
  intro s
  change Decidable (_ = true ∧ final s.2.1 ∧ _ = false)
  infer_instance

theorem eval_pair (M : Machine Q A H) (bd : DecidableRel M.birth)
    (hr : 0 < r) (cycle : Fin r → A) (p w : List A) (final : Q → Prop) :
    (automaton M bd hr cycle p final).eval w =
      ((P0SuffixPatternDFA.automaton p).eval w,(P0PeriodicMonitor.automaton M bd hr cycle).eval w) := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
    rw [DFA.eval_append_singleton,DFA.eval_append_singleton,DFA.eval_append_singleton,ih]
    rfl

theorem monitor_state (M : Machine Q A H) (bd : DecidableRel M.birth)
    (hr : 0 < r) (cycle : Fin r → A) (w : List A) :
    ((P0PeriodicMonitor.automaton M bd hr cycle).eval w).1 = state M w w.length := by
  let z := lasso w hr cycle
  have he := P0PeriodicMonitor.eval_prefix M bd hr cycle z w.length
  rw [P0PeriodicMonitor.prefix_lasso] at he
  rw [he,(P0PeriodicMonitor.invariant_trace M bd hr cycle z w.length).1,
    state_eq_run M w z (P0PeriodicBlocks.lasso_spells w hr cycle) w.length (by omega)]

theorem recognizes (M : Machine Q A H) (bd : DecidableRel M.birth)
    (hr : 0 < r) (cycle : Fin r → A) (p w : List A) (final : Q → Prop) :
    w ∈ (automaton M bd hr cycle p final).accepts ↔
      p.IsSuffix w ∧ final (state M w w.length) ∧
        ¬P0PeriodicMonitorInvariant.Permanent M (lasso w hr cycle) w.length := by
  rw [DFA.mem_accepts,eval_pair]
  change (P0SuffixPatternDFA.inspect p w = true ∧
    final (((P0PeriodicMonitor.automaton M bd hr cycle).eval w).1) ∧
    P0PeriodicMonitor.inspect M bd hr cycle w = false) ↔ _
  rw [P0SuffixPatternDFA.inspect_correct,monitor_state]
  simp only [Bool.eq_false_iff,ne_eq,P0PeriodicMonitor.inspect_correct]

theorem accepted_good (M : Machine Q A H) (bd : DecidableRel M.birth)
    (hr : 0 < r) (cycle : Fin r → A) (w : List A) (final : Q → Prop)
    (hw : GoodWord M w)
    (hf : w ∈ (automaton M bd hr cycle (P0PeriodicSuffixGood.pattern Q hr cycle) final).accepts) :
    Good M (lasso w hr cycle) ∧ final (state M w w.length) ∧
      ¬P0PeriodicMonitorInvariant.Permanent M (lasso w hr cycle) w.length := by
  obtain ⟨hs,hq,hp⟩ := (recognizes M bd hr cycle _ w final).mp hf
  exact ⟨P0PeriodicSuffixGood.suffix_extend M w hr cycle hs hw,hq,hp⟩

end NSSE.P0ResidualDFA
