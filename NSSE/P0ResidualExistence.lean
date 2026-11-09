import NSSE.P0ResidualDFA
import NSSE.P0RegularExistence

/-! The explicit regular residual now has a total Good-intersection
decision and a short Good infinite-continuation witness. Token semantics
and original-input witness realization are separate obligations. -/
namespace NSSE.P0ResidualExistence
open P0ProperMachine P0ProperWords P0PeriodicInspectionDecision
variable {Q A H : Type*} [Fintype Q] [DecidableEq Q] [DecidableEq A] [DecidableEq H] {r : Nat}

def Condition (M : Machine Q A H) (hr : 0 < r) (cycle : Fin r → A)
    (final : Q → Prop) (w : List A) : Prop :=
  (P0PeriodicSuffixGood.pattern Q hr cycle).IsSuffix w ∧ final (state M w w.length) ∧
    ¬P0PeriodicMonitorInvariant.Permanent M (lasso w hr cycle) w.length

abbrev FilterState (Q : Type*) [Fintype Q] (r : Nat) :=
  P0ResidualDFA.State Q (P0PeriodicSuffixGood.copies (Fintype.card Q)*r) r

def stateCount (N r : Nat) : Nat :=
  2^(P0PeriodicSuffixGood.copies N*r+1) * (N*2^(N*r^2+r+1))

def bound (N r : Nat) : Nat := P0ColorBound.bound (N*stateCount N r+1)-2

theorem card_filter : Fintype.card (FilterState Q r) = stateCount (Fintype.card Q) r :=
  P0ResidualDFA.card_state _ _

theorem regularBound_eq : P0RegularExistence.regularBound Q (FilterState Q r) =
    bound (Fintype.card Q) r := by
  unfold P0RegularExistence.regularBound
  rw [card_filter]
  rfl

omit [DecidableEq H] in
theorem exists_short (M : Machine Q A H) (vd : DecidablePred M.valid) (bd : DecidableRel M.birth)
    (hr : 0 < r) (cycle : Fin r → A) (final : Q → Prop) (fd : DecidablePred final)
    (hex : ∃ w, GoodWord M w ∧ Condition M hr cycle final w) :
    ∃ w, GoodWord M w ∧ Condition M hr cycle final w ∧ Good M (lasso w hr cycle) ∧
      w.length ≤ P0RegularExistence.regularBound Q (FilterState Q r) := by
  let p := P0PeriodicSuffixGood.pattern Q hr cycle
  let F := P0ResidualDFA.automaton M bd hr cycle p final
  have hsource : ∃ w, GoodWord M w ∧ w ∈ F.accepts := by
    obtain ⟨w,hg,hc⟩ := hex
    exact ⟨w,hg,(P0ResidualDFA.recognizes M bd hr cycle p w final).mpr hc⟩
  obtain ⟨w,hg,hf,hlen⟩ := P0RegularExistence.exists_short M vd F
    (P0ResidualDFA.acceptDecision M bd hr cycle p final fd) hsource
  have hc := (P0ResidualDFA.recognizes M bd hr cycle p w final).mp hf
  refine ⟨w,hg,hc,(P0ResidualDFA.accepted_good M bd hr cycle w final hg hf).1,?_⟩
  have hp : p.length = P0PeriodicSuffixGood.copies (Fintype.card Q)*r :=
    P0PeriodicBlocks.block_length hr cycle _
  have hb := congrArg (fun m => P0RegularExistence.regularBound Q
    (P0ResidualDFA.State Q m r)) hp
  exact hlen.trans_eq hb

variable [Fintype A]

def decideExists (M : Machine Q A H) (vd : DecidablePred M.valid) (bd : DecidableRel M.birth)
    (hr : 0 < r) (cycle : Fin r → A) (final : Q → Prop) (fd : DecidablePred final) : Bool :=
  P0RegularExistence.decideExists M vd bd
    (P0ResidualDFA.automaton M bd hr cycle (P0PeriodicSuffixGood.pattern Q hr cycle) final)
    (P0ResidualDFA.acceptDecision M bd hr cycle _ final fd)

theorem decideExists_correct (M : Machine Q A H) (vd : DecidablePred M.valid) (bd : DecidableRel M.birth)
    (hr : 0 < r) (cycle : Fin r → A) (final : Q → Prop) (fd : DecidablePred final) :
    decideExists M vd bd hr cycle final fd = true ↔
      ∃ w, GoodWord M w ∧ Condition M hr cycle final w := by
  unfold decideExists
  rw [P0RegularExistence.decideExists_correct]
  simp_rw [P0ResidualDFA.recognizes]
  rfl

def existenceDecision (M : Machine Q A H) (vd : DecidablePred M.valid) (bd : DecidableRel M.birth)
    (hr : 0 < r) (cycle : Fin r → A) (final : Q → Prop) (fd : DecidablePred final) :
    Decidable (∃ w, GoodWord M w ∧ Condition M hr cycle final w) :=
  decidable_of_iff (decideExists M vd bd hr cycle final fd = true)
    (decideExists_correct M vd bd hr cycle final fd)

end NSSE.P0ResidualExistence
