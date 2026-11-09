import NSSE.P0ResidualExistence

/-! Full safety and permanent-pair monitoring may use DIFFERENT birth
relations. Intersect the actual full-Good language with the monitor's DFA;
the inspection suffix extends full safety independently of the monitor.
No equivalence between the two Good predicates is assumed. -/
namespace NSSE.P0MixedResidual
open P0ProperMachine P0ProperWords P0PeriodicInspectionDecision P0ResidualExistence
variable {Q A H : Type*} [Fintype Q] [DecidableEq Q] [DecidableEq A] [DecidableEq H] {r : Nat}

omit [DecidableEq H] in
theorem exists_short (M T : Machine Q A H) (vd : DecidablePred M.valid) (td : DecidableRel T.birth)
    (hr : 0<r) (cycle : Fin r → A) (final : Q → Prop) (fd : DecidablePred final)
    (hex : ∃ w, GoodWord M w ∧ Condition T hr cycle final w) :
    ∃ w, GoodWord M w ∧ Condition T hr cycle final w ∧ Good M (lasso w hr cycle) ∧
      w.length≤bound (Fintype.card Q) r := by
  let p := P0PeriodicSuffixGood.pattern Q hr cycle
  let F := P0ResidualDFA.automaton T td hr cycle p final
  have hsource : ∃ w, GoodWord M w ∧ w∈F.accepts := by
    obtain ⟨w,hg,hc⟩ := hex
    exact ⟨w,hg,(P0ResidualDFA.recognizes T td hr cycle p w final).mpr hc⟩
  obtain ⟨w,hg,hf,hlen⟩ := P0RegularExistence.exists_short M vd F
    (P0ResidualDFA.acceptDecision T td hr cycle p final fd) hsource
  have hc := (P0ResidualDFA.recognizes T td hr cycle p w final).mp hf
  refine ⟨w,hg,hc,P0PeriodicSuffixGood.suffix_extend M w hr cycle hc.1 hg,?_⟩
  have hp : p.length=P0PeriodicSuffixGood.copies (Fintype.card Q)*r :=
    P0PeriodicBlocks.block_length hr cycle _
  have hb := congrArg (fun m => P0RegularExistence.regularBound Q (P0ResidualDFA.State Q m r)) hp
  exact (hlen.trans_eq hb).trans_eq P0ResidualExistence.regularBound_eq

variable [Fintype A]

def decideExists (M T : Machine Q A H) (vd : DecidablePred M.valid) (bd : DecidableRel M.birth)
    (td : DecidableRel T.birth) (hr : 0<r) (cycle : Fin r → A) (final : Q → Prop) (fd : DecidablePred final) : Bool :=
  P0RegularExistence.decideExists M vd bd
    (P0ResidualDFA.automaton T td hr cycle (P0PeriodicSuffixGood.pattern Q hr cycle) final)
    (P0ResidualDFA.acceptDecision T td hr cycle _ final fd)

theorem decideExists_correct (M T : Machine Q A H) (vd : DecidablePred M.valid) (bd : DecidableRel M.birth)
    (td : DecidableRel T.birth) (hr : 0<r) (cycle : Fin r → A) (final : Q → Prop) (fd : DecidablePred final) :
    decideExists M T vd bd td hr cycle final fd=true ↔ ∃ w, GoodWord M w ∧ Condition T hr cycle final w := by
  unfold decideExists
  rw [P0RegularExistence.decideExists_correct]
  simp_rw [P0ResidualDFA.recognizes]
  rfl

def existenceDecision (M T : Machine Q A H) (vd : DecidablePred M.valid) (bd : DecidableRel M.birth)
    (td : DecidableRel T.birth) (hr : 0<r) (cycle : Fin r → A) (final : Q → Prop) (fd : DecidablePred final) :
    Decidable (∃ w, GoodWord M w ∧ Condition T hr cycle final w) :=
  decidable_of_iff (decideExists M T vd bd td hr cycle final fd=true)
    (decideExists_correct M T vd bd td hr cycle final fd)

end NSSE.P0MixedResidual
