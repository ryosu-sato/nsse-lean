import NSSE.MultiVariancePeriodicIncidence
import NSSE.MultiVarianceBranchSoundness

/-! An isolated empty physical frontier yields an ACTUAL signed branch
witness by changing only its terminal labels. The chosen extreme follows
the final raw role, and original source consistency is retained. -/
namespace NSSE.MultiVarianceIsolatedWitness
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceTokenExact
open MultiVarianceBranch MultiVarianceBranchLocal MultiVarianceBranchAssignment
open MultiVarianceProperTrace MultiVarianceSideTokens MultiVarianceTerminalIsolation
open MultiVarianceClashCharacterization P0ProperWords
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}
variable (pol : Polarity arity)

def extreme (r : Bool) : Label H := if r then .bot else .top

def changed (C : Parameters arity n) (w : List (Fin D)) (side : Bool) : Parameters arity n :=
  let h := headAt pol C w w.length
  let e := extreme (roleOf (rawAt pol C w w.length).sign side)
  { C with endX := if side then .node h else e, endY := if side then e else .node h }

theorem changed_end (C : Parameters arity n) (w : List (Fin D)) (side : Bool)
    (hw : w≠[]) (hg : GoodWord (P0DZProperMachine.machine (branch pol C D)) w)
    (he : tokensOf (rawAt pol C w w.length) side=∅) :
    EndValid (changed pol C w side) (rawAt pol C w w.length) := by
  have hc := ((P0DZProperMachine.good_iff (branch pol C D) w).mp hg).1
  have hr := (terminal_ready pol C w hw hc).1
  have hr' : MultiVarianceSelectorHead.Ready C.query.constraints (rawAt pol C w w.length)
      (headAt pol C w w.length) := by simpa only [rawAt,headAt,List.take_length] using hr
  have hem (r : Bool) (a : Label H) : Compatible C.query.constraints r ∅ a := by
    intro x hx
    exact (Finset.not_mem_empty x hx).elim
  dsimp only [MultiVarianceSelectorHead.Ready] at hr'
  cases side <;> cases hs : (rawAt pol C w w.length).sign <;>
    simp only [EndValid,changed,extreme,roleOf,tokensOf,hs,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,if_false,if_true] at he hr' ⊢
  · exact ⟨by rw [he]; exact hem false .top,hr'.2,Label.top_not_le_node _⟩
  · exact ⟨by rw [he]; exact hem true .bot,hr'.2,Label.node_not_le_bot _⟩
  · exact ⟨hr'.1,by rw [he]; exact hem true .bot,Label.node_not_le_bot _⟩
  · exact ⟨hr'.1,by rw [he]; exact hem false .top,Label.top_not_le_node _⟩

theorem unchanged_value (C : Parameters arity n) (w : List (Fin D)) (side s : Bool)
    (k : Nat) (hk : k≤w.length) (hn : ¬(k=w.length ∧ s=side)) :
    value pol (changed pol C w side) w s k=.node (headAt pol C w k) := by
  by_cases hl : k<w.length
  · rw [value,if_pos hl]
    rfl
  · have he : k=w.length := by omega
    subst k
    rw [value,if_neg (by omega)]
    cases side <;> cases s <;> simp_all [changed]

theorem accepted (C : Parameters arity n) (w : List (Fin D)) (side : Bool)
    (hw : w≠[]) (hg : GoodWord (P0DZProperMachine.machine (branch pol C D)) w)
    (he : tokensOf (rawAt pol C w w.length) side=∅)
    (hi : ¬Incident pol C w side w.length) : P0DZBranch.Accepted (branch pol (changed pol C w side) D) w := by
  have hc := ((P0DZProperMachine.good_iff (branch pol C D) w).mp hg).1
  apply (MultiVarianceBranchAssignment.accepted_iff pol (changed pol C w side) w).mpr
  constructor
  · apply (local_iff_pointwise pol (changed pol C w side) w _).mpr
    refine ⟨hw,?_,?_⟩
    · intro k hk
      exact (d_guard pol C w hc k hk).1
    · simpa only [rawAt,List.take_length] using changed_end pol C w side hw hg he
  · intro a ha b hb s t hborn l _ hal hbl hm
    have hb' : SymBirth (rawAt pol C w a) s (rawAt pol C w b) t := Or.inl hborn
    have hna : ¬(a+l=w.length ∧ s=side) := by
      rintro ⟨hae,rfl⟩
      exact hi ⟨b,a,l,t,hbl,hae,hb'.symm,fun i h => (hm i h).symm⟩
    have hnb : ¬(b+l=w.length ∧ t=side) := by
      rintro ⟨hbe,rfl⟩
      exact hi ⟨a,b,l,s,hal,hbe,hb',hm⟩
    rw [unchanged_value pol C w side s (a+l) hal hna,unchanged_value pol C w side t (b+l) hbl hnb]
    exact head_match pol C w hg a b l s t hal hbl hb' hm

theorem inspect (C : Parameters arity n) (w : List (Fin D)) (side : Bool)
    (hw : w≠[]) (hg : GoodWord (P0DZProperMachine.machine (branch pol C D)) w)
    (he : tokensOf (rawAt pol C w w.length) side=∅) (hi : ¬Incident pol C w side w.length)
    (ho : ¬MultiVarianceConstraints.LabelClash pol C.query.constraints) :
    MultiVarianceBranchSoundness.inspect pol (changed pol C w side) w=true :=
  (MultiVarianceBranchSoundness.inspect_correct pol _ w).mpr ⟨ho,accepted pol C w side hw hg he hi⟩

theorem periodic_witness (C : Parameters arity n) (side : Bool) (z : Nat → Fin D)
    (hg : P0ProperMachine.Good (P0DZProperMachine.machine (branch pol C D)) z) (k r : Nat)
    (hr : 0<r) (hp : PeriodicCopyHeadNormalization.PhasePeriodic z k r)
    (he : tokensOf (MultiVarianceStreamTrace.rawFrame pol C z k) side=∅)
    (hn : ¬P0PeriodicMonitorInvariant.Permanent (MultiVarianceSelectedMachine.selected pol C D side) z k)
    (ho : ¬MultiVarianceConstraints.LabelClash pol C.query.constraints) :
    MultiVarianceBranchSoundness.inspect pol
      (changed pol C (prefixWord z (2*k+r)) side) (prefixWord z (2*k+r))=true := by
  have hi := (MultiVariancePeriodicIncidence.isolated_at_bound_iff pol C side z hg k r hr hp he).mpr hn
  apply inspect pol C (prefixWord z (2*k+r)) side
  · apply List.length_pos_iff.mp
    rw [prefix_length]
    omega
  · exact MultiVarianceStreamTrace.good_prefix pol C z hg (2*k+r)
  · rw [prefix_length,MultiVarianceStreamTrace.raw_spells pol C _ z (spells_prefix z (2*k+r)) (2*k+r) (by simp)]
    exact MultiVarianceStreamTrace.empty_after pol C z hg side k (2*k+r) (by omega) he
  · rw [prefix_length]
    exact fun h => hi ((MultiVarianceStreamIncidence.incident_spells pol C _ z
      (spells_prefix z (2*k+r)) side (2*k+r) (by simp)).mp h)
  · exact ho

end NSSE.MultiVarianceIsolatedWitness
