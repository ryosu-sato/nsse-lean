import NSSE.MultiVarianceModelTokens
import Mathlib.Logic.Relation

/-! Original signed supported-pair edges, including support closure at
their targets. Negative child edges reverse the actual two literal
children. Every edge still descends through an original tree interval. -/
namespace NSSE.MultiVariancePairGraph
open MultiConstructorConstraints (Bound Constraints)
open MultiVarianceEncoding MultiVarianceConstraints
variable {H : Type*} {arity : H → Nat} {n : Nat} (pol : Polarity arity)

abbrev Pair (n : Nat) := Fin n × Fin n

def Move (phi : Constraints arity n) (p q : Pair n) : Prop :=
  Support pol phi p.1 p.2 ∧ ∃ a ∈ phi.lower, ∃ b ∈ phi.upper,
    Support pol phi a.parent p.1 ∧ Support pol phi p.2 b.parent ∧
    ∃ i : Fin (arity a.head), ∃ j : Fin (arity b.head),
      a.head=b.head ∧ i.val=j.val ∧
      if pol a.head i then Support pol phi q.1 (b.children j) ∧ Support pol phi (a.children i) q.2
      else Support pol phi q.1 (a.children i) ∧ Support pol phi (b.children j) q.2

def moveDecision [DecidableEq H] (phi : Constraints arity n) : DecidableRel (Move pol phi) := by
  intro p q
  letI := MultiVarianceSupportDecision.supportDecision pol phi
  unfold Move
  infer_instance

def inspectMove [DecidableEq H] (phi : Constraints arity n) (p q : Pair n) : Bool :=
  @decide (Move pol phi p q) (moveDecision pol phi p q)

theorem inspectMove_correct [DecidableEq H] (phi : Constraints arity n) (p q : Pair n) :
    inspectMove pol phi p q=true ↔ Move pol phi p q := by
  simp only [inspectMove,decide_eq_true_eq]

theorem target_support (phi : Constraints arity n) {p q : Pair n} (hm : Move pol phi p q) :
    Support pol phi q.1 q.2 := by
  obtain ⟨hp,⟨x,h,ac⟩,ha,⟨y,g,bc⟩,hb,hap,hpb,i,j,hh,hij,hc⟩ := hm
  dsimp only at hh i j hij hc hap hpb
  subst g
  have he : i=j := Fin.ext hij
  subst j
  cases hs : pol h i <;> simp only [hs,Bool.false_eq_true,if_false,if_true] at hc
  · exact hc.1.trans ((Support.decompCov ha hb (hap.trans (hp.trans hpb)) i hs).trans hc.2)
  · exact hc.1.trans ((Support.decompCon ha hb (hap.trans (hp.trans hpb)) i hs).trans hc.2)

def Reach (phi : Constraints arity n) : Pair n → Pair n → Prop := Relation.TransGen (Move pol phi)
def Cycle (phi : Constraints arity n) : Prop := ∃ p, Reach pol phi p p

theorem one_reach (phi : Constraints arity n) {p q : Pair n} (hm : Move pol phi p q) :
    Reach pol phi p q := .single hm
theorem reach_trans (phi : Constraints arity n) {p q r : Pair n}
    (hp : Reach pol phi p q) (hq : Reach pol phi q r) : Reach pol phi p r := hp.trans hq
theorem reach_source (phi : Constraints arity n) {p q : Pair n} (hr : Reach pol phi p q) :
    Support pol phi p.1 p.2 := by
  induction hr with
  | single h => exact h.1
  | tail _ _ ih => exact ih
theorem reach_target (phi : Constraints arity n) {p q : Pair n} (hr : Reach pol phi p q) :
    Support pol phi q.1 q.2 := by
  induction hr with
  | single h => exact target_support pol phi h
  | tail _ h _ => exact target_support pol phi h
theorem no_cycle_irrefl (phi : Constraints arity n) (hc : ¬Cycle pol phi) (p : Pair n) :
    ¬Reach pol phi p p := fun hp => hc ⟨p,hp⟩
theorem no_cycle_of_no_moves (phi : Constraints arity n) (hm : ∀ p q, ¬Move pol phi p q) :
    ¬Cycle pol phi := by
  rintro ⟨p,hp⟩
  cases hp with
  | single h => exact hm _ _ h
  | tail _ h => exact hm _ _ h
theorem nullary_no_cycle (phi : Constraints arity n) (ha : ∀ h, arity h=0) : ¬Cycle pol phi := by
  apply no_cycle_of_no_moves pol phi
  rintro p q ⟨_,a,_,_,_,_,_,i,_⟩
  have hi := i.isLt
  have hz := ha a.head
  omega

theorem exists_rank (phi : Constraints arity n) (hc : ¬Cycle pol phi) :
    ∃ rank : Pair n → Nat, (∀ p, rank p<n*n) ∧ (∀ p q, Reach pol phi p q → rank q<rank p) := by
  classical
  let descendants (p : Pair n) : Finset (Pair n) := Finset.univ.filter (fun q => Reach pol phi p q)
  have hnot (p : Pair n) : p∉descendants p := by
    intro hp
    exact no_cycle_irrefl pol phi hc p (Finset.mem_filter.mp hp).2
  refine ⟨fun p => (descendants p).card,?_,?_⟩
  · intro p
    have hs : descendants p⊂Finset.univ := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.subset_univ _,?_⟩
      intro he
      apply hnot p
      rw [he]
      exact Finset.mem_univ _
    simpa only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin] using Finset.card_lt_card hs
  · intro p q hpq
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro r hr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,reach_trans pol phi hpq (Finset.mem_filter.mp hr).2⟩
    · intro he
      have hq : q∈descendants p := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpq⟩
      rw [← he] at hq
      exact hnot q hq

end NSSE.MultiVariancePairGraph
