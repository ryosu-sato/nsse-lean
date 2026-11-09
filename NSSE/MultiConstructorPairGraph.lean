import NSSE.MultiConstructorSpineClosure

/-! The actual supported-pair graph uses simultaneous original lower and
upper child moves with the same head and literal child index. -/
namespace NSSE.MultiConstructorPairGraph
open MultiConstructorConstraints
variable {H : Type*} {arity : H → Nat} {n : Nat}

abbrev Pair (n : Nat) := Fin n × Fin n

def Move (phi : Constraints arity n) (p q : Pair n) : Prop :=
  Support phi p.1 p.2 ∧ ∃ a ∈ phi.lower, ∃ b ∈ phi.upper,
    Support phi a.parent p.1 ∧ Support phi p.2 b.parent ∧
    ∃ i : Fin (arity a.head), ∃ j : Fin (arity b.head),
      a.head = b.head ∧ i.val = j.val ∧ Support phi q.1 (a.children i) ∧ Support phi (b.children j) q.2

def moveDecision [DecidableEq H] (phi : Constraints arity n) : DecidableRel (Move phi) := by
  intro p q
  letI := MultiConstructorSupportDecision.supportDecision phi
  unfold Move
  infer_instance

theorem target_support (phi : Constraints arity n) {p q : Pair n} (hm : Move phi p q) : Support phi q.1 q.2 := by
  obtain ⟨hp,a,ha,b,hb,hap,hpb,i,j,hh,hij,hqi,hjq⟩ := hm
  exact hqi.trans ((MultiConstructorSpineClosure.original_decomp phi a b ha hb hh
    (hap.trans (hp.trans hpb)) i j hij).trans hjq)

theorem move_tokens [DecidableEq H] (phi : Constraints arity n) (hn : ¬LabelClash phi) (p q : Pair n) :
    Move phi p q ↔ Support phi p.1 p.2 ∧ ∃ k : Nat,
      q.1 ∈ MultiConstructorTokens.lowerNext phi {p.1} k ∧
      q.2 ∈ MultiConstructorTokens.upperNext phi {p.2} k := by
  constructor
  · rintro ⟨hp,a,ha,b,hb,hap,hpb,i,j,_,hij,hqi,hjq⟩
    refine ⟨hp,i.val,?_,?_⟩
    · exact (MultiConstructorTokens.mem_lowerNext phi _ _ _).mpr
        ⟨a,ha,⟨p.1,Finset.mem_singleton_self _,hap⟩,i,rfl,hqi⟩
    · exact (MultiConstructorTokens.mem_upperNext phi _ _ _).mpr
        ⟨b,hb,⟨p.2,Finset.mem_singleton_self _,hpb⟩,j,hij.symm,hjq⟩
  · rintro ⟨hp,k,hl,hu⟩
    obtain ⟨a,ha,⟨u,hu',hau⟩,i,hi,hqi⟩ := (MultiConstructorTokens.mem_lowerNext phi _ _ _).mp hl
    obtain ⟨b,hb,⟨v,hv',hvb⟩,j,hj,hjq⟩ := (MultiConstructorTokens.mem_upperNext phi _ _ _).mp hu
    have hu0 : u = p.1 := Finset.mem_singleton.mp hu'
    have hv0 : v = p.2 := Finset.mem_singleton.mp hv'
    subst u; subst v
    have hh : a.head = b.head := by
      by_contra hne
      exact hn (Or.inr (Or.inr (Or.inr ⟨a,ha,b,hb,hau.trans (hp.trans hvb),hne⟩)))
    exact ⟨hp,a,ha,b,hb,hau,hvb,i,j,hh,hi.trans hj.symm,hqi,hjq⟩

def Reach (phi : Constraints arity n) : Pair n → Pair n → Prop := Relation.TransGen (Move phi)
def Cycle (phi : Constraints arity n) : Prop := ∃ p, Reach phi p p

theorem one_reach (phi : Constraints arity n) {p q : Pair n} (hm : Move phi p q) : Reach phi p q := .single hm

theorem reach_trans (phi : Constraints arity n) {p q r : Pair n} (hp : Reach phi p q) (hq : Reach phi q r) :
    Reach phi p r := hp.trans hq

theorem reach_source (phi : Constraints arity n) {p q : Pair n} (hr : Reach phi p q) : Support phi p.1 p.2 := by
  induction hr with
  | single h => exact h.1
  | tail _ _ ih => exact ih

theorem reach_target (phi : Constraints arity n) {p q : Pair n} (hr : Reach phi p q) : Support phi q.1 q.2 := by
  induction hr with
  | single h => exact target_support phi h
  | tail _ h _ => exact target_support phi h

theorem no_cycle_irrefl (phi : Constraints arity n) (hc : ¬Cycle phi) (p : Pair n) : ¬Reach phi p p :=
  fun hp => hc ⟨p,hp⟩

theorem no_cycle_of_no_moves (phi : Constraints arity n) (hm : ∀ p q, ¬Move phi p q) : ¬Cycle phi := by
  rintro ⟨p,hp⟩
  cases hp with
  | single h => exact hm _ _ h
  | tail _ h => exact hm _ _ h

theorem nullary_no_cycle (phi : Constraints arity n) (ha : ∀ h, arity h = 0) : ¬Cycle phi := by
  apply no_cycle_of_no_moves phi
  rintro p q ⟨_,a,_,_,_,_,_,i,_⟩
  have hi := i.isLt
  have hz := ha a.head
  omega

theorem exists_rank (phi : Constraints arity n) (hc : ¬Cycle phi) :
    ∃ rank : Pair n → Nat, (∀ p, rank p < n*n) ∧ (∀ p q, Reach phi p q → rank q < rank p) := by
  classical
  let descendants (p : Pair n) : Finset (Pair n) := Finset.univ.filter (fun q => Reach phi p q)
  have hnot (p : Pair n) : p ∉ descendants p := by
    intro hp
    exact no_cycle_irrefl phi hc p (Finset.mem_filter.mp hp).2
  refine ⟨fun p => (descendants p).card,?_,?_⟩
  · intro p
    have hs : descendants p ⊂ Finset.univ := by
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
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,reach_trans phi hpq (Finset.mem_filter.mp hr).2⟩
    · intro he
      have hq : q ∈ descendants p := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpq⟩
      rw [← he] at hq
      exact hnot q hq

end NSSE.MultiConstructorPairGraph
