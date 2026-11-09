import NSSE.MultiConstructorLabelSup
import NSSE.MultiConstructorTokens

/-! Actual lower-token states determine canonical root labels. Label
clash freedom supplies exactly the bounds needed by every upper literal. -/
namespace NSSE.MultiConstructorLowerHead
open MultiConstructorConstraints MultiConstructorSupportDecision MultiConstructorTokens MultiConstructorTrees
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

def TopRequired (phi : Constraints arity n) (S : Tokens n) : Prop :=
  ∃ t ∈ phi.top, ∃ v ∈ S, Support phi t v

def topDecision (phi : Constraints arity n) (S : Tokens n) : Decidable (TopRequired phi S) := by
  letI := supportDecision phi
  unfold TopRequired
  infer_instance

def head (phi : Constraints arity n) (S : Tokens n) : Label H :=
  if @decide (TopRequired phi S) (topDecision phi S) then .top else (lowerPins phi S).sup Label.node

theorem head_top (phi : Constraints arity n) (S : Tokens n) (ht : TopRequired phi S) : head phi S = .top := by
  letI := topDecision phi S
  simp only [head,decide_eq_true ht,if_true]

theorem head_no_top (phi : Constraints arity n) (S : Tokens n) (ht : ¬TopRequired phi S) :
    head phi S = (lowerPins phi S).sup Label.node := by
  letI := topDecision phi S
  simp only [head,decide_eq_false ht,Bool.false_eq_true,if_false]

theorem pins_mono (phi : Constraints arity n) (S T : Tokens n) (hst : S ⊆ T) :
    lowerPins phi S ⊆ lowerPins phi T := by
  intro h hh
  obtain ⟨a,ha,⟨v,hv,hav⟩,he⟩ := (mem_lowerPins phi S h).mp hh
  exact (mem_lowerPins phi T h).mpr ⟨a,ha,⟨v,hst hv,hav⟩,he⟩

theorem next_mono (phi : Constraints arity n) (S T : Tokens n) (hst : S ⊆ T) (i : Nat) :
    lowerNext phi S i ⊆ lowerNext phi T i := by
  intro v hv
  obtain ⟨a,ha,⟨t,ht,hat⟩,j,hj,hv⟩ := (mem_lowerNext phi S i v).mp hv
  exact (mem_lowerNext phi T i v).mpr ⟨a,ha,⟨t,hst ht,hat⟩,j,hj,hv⟩

omit [DecidableEq H] in
theorem top_mono (phi : Constraints arity n) (S T : Tokens n) (hst : S ⊆ T) :
    TopRequired phi S → TopRequired phi T := by
  rintro ⟨t,ht,v,hv,htv⟩
  exact ⟨t,ht,v,hst hv,htv⟩

theorem head_mono (phi : Constraints arity n) (S T : Tokens n) (hst : S ⊆ T) : head phi S ≤ head phi T := by
  by_cases ht : TopRequired phi T
  · rw [head_top phi T ht]; exact le_top
  · rw [head_no_top phi T ht,head_no_top phi S (fun h => ht (top_mono phi S T hst h))]
    exact Label.join_heads_mono _ _ (pins_mono phi S T hst)

theorem pin_below (phi : Constraints arity n) (S : Tokens n) (h : H) (hh : h ∈ lowerPins phi S) :
    .node h ≤ head phi S := by
  by_cases ht : TopRequired phi S
  · rw [head_top phi S ht]; exact le_top
  · rw [head_no_top phi S ht]
    exact Label.node_le_join_heads _ h hh

theorem below_upper (phi : Constraints arity n) (hn : ¬LabelClash phi) (S : Tokens n)
    (b : Bound arity n) (hb : b ∈ phi.upper) (hs : ∀ v ∈ S, Support phi v b.parent) :
    head phi S ≤ .node b.head := by
  have ht : ¬TopRequired phi S := by
    rintro ⟨t,ht,v,hv,htv⟩
    exact hn (Or.inr (Or.inl ⟨t,ht,b,hb,htv.trans (hs v hv)⟩))
  rw [head_no_top phi S ht]
  apply Label.join_heads_le
  intro h hh
  obtain ⟨a,ha,⟨v,hv,hav⟩,he⟩ := (mem_lowerPins phi S h).mp hh
  by_contra hne
  exact hn (Or.inr (Or.inr (Or.inr ⟨a,ha,b,hb,hav.trans (hs v hv),by rwa [he]⟩)))

theorem at_bottom (phi : Constraints arity n) (hn : ¬LabelClash phi) (S : Tokens n)
    (b : Fin n) (hb : b ∈ phi.bot) (hs : ∀ v ∈ S, Support phi v b) : head phi S = .bot := by
  have ht : ¬TopRequired phi S := by
    rintro ⟨t,ht,v,hv,htv⟩
    exact hn (Or.inl ⟨t,ht,b,hb,htv.trans (hs v hv)⟩)
  have he : lowerPins phi S = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro h hh
    obtain ⟨a,ha,⟨v,hv,hav⟩,_⟩ := (mem_lowerPins phi S h).mp hh
    exact hn (Or.inr (Or.inr (Or.inl ⟨a,ha,b,hb,hav.trans (hs v hv)⟩)))
  rw [head_no_top phi S ht,he]
  exact Finset.sup_empty

end NSSE.MultiConstructorLowerHead
