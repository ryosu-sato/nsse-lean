import NSSE.MultiVarianceModelTokens
import NSSE.MultiConstructorLabelSup

/-! Root labels of the canonical signed model are joins of lower root demands.
No leastness in the order on original variable valuations is asserted. -/
namespace NSSE.MultiVarianceModelHead
open MultiConstructorConstraints (Bound Constraints)
open MultiVarianceConstraints MultiVarianceEncoding MultiVarianceModelTokens
open MultiConstructorTrees (Label)
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}
variable (phi : Constraints arity n)

def Pins (S : Tokens n) : Finset H :=
  ((phi.lower.filter (fun a => a.parent ∈ S)).map Bound.head).toFinset

theorem mem_pins (S : Tokens n) (h : H) :
    h ∈ Pins phi S ↔ ∃ a ∈ phi.lower, a.parent ∈ S ∧ a.head = h := by
  simp only [Pins,List.mem_toFinset,List.mem_map,List.mem_filter,decide_eq_true_eq,and_assoc]

def TopRequired (S : Tokens n) : Prop := ∃ t ∈ phi.top, t ∈ S

instance topDecision (S : Tokens n) : Decidable (TopRequired phi S) := by
  unfold TopRequired
  infer_instance

def head (S : Tokens n) : Label H :=
  if TopRequired phi S then .top else (Pins phi S).sup Label.node

theorem head_top (S : Tokens n) (ht : TopRequired phi S) : head phi S = .top := by
  simp only [head,if_pos ht]

theorem head_no_top (S : Tokens n) (ht : ¬TopRequired phi S) :
    head phi S = (Pins phi S).sup Label.node := by
  simp only [head,if_neg ht]

theorem pins_mono (S T : Tokens n) (hst : S ⊆ T) : Pins phi S ⊆ Pins phi T := by
  intro h hh
  obtain ⟨a,ha,hp,he⟩ := (mem_pins phi S h).mp hh
  exact (mem_pins phi T h).mpr ⟨a,ha,hst hp,he⟩

theorem head_mono (S T : Tokens n) (hst : S ⊆ T) : head phi S ≤ head phi T := by
  by_cases ht : TopRequired phi T
  · rw [head_top phi T ht]; exact le_top
  · have hs : ¬TopRequired phi S := by
      rintro ⟨t,htop,hm⟩
      exact ht ⟨t,htop,hst hm⟩
    rw [head_no_top phi S hs,head_no_top phi T ht]
    exact Label.join_heads_mono _ _ (pins_mono phi S T hst)

theorem pin_below (S : Tokens n) (a : Bound arity n)
    (ha : a ∈ phi.lower) (hp : a.parent ∈ S) : .node a.head ≤ head phi S := by
  by_cases ht : TopRequired phi S
  · rw [head_top phi S ht]; exact le_top
  · rw [head_no_top phi S ht]
    exact Label.node_le_join_heads _ a.head ((mem_pins phi S a.head).mpr ⟨a,ha,hp,rfl⟩)

variable (pol : Polarity arity)

theorem below_upper (hn : ¬LabelClash pol phi) (S : Tokens n)
    (b : Bound arity n) (hb : b ∈ phi.upper)
    (hs : ∀ v ∈ S, Support pol phi v b.parent) : head phi S ≤ .node b.head := by
  have ht : ¬TopRequired phi S := by
    rintro ⟨t,ht,hv⟩
    exact hn (Or.inr (Or.inl ⟨t,ht,b,hb,hs t hv⟩))
  rw [head_no_top phi S ht]
  apply Label.join_heads_le
  intro h hh
  obtain ⟨a,ha,hp,he⟩ := (mem_pins phi S h).mp hh
  by_contra hne
  exact hn (Or.inr (Or.inr (Or.inr ⟨a,ha,b,hb,hs a.parent hp,by rwa [he]⟩)))

theorem at_bottom (hn : ¬LabelClash pol phi) (S : Tokens n)
    (b : Fin n) (hb : b ∈ phi.bot)
    (hs : ∀ v ∈ S, Support pol phi v b) : head phi S = .bot := by
  have ht : ¬TopRequired phi S := by
    rintro ⟨t,ht,hv⟩
    exact hn (Or.inl ⟨t,ht,b,hb,hs t hv⟩)
  have he : Pins phi S = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro h hh
    obtain ⟨a,ha,hp,_⟩ := (mem_pins phi S h).mp hh
    exact hn (Or.inr (Or.inr (Or.inl ⟨a,ha,b,hb,hs a.parent hp⟩)))
  rw [head_no_top phi S ht,he]
  exact Finset.sup_empty

end NSSE.MultiVarianceModelHead
