import NSSE.MultiVariancePairGraph
import NSSE.MultiVarianceModelHead

/-! The finite shape grammar uses actual lower/upper token sets. Every
Cartesian pair in a signed successor comes from ONE supported parent
pair edge, including reversed and support-closed target intervals. -/
namespace NSSE.MultiVarianceShapeTokens
open MultiConstructorConstraints (Bound Constraints)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceModelTokens
open MultiConstructorTrees (Label)
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

def lowerPins (phi : Constraints arity n) (S : Tokens n) : Finset H := MultiVarianceModelHead.Pins phi S
def upperPins (phi : Constraints arity n) (S : Tokens n) : Finset H :=
  ((phi.upper.filter (fun a => a.parent∈S)).map Bound.head).toFinset

theorem mem_lowerPins (phi : Constraints arity n) (S : Tokens n) (h : H) :
    h∈lowerPins phi S ↔ ∃ a∈phi.lower, a.parent∈S ∧ a.head=h := MultiVarianceModelHead.mem_pins phi S h
theorem mem_upperPins (phi : Constraints arity n) (S : Tokens n) (h : H) :
    h∈upperPins phi S ↔ ∃ a∈phi.upper, a.parent∈S ∧ a.head=h := by
  simp only [upperPins,List.mem_toFinset,List.mem_map,List.mem_filter,decide_eq_true_eq,and_assoc]
theorem lower_pins_mono (phi : Constraints arity n) (S T : Tokens n) (hst : S⊆T) :
    lowerPins phi S⊆lowerPins phi T := MultiVarianceModelHead.pins_mono phi S T hst
theorem upper_pins_mono (phi : Constraints arity n) (S T : Tokens n) (hst : S⊆T) :
    upperPins phi S⊆upperPins phi T := by
  intro h hh
  obtain ⟨a,ha,hp,he⟩ := (mem_upperPins phi S h).mp hh
  exact (mem_upperPins phi T h).mpr ⟨a,ha,hst hp,he⟩

def BottomHit (phi : Constraints arity n) (U : Tokens n) : Prop := ∃ b∈phi.bot, b∈U
instance bottomDecision (phi : Constraints arity n) (U : Tokens n) : Decidable (BottomHit phi U) := by
  unfold BottomHit
  infer_instance
omit [DecidableEq H] in
theorem bottom_mono (phi : Constraints arity n) (S T : Tokens n) (hst : S⊆T) :
    BottomHit phi S → BottomHit phi T := by
  rintro ⟨b,hb,hm⟩
  exact ⟨b,hb,hst hm⟩

variable (pol : Polarity arity)

omit [DecidableEq H] in
theorem bound_heads (phi : Constraints arity n) (hn : ¬LabelClash pol phi) (a b : Bound arity n)
    (ha : a∈phi.lower) (hb : b∈phi.upper) (hs : Support pol phi a.parent b.parent) : a.head=b.head := by
  by_contra hne
  exact hn (Or.inr (Or.inr (Or.inr ⟨a,ha,b,hb,hs,hne⟩)))

theorem pins_equal (phi : Constraints arity n) (hn : ¬LabelClash pol phi) (S : State n)
    (hs : Compatible pol phi S) (h g : H) (hl : h∈lowerPins phi S.1) (hu : g∈upperPins phi S.2) : h=g := by
  obtain ⟨a,ha,hp,he⟩ := (mem_lowerPins phi _ _).mp hl
  obtain ⟨b,hb,hq,hf⟩ := (mem_upperPins phi _ _).mp hu
  exact he.symm.trans ((bound_heads pol phi hn a b ha hb (hs a.parent hp b.parent hq)).trans hf)

theorem child_pair (phi : Constraints arity n) (S : State n) (hs : Compatible pol phi S)
    (h : H) (i : Fin (arity h)) (c e : Fin n)
    (hc : c∈(move pol phi S h i).1) (he : e∈(move pol phi S h i).2) :
    ∃ x∈S.1, ∃ y∈S.2, MultiVariancePairGraph.Move pol phi (x,y) (c,e) := by
  cases hp : pol h i <;> simp only [move,hp,Bool.false_eq_true,if_false,if_true] at hc he
  · obtain ⟨x,ac,ha,hx,hca⟩ := (mem_children_typed pol phi phi.lower S.1 h i false c).mp hc
    obtain ⟨y,bc,hb,hy,hbe⟩ := (mem_children_typed pol phi phi.upper S.2 h i true e).mp he
    refine ⟨x,hx,y,hy,hs x hx y hy,⟨x,h,ac⟩,ha,⟨y,h,bc⟩,hb,.refl x,.refl y,i,i,rfl,rfl,?_⟩
    simpa only [hp,Bool.false_eq_true,if_false] using And.intro hca hbe
  · obtain ⟨y,bc,hb,hy,hcb⟩ := (mem_children_typed pol phi phi.upper S.2 h i false c).mp hc
    obtain ⟨x,ac,ha,hx,hae⟩ := (mem_children_typed pol phi phi.lower S.1 h i true e).mp he
    refine ⟨x,hx,y,hy,hs x hx y hy,⟨x,h,ac⟩,ha,⟨y,h,bc⟩,hb,.refl x,.refl y,i,i,rfl,rfl,?_⟩
    simpa only [hp,if_true] using And.intro hcb hae

end NSSE.MultiVarianceShapeTokens
