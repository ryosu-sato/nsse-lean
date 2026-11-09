import NSSE.MultiConstructorPairGraph
import NSSE.MultiConstructorLowerHead

/-! Actual two-sided shape states use lower tokens first and upper tokens
second. Coherence and refinement are proved from original support. -/
namespace NSSE.MultiConstructorShapeTokens
open MultiConstructorConstraints MultiConstructorTokens MultiConstructorTrees
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

abbrev State (n : Nat) := Tokens n × Tokens n

def initial (phi : Constraints arity n) (x : Fin n) : State n := (down phi {x},up phi {x})
def next (phi : Constraints arity n) (s : State n) (i : Nat) : State n :=
  (lowerNext phi s.1 i,upperNext phi s.2 i)
def Coherent (phi : Constraints arity n) (s : State n) : Prop := ∀ a ∈ s.1, ∀ b ∈ s.2, Support phi a b
def Refines (s t : State n) : Prop := s.1 ⊆ t.1 ∧ t.2 ⊆ s.2

theorem initial_coherent (phi : Constraints arity n) (x : Fin n) : Coherent phi (initial phi x) := by
  intro a ha b hb
  change a ∈ down phi {x} at ha
  change b ∈ up phi {x} at hb
  simp only [mem_down,Finset.mem_singleton,exists_eq_left] at ha
  simp only [mem_up,Finset.mem_singleton,exists_eq_left] at hb
  exact ha.trans hb

omit [DecidableEq H] in
theorem bound_heads (phi : Constraints arity n) (hn : ¬LabelClash phi) (a b : Bound arity n)
    (ha : a ∈ phi.lower) (hb : b ∈ phi.upper) (hs : Support phi a.parent b.parent) : a.head = b.head := by
  by_contra hne
  exact hn (Or.inr (Or.inr (Or.inr ⟨a,ha,b,hb,hs,hne⟩)))

theorem pins_equal (phi : Constraints arity n) (hn : ¬LabelClash phi) (s : State n) (hs : Coherent phi s)
    (h g : H) (hl : h ∈ lowerPins phi s.1) (hu : g ∈ upperPins phi s.2) : h = g := by
  obtain ⟨a,ha,⟨x,hx,hax⟩,hah⟩ := (mem_lowerPins phi _ _).mp hl
  obtain ⟨b,hb,⟨y,hy,hyb⟩,hbg⟩ := (mem_upperPins phi _ _).mp hu
  exact hah.symm.trans ((bound_heads phi hn a b ha hb (hax.trans ((hs x hx y hy).trans hyb))).trans hbg)

theorem child_pair (phi : Constraints arity n) (hn : ¬LabelClash phi) (s : State n) (hs : Coherent phi s)
    (i : Nat) (c e : Fin n) (hc : c ∈ (next phi s i).1) (he : e ∈ (next phi s i).2) :
    ∃ x ∈ s.1, ∃ y ∈ s.2, MultiConstructorPairGraph.Move phi (x,y) (c,e) := by
  obtain ⟨a,ha,⟨x,hx,hax⟩,j,hj,hcj⟩ := (mem_lowerNext phi _ _ _).mp hc
  obtain ⟨b,hb,⟨y,hy,hyb⟩,k,hk,hke⟩ := (mem_upperNext phi _ _ _).mp he
  have hh := bound_heads phi hn a b ha hb (hax.trans ((hs x hx y hy).trans hyb))
  exact ⟨x,hx,y,hy,hs x hx y hy,a,ha,b,hb,hax,hyb,j,k,hh,hj.trans hk.symm,hcj,hke⟩

theorem next_coherent (phi : Constraints arity n) (hn : ¬LabelClash phi) (s : State n) (hs : Coherent phi s)
    (i : Nat) : Coherent phi (next phi s i) := by
  intro c hc e he
  obtain ⟨x,_,y,_,hm⟩ := child_pair phi hn s hs i c e hc he
  exact MultiConstructorPairGraph.target_support phi hm

theorem upper_pins_mono (phi : Constraints arity n) (S T : Tokens n) (hst : S ⊆ T) :
    upperPins phi S ⊆ upperPins phi T := by
  intro h hh
  obtain ⟨a,ha,⟨v,hv,hva⟩,he⟩ := (mem_upperPins phi S h).mp hh
  exact (mem_upperPins phi T h).mpr ⟨a,ha,⟨v,hst hv,hva⟩,he⟩

theorem upper_next_mono (phi : Constraints arity n) (S T : Tokens n) (hst : S ⊆ T) (i : Nat) :
    upperNext phi S i ⊆ upperNext phi T i := by
  intro v hv
  obtain ⟨a,ha,⟨t,ht,hta⟩,j,hj,hv⟩ := (mem_upperNext phi S i v).mp hv
  exact (mem_upperNext phi T i v).mpr ⟨a,ha,⟨t,hst ht,hta⟩,j,hj,hv⟩

theorem next_refines (phi : Constraints arity n) (s t : State n) (hst : Refines s t) (i : Nat) :
    Refines (next phi s i) (next phi t i) :=
  ⟨MultiConstructorLowerHead.next_mono phi _ _ hst.1 i,upper_next_mono phi _ _ hst.2 i⟩

def BottomHit (phi : Constraints arity n) (U : Tokens n) : Prop :=
  ∃ u ∈ U, ∃ b ∈ phi.bot, Support phi u b

def bottomDecision (phi : Constraints arity n) (U : Tokens n) : Decidable (BottomHit phi U) := by
  letI := MultiConstructorSupportDecision.supportDecision phi
  unfold BottomHit
  infer_instance

omit [DecidableEq H] in
theorem bottom_mono (phi : Constraints arity n) (S T : Tokens n) (hst : S ⊆ T) :
    BottomHit phi S → BottomHit phi T := by
  rintro ⟨u,hu,b,hb,hs⟩
  exact ⟨u,hst hu,b,hb,hs⟩

end NSSE.MultiConstructorShapeTokens
