import NSSE.MultiVarianceSupportDecision

/-! Executable two-set states for the original mixed-variance SAT model.
Child moves are head-filtered and close in the signed support relation. -/
namespace NSSE.MultiVarianceModelTokens
open MultiConstructorConstraints (Bound Constraints)
open MultiVarianceConstraints MultiVarianceEncoding
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity) (phi : Constraints arity n)

abbrev Tokens (n : Nat) := Finset (Fin n)
abbrev State (n : Nat) := Tokens n × Tokens n

def Refines (S T : State n) : Prop := S.1 ⊆ T.1 ∧ T.2 ⊆ S.2

def down (x : Fin n) : Tokens n :=
  letI := MultiVarianceSupportDecision.supportDecision pol phi
  Finset.univ.filter (fun v => Support pol phi v x)

def up (x : Fin n) : Tokens n :=
  letI := MultiVarianceSupportDecision.supportDecision pol phi
  Finset.univ.filter (fun v => Support pol phi x v)

@[simp] theorem mem_down (x v : Fin n) : v ∈ down pol phi x ↔ Support pol phi v x := by
  simp only [down,Finset.mem_filter,Finset.mem_univ,true_and]

@[simp] theorem mem_up (x v : Fin n) : v ∈ up pol phi x ↔ Support pol phi x v := by
  simp only [up,Finset.mem_filter,Finset.mem_univ,true_and]

theorem down_self (x : Fin n) : x ∈ down pol phi x :=
  (mem_down pol phi x x).mpr (.refl x)

theorem up_self (x : Fin n) : x ∈ up pol phi x :=
  (mem_up pol phi x x).mpr (.refl x)

def start (x : Fin n) : State n := (down pol phi x,up pol phi x)

theorem start_mono {x y : Fin n} (hxy : Support pol phi x y) :
    Refines (start pol phi x) (start pol phi y) := by
  constructor
  · intro v hv
    exact (mem_down pol phi y v).mpr (((mem_down pol phi x v).mp hv).trans hxy)
  · intro v hv
    exact (mem_up pol phi x v).mpr (hxy.trans ((mem_up pol phi y v).mp hv))

/-- `upward` chooses the closure of the actual child tokens, not the polarity. -/
def children (bounds : List (Bound arity n)) (S : Tokens n) (h : H)
    (letter : Nat) (upward : Bool) : Tokens n :=
  letI := MultiVarianceSupportDecision.supportDecision pol phi
  Finset.univ.filter (fun v => ∃ a ∈ bounds, a.parent ∈ S ∧ a.head = h ∧
    ∃ j : Fin (arity a.head), j.val = letter ∧
      if upward then Support pol phi (a.children j) v else Support pol phi v (a.children j))

theorem mem_children (bounds : List (Bound arity n)) (S : Tokens n) (h : H)
    (letter : Nat) (upward : Bool) (v : Fin n) :
    v ∈ children pol phi bounds S h letter upward ↔
      ∃ a ∈ bounds, a.parent ∈ S ∧ a.head = h ∧
        ∃ j : Fin (arity a.head), j.val = letter ∧
          if upward then Support pol phi (a.children j) v else Support pol phi v (a.children j) := by
  simp only [children,Finset.mem_filter,Finset.mem_univ,true_and]

theorem children_mono (bounds : List (Bound arity n)) (S T : Tokens n)
    (hst : S ⊆ T) (h : H) (letter : Nat) (upward : Bool) :
    children pol phi bounds S h letter upward ⊆ children pol phi bounds T h letter upward := by
  intro v hv
  obtain ⟨a,ha,hp,he,j,hj,hs⟩ := (mem_children pol phi bounds S h letter upward v).mp hv
  exact (mem_children pol phi bounds T h letter upward v).mpr ⟨a,ha,hst hp,he,j,hj,hs⟩

/-- Eliminate the dependent head cast by returning a bound with exactly head h. -/
theorem mem_children_typed (bounds : List (Bound arity n)) (S : Tokens n)
    (h : H) (i : Fin (arity h)) (upward : Bool) (v : Fin n) :
    v ∈ children pol phi bounds S h i.val upward ↔
      ∃ p : Fin n, ∃ cs : Fin (arity h) → Fin n,
        (⟨p,h,cs⟩ : Bound arity n) ∈ bounds ∧ p ∈ S ∧
          if upward then Support pol phi (cs i) v else Support pol phi v (cs i) := by
  constructor
  · intro hv
    obtain ⟨⟨p,k,cs⟩,ha,hp,he,j,hj,hs⟩ :=
      (mem_children pol phi bounds S h i.val upward v).mp hv
    dsimp only at he j hj hs hp ha
    subst k
    have hji : j = i := Fin.ext hj
    subst j
    exact ⟨p,cs,ha,hp,hs⟩
  · rintro ⟨p,cs,ha,hp,hs⟩
    exact (mem_children pol phi bounds S h i.val upward v).mpr
      ⟨⟨p,h,cs⟩,ha,hp,rfl,i,rfl,hs⟩

def move (S : State n) (h : H) (i : Fin (arity h)) : State n :=
  if pol h i then
    (children pol phi phi.upper S.2 h i.val false,
     children pol phi phi.lower S.1 h i.val true)
  else
    (children pol phi phi.lower S.1 h i.val false,
     children pol phi phi.upper S.2 h i.val true)

theorem move_refines (S T : State n) (hst : Refines S T) (h : H) (i : Fin (arity h)) :
    if pol h i then Refines (move pol phi T h i) (move pol phi S h i)
      else Refines (move pol phi S h i) (move pol phi T h i) := by
  rcases hst with ⟨hl,hu⟩
  cases hp : pol h i <;> simp only [move,hp,Bool.false_eq_true,if_false,if_true,Refines]
  · exact ⟨children_mono pol phi phi.lower S.1 T.1 hl h i.val false,
      children_mono pol phi phi.upper T.2 S.2 hu h i.val true⟩
  · exact ⟨children_mono pol phi phi.upper T.2 S.2 hu h i.val false,
      children_mono pol phi phi.lower S.1 T.1 hl h i.val true⟩

/-- Compatibility is available to the later finite-shape construction. -/
def Compatible (S : State n) : Prop := ∀ a ∈ S.1, ∀ b ∈ S.2, Support pol phi a b

theorem start_compatible (x : Fin n) : Compatible pol phi (start pol phi x) := by
  intro a ha b hb
  exact ((mem_down pol phi x a).mp ha).trans ((mem_up pol phi x b).mp hb)

theorem move_compatible (S : State n) (hs : Compatible pol phi S)
    (h : H) (i : Fin (arity h)) : Compatible pol phi (move pol phi S h i) := by
  intro x hx y hy
  cases hp : pol h i <;> simp only [move,hp,Bool.false_eq_true,if_false,if_true] at hx hy
  · obtain ⟨a,ca,ha,hpa,hxa⟩ := (mem_children_typed pol phi phi.lower S.1 h i false x).mp hx
    obtain ⟨b,cb,hb,hpb,hby⟩ := (mem_children_typed pol phi phi.upper S.2 h i true y).mp hy
    exact hxa.trans ((Support.decompCov ha hb (hs a hpa b hpb) i hp).trans hby)
  · obtain ⟨b,cb,hb,hpb,hxb⟩ := (mem_children_typed pol phi phi.upper S.2 h i false x).mp hx
    obtain ⟨a,ca,ha,hpa,hay⟩ := (mem_children_typed pol phi phi.lower S.1 h i true y).mp hy
    exact hxb.trans ((Support.decompCon ha hb (hs a hpa b hpb) i hp).trans hay)

theorem card_states : Fintype.card (State n) = 4^n := by
  simp only [State,Tokens,Fintype.card_prod,Fintype.card_finset,Fintype.card_fin]
  rw [← Nat.mul_pow]

end NSSE.MultiVarianceModelTokens
