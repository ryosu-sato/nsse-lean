import NSSE.MultiVarianceZipperRays

/-! Uniform actual constructor/extremal label bounds. LabelClash is exactly
a supported lower/upper bound pair whose labels are not ordered. -/
namespace NSSE.MultiVarianceLabelBounds
open MultiConstructorConstraints (Bound Constraints)
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceGlobal MultiVarianceSpineSuffixes
variable {H : Type*} {arity : H → Nat} {n m : Nat}

def extreme (upper : Bool) : Label H := if upper then .bot else .top

def assertions (phi : Constraints arity n) (upper : Bool) : List (Fin n) :=
  if upper then phi.bot else phi.top

def LabelBound (phi : Constraints arity n) (upper : Bool) (x : Fin n) (a : Label H) : Prop :=
  (∃ b ∈ bounds phi upper, b.parent=x ∧ a=.node b.head) ∨
    (x ∈ assertions phi upper ∧ a=extreme upper)

@[simp] theorem assertions_remap (f : Fin n → Fin m) (phi : Constraints arity n) (r : Bool) :
    assertions (remap f phi) r = (assertions phi r).map f := by cases r <;> rfl

@[simp] theorem assertions_combine (phi psi : Constraints arity n) (r : Bool) :
    assertions (combine phi psi) r = assertions phi r ++ assertions psi r := by cases r <;> rfl

theorem labelBound_combine (phi psi : Constraints arity n) (r : Bool) (x : Fin n) (a : Label H) :
    LabelBound (combine phi psi) r x a ↔ LabelBound phi r x a ∨ LabelBound psi r x a := by
  simp only [LabelBound,bounds_combine,assertions_combine,List.mem_append]
  constructor
  · rintro (⟨b,hb,hp,ha⟩ | ⟨hx,ha⟩)
    · rcases hb with hb | hb
      · exact Or.inl (Or.inl ⟨b,hb,hp,ha⟩)
      · exact Or.inr (Or.inl ⟨b,hb,hp,ha⟩)
    · rcases hx with hx | hx
      · exact Or.inl (Or.inr ⟨hx,ha⟩)
      · exact Or.inr (Or.inr ⟨hx,ha⟩)
  · rintro ((⟨b,hb,hp,ha⟩ | ⟨hx,ha⟩) | (⟨b,hb,hp,ha⟩ | ⟨hx,ha⟩))
    · exact Or.inl ⟨b,Or.inl hb,hp,ha⟩
    · exact Or.inr ⟨Or.inl hx,ha⟩
    · exact Or.inl ⟨b,Or.inr hb,hp,ha⟩
    · exact Or.inr ⟨Or.inr hx,ha⟩

theorem labelBound_remap (f : Fin n → Fin m) (phi : Constraints arity n) (r : Bool) (x : Fin m) (a : Label H) :
    LabelBound (remap f phi) r x a ↔ ∃ y, x=f y ∧ LabelBound phi r y a := by
  simp only [LabelBound,bounds_remap,assertions_remap]
  constructor
  · rintro (⟨b,hb,hp,ha⟩ | ⟨hx,ha⟩)
    · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
      exact ⟨c.parent,hp.symm,Or.inl ⟨c,hc,rfl,ha⟩⟩
    · obtain ⟨y,hy,he⟩ := List.mem_map.mp hx
      exact ⟨y,he.symm,Or.inr ⟨hy,ha⟩⟩
  · rintro ⟨y,rfl,⟨b,hb,hp,ha⟩ | ⟨hy,ha⟩⟩
    · exact Or.inl ⟨mapBound f b,List.mem_map.mpr ⟨b,hb,rfl⟩,congrArg f hp,ha⟩
    · exact Or.inr ⟨List.mem_map.mpr ⟨y,hy,rfl⟩,ha⟩

variable (pol : Polarity arity)

theorem clash_iff_bounds (phi : Constraints arity n) : LabelClash pol phi ↔
    ∃ x y a b, LabelBound phi false x a ∧ LabelBound phi true y b ∧
      Support pol phi x y ∧ ¬a ≤ b := by
  constructor
  · rintro (⟨x,hx,y,hy,hs⟩ | ⟨x,hx,b,hb,hs⟩ | ⟨a,ha,y,hy,hs⟩ | ⟨a,ha,b,hb,hs,hne⟩)
    · exact ⟨x,y,.top,.bot,Or.inr ⟨hx,rfl⟩,Or.inr ⟨hy,rfl⟩,hs,
        by change ¬Label.Below (.top : Label H) .bot; simp [Label.Below]⟩
    · exact ⟨x,b.parent,.top,.node b.head,Or.inr ⟨hx,rfl⟩,Or.inl ⟨b,hb,rfl,rfl⟩,
        hs,Label.top_not_le_node _⟩
    · exact ⟨a.parent,y,.node a.head,.bot,Or.inl ⟨a,ha,rfl,rfl⟩,Or.inr ⟨hy,rfl⟩,
        hs,Label.node_not_le_bot _⟩
    · exact ⟨a.parent,b.parent,.node a.head,.node b.head,Or.inl ⟨a,ha,rfl,rfl⟩,
        Or.inl ⟨b,hb,rfl,rfl⟩,hs,fun h => hne (Label.node_le_node _ _ |>.mp h)⟩
  · rintro ⟨x,y,a,b,hl,hu,hs,hn⟩
    rcases hl with ⟨c,hc,rfl,rfl⟩ | ⟨hx,rfl⟩ <;>
      rcases hu with ⟨d,hd,rfl,rfl⟩ | ⟨hy,rfl⟩
    · exact Or.inr (Or.inr (Or.inr ⟨c,hc,d,hd,hs,fun he => hn (he ▸ le_rfl)⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨c,hc,y,hy,hs⟩))
    · exact Or.inr (Or.inl ⟨x,hx,d,hd,hs⟩)
    · exact Or.inl ⟨x,hx,y,hy,hs⟩

theorem no_clash_iff (phi : Constraints arity n) : ¬LabelClash pol phi ↔
    ∀ x y a b, LabelBound phi false x a → LabelBound phi true y b → Support pol phi x y → a ≤ b := by
  rw [clash_iff_bounds]
  constructor
  · intro hn x y a b hl hu hs
    by_contra hb
    exact hn ⟨x,y,a,b,hl,hu,hs,hb⟩
  · intro hh ⟨x,y,a,b,hl,hu,hs,hn⟩
    exact hn (hh x y a b hl hu hs)

end NSSE.MultiVarianceLabelBounds
