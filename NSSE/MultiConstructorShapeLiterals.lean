import NSSE.MultiConstructorShapeRank

/-! The original four literal forms constrain initial shape heads and
relate their child states to the initial states of the child variables. -/
namespace NSSE.MultiConstructorShapeLiterals
open MultiConstructorConstraints MultiConstructorTokens MultiConstructorShapeTokens
open MultiConstructorShapeHead
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

theorem mem_initial_lower (phi : Constraints arity n) (x v : Fin n) :
    v ∈ (initial phi x).1 ↔ Support phi v x := by
  simp only [initial,mem_down,Finset.mem_singleton,exists_eq_left]

theorem mem_initial_upper (phi : Constraints arity n) (x v : Fin n) :
    v ∈ (initial phi x).2 ↔ Support phi x v := by
  simp only [initial,mem_up,Finset.mem_singleton,exists_eq_left]

theorem lower_pin (phi : Constraints arity n) (a : Bound arity n) (ha : a ∈ phi.lower) :
    a.head ∈ lowerPins phi (initial phi a.parent).1 :=
  (mem_lowerPins phi _ _).mpr ⟨a,ha,⟨a.parent,
    (mem_initial_lower phi _ _).mpr (.refl _),.refl _⟩,rfl⟩

theorem upper_pin (phi : Constraints arity n) (a : Bound arity n) (ha : a ∈ phi.upper) :
    a.head ∈ upperPins phi (initial phi a.parent).2 :=
  (mem_upperPins phi _ _).mpr ⟨a,ha,⟨a.parent,
    (mem_initial_upper phi _ _).mpr (.refl _),.refl _⟩,rfl⟩

theorem upper_child (phi : Constraints arity n) (hn : ¬LabelClash phi)
    (a : Bound arity n) (ha : a ∈ phi.upper) (i : Fin (arity a.head)) :
    Refines (next phi (initial phi a.parent) i.val) (initial phi (a.children i)) := by
  constructor
  · intro v hv
    obtain ⟨b,hb,⟨t,ht,hbt⟩,j,hj,hvj⟩ := (mem_lowerNext phi _ _ _).mp hv
    have hp := hbt.trans ((mem_initial_lower phi _ _).mp ht)
    have hh := bound_heads phi hn b a hb ha hp
    exact (mem_initial_lower phi _ _).mpr
      (hvj.trans (MultiConstructorSpineClosure.original_decomp phi b a hb ha hh hp j i hj))
  · intro v hv
    exact (mem_upperNext phi _ _ _).mpr ⟨a,ha,⟨a.parent,
      (mem_initial_upper phi _ _).mpr (.refl _),.refl _⟩,i,rfl,
      (mem_initial_upper phi _ _).mp hv⟩

theorem lower_child (phi : Constraints arity n) (hn : ¬LabelClash phi)
    (a : Bound arity n) (ha : a ∈ phi.lower) (i : Fin (arity a.head)) :
    Refines (initial phi (a.children i)) (next phi (initial phi a.parent) i.val) := by
  constructor
  · intro v hv
    exact (mem_lowerNext phi _ _ _).mpr ⟨a,ha,⟨a.parent,
      (mem_initial_lower phi _ _).mpr (.refl _),.refl _⟩,i,rfl,
      (mem_initial_lower phi _ _).mp hv⟩
  · intro v hv
    obtain ⟨b,hb,⟨t,ht,htb⟩,j,hj,hjv⟩ := (mem_upperNext phi _ _ _).mp hv
    have hp := ((mem_initial_upper phi _ _).mp ht).trans htb
    have hh := bound_heads phi hn a b ha hb hp
    exact (mem_initial_upper phi _ _).mpr
      ((MultiConstructorSpineClosure.original_decomp phi a b ha hb hh hp i j hj.symm).trans hjv)

theorem upper_head (phi : Constraints arity n) (hn : ¬LabelClash phi)
    (a : Bound arity n) (ha : a ∈ phi.upper) :
    head phi (initial phi a.parent) = .bot ∨ head phi (initial phi a.parent) = .node a.head := by
  have hu := upper_pin phi a ha
  by_cases hl : lowerPins phi (initial phi a.parent).1 = ∅
  · exact Or.inl (empty_lower_upper phi _ hl (Finset.nonempty_iff_ne_empty.mp ⟨a.head,hu⟩))
  · obtain ⟨g,hg⟩ := Finset.nonempty_iff_ne_empty.mpr hl
    have he := pins_equal phi hn _ (initial_coherent phi a.parent) g a.head hg hu
    exact Or.inr (node_of_pins phi hn _ (initial_coherent phi a.parent) a.head (he ▸ hg) hu)

theorem lower_head (phi : Constraints arity n) (hn : ¬LabelClash phi)
    (a : Bound arity n) (ha : a ∈ phi.lower) :
    head phi (initial phi a.parent) = .top ∨ head phi (initial phi a.parent) = .node a.head := by
  have hl := lower_pin phi a ha
  by_cases hu : upperPins phi (initial phi a.parent).2 = ∅
  · exact Or.inl (nonempty_lower_no_upper phi _ (Finset.nonempty_iff_ne_empty.mp ⟨a.head,hl⟩) hu)
  · obtain ⟨g,hg⟩ := Finset.nonempty_iff_ne_empty.mpr hu
    have he := pins_equal phi hn _ (initial_coherent phi a.parent) a.head g hl hg
    exact Or.inr (node_of_pins phi hn _ (initial_coherent phi a.parent) a.head hl (he.symm ▸ hg))

theorem bot_head (phi : Constraints arity n) (hn : ¬LabelClash phi)
    (x : Fin n) (hx : x ∈ phi.bot) : head phi (initial phi x) = .bot := by
  have hl : lowerPins phi (initial phi x).1 = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro h hh
    obtain ⟨a,ha,⟨t,ht,hat⟩,_⟩ := (mem_lowerPins phi _ _).mp hh
    exact hn (Or.inr (Or.inr (Or.inl ⟨a,ha,x,hx,
      hat.trans ((mem_initial_lower phi _ _).mp ht)⟩)))
  exact empty_lower_bottom phi _ hl ⟨x,(mem_initial_upper phi _ _).mpr (.refl _),x,hx,.refl _⟩

theorem top_head (phi : Constraints arity n) (hn : ¬LabelClash phi)
    (x : Fin n) (hx : x ∈ phi.top) : head phi (initial phi x) = .top := by
  have hu : upperPins phi (initial phi x).2 = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro h hh
    obtain ⟨a,ha,⟨t,ht,hta⟩,_⟩ := (mem_upperPins phi _ _).mp hh
    exact hn (Or.inr (Or.inl ⟨x,hx,a,ha,
      ((mem_initial_upper phi _ _).mp ht).trans hta⟩))
  have hb : ¬BottomHit phi (initial phi x).2 := by
    rintro ⟨u,hu,b,hb,hub⟩
    exact hn (Or.inl ⟨x,hx,b,hb,((mem_initial_upper phi _ _).mp hu).trans hub⟩)
  exact no_upper_no_bottom phi _ hu hb

end NSSE.MultiConstructorShapeLiterals
