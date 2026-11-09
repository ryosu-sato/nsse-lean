import NSSE.MultiVarianceGlobal

/-! Syntactic conservation of original signed support.  The fresh classes
are bound roles, not physical rails.  Negative children exchange classes
and reverse decomposition together.  No satisfiability premise is used. -/
namespace NSSE.MultiVarianceSupportClasses
open MultiConstructorConstraints (Bound Constraints)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceGlobal
variable {H : Type*} {arity : H → Nat} {n m : Nat}

inductive Kind (n : Nat)
  | old : Fin n → Kind n
  | lower : Kind n
  | upper : Kind n
  deriving DecidableEq

def Allowed (pol : Polarity arity) (phi : Constraints arity n) : Kind n → Kind n → Prop
  | .old x, .old y => Support pol phi x y
  | .lower, .old _ => True
  | .old _, .upper => True
  | .lower, .upper => True
  | _, _ => False

def Relation (pol : Polarity arity) (phi : Constraints arity n)
    (tag : Fin m → Kind n) (x y : Fin m) : Prop :=
  x = y ∨ Allowed pol phi (tag x) (tag y)

variable (pol : Polarity arity) (phi : Constraints arity n)
variable (old : Fin n → Fin m) (tag : Fin m → Kind n)
variable (ho : ∀ x, tag (old x) = .old x)

include ho in
theorem relation_old (x y : Fin n) :
    Relation pol phi tag (old x) (old y) ↔ Support pol phi x y := by
  constructor
  · rintro (he | hr)
    · have ht := congrArg tag he
      rw [ho x,ho y] at ht
      cases ht
      exact .refl x
    · simpa only [ho,Allowed] using hr
  · intro hs
    exact Or.inr (by simpa only [ho,Allowed] using hs)

theorem relation_trans {x y z : Fin m}
    (hxy : Relation pol phi tag x y) (hyz : Relation pol phi tag y z) :
    Relation pol phi tag x z := by
  rcases hxy with rfl | hxy
  · exact hyz
  rcases hyz with rfl | hyz
  · exact Or.inr hxy
  apply Or.inr
  cases hx : tag x <;> cases hy : tag y <;> cases hz : tag z <;>
    simp_all only [Allowed]
  exact hxy.trans hyz

def LowerCase (h : H) (p : Fin m) (cs : Fin (arity h) → Fin m) : Prop :=
  (∃ x ds, (⟨x,h,ds⟩ : Bound arity n) ∈ phi.lower ∧
    p = old x ∧ cs = fun i => old (ds i)) ∨
  (∀ i, tag (cs i) = if pol h i then .upper else .lower)

def UpperCase (h : H) (p : Fin m) (cs : Fin (arity h) → Fin m) : Prop :=
  (∃ x ds, (⟨x,h,ds⟩ : Bound arity n) ∈ phi.upper ∧
    p = old x ∧ cs = fun i => old (ds i)) ∨
  (∀ i, tag (cs i) = if pol h i then .lower else .upper)

include ho in
theorem decomp_cov {h : H} {x y : Fin m} {a b : Fin (arity h) → Fin m}
    (hl : LowerCase pol phi old tag h x a) (hu : UpperCase pol phi old tag h y b)
    (hp : Relation pol phi tag x y) (i : Fin (arity h)) (hi : pol h i = false) :
    Relation pol phi tag (a i) (b i) := by
  rcases hl with ⟨x',a',hl,rfl,rfl⟩ | hl <;>
    rcases hu with ⟨y',b',hu,rfl,rfl⟩ | hu
  · exact (relation_old pol phi old tag ho _ _).mpr
      (.decompCov hl hu ((relation_old pol phi old tag ho _ _).mp hp) i hi)
  · exact Or.inr (by simp only [ho,hu,hi,Bool.false_eq_true,if_false,Allowed])
  · exact Or.inr (by simp only [ho,hl,hi,Bool.false_eq_true,if_false,Allowed])
  · exact Or.inr (by simp only [hl,hu,hi,Bool.false_eq_true,if_false,Allowed])

include ho in
theorem decomp_con {h : H} {x y : Fin m} {a b : Fin (arity h) → Fin m}
    (hl : LowerCase pol phi old tag h x a) (hu : UpperCase pol phi old tag h y b)
    (hp : Relation pol phi tag x y) (i : Fin (arity h)) (hi : pol h i = true) :
    Relation pol phi tag (b i) (a i) := by
  rcases hl with ⟨x',a',hl,rfl,rfl⟩ | hl <;>
    rcases hu with ⟨y',b',hu,rfl,rfl⟩ | hu
  · exact (relation_old pol phi old tag ho _ _).mpr
      (.decompCon hl hu ((relation_old pol phi old tag ho _ _).mp hp) i hi)
  · exact Or.inr (by simp only [ho,hu,hi,if_true,Allowed])
  · exact Or.inr (by simp only [ho,hl,hi,if_true,Allowed])
  · exact Or.inr (by simp only [hl,hu,hi,if_true,Allowed])

include ho in
theorem support_class (theta : Constraints arity m)
    (hl : ∀ h x cs, (⟨x,h,cs⟩ : Bound arity m) ∈ theta.lower →
      LowerCase pol phi old tag h x cs)
    (hu : ∀ h x cs, (⟨x,h,cs⟩ : Bound arity m) ∈ theta.upper →
      UpperCase pol phi old tag h x cs)
    {x y : Fin m} (hs : Support pol theta x y) : Relation pol phi tag x y := by
  induction hs with
  | refl x => exact Or.inl rfl
  | trans _ _ ih1 ih2 => exact relation_trans pol phi tag ih1 ih2
  | decompCov lo up _ i hi ih => exact decomp_cov pol phi old tag ho (hl _ _ _ lo) (hu _ _ _ up) ih i hi
  | decompCon lo up _ i hi ih => exact decomp_con pol phi old tag ho (hl _ _ _ lo) (hu _ _ _ up) ih i hi

/-- Renaming may alias variables: injectivity is unnecessary for lifting. -/
theorem lift_support (theta : Constraints arity m)
    (hl : ∀ a ∈ phi.lower, mapBound old a ∈ theta.lower)
    (hu : ∀ a ∈ phi.upper, mapBound old a ∈ theta.upper)
    {x y : Fin n} (hs : Support pol phi x y) : Support pol theta (old x) (old y) := by
  induction hs with
  | refl x => exact .refl _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | @decompCov h x y a b lo up _ i hi ih =>
    exact Support.decompCov (a := fun j => old (a j)) (b := fun j => old (b j))
      (hl _ lo) (hu _ up) ih i hi
  | @decompCon h x y a b lo up _ i hi ih =>
    exact Support.decompCon (a := fun j => old (a j)) (b := fun j => old (b j))
      (hl _ lo) (hu _ up) ih i hi

end NSSE.MultiVarianceSupportClasses
