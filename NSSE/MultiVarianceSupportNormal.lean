import NSSE.MultiVarianceSpineClasses

/-! A syntactic normal form for signed support in an original-plus-spine
extension.  Crossings use only original support and one added/original
decomposition.  Zippers use only old-variable births and added/added
decomposition.  Neither relation contains a general transitivity rule. -/
namespace NSSE.MultiVarianceSupportNormal
open MultiConstructorConstraints (Bound Constraints)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceGlobal
variable {H : Type*} {arity : H → Nat} {n m : Nat}

def extended (phi : Constraints arity n) (extra : Constraints arity m) (old : Fin n → Fin m) :
    Constraints arity m := combine (remap old phi) extra

inductive Crossing (pol : Polarity arity) (phi : Constraints arity n)
    (extra : Constraints arity m) (old : Fin n → Fin m) : Bool → Fin m → Fin n → Prop
  | lowerRoot {x z} : Support pol phi x z → Crossing pol phi extra old false (old x) z
  | upperRoot {x z} : Support pol phi z x → Crossing pol phi extra old true (old x) z
  | lowerClose {p z v} : Crossing pol phi extra old false p z → Support pol phi z v →
      Crossing pol phi extra old false p v
  | upperClose {p z v} : Support pol phi v z → Crossing pol phi extra old true p z →
      Crossing pol phi extra old true p v
  | lowerCov {h p cs x ds}
      (added : (⟨p,h,cs⟩ : Bound arity m) ∈ extra.lower)
      (original : (⟨x,h,ds⟩ : Bound arity n) ∈ phi.upper)
      (parent : Crossing pol phi extra old false p x) (i : Fin (arity h))
      (positive : pol h i = false) : Crossing pol phi extra old false (cs i) (ds i)
  | lowerCon {h p cs x ds}
      (added : (⟨p,h,cs⟩ : Bound arity m) ∈ extra.lower)
      (original : (⟨x,h,ds⟩ : Bound arity n) ∈ phi.upper)
      (parent : Crossing pol phi extra old false p x) (i : Fin (arity h))
      (negative : pol h i = true) : Crossing pol phi extra old true (cs i) (ds i)
  | upperCov {h p cs x ds}
      (original : (⟨x,h,ds⟩ : Bound arity n) ∈ phi.lower)
      (added : (⟨p,h,cs⟩ : Bound arity m) ∈ extra.upper)
      (parent : Crossing pol phi extra old true p x) (i : Fin (arity h))
      (positive : pol h i = false) : Crossing pol phi extra old true (cs i) (ds i)
  | upperCon {h p cs x ds}
      (original : (⟨x,h,ds⟩ : Bound arity n) ∈ phi.lower)
      (added : (⟨p,h,cs⟩ : Bound arity m) ∈ extra.upper)
      (parent : Crossing pol phi extra old true p x) (i : Fin (arity h))
      (negative : pol h i = true) : Crossing pol phi extra old false (cs i) (ds i)

inductive Zipper (pol : Polarity arity) (phi : Constraints arity n)
    (extra : Constraints arity m) (old : Fin n → Fin m) : Fin m → Fin m → Prop
  | birth {p q z} : Crossing pol phi extra old false p z → Crossing pol phi extra old true q z →
      Zipper pol phi extra old p q
  | positive {h p q cs ds}
      (lower : (⟨p,h,cs⟩ : Bound arity m) ∈ extra.lower)
      (upper : (⟨q,h,ds⟩ : Bound arity m) ∈ extra.upper)
      (parent : Zipper pol phi extra old p q) (i : Fin (arity h))
      (positive : pol h i = false) : Zipper pol phi extra old (cs i) (ds i)
  | negative {h p q cs ds}
      (lower : (⟨p,h,cs⟩ : Bound arity m) ∈ extra.lower)
      (upper : (⟨q,h,ds⟩ : Bound arity m) ∈ extra.upper)
      (parent : Zipper pol phi extra old p q) (i : Fin (arity h))
      (negative : pol h i = true) : Zipper pol phi extra old (ds i) (cs i)

def Normal (pol : Polarity arity) (phi : Constraints arity n)
    (extra : Constraints arity m) (old : Fin n → Fin m) (p q : Fin m) : Prop :=
  p = q ∨ (∃ z, q = old z ∧ Crossing pol phi extra old false p z) ∨
    (∃ z, p = old z ∧ Crossing pol phi extra old true q z) ∨ Zipper pol phi extra old p q

variable (pol : Polarity arity) (phi : Constraints arity n) (extra : Constraints arity m)
variable (old : Fin n → Fin m)

theorem lift {x y} (hs : Support pol phi x y) :
    Support pol (extended phi extra old) (old x) (old y) := by
  apply MultiVarianceSupportClasses.lift_support pol phi old (extended phi extra old) ?_ ?_ hs
  · intro a ha
    exact List.mem_append_left _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
  · intro a ha
    exact List.mem_append_left _ (List.mem_map.mpr ⟨a,ha,rfl⟩)

theorem crossing_sound {r p z} (hc : Crossing pol phi extra old r p z) :
    if r then Support pol (extended phi extra old) (old z) p
    else Support pol (extended phi extra old) p (old z) := by
  induction hc with
  | lowerRoot hs => exact lift pol phi extra old hs
  | upperRoot hs => exact lift pol phi extra old hs
  | lowerClose _ hs ih => exact ih.trans (lift pol phi extra old hs)
  | upperClose hs _ ih => exact (lift pol phi extra old hs).trans ih
  | lowerCov ha ho _ i hi ih =>
    exact Support.decompCov (List.mem_append_right _ ha)
      (List.mem_append_left _ (List.mem_map.mpr ⟨_,ho,rfl⟩)) ih i hi
  | lowerCon ha ho _ i hi ih =>
    exact Support.decompCon (List.mem_append_right _ ha)
      (List.mem_append_left _ (List.mem_map.mpr ⟨_,ho,rfl⟩)) ih i hi
  | upperCov ho ha _ i hi ih =>
    exact Support.decompCov (List.mem_append_left _ (List.mem_map.mpr ⟨_,ho,rfl⟩))
      (List.mem_append_right _ ha) ih i hi
  | upperCon ho ha _ i hi ih =>
    exact Support.decompCon (List.mem_append_left _ (List.mem_map.mpr ⟨_,ho,rfl⟩))
      (List.mem_append_right _ ha) ih i hi

theorem zipper_sound {p q} (hz : Zipper pol phi extra old p q) :
    Support pol (extended phi extra old) p q := by
  induction hz with
  | birth hL hR => exact (crossing_sound pol phi extra old hL).trans (crossing_sound pol phi extra old hR)
  | positive hl hu _ i hi ih =>
    exact .decompCov (List.mem_append_right _ hl) (List.mem_append_right _ hu) ih i hi
  | negative hl hu _ i hi ih =>
    exact .decompCon (List.mem_append_right _ hl) (List.mem_append_right _ hu) ih i hi

theorem normal_sound {p q} (hn : Normal pol phi extra old p q) :
    Support pol (extended phi extra old) p q := by
  rcases hn with rfl | ⟨z,rfl,hc⟩ | ⟨z,rfl,hc⟩ | hz
  · exact .refl _
  · exact crossing_sound pol phi extra old hc
  · exact crossing_sound pol phi extra old hc
  · exact zipper_sound pol phi extra old hz

/-- These syntactic conditions are discharged by actual spine compilation
in the next module, without assuming any normal-form conclusion. -/
structure Geometry : Prop where
  old_exact : ∀ x y, Support pol (extended phi extra old) (old x) (old y) ↔ Support pol phi x y
  middle : ∀ p q r, Support pol (extended phi extra old) p q → Support pol (extended phi extra old) q r →
    p = q ∨ q = r ∨ ∃ z, q = old z
  lower_fresh : ∀ b ∈ extra.lower, ∀ i z, b.children i ≠ old z
  upper_fresh : ∀ b ∈ extra.upper, ∀ i z, b.children i ≠ old z
  joint_parent : ∀ a ∈ extra.lower, ∀ b ∈ extra.upper, a.parent = b.parent → ∃ z, a.parent = old z

variable (G : Geometry pol phi extra old)

include G in
theorem crossing_old {r x z} (hc : Crossing pol phi extra old r (old x) z) :
    if r then Support pol phi z x else Support pol phi x z := by
  have hs := crossing_sound pol phi extra old hc
  cases r <;> simp only [Bool.false_eq_true,if_false,if_true] at hs ⊢
  all_goals exact (G.old_exact _ _).mp hs

include G in
theorem zipper_to_old {p q} (hz : Zipper pol phi extra old p q) (z : Fin n) (he : q = old z) :
    Crossing pol phi extra old false p z := by
  cases hz with
  | birth hL hR =>
    subst q
    exact .lowerClose hL (crossing_old pol phi extra old G hR)
  | positive hl hu hp i hi => exact False.elim (G.upper_fresh _ hu i z he)
  | negative hl hu hp i hi => exact False.elim (G.lower_fresh _ hl i z he)

include G in
theorem zipper_from_old {p q} (hz : Zipper pol phi extra old p q) (z : Fin n) (he : p = old z) :
    Crossing pol phi extra old true q z := by
  cases hz with
  | birth hL hR =>
    subst p
    exact .upperClose (crossing_old pol phi extra old G hL) hR
  | positive hl hu hp i hi => exact False.elim (G.lower_fresh _ hl i z he)
  | negative hl hu hp i hi => exact False.elim (G.upper_fresh _ hu i z he)

include G in
theorem normal_to_old {p} (z : Fin n) (hn : Normal pol phi extra old p (old z)) :
    Crossing pol phi extra old false p z := by
  rcases hn with rfl | ⟨v,he,hc⟩ | ⟨v,rfl,hc⟩ | hz
  · exact .lowerRoot (.refl z)
  · have hvz : Support pol phi v z := (G.old_exact v z).mp (he ▸ Support.refl _)
    exact .lowerClose hc hvz
  · exact .lowerRoot (crossing_old pol phi extra old G hc)
  · exact zipper_to_old pol phi extra old G hz z rfl

include G in
theorem normal_from_old {q} (z : Fin n) (hn : Normal pol phi extra old (old z) q) :
    Crossing pol phi extra old true q z := by
  rcases hn with rfl | ⟨v,rfl,hc⟩ | ⟨v,he,hc⟩ | hz
  · exact .upperRoot (.refl z)
  · exact .upperRoot (crossing_old pol phi extra old G hc)
  · have hzv : Support pol phi z v := (G.old_exact z v).mp (he ▸ Support.refl _)
    exact .upperClose hzv hc
  · exact zipper_from_old pol phi extra old G hz z rfl

include G in
theorem normal_trans {p q r} (hp : Normal pol phi extra old p q) (hq : Normal pol phi extra old q r) :
    Normal pol phi extra old p r := by
  rcases G.middle p q r (normal_sound pol phi extra old hp) (normal_sound pol phi extra old hq) with
    rfl | rfl | ⟨z,rfl⟩
  · exact hq
  · exact hp
  · exact Or.inr (Or.inr (Or.inr (.birth (normal_to_old pol phi extra old G z hp)
      (normal_from_old pol phi extra old G z hq))))

include G in
theorem added_zipper (a : Bound arity m) (ha : a ∈ extra.lower)
    (b : Bound arity m) (hb : b ∈ extra.upper)
    (hn : Normal pol phi extra old a.parent b.parent) : Zipper pol phi extra old a.parent b.parent := by
  rcases hn with he | ⟨z,he,hc⟩ | ⟨z,he,hc⟩ | hz
  · obtain ⟨z,hz⟩ := G.joint_parent a ha b hb he
    rw [← he,hz]
    exact .birth (.lowerRoot (.refl z)) (.upperRoot (.refl z))
  · rw [he]
    exact .birth hc (.upperRoot (.refl z))
  · rw [he]
    exact .birth (.lowerRoot (.refl z)) hc
  · exact hz

theorem lower_cases {h p cs}
    (hb : (⟨p,h,cs⟩ : Bound arity m) ∈ (extended phi extra old).lower) :
    (∃ x ds, (⟨x,h,ds⟩ : Bound arity n) ∈ phi.lower ∧ p = old x ∧ cs = fun i => old (ds i)) ∨
      (⟨p,h,cs⟩ : Bound arity m) ∈ extra.lower := by
  rcases List.mem_append.mp hb with hb | hb
  · obtain ⟨⟨x,k,ds⟩,hmem,he⟩ := (List.mem_map (f := mapBound old)).mp hb
    dsimp only [mapBound] at he
    cases he
    exact Or.inl ⟨x,ds,hmem,rfl,rfl⟩
  · exact Or.inr hb

theorem upper_cases {h p cs}
    (hb : (⟨p,h,cs⟩ : Bound arity m) ∈ (extended phi extra old).upper) :
    (∃ x ds, (⟨x,h,ds⟩ : Bound arity n) ∈ phi.upper ∧ p = old x ∧ cs = fun i => old (ds i)) ∨
      (⟨p,h,cs⟩ : Bound arity m) ∈ extra.upper := by
  rcases List.mem_append.mp hb with hb | hb
  · obtain ⟨⟨x,k,ds⟩,hmem,he⟩ := (List.mem_map (f := mapBound old)).mp hb
    dsimp only [mapBound] at he
    cases he
    exact Or.inl ⟨x,ds,hmem,rfl,rfl⟩
  · exact Or.inr hb

include G in
theorem normal_cov {h p q cs ds}
    (hl : (⟨p,h,cs⟩ : Bound arity m) ∈ (extended phi extra old).lower)
    (hu : (⟨q,h,ds⟩ : Bound arity m) ∈ (extended phi extra old).upper)
    (hp : Normal pol phi extra old p q) (i : Fin (arity h)) (hi : pol h i = false) :
    Normal pol phi extra old (cs i) (ds i) := by
  rcases lower_cases phi extra old hl with ⟨x,a,hlo,rfl,rfl⟩ | hlo <;>
    rcases upper_cases phi extra old hu with ⟨y,b,hup,rfl,rfl⟩ | hup
  · have hs := (G.old_exact x y).mp (normal_sound pol phi extra old hp)
    exact Or.inr (Or.inl ⟨b i,rfl,.lowerRoot (.decompCov hlo hup hs i hi)⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a i,rfl,
      .upperCov hlo hup (normal_from_old pol phi extra old G x hp) i hi⟩))
  · exact Or.inr (Or.inl ⟨b i,rfl,
      .lowerCov hlo hup (normal_to_old pol phi extra old G y hp) i hi⟩)
  · exact Or.inr (Or.inr (Or.inr (.positive hlo hup (added_zipper pol phi extra old G _ hlo _ hup hp) i hi)))

include G in
theorem normal_con {h p q cs ds}
    (hl : (⟨p,h,cs⟩ : Bound arity m) ∈ (extended phi extra old).lower)
    (hu : (⟨q,h,ds⟩ : Bound arity m) ∈ (extended phi extra old).upper)
    (hp : Normal pol phi extra old p q) (i : Fin (arity h)) (hi : pol h i = true) :
    Normal pol phi extra old (ds i) (cs i) := by
  rcases lower_cases phi extra old hl with ⟨x,a,hlo,rfl,rfl⟩ | hlo <;>
    rcases upper_cases phi extra old hu with ⟨y,b,hup,rfl,rfl⟩ | hup
  · have hs := (G.old_exact x y).mp (normal_sound pol phi extra old hp)
    exact Or.inr (Or.inl ⟨a i,rfl,.lowerRoot (.decompCon hlo hup hs i hi)⟩)
  · exact Or.inr (Or.inl ⟨a i,rfl,
      .upperCon hlo hup (normal_from_old pol phi extra old G x hp) i hi⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨b i,rfl,
      .lowerCon hlo hup (normal_to_old pol phi extra old G y hp) i hi⟩))
  · exact Or.inr (Or.inr (Or.inr (.negative hlo hup (added_zipper pol phi extra old G _ hlo _ hup hp) i hi)))

include G in
theorem normal_complete {p q} (hs : Support pol (extended phi extra old) p q) : Normal pol phi extra old p q := by
  induction hs with
  | refl _ => exact Or.inl rfl
  | trans _ _ ih1 ih2 => exact normal_trans pol phi extra old G ih1 ih2
  | decompCov hl hu _ i hi ih => exact normal_cov pol phi extra old G hl hu ih i hi
  | decompCon hl hu _ i hi ih => exact normal_con pol phi extra old G hl hu ih i hi

include G in
theorem support_iff_normal (p q : Fin m) :
    Support pol (extended phi extra old) p q ↔ Normal pol phi extra old p q :=
  ⟨normal_complete pol phi extra old G,normal_sound pol phi extra old⟩

end NSSE.MultiVarianceSupportNormal
