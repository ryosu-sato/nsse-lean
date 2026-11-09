import NSSE.MultiVarianceFillClashes

/-! Exact LabelClash characterization for the actual signed spine extension:
original clash freedom, local original/token compatibility, and all physical
ray endpoint orders. No validity or satisfiability assumption is supplied. -/
namespace NSSE.MultiVarianceClashCharacterization
open MultiConstructorConstraints (Constraints Query)
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceOriginalSpine
open MultiVarianceSpineSeparation MultiVarianceSpineClasses MultiVarianceSpineNormal
open MultiVarianceSpineSuffixes MultiVarianceLiteralGeometry MultiVariancePositionLiterals
open MultiVarianceRailBirths MultiVarianceRailCoordinates MultiVariancePhysicalRays MultiVarianceZipperRays
open MultiVarianceLabelBounds MultiVarianceSpineLabels MultiVarianceFillClashes
open MultiVarianceModelTokens (Tokens)
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

def Compatible (phi : Constraints arity n) (r : Bool) (S : Tokens n) (a : Label H) : Prop :=
  ∀ z ∈ S, ∀ b, LabelBound phi (!r) z b → if r then b ≤ a else a ≤ b

variable (pol : Polarity arity)

def LocalGood (Q : Query arity n) (s : Spine arity) : Prop :=
  ∀ d, ∀ hd : d ≤ s.depth, ∀ r,
    Compatible Q.constraints r (tokensAt pol Q s (rolePosition pol Q s d hd r)) (label (suffix s d) r)

def RayGood (Q : Query arity n) (s : Spine arity) : Prop :=
  ∀ d, ∀ hd : d ≤ s.depth, ∀ e, ∀ he : e ≤ s.depth,
    Ray pol Q s (rolePosition pol Q s d hd false) (rolePosition pol Q s e he true) →
      label (suffix s d) false ≤ label (suffix s e) true

omit [DecidableEq H] in
theorem old_label (Q : Query arity n) (s : Spine arity) (r : Bool) (z : Fin n) (a : Label H)
    (ha : LabelBound Q.constraints r z a) : LabelBound (extension pol Q s) r (old s.depth z) a :=
  (extension_label_origin pol Q s r _ a).mpr (Or.inl ⟨z,rfl,ha⟩)

omit [DecidableEq H] in
theorem actual_rail_label (Q : Query arity n) (s : Spine arity) (d : Nat) (hd : d ≤ s.depth)
    (r : Bool) (ha : Active r (label (suffix s d) r)) :
    LabelBound (extension pol Q s) r (roleVariable Q s d hd r) (label (suffix s d) r) :=
  (extension_label_origin pol Q s r _ _).mpr (Or.inr (Or.inl ⟨d,hd,rfl,rfl,ha⟩))

omit [DecidableEq H] in
theorem original_no_clash (Q : Query arity n) (s : Spine arity) (hc : ¬LabelClash pol (extension pol Q s)) :
    ¬LabelClash pol Q.constraints := by
  apply (no_clash_iff pol Q.constraints).mpr
  intro x y a b hl hu hs
  exact (no_clash_iff pol (extension pol Q s)).mp hc _ _ a b
    (old_label pol Q s false x a hl) (old_label pol Q s true y b hu)
    ((old_support_iff pol Q s x y).mpr hs)

theorem local_of_no_clash (Q : Query arity n) (s : Spine arity) (hc : ¬LabelClash pol (extension pol Q s)) :
    LocalGood pol Q s := by
  intro d hd r z hz b hb
  by_cases ha : Active r (label (suffix s d) r)
  · have hl := actual_rail_label pol Q s d hd r ha
    have ho := old_label pol Q s (!r) z b hb
    have hs := (crossing_iff pol Q s (rolePosition pol Q s d hd r) z).mpr hz
    simp only [rolePosition_role,rolePosition_variable] at hs
    cases r <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true] at ho hs ⊢
    · exact (no_clash_iff pol (extension pol Q s)).mp hc _ _ _ b hl ho hs
    · exact (no_clash_iff pol (extension pol Q s)).mp hc _ _ b _ ho hl hs
  · have he : label (suffix s d) r = extreme (!r) := not_not.mp ha
    rw [he]
    cases r
    · exact bot_le
    · exact le_top

theorem rays_of_no_clash (Q : Query arity n) (s : Spine arity) (hc : ¬LabelClash pol (extension pol Q s)) :
    RayGood pol Q s := by
  intro d hd e he hr
  by_cases hl : Active false (label (suffix s d) false)
  · by_cases hu : Active true (label (suffix s e) true)
    · exact (no_clash_iff pol (extension pol Q s)).mp hc _ _ _ _
        (actual_rail_label pol Q s d hd false hl) (actual_rail_label pol Q s e he true hu)
        (ray_role_support pol Q s d hd e he hr)
    · have hh : label (suffix s e) true = .top := not_not.mp hu
      rw [hh]
      exact le_top
  · have hh : label (suffix s d) false = .bot := not_not.mp hl
    rw [hh]
    exact bot_le

theorem no_clash_of_conditions (Q : Query arity n) (s : Spine arity)
    (ho : ¬LabelClash pol Q.constraints) (hl : LocalGood pol Q s) (hr : RayGood pol Q s) :
    ¬LabelClash pol (extension pol Q s) := by
  apply (no_clash_iff pol (extension pol Q s)).mpr
  intro x y a b hx hy hs
  have hx' := (extension_label_origin pol Q s false x a).mp hx
  have hy' := (extension_label_origin pol Q s true y b).mp hy
  rcases hx' with ⟨u,rfl,hu⟩ | ⟨d,hd,rfl,hda,_⟩ | ⟨rfl,_⟩
  · rcases hy' with ⟨v,rfl,hv⟩ | ⟨e,he,rfl,heb,_⟩ | ⟨rfl,_⟩
    · exact (no_clash_iff pol Q.constraints).mp ho u v a b hu hv ((old_support_iff pol Q s u v).mp hs)
    · have hm : u ∈ tokensAt pol Q s (rolePosition pol Q s e he true) := by
        apply (crossing_iff pol Q s (rolePosition pol Q s e he true) u).mp
        simpa only [rolePosition_role,rolePosition_variable,if_true] using hs
      have hh := hl e he true u hm a hu
      simpa only [if_true,heb] using hh
    · exact False.elim (no_support_to_bottom_fill pol Q s _ a hx hs)
  · rcases hy' with ⟨v,rfl,hv⟩ | ⟨e,he,rfl,heb,_⟩ | ⟨rfl,_⟩
    · have hm : v ∈ tokensAt pol Q s (rolePosition pol Q s d hd false) := by
        apply (crossing_iff pol Q s (rolePosition pol Q s d hd false) v).mp
        simpa only [rolePosition_role,rolePosition_variable,Bool.false_eq_true,if_false] using hs
      have hh := hl d hd false v hm b hv
      simpa only [Bool.false_eq_true,if_false,hda] using hh
    · have hh := hr d hd e he (support_ray pol Q s d hd e he hs)
      simpa only [hda,heb] using hh
    · exact False.elim (no_support_to_bottom_fill pol Q s _ a hx hs)
  · exact False.elim (no_support_from_top_fill pol Q s _ b hy hs)

/-- The complete actual gadget clash test, including all original,
crossing, terminal/extremal and physical-ray cases. -/
theorem no_label_clash_iff (Q : Query arity n) (s : Spine arity) :
    ¬LabelClash pol (extension pol Q s) ↔
      ¬LabelClash pol Q.constraints ∧ LocalGood pol Q s ∧ RayGood pol Q s :=
  ⟨fun hc => ⟨original_no_clash pol Q s hc,local_of_no_clash pol Q s hc,rays_of_no_clash pol Q s hc⟩,
    fun ⟨ho,hl,hr⟩ => no_clash_of_conditions pol Q s ho hl hr⟩

end NSSE.MultiVarianceClashCharacterization
