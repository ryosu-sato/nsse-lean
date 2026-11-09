import NSSE.MultiVarianceClashCharacterization

/-! On a valid separating spine, lower labels are heads/Top and upper
labels are heads/Bottom. Ordered ray endpoints therefore mean equal
proper heads, exactly the symmetric Agree predicate used by the reader. -/
namespace NSSE.MultiVarianceValidAgreement
open MultiConstructorConstraints (Query)
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceSpineSeparation MultiVarianceSpineSuffixes
open MultiVarianceLiteralGeometry MultiVarianceLabelBounds MultiVarianceSpineLabels
open MultiVarianceTokenExact MultiVarianceRailBirths MultiVarianceRaySupport
open MultiVarianceRailCoordinates MultiVariancePhysicalRays MultiVarianceClashCharacterization
variable {H : Type*} {arity : H → Nat} {n : Nat}

def Agree (a b : Label H) : Prop := ∃ h, a=.node h ∧ b=.node h

theorem agree_symm {a b : Label H} (h : Agree a b) : Agree b a := by
  obtain ⟨k,ha,hb⟩ := h
  exact ⟨k,hb,ha⟩

theorem active_of_valid (s : Spine arity) (hv : s.Valid) (d : Nat) (hd : d ≤ s.depth) (r : Bool) :
    Active r (label (suffix s d) r) := by
  induction s generalizing d with
  | stop a b =>
    have hz : d=0 := by change d ≤ 0 at hd; omega
    subst d
    cases r
    · intro ha
      apply hv
      change a = .bot at ha
      rw [ha]
      exact bot_le
    · intro hb
      apply hv
      change b = .top at hb
      rw [hb]
      exact le_top
  | step h i s ih =>
    cases d with
    | zero => cases r <;> simp [Active,suffix,label,extreme]
    | succ d =>
      have ht : d ≤ s.depth := by change d+1 ≤ s.depth+1 at hd; omega
      exact ih hv d ht

theorem active_order_iff_agree (a b : Label H) (ha : Active false a) (hb : Active true b) :
    a ≤ b ↔ Agree a b := by
  change Label.Below a b ↔ _
  cases a <;> cases b <;> simp_all [Active,extreme,Agree,Label.Below,eq_comm]

variable [DecidableEq H] (pol : Polarity arity)

def labelAt (Q : Query arity n) (s : Spine arity) (p : Position s) : Label H :=
  label (suffix s p.1.val) (roleAt pol Q s p)

@[simp] theorem labelAt_role (Q : Query arity n) (s : Spine arity) (d : Nat) (hd : d ≤ s.depth) (r : Bool) :
    labelAt pol Q s (rolePosition pol Q s d hd r) = label (suffix s d) r := by
  change label (suffix s d) (roleAt pol Q s (rolePosition pol Q s d hd r)) = _
  rw [rolePosition_role]

def AllRayAgree (Q : Query arity n) (s : Spine arity) : Prop :=
  ∀ p q : Position s, Ray pol Q s p q → Agree (labelAt pol Q s p) (labelAt pol Q s q)

theorem rayGood_iff_agree (Q : Query arity n) (s : Spine arity) (hv : s.Valid) :
    RayGood pol Q s ↔ AllRayAgree pol Q s := by
  constructor
  · intro hh p q hr
    have hp := rolePosition_of_position pol Q s p
    have hq := rolePosition_of_position pol Q s q
    have hop := (ray_compare pol Q s p q hr).1
    change roleAt pol Q s q = !(roleAt pol Q s p) at hop
    cases hs : roleAt pol Q s p with
    | false =>
      have ht : roleAt pol Q s q = true := by rw [hop,hs]; rfl
      rw [hs] at hp
      rw [ht] at hq
      rw [← hp,← hq] at hr ⊢
      rw [labelAt_role,labelAt_role]
      exact (active_order_iff_agree _ _ (active_of_valid s hv p.1.val (level_le s p) false)
        (active_of_valid s hv q.1.val (level_le s q) true)).mp (hh _ _ _ _ hr)
    | true =>
      have ht : roleAt pol Q s q = false := by rw [hop,hs]; rfl
      rw [hs] at hp
      rw [ht] at hq
      rw [← hp,← hq] at hr ⊢
      rw [labelAt_role,labelAt_role]
      apply agree_symm
      exact (active_order_iff_agree _ _ (active_of_valid s hv q.1.val (level_le s q) false)
        (active_of_valid s hv p.1.val (level_le s p) true)).mp (hh _ _ _ _ (ray_symm pol Q s hr))
  · intro hh d hd e he hr
    have ha := hh _ _ hr
    rw [labelAt_role,labelAt_role] at ha
    exact (active_order_iff_agree _ _ (active_of_valid s hv d hd false)
      (active_of_valid s hv e he true)).mpr ha

def BirthRayGood (Q : Query arity n) (s : Spine arity) : Prop :=
  ∀ a b : Position s, MultiVarianceRailBirths.Birth pol Q s a b → ∀ l,
    ∀ ha : a.1.val+l ≤ s.depth, ∀ hb : b.1.val+l ≤ s.depth,
      P0ProperWords.WordMatch (path s) a.1.val b.1.val l →
        Agree (labelAt pol Q s (advancePosition s a l ha)) (labelAt pol Q s (advancePosition s b l hb))

theorem allRayAgree_iff_births (Q : Query arity n) (s : Spine arity) :
    AllRayAgree pol Q s ↔ BirthRayGood pol Q s := by
  constructor
  · intro hh a b hborn l ha hb hm
    exact hh (advancePosition s a l ha) (advancePosition s b l hb) ⟨a,b,l,ha,hb,Or.inl hborn,hm,rfl,rfl⟩
  · intro hh p q hr
    rcases hr with ⟨a,b,l,ha,hb,hborn,hm,rfl,rfl⟩
    rcases hborn with hborn | hborn
    · exact hh a b hborn l ha hb hm
    · exact agree_symm (hh b a hborn l hb ha (fun k hk => (hm k hk).symm))

/-- The original gadget's full no-clash theorem in the reader's actual
all-birth/current-head-factor formulation. -/
theorem no_clash_iff_birth_rays (Q : Query arity n) (s : Spine arity) (hv : s.Valid) :
    ¬MultiVarianceConstraints.LabelClash pol (MultiVarianceOriginalSpine.extension pol Q s) ↔
      ¬MultiVarianceConstraints.LabelClash pol Q.constraints ∧ LocalGood pol Q s ∧ BirthRayGood pol Q s := by
  rw [no_label_clash_iff,rayGood_iff_agree pol Q s hv,allRayAgree_iff_births]

end NSSE.MultiVarianceValidAgreement
