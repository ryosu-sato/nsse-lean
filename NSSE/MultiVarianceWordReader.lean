import NSSE.MultiVarianceBranchSpineLocal
import NSSE.MultiVarianceBranchSpineRays

/-! Original signed reader semantics for an arbitrary current-head/child
word, independently of any deterministic selector. This is the language
whose first accepted prefix will be covered by the finite branch family. -/
namespace NSSE.MultiVarianceWordReader
open MultiConstructorConstraints (Query)
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceTokenExact
open MultiVarianceSpineSeparation MultiVarianceSpineWords MultiVarianceSpineSuffixes MultiVarianceLiteralGeometry
open MultiVarianceRailBirths MultiVarianceBranchSpineLocal MultiVarianceBranchSpineRays
open MultiVarianceClashCharacterization MultiVarianceValidAgreement MultiVarianceBranch
open P0ProperWords (WordMatch)
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

def frame (Q : Query arity n) (w : List (Letter arity)) (k : Nat) : Frame n :=
  runPhysical pol Q.constraints (startFrame pol Q) (w.take k)

def value (w : List (Letter arity)) (ex ey : Label H) (side : Bool) (k : Nat) : Label H :=
  match w[k]? with
  | some a => .node a.1
  | none => if side then ey else ex

def make (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H) : Spine arity :=
  physical w (frame pol Q w w.length).sign ex ey

theorem make_path (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H) :
    path (make pol Q w ex ey)=w := physical_path _ _ _ _

theorem make_depth (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H) :
    (make pol Q w ex ey).depth=w.length := physical_depth _ _ _ _

theorem make_frame (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H) (k : Nat) :
    MultiVariancePhysicalTrace.stateAt pol Q (make pol Q w ex ey) k = frame pol Q w k := by
  unfold MultiVariancePhysicalTrace.stateAt
  rw [make_path]
  rfl

theorem make_label (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H)
    (k : Nat) (hk : k ≤ w.length) (side : Bool) :
    label (suffix (make pol Q w ex ey) k) (roleOf (frame pol Q w k).sign side)=value w ex ey side k := by
  by_cases hl : k<w.length
  · have he : (path (make pol Q w ex ey))[k]?=some w[k] := by rw [make_path]; exact List.getElem?_eq_getElem hl
    rw [value,List.getElem?_eq_getElem hl]
    exact (MultiVariancePhysicalTrace.geometry_of_letter _ k _ w[k].1 w[k].2 he).1
  · have he : k=w.length := by omega
    subst k
    rw [value,List.getElem?_length]
    exact physical_terminal _ _ _ _ _

theorem make_labelAt (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H)
    (p : Position (make pol Q w ex ey)) :
    labelAt pol Q (make pol Q w ex ey) p = value w ex ey p.2 p.1.val := by
  change label (suffix (make pol Q w ex ey) p.1.val)
    (roleOf (MultiVariancePhysicalTrace.stateAt pol Q (make pol Q w ex ey) p.1.val).sign p.2) = _
  rw [make_frame]
  exact make_label pol Q w ex ey p.1.val (by simpa only [make_depth] using level_le _ p) p.2

def Local (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H) : Prop :=
  ∀ k, k ≤ w.length → ∀ side, Compatible Q.constraints (roleOf (frame pol Q w k).sign side)
    (tokensOf (frame pol Q w k) side) (value w ex ey side k)

def Born (Q : Query arity n) (w : List (Letter arity)) (a : Nat) (s : Bool) (b : Nat) (t : Bool) : Prop :=
  RawBirth (frame pol Q w a) s (frame pol Q w b) t

def Rays (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H) : Prop :=
  ∀ a, a ≤ w.length → ∀ b, b ≤ w.length → ∀ s t, Born pol Q w a s b t →
    ∀ l, a+l ≤ w.length → b+l ≤ w.length → WordMatch w a b l →
      P0DZBranch.Agree (value w ex ey s (a+l)) (value w ex ey t (b+l))

def ValidEnd (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H) : Prop :=
  if (frame pol Q w w.length).sign then ¬ey ≤ ex else ¬ex ≤ ey

def Accepted (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H) : Prop :=
  ValidEnd pol Q w ex ey ∧ ¬MultiVarianceConstraints.LabelClash pol Q.constraints ∧
    Local pol Q w ex ey ∧ Rays pol Q w ex ey

def Witness (Q : Query arity n) (w : List (Letter arity)) : Prop := ∃ ex ey, Accepted pol Q w ex ey

theorem local_iff (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H) :
    LocalGood pol Q (make pol Q w ex ey) ↔ Local pol Q w ex ey := by
  rw [local_iff_physical]
  constructor
  · intro hl k hk side
    let p : Position (make pol Q w ex ey) := (⟨k,by rw [make_depth]; omega⟩,side)
    have hh := hl p
    rw [make_labelAt] at hh
    change Compatible Q.constraints
      (roleOf (MultiVariancePhysicalTrace.stateAt pol Q (make pol Q w ex ey) k).sign side)
      (tokensOf (MultiVariancePhysicalTrace.stateAt pol Q (make pol Q w ex ey) k) side) _ at hh
    rwa [make_frame] at hh
  · intro hl p
    rw [make_labelAt]
    change Compatible Q.constraints
      (roleOf (MultiVariancePhysicalTrace.stateAt pol Q (make pol Q w ex ey) p.1.val).sign p.2)
      (tokensOf (MultiVariancePhysicalTrace.stateAt pol Q (make pol Q w ex ey) p.1.val) p.2) _
    rw [make_frame]
    exact hl p.1.val (by simpa only [make_depth] using level_le _ p) p.2

theorem birth_iff (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H)
    (p q : Position (make pol Q w ex ey)) :
    MultiVarianceRailBirths.Birth pol Q (make pol Q w ex ey) p q ↔ Born pol Q w p.1.val p.2 q.1.val q.2 := by
  rw [← MultiVarianceRailBirths.inspect_correct]
  change inspectBirth
    (roleOf (MultiVariancePhysicalTrace.stateAt pol Q (make pol Q w ex ey) p.1.val).sign p.2)
    (tokensOf (MultiVariancePhysicalTrace.stateAt pol Q (make pol Q w ex ey) p.1.val) p.2)
    (roleOf (MultiVariancePhysicalTrace.stateAt pol Q (make pol Q w ex ey) q.1.val).sign q.2)
    (tokensOf (MultiVariancePhysicalTrace.stateAt pol Q (make pol Q w ex ey) q.1.val) q.2) = true ↔ _
  rw [make_frame,make_frame]
  rfl

theorem rays_iff (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H) :
    BirthRayGood pol Q (make pol Q w ex ey) ↔ Rays pol Q w ex ey := by
  constructor
  · intro hr a ha b hb s t hborn l hal hbl hm
    let p : Position (make pol Q w ex ey) := (⟨a,by rw [make_depth]; omega⟩,s)
    let q : Position (make pol Q w ex ey) := (⟨b,by rw [make_depth]; omega⟩,t)
    have hh := hr p q ((birth_iff pol Q w ex ey p q).mpr hborn) l
      (by change a+l ≤ _; rwa [make_depth]) (by change b+l ≤ _; rwa [make_depth])
      (by simpa only [make_path] using hm)
    rw [make_labelAt,make_labelAt] at hh
    exact (agree_iff _ _).mp hh
  · intro hr p q hborn l hp hq hm
    have hpa : p.1.val ≤ w.length := by simpa only [make_depth] using level_le _ p
    have hqa : q.1.val ≤ w.length := by simpa only [make_depth] using level_le _ q
    have hh := hr p.1.val hpa q.1.val hqa p.2 q.2 ((birth_iff pol Q w ex ey p q).mp hborn) l
      (by simpa only [make_depth] using hp) (by simpa only [make_depth] using hq)
      (by simpa only [make_path] using hm)
    rw [make_labelAt,make_labelAt]
    exact (agree_iff _ _).mpr hh

theorem accepted_iff_inspect (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H) :
    Accepted pol Q w ex ey ↔ MultiVarianceRawSpine.inspectSpine pol Q (make pol Q w ex ey)=true := by
  rw [MultiVarianceRawSpine.inspectSpine_iff_conditions,local_iff,rays_iff]
  change _ ↔ (physical w (frame pol Q w w.length).sign ex ey).Valid ∧ _
  rw [physical_valid]
  rfl

end NSSE.MultiVarianceWordReader
