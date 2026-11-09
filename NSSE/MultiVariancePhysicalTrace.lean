import NSSE.MultiVarianceSignedTransport

/-! The actual selected-literal geometry follows the physical frame trace.
Decorated letters contain the CURRENT head and child index. -/
namespace NSSE.MultiVariancePhysicalTrace
open MultiConstructorConstraints (Constraints Query)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceSpineSeparation
open MultiVarianceSpineTokens MultiVarianceTokenExact MultiVarianceRailBirths
open MultiVarianceSpineSuffixes MultiVarianceLiteralGeometry MultiVariancePositionLiterals
open MultiVarianceSignedTransport
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

theorem runPhysical_append (phi : Constraints arity n) (F : Frame n) (u v : List (Letter arity)) :
    runPhysical pol phi F (u++v) = runPhysical pol phi (runPhysical pol phi F u) v := by
  induction u generalizing F with
  | nil => rfl
  | cons a u ih => exact ih _

def stateAt (Q : Query arity n) (s : Spine arity) (d : Nat) : Frame n :=
  runPhysical pol Q.constraints (startFrame pol Q) ((path s).take d)

def sideRole (Q : Query arity n) (s : Spine arity) (d : Nat) (side : Bool) : Bool :=
  roleOf (stateAt pol Q s d).sign side

theorem stateAt_step (Q : Query arity n) (s : Spine arity) (d : Nat) (a : Letter arity)
    (ha : (path s)[d]? = some a) :
    stateAt pol Q s (d+1) = physicalMove pol Q.constraints (stateAt pol Q s d) a.1 a.2 := by
  obtain ⟨hd,he⟩ := List.getElem?_eq_some_iff.mp ha
  unfold stateAt
  rw [List.take_succ_eq_append_getElem hd,runPhysical_append,he]
  rfl

theorem roleOf_next (sign side neg : Bool) :
    roleOf (nextRole sign neg) side = nextRole (roleOf sign side) neg := by
  cases sign <;> cases side <;> cases neg <;> rfl

theorem nextRole_not (r neg : Bool) : nextRole (!r) neg = !(nextRole r neg) := by
  cases r <;> cases neg <;> rfl

theorem sideRole_step (Q : Query arity n) (s : Spine arity) (d : Nat) (side : Bool) (a : Letter arity)
    (ha : (path s)[d]? = some a) :
    sideRole pol Q s (d+1) side = nextRole (sideRole pol Q s d side) (pol a.1 a.2) := by
  unfold sideRole
  rw [stateAt_step pol Q s d a ha]
  exact roleOf_next _ side _

omit [DecidableEq H] in
theorem suffix_first (s : Spine arity) (d : Nat) : (path (suffix s d)).head? = (path s)[d]? := by
  induction d generalizing s with
  | zero => cases s <;> rfl
  | succ d ih => cases s <;> simp only [suffix,path,List.head?_nil,List.getElem?_nil,List.getElem?_cons_succ,ih]

omit [DecidableEq H] in
theorem geometry_of_letter (s : Spine arity) (d : Nat) (r : Bool) (h : H) (j : Fin (arity h))
    (ha : (path s)[d]? = some ⟨h,j⟩) :
    label (suffix s d) r = .node h ∧ selected (suffix s d) = some j.val := by
  have he := (suffix_first s d).trans ha
  cases hs : suffix s d with
  | stop a b => simp only [hs,path,List.head?_nil,reduceCtorEq] at he
  | step k i t =>
    rw [hs] at he
    change some (⟨k,i⟩ : Letter arity) = some ⟨h,j⟩ at he
    have hi := Option.some.inj he
    cases hi
    exact ⟨rfl,rfl⟩

def PhysicalCompare (Q : Query arity n) (s : Spine arity) (d : Nat) (hd : d ≤ s.depth)
    (side : Bool) (e : Nat) (he : e ≤ s.depth) (other : Bool) : Prop :=
  sideRole pol Q s e other = !(sideRole pol Q s d side) ∧
    Compare pol Q s d hd e he (sideRole pol Q s d side)

theorem physical_transport (Q : Query arity n) (s : Spine arity) (d : Nat) (hd : d ≤ s.depth)
    (side : Bool) (e : Nat) (he : e ≤ s.depth) (other : Bool) (a : Letter arity)
    (ha : (path s)[d]? = some a) (hb : (path s)[e]? = some a)
    (dn : d+1 ≤ s.depth) (en : e+1 ≤ s.depth)
    (hc : PhysicalCompare pol Q s d hd side e he other) :
    PhysicalCompare pol Q s (d+1) dn side (e+1) en other := by
  constructor
  · rw [sideRole_step pol Q s d side a ha,sideRole_step pol Q s e other a hb,hc.1,nextRole_not]
  · change Compare pol Q s (d+1) dn (e+1) en (sideRole pol Q s (d+1) side)
    rw [sideRole_step pol Q s d side a ha]
    obtain ⟨hl,sl⟩ := geometry_of_letter s d (sideRole pol Q s d side) a.1 a.2 ha
    obtain ⟨hr,sr⟩ := geometry_of_letter s e (!(sideRole pol Q s d side)) a.1 a.2 hb
    exact selected_transport pol Q s d hd e he _ a.1 a.2 hl hr sl sr dn en hc.2

theorem birth_compare (Q : Query arity n) (s : Spine arity) (p q : Position s)
    (hb : MultiVarianceRailBirths.Birth pol Q s p q) :
    PhysicalCompare pol Q s p.1.val (level_le s p) p.2 q.1.val (level_le s q) q.2 := by
  obtain ⟨hp,hq,z,hpz,hzq⟩ := hb
  constructor
  · change roleAt pol Q s q = !(roleAt pol Q s p)
    rw [hp,hq]
    rfl
  · have hs := hpz.trans hzq
    change Compare pol Q s p.1.val (level_le s p) q.1.val (level_le s q) (roleAt pol Q s p)
    change Support pol (MultiVarianceOriginalSpine.extension pol Q s)
      (roleVariable Q s p.1.val (level_le s p) (roleAt pol Q s p))
      (roleVariable Q s q.1.val (level_le s q) (roleAt pol Q s q)) at hs
    simp only [Compare,hp,hq,Bool.not_false,Bool.false_eq_true,if_false]
    simpa only [hp,hq] using hs

end NSSE.MultiVariancePhysicalTrace
