import NSSE.MultiVarianceTokenExact

/-! Exact executable birth matrices on all physical rail positions.
Both same-rail and cross-rail origins, including terminal origins and
coincident original roots, are retained.  Propagated rays are separate. -/
namespace NSSE.MultiVarianceRailBirths
open MultiConstructorConstraints (Query)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceGlobal
open MultiVarianceModelTokens (Tokens)
open MultiVarianceSpineTokens MultiVarianceSpineSeparation MultiVarianceOriginalSpine
open MultiVarianceTokenExact
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

abbrev Position (s : Spine arity) := Fin (s.depth+1) × Bool

def level_le (s : Spine arity) (p : Position s) : p.1.val ≤ s.depth := Nat.lt_succ_iff.mp p.1.isLt

omit [DecidableEq H] in
theorem card_positions (s : Spine arity) : Fintype.card (Position s) = 2*(s.depth+1) := by
  simp [Position,Nat.mul_comm]

variable (pol : Polarity arity)

def frameAt (Q : Query arity n) (s : Spine arity) (p : Position s) : Frame n :=
  runPhysical pol Q.constraints (startFrame pol Q) ((path s).take p.1.val)

def roleAt (Q : Query arity n) (s : Spine arity) (p : Position s) : Bool :=
  roleOf (frameAt pol Q s p).sign p.2

def tokensAt (Q : Query arity n) (s : Spine arity) (p : Position s) : Tokens n :=
  tokensOf (frameAt pol Q s p) p.2

def variableAt (Q : Query arity n) (s : Spine arity) (p : Position s) : Fin (count n s.depth) :=
  slot Q.left Q.right s.depth (railSlot s p.1.val (level_le s p) (roleAt pol Q s p))

theorem crossing_iff (Q : Query arity n) (s : Spine arity) (p : Position s) (z : Fin n) :
    (if roleAt pol Q s p then Support pol (extension pol Q s) (old s.depth z) (variableAt pol Q s p)
      else Support pol (extension pol Q s) (variableAt pol Q s p) (old s.depth z)) ↔
      z ∈ tokensAt pol Q s p :=
  physical_crossing_iff pol Q s p.1.val (level_le s p) p.2 z

def Birth (Q : Query arity n) (s : Spine arity) (p q : Position s) : Prop :=
  roleAt pol Q s p = false ∧ roleAt pol Q s q = true ∧
    ∃ z, Support pol (extension pol Q s) (variableAt pol Q s p) (old s.depth z) ∧
      Support pol (extension pol Q s) (old s.depth z) (variableAt pol Q s q)

def inspect (Q : Query arity n) (s : Spine arity) (p q : Position s) : Bool :=
  inspectBirth (roleAt pol Q s p) (tokensAt pol Q s p) (roleAt pol Q s q) (tokensAt pol Q s q)

theorem common_old_iff_inter (Q : Query arity n) (s : Spine arity) (p q : Position s)
    (hp : roleAt pol Q s p = false) (hq : roleAt pol Q s q = true) :
    (∃ z, Support pol (extension pol Q s) (variableAt pol Q s p) (old s.depth z) ∧
      Support pol (extension pol Q s) (old s.depth z) (variableAt pol Q s q)) ↔
      (tokensAt pol Q s p ∩ tokensAt pol Q s q).Nonempty := by
  have hL (z : Fin n) := crossing_iff pol Q s p z
  have hR (z : Fin n) := crossing_iff pol Q s q z
  simp only [hp,Bool.false_eq_true,if_false] at hL
  simp only [hq,if_true] at hR
  constructor
  · rintro ⟨z,hl,hr⟩
    exact ⟨z,Finset.mem_inter.mpr ⟨(hL z).mp hl,(hR z).mp hr⟩⟩
  · rintro ⟨z,hz⟩
    obtain ⟨hl,hr⟩ := Finset.mem_inter.mp hz
    exact ⟨z,(hL z).mpr hl,(hR z).mpr hr⟩

theorem inspect_correct (Q : Query arity n) (s : Spine arity) (p q : Position s) :
    inspect pol Q s p q = true ↔ Birth pol Q s p q := by
  cases hp : roleAt pol Q s p <;> cases hq : roleAt pol Q s q <;>
    simp only [inspect,inspectBirth,Birth,hp,hq,Bool.not_false,Bool.not_true,
      Bool.true_and,Bool.false_and,Bool.and_false,Bool.and_true,Bool.false_eq_true,
      Bool.true_eq_false,true_and,false_and,and_false,decide_eq_true_eq]
  exact (common_old_iff_inter pol Q s p q hp hq).symm

theorem birth_support (Q : Query arity n) (s : Spine arity) (p q : Position s)
    (hb : Birth pol Q s p q) :
    Support pol (extension pol Q s) (variableAt pol Q s p) (variableAt pol Q s q) := by
  obtain ⟨_,_,z,hp,hq⟩ := hb
  exact hp.trans hq

end NSSE.MultiVarianceRailBirths
