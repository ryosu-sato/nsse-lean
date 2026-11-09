import NSSE.MultiVariancePositionLiterals

/-! Actual signed support propagation along two matching selected edges.
The endpoint coordinates stay fixed; negative arguments reverse support. -/
namespace NSSE.MultiVarianceSignedTransport
open MultiConstructorConstraints (Bound Query)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceGlobal
open MultiVarianceOriginalSpine MultiVarianceSpineNormal MultiVarianceSpineTokens
open MultiVarianceSpineSeparation MultiVarianceSpineSuffixes MultiVarianceLiteralGeometry
open MultiVariancePositionLiterals
variable {H : Type*} {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

theorem seed_mem_extension (Q : Query arity n) (s : Spine arity) (r : Bool)
    (b : Bound arity (count n s.depth)) (hb : b ∈ bounds (seeds pol Q s) r) :
    b ∈ bounds (extension pol Q s) r := by
  change b ∈ bounds (combine (remap (old s.depth) Q.constraints) (seeds pol Q s)) r
  rw [bounds_combine]
  exact List.mem_append_right _ hb

def Compare (Q : Query arity n) (s : Spine arity) (d : Nat) (hd : d ≤ s.depth)
    (e : Nat) (he : e ≤ s.depth) (r : Bool) : Prop :=
  if r then
    Support pol (extension pol Q s) (roleVariable Q s e he (!r)) (roleVariable Q s d hd r)
  else Support pol (extension pol Q s) (roleVariable Q s d hd r) (roleVariable Q s e he (!r))

theorem selected_transport (Q : Query arity n) (s : Spine arity) (d : Nat) (hd : d ≤ s.depth)
    (e : Nat) (he : e ≤ s.depth) (r : Bool) (h : H) (j : Fin (arity h))
    (hL : label (suffix s d) r = .node h) (hR : label (suffix s e) (!r) = .node h)
    (sd : selected (suffix s d) = some j.val) (se : selected (suffix s e) = some j.val)
    (dn : d+1 ≤ s.depth) (en : e+1 ≤ s.depth) (hc : Compare pol Q s d hd e he r) :
    Compare pol Q s (d+1) dn (e+1) en (nextRole r (pol h j)) := by
  obtain ⟨cx,hcx,hx⟩ := literal_exists pol Q s d hd r h hL
  obtain ⟨cy,hcy,hy⟩ := literal_exists pol Q s e he (!r) h hR
  have mx := seed_mem_extension pol Q s r _ hcx
  have my := seed_mem_extension pol Q s (!r) _ hcy
  have vx := (hx j).trans (selected_child pol Q s d hd r h j sd dn)
  have vy := (hy j).trans (selected_child pol Q s e he (!r) h j se en)
  cases r <;> cases hn : pol h j <;>
    simp only [Compare,MultiVarianceSpineSuffixes.bounds,nextRole,hn,Bool.not_true,Bool.not_false,
      Bool.false_eq_true,if_false,if_true] at mx my vx vy hc ⊢
  · have hs := Support.decompCov (a := cx) (b := cy) mx my hc j hn
    simpa only [vx,vy] using hs
  · have hs := Support.decompCon (a := cx) (b := cy) mx my hc j hn
    simpa only [vx,vy] using hs
  · have hs := Support.decompCov (a := cy) (b := cx) my mx hc j hn
    simpa only [vx,vy] using hs
  · have hs := Support.decompCon (a := cy) (b := cx) my mx hc j hn
    simpa only [vx,vy] using hs

end NSSE.MultiVarianceSignedTransport
