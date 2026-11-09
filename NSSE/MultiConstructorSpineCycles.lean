import NSSE.MultiConstructorSpineDescent

/-! The actual extension conserves supported-pair cycles. The proof uses
only the universal support certificate, without an assignment or model. -/
namespace NSSE.MultiConstructorSpineCycles
open MultiConstructorConstraints MultiConstructorSpineInput MultiConstructorSpineInput.Data
open MultiConstructorSpineDescent MultiConstructorPairGraph
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

def oldPair (S : Data arity n D) (p : Pair n) : Pair S.size := (S.old p.1,S.old p.2)

omit [DecidableEq H] in
theorem oldPair_injective (S : Data arity n D) : Function.Injective (oldPair S) := by
  intro p q he
  apply Prod.ext
  · apply Fin.ext
    exact congrArg (fun r : Pair S.size => r.1.val) he
  · apply Fin.ext
    exact congrArg (fun r : Pair S.size => r.2.val) he

theorem reach_nonincrease (phi : Constraints arity n) (S : Data arity n D) {p q : Pair S.size}
    (hr : Reach (S.program phi) p q) : mass S q ≤ mass S p := by
  induction hr with
  | single hm => exact mass_nonincrease phi S hm
  | tail _ hm ih => exact (mass_nonincrease phi S hm).trans ih

theorem same_mass_reach (phi : Constraints arity n) (S : Data arity n D) {p q : Pair S.size}
    (hr : Reach (S.program phi) p q) (he : mass S q = mass S p) :
    ∃ u v : Pair n, p = oldPair S u ∧ q = oldPair S v ∧ Reach phi u v := by
  induction hr with
  | single hm =>
    obtain ⟨u,v,hp,hq,h⟩ := same_mass_original phi S hm he
    exact ⟨u,v,hp,hq,one_reach phi h⟩
  | tail hr hm ih =>
    have h1 := reach_nonincrease phi S hr
    have h2 := mass_nonincrease phi S hm
    obtain ⟨u,v,hp,hv,h⟩ := ih (by omega)
    obtain ⟨v',w,hv',hw,h'⟩ := same_mass_original phi S hm (by omega)
    have hvv : v = v' := oldPair_injective S (hv.symm.trans hv')
    subst v'
    exact ⟨u,w,hp,hw,reach_trans phi h (one_reach phi h')⟩

theorem cycle_original (phi : Constraints arity n) (S : Data arity n D)
    (hc : Cycle (S.program phi)) : Cycle phi := by
  obtain ⟨p,hp⟩ := hc
  obtain ⟨u,v,hu,hv,hr⟩ := same_mass_reach phi S hp rfl
  have he : u = v := oldPair_injective S (hu.symm.trans hv)
  subst v
  exact ⟨u,hr⟩

theorem no_cycle (phi : Constraints arity n) (S : Data arity n D)
    (hc : ¬Cycle phi) : ¬Cycle (S.program phi) := fun h => hc (cycle_original phi S h)

omit [DecidableEq H] in
theorem lift_move (phi : Constraints arity n) (S : Data arity n D) {p q : Pair n}
    (hm : Move phi p q) : Move (S.program phi) (oldPair S p) (oldPair S q) := by
  obtain ⟨hp,a,ha,b,hb,hap,hpb,i,j,hh,hij,hqi,hjq⟩ := hm
  refine ⟨MultiConstructorSpineClosure.lift_support phi S _ _ hp,
    MultiConstructorInputMap.bound S.old a,?_,MultiConstructorInputMap.bound S.old b,?_,
    MultiConstructorSpineClosure.lift_support phi S _ _ hap,
    MultiConstructorSpineClosure.lift_support phi S _ _ hpb,i,j,hh,hij,
    MultiConstructorSpineClosure.lift_support phi S _ _ hqi,
    MultiConstructorSpineClosure.lift_support phi S _ _ hjq⟩
  · exact List.mem_append_left _ (List.mem_map_of_mem ha)
  · exact List.mem_append_left _ (List.mem_map_of_mem hb)

omit [DecidableEq H] in
theorem lift_reach (phi : Constraints arity n) (S : Data arity n D) {p q : Pair n}
    (hr : Reach phi p q) : Reach (S.program phi) (oldPair S p) (oldPair S q) := by
  induction hr with
  | single hm => exact one_reach _ (lift_move phi S hm)
  | tail _ hm ih => exact reach_trans _ ih (one_reach _ (lift_move phi S hm))

theorem cycle_iff (phi : Constraints arity n) (S : Data arity n D) :
    Cycle (S.program phi) ↔ Cycle phi :=
  ⟨cycle_original phi S,fun ⟨p,hp⟩ => ⟨oldPair S p,lift_reach phi S hp⟩⟩

end NSSE.MultiConstructorSpineCycles
