import NSSE.MultiVarianceSpineDescent

/-! Actual signed spine extensions preserve exactly the original
supported-pair cycles, without a validity or satisfiability premise. -/
namespace NSSE.MultiVarianceSpineCycles
open MultiConstructorConstraints (Query)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceGlobal MultiVarianceSpineSeparation
open MultiVarianceOriginalSpine MultiVarianceSpineClasses MultiVarianceSpineDescent MultiVariancePairGraph
variable {H : Type*} {arity : H → Nat} {n : Nat}

def oldPair (d : Nat) (p : Pair n) : Pair (count n d) := (old d p.1,old d p.2)

theorem oldPair_injective (d : Nat) : Function.Injective (oldPair (n := n) d) := by
  intro p q he
  apply Prod.ext
  · apply Fin.ext
    exact congrArg (fun r : Pair (count n d) => r.1.val) he
  · apply Fin.ext
    exact congrArg (fun r : Pair (count n d) => r.2.val) he

variable (pol : Polarity arity)

theorem reach_nonincrease (Q : Query arity n) (s : Spine arity) {p q : Pair (count n s.depth)}
    (hr : Reach pol (extension pol Q s) p q) : mass s.depth q≤mass s.depth p := by
  induction hr with
  | single hm => exact mass_nonincrease pol Q s hm
  | tail _ hm ih => exact (mass_nonincrease pol Q s hm).trans ih

theorem same_mass_reach (Q : Query arity n) (s : Spine arity) {p q : Pair (count n s.depth)}
    (hr : Reach pol (extension pol Q s) p q) (he : mass s.depth q=mass s.depth p) :
    ∃ u v : Pair n, p=oldPair s.depth u ∧ q=oldPair s.depth v ∧ Reach pol Q.constraints u v := by
  induction hr with
  | single hm =>
    obtain ⟨u,v,hp,hq,h⟩ := same_mass_original pol Q s hm he
    exact ⟨u,v,hp,hq,one_reach pol Q.constraints h⟩
  | tail hr hm ih =>
    have h1 := reach_nonincrease pol Q s hr
    have h2 := mass_nonincrease pol Q s hm
    obtain ⟨u,v,hp,hv,h⟩ := ih (by omega)
    obtain ⟨v',w,hv',hw,h'⟩ := same_mass_original pol Q s hm (by omega)
    have hvv : v=v' := oldPair_injective s.depth (hv.symm.trans hv')
    subst v'
    exact ⟨u,w,hp,hw,reach_trans pol Q.constraints h (one_reach pol Q.constraints h')⟩

theorem cycle_original (Q : Query arity n) (s : Spine arity)
    (hc : Cycle pol (extension pol Q s)) : Cycle pol Q.constraints := by
  obtain ⟨p,hp⟩ := hc
  obtain ⟨u,v,hu,hv,hr⟩ := same_mass_reach pol Q s hp rfl
  have he : u=v := oldPair_injective s.depth (hu.symm.trans hv)
  subst v
  exact ⟨u,hr⟩

theorem no_cycle (Q : Query arity n) (s : Spine arity)
    (hc : ¬Cycle pol Q.constraints) : ¬Cycle pol (extension pol Q s) :=
  fun h => hc (cycle_original pol Q s h)

theorem lift_move (Q : Query arity n) (s : Spine arity) {p q : Pair n}
    (hm : Move pol Q.constraints p q) : Move pol (extension pol Q s) (oldPair s.depth p) (oldPair s.depth q) := by
  obtain ⟨hp,a,ha,b,hb,hap,hpb,i,j,hh,hij,hc⟩ := hm
  refine ⟨(old_support_iff pol Q s _ _).mpr hp,mapBound (old s.depth) a,?_,
    mapBound (old s.depth) b,?_,(old_support_iff pol Q s _ _).mpr hap,
    (old_support_iff pol Q s _ _).mpr hpb,i,j,hh,hij,?_⟩
  · exact List.mem_append_left _ (List.mem_map_of_mem ha)
  · exact List.mem_append_left _ (List.mem_map_of_mem hb)
  · change if pol a.head i then _ else _
    cases hs : pol a.head i <;> simp only [hs,Bool.false_eq_true,if_false,if_true] at hc ⊢
    all_goals exact ⟨(old_support_iff pol Q s _ _).mpr hc.1,(old_support_iff pol Q s _ _).mpr hc.2⟩

theorem lift_reach (Q : Query arity n) (s : Spine arity) {p q : Pair n}
    (hr : Reach pol Q.constraints p q) : Reach pol (extension pol Q s) (oldPair s.depth p) (oldPair s.depth q) := by
  induction hr with
  | single hm => exact one_reach pol _ (lift_move pol Q s hm)
  | tail _ hm ih => exact reach_trans pol _ ih (one_reach pol _ (lift_move pol Q s hm))

theorem cycle_iff (Q : Query arity n) (s : Spine arity) :
    Cycle pol (extension pol Q s) ↔ Cycle pol Q.constraints :=
  ⟨cycle_original pol Q s,fun ⟨p,hp⟩ => ⟨oldPair s.depth p,lift_reach pol Q s hp⟩⟩

end NSSE.MultiVarianceSpineCycles
