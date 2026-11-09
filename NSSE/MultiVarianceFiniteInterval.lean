import NSSE.MultiVarianceFiniteTrees
import NSSE.MultiVariancePairGraph

/-! Every signed pair edge descends through a genuine finite child.
Negative arguments reverse interval endpoints. No monotonicity of height
under subtyping is assumed; a nonempty cycle forbids every finite model. -/
namespace NSSE.MultiVarianceFiniteInterval
open MultiConstructorConstraints (Constraints)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceFiniteTrees MultiVariancePairGraph
open MultiConstructorFiniteTrees (height child_height_lt)
variable {H : Type*} {arity : H → Nat} {n : Nat} (pol : Polarity arity)

theorem child_between (h : H) (a b : Fin (arity h) → MultiVarianceTrees.Tree pol) (t : Value arity)
    (hl : MultiVarianceTrees.node h a≤embed pol t) (hu : embed pol t≤MultiVarianceTrees.node h b)
    (i : Fin (arity h)) :
    ∃ u : Value arity, (if pol h i then b i≤embed pol u ∧ embed pol u≤a i
      else a i≤embed pol u ∧ embed pol u≤b i) ∧ height u<height t := by
  cases t with
  | bot => exact False.elim (MultiVarianceTrees.node_not_le_bot h a hl)
  | top => exact False.elim (MultiVarianceTrees.top_not_le_node h b hu)
  | node g c =>
    have hg : h=g := MultiVarianceTrees.node_head_eq hl
    subst g
    have ha := (MultiVarianceTrees.node_le_node h a (fun j => embed pol (c j))).mp hl i
    have hb := (MultiVarianceTrees.node_le_node h (fun j => embed pol (c j)) b).mp hu i
    refine ⟨c i,?_,child_height_lt h c i⟩
    cases hp : pol h i <;> simp only [hp,Bool.false_eq_true,if_false,if_true] at ha hb ⊢
    · exact ⟨ha,hb⟩
    · exact ⟨hb,ha⟩

theorem move_interval (phi : Constraints arity n) (rho : Fin n → Value arity)
    (hs : Satisfies phi (fun x => embed pol (rho x))) {p q : Pair n} (hm : Move pol phi p q)
    (t : Value arity) (hl : embed pol (rho p.1)≤embed pol t) (hu : embed pol t≤embed pol (rho p.2)) :
    ∃ u : Value arity, embed pol (rho q.1)≤embed pol u ∧ embed pol u≤embed pol (rho q.2) ∧ height u<height t := by
  obtain ⟨_,⟨x,h,ac⟩,ha,⟨y,g,bc⟩,hb,hap,hpb,i,j,hh,hij,hc⟩ := hm
  dsimp only at hh i j hij hc hap hpb
  subst g
  have he : i=j := Fin.ext hij
  subst j
  have hlo : MultiVarianceTrees.node h (fun k => embed pol (rho (ac k)))≤embed pol t :=
    (hs.2.1 _ ha).trans ((support_sound phi _ hs hap).trans hl)
  have hhi : embed pol t≤MultiVarianceTrees.node h (fun k => embed pol (rho (bc k))) :=
    hu.trans ((support_sound phi _ hs hpb).trans (hs.1 _ hb))
  obtain ⟨u,hi,ht⟩ := child_between pol h _ _ t hlo hhi i
  cases hp : pol h i <;> simp only [hp,Bool.false_eq_true,if_false,if_true] at hc hi
  all_goals exact ⟨u,(support_sound phi _ hs hc.1).trans hi.1,hi.2.trans (support_sound phi _ hs hc.2),ht⟩

theorem reach_interval (phi : Constraints arity n) (rho : Fin n → Value arity)
    (hs : Satisfies phi (fun x => embed pol (rho x))) {p q : Pair n} (hr : Reach pol phi p q)
    (t : Value arity) (hl : embed pol (rho p.1)≤embed pol t) (hu : embed pol t≤embed pol (rho p.2)) :
    ∃ u : Value arity, embed pol (rho q.1)≤embed pol u ∧ embed pol u≤embed pol (rho q.2) ∧ height u<height t := by
  induction hr generalizing t with
  | single hm => exact move_interval pol phi rho hs hm t hl hu
  | tail _ hm ih =>
    obtain ⟨u,hl',hu',ht⟩ := ih t hl hu
    obtain ⟨v,hl'',hu'',ht'⟩ := move_interval pol phi rho hs hm u hl' hu'
    exact ⟨v,hl'',hu'',ht'.trans ht⟩

theorem solution_no_cycle (phi : Constraints arity n) (rho : Fin n → Value arity)
    (hs : Satisfies phi (fun x => embed pol (rho x))) : ¬Cycle pol phi := by
  rintro ⟨p,hp⟩
  have hbad : ∀ k : Nat, ∀ t : Value arity, height t=k →
      embed pol (rho p.1)≤embed pol t → embed pol t≤embed pol (rho p.2) → False := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro t ht hl hu
      obtain ⟨u,huL,huU,hut⟩ := reach_interval pol phi rho hs hp t hl hu
      exact ih (height u) (by omega) u rfl huL huU
  exact hbad _ (rho p.1) rfl le_rfl (support_sound phi _ hs (reach_source pol phi hp))

theorem finite_sat_no_cycle (phi : Constraints arity n) (hs : MultiVarianceFiniteTrees.Satisfiable pol phi) :
    ¬Cycle pol phi := by
  obtain ⟨rho,hr⟩ := hs
  exact solution_no_cycle pol phi rho hr

end NSSE.MultiVarianceFiniteInterval
