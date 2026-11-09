import NSSE.MultiVarianceSpinePotential
import NSSE.MultiVariancePairGraph

/-! Signed pair edges conserve a sum of role potentials. Negative edges
exchange the roles. Equality forces both literals and both endpoints to
be original; no validity, satisfiability or no-clash premise is used. -/
namespace NSSE.MultiVarianceSpineDescent
open MultiConstructorConstraints (Bound Query)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceGlobal MultiVarianceSpineSeparation
open MultiVarianceOriginalSpine MultiVarianceSpineClasses MultiVarianceSpinePotential
open MultiVarianceSpineSuffixes (bounds)
open MultiVarianceSpineTokens (nextRole)
open MultiVariancePairGraph
variable {H : Type*} {arity : H → Nat} {n : Nat} (pol : Polarity arity)

theorem bound_origin (Q : Query arity n) (s : Spine arity) (r : Bool)
    (a : Bound arity (count n s.depth)) (ha : a∈bounds (extension pol Q s) r)
    (i : Fin (arity a.head)) :
    (∃ b∈bounds Q.constraints r, a=mapBound (old s.depth) b) ∨
      value s.depth (nextRole r (pol a.head i)) (a.children i)<value s.depth r a.parent := by
  simp only [extension,MultiVarianceSpineSuffixes.bounds_combine,
    MultiVarianceSpineSuffixes.bounds_remap,List.mem_append,List.mem_map] at ha
  rcases ha with ⟨b,hb,rfl⟩ | ⟨b,hb,rfl⟩
  · exact Or.inl ⟨b,hb,rfl⟩
  · exact Or.inr (added_strict pol Q s r b hb i)

theorem bound_nonincrease (Q : Query arity n) (s : Spine arity) (r : Bool)
    (a : Bound arity (count n s.depth)) (ha : a∈bounds (extension pol Q s) r)
    (i : Fin (arity a.head)) :
    value s.depth (nextRole r (pol a.head i)) (a.children i)≤value s.depth r a.parent := by
  rcases bound_origin pol Q s r a ha i with ⟨b,_,rfl⟩ | h
  · change value s.depth _ (old s.depth (b.children i))≤value s.depth r (old s.depth b.parent)
    simp only [value_old,le_refl]
  · exact h.le

def mass (d : Nat) (p : Pair (count n d)) : Nat := value d false p.1+value d true p.2

theorem mass_nonincrease (Q : Query arity n) (s : Spine arity)
    {p q : Pair (count n s.depth)} (hm : Move pol (extension pol Q s) p q) :
    mass s.depth q≤mass s.depth p := by
  obtain ⟨_,⟨a,h,ac⟩,ha,⟨b,g,bc⟩,hb,hap,hpb,i,j,hh,hij,hc⟩ := hm
  dsimp only at hh i j hij hc hap hpb
  subst g
  have he : i=j := Fin.ext hij
  subst j
  have hpa := left_support pol Q s hap
  have hpb' := right_support pol Q s hpb
  have hal := bound_nonincrease pol Q s false _ ha i
  have hbu := bound_nonincrease pol Q s true _ hb i
  cases hp : pol h i <;> simp only [hp,Bool.false_eq_true,if_false,if_true] at hc
  · have hqa := left_support pol Q s hc.1
    have hbq := right_support pol Q s hc.2
    simp only [nextRole,hp,Bool.false_eq_true,if_false] at hal hbu
    unfold mass
    omega
  · have hqb := left_support pol Q s hc.1
    have haq := right_support pol Q s hc.2
    simp only [nextRole,hp,if_true,Bool.not_false,Bool.not_true] at hal hbu
    unfold mass
    omega

theorem same_mass_original (Q : Query arity n) (s : Spine arity)
    {p q : Pair (count n s.depth)} (hm : Move pol (extension pol Q s) p q)
    (he : mass s.depth q=mass s.depth p) :
    ∃ u v : Pair n, p=(old s.depth u.1,old s.depth u.2) ∧
      q=(old s.depth v.1,old s.depth v.2) ∧ Move pol Q.constraints u v := by
  have hq := target_support pol (extension pol Q s) hm
  obtain ⟨hp,a,ha,b,hb,hap,hpb,i,j,hh,hij,hc⟩ := hm
  have hsign : pol a.head i=pol b.head j := by
    obtain ⟨a,h,ac⟩ := a
    obtain ⟨b,g,bc⟩ := b
    dsimp only at hh i j hij ⊢
    subst g
    have he : i=j := Fin.ext hij
    subst j
    rfl
  have hpa := left_support pol Q s hap
  have hpb' := right_support pol Q s hpb
  have hal := bound_nonincrease pol Q s false a ha i
  have hbu := bound_nonincrease pol Q s true b hb j
  have hlit : (∃ a'∈Q.constraints.lower, a=mapBound (old s.depth) a') ∧
      (∃ b'∈Q.constraints.upper, b=mapBound (old s.depth) b') := by
    cases hs : pol a.head i <;> have ht := hs ▸ hsign
    all_goals rw [← ht] at hbu
    · simp only [hs,Bool.false_eq_true,if_false] at hc
      have hqa := left_support pol Q s hc.1
      have hbq := right_support pol Q s hc.2
      simp only [nextRole,hs,Bool.false_eq_true,if_false] at hal hbu
      rcases bound_origin pol Q s false a ha i with hao | hlt
      swap
      · simp only [nextRole,hs,Bool.false_eq_true,if_false] at hlt
        unfold mass at he
        omega
      rcases bound_origin pol Q s true b hb j with hbo | hlt
      · exact ⟨hao,hbo⟩
      · rw [← ht] at hlt
        simp only [nextRole,Bool.false_eq_true,if_false] at hlt
        unfold mass at he
        omega
    · simp only [hs,if_true] at hc
      have hqb := left_support pol Q s hc.1
      have haq := right_support pol Q s hc.2
      simp only [nextRole,hs,if_true,Bool.not_false,Bool.not_true] at hal hbu
      rcases bound_origin pol Q s false a ha i with hao | hlt
      swap
      · simp only [nextRole,hs,if_true,Bool.not_false] at hlt
        unfold mass at he
        omega
      rcases bound_origin pol Q s true b hb j with hbo | hlt
      · exact ⟨hao,hbo⟩
      · rw [← ht] at hlt
        simp only [nextRole,if_true,Bool.not_true] at hlt
        unfold mass at he
        omega
  obtain ⟨⟨a,hao,rfl⟩,⟨b,hbo,rfl⟩⟩ := hlit
  change value s.depth false (old s.depth a.parent)≤value s.depth false p.1 at hpa
  change value s.depth true (old s.depth b.parent)≤value s.depth true p.2 at hpb'
  rw [value_old] at hpa hpb'
  have hpl := le_antisymm (value_bound s.depth false p.1) hpa
  have hpr := le_antisymm (value_bound s.depth true p.2) hpb'
  have hql : value s.depth false q.1=s.depth+1 := by
    have := value_bound s.depth true q.2
    have := value_bound s.depth false q.1
    unfold mass at he
    omega
  have hqr : value s.depth true q.2=s.depth+1 := by unfold mass at he; omega
  obtain ⟨u1,u2,hu1,hu2⟩ := maximal_original pol Q s hp hpl hpr
  obtain ⟨v1,v2,hv1,hv2⟩ := maximal_original pol Q s hq hql hqr
  refine ⟨(u1,u2),(v1,v2),Prod.ext hu1 hu2,Prod.ext hv1 hv2,?_,a,hao,b,hbo,?_,?_,i,j,hh,hij,?_⟩
  · exact (old_support_iff pol Q s _ _).mp (by simpa only [hu1,hu2] using hp)
  · exact (old_support_iff pol Q s _ _).mp (by simpa only [hu1] using hap)
  · exact (old_support_iff pol Q s _ _).mp (by simpa only [hu2] using hpb)
  · change if pol a.head i then _ else _ at hc ⊢
    cases hs : pol a.head i <;> simp only [hs,Bool.false_eq_true,if_false,if_true] at hc ⊢
    all_goals exact ⟨(old_support_iff pol Q s _ _).mp (by simpa only [hv1] using hc.1),
      (old_support_iff pol Q s _ _).mp (by simpa only [hv2] using hc.2)⟩

end NSSE.MultiVarianceSpineDescent
