import NSSE.MultiConstructorSpinePotential
import NSSE.MultiConstructorPairGraph

/-! Every new bound strictly decreases a rail potential; only original
bounds can preserve it. Pair edges inherit simultaneous nonincrease. -/
namespace NSSE.MultiConstructorSpineDescent
open MultiConstructorConstraints MultiConstructorSpineInput MultiConstructorSpineInput.Data
open MultiConstructorSpineMembership MultiConstructorSpinePotential MultiConstructorPairGraph
variable {H : Type*} {arity : H → Nat} {n D : Nat}

theorem lower_origin (phi : Constraints arity n) (S : Data arity n D) (a : Bound arity S.size)
    (ha : a ∈ (S.program phi).lower) (i : Fin (arity a.head)) :
    (∃ b ∈ phi.lower, a = MultiConstructorInputMap.bound S.old b) ∨
      left S (a.children i) < left S a.parent := by
  rcases lower_cases phi S a ha with ho | ⟨k,rfl⟩ | ⟨h,_,rfl⟩
  · exact Or.inl ho
  · right
    change left S (if i.val = S.word[k.val].val then S.xAt (S.after k) else S.botVar) <
      left S (S.xAt (S.here k))
    split_ifs
    · rw [left_x,left_x]
      have := k.isLt
      change S.word.length+1-(k.val+1) < S.word.length+1-k.val
      omega
    · rw [left_bot,left_x]
      have := k.isLt
      change 0 < S.word.length+1-k.val
      omega
  · right
    change left S S.botVar < left S (S.xAt S.last)
    rw [left_bot,left_x]
    change 0 < S.word.length+1-S.word.length
    omega

theorem upper_origin (phi : Constraints arity n) (S : Data arity n D) (a : Bound arity S.size)
    (ha : a ∈ (S.program phi).upper) (i : Fin (arity a.head)) :
    (∃ b ∈ phi.upper, a = MultiConstructorInputMap.bound S.old b) ∨
      right S (a.children i) < right S a.parent := by
  rcases upper_cases phi S a ha with ho | ⟨k,rfl⟩ | ⟨h,_,rfl⟩
  · exact Or.inl ho
  · right
    change right S (if i.val = S.word[k.val].val then S.yAt (S.after k) else S.topVar) <
      right S (S.yAt (S.here k))
    split_ifs
    · rw [right_y,right_y]
      have := k.isLt
      change S.word.length+1-(k.val+1) < S.word.length+1-k.val
      omega
    · rw [right_top,right_y]
      have := k.isLt
      change 0 < S.word.length+1-k.val
      omega
  · right
    change right S S.topVar < right S (S.yAt S.last)
    rw [right_top,right_y]
    change 0 < S.word.length+1-S.word.length
    omega

theorem lower_nonincrease (phi : Constraints arity n) (S : Data arity n D) (a : Bound arity S.size)
    (ha : a ∈ (S.program phi).lower) (i : Fin (arity a.head)) :
    left S (a.children i) ≤ left S a.parent := by
  rcases lower_origin phi S a ha i with ⟨b,_,rfl⟩ | h
  · change left S (S.old (b.children i)) ≤ left S (S.old b.parent)
    simp only [left_old,le_refl]
  · exact h.le

theorem upper_nonincrease (phi : Constraints arity n) (S : Data arity n D) (a : Bound arity S.size)
    (ha : a ∈ (S.program phi).upper) (i : Fin (arity a.head)) :
    right S (a.children i) ≤ right S a.parent := by
  rcases upper_origin phi S a ha i with ⟨b,_,rfl⟩ | h
  · change right S (S.old (b.children i)) ≤ right S (S.old b.parent)
    simp only [right_old,le_refl]
  · exact h.le

def mass (S : Data arity n D) (p : Pair S.size) : Nat := left S p.1 + right S p.2

variable [DecidableEq H]

theorem move_nonincrease (phi : Constraints arity n) (S : Data arity n D) {p q : Pair S.size}
    (hm : Move (S.program phi) p q) : left S q.1 ≤ left S p.1 ∧ right S q.2 ≤ right S p.2 := by
  obtain ⟨_,a,ha,b,hb,hap,hpb,i,j,_,_,hqi,hjq⟩ := hm
  exact ⟨(left_support phi S _ _ hqi).trans ((lower_nonincrease phi S a ha i).trans
      (left_support phi S _ _ hap)),
    (right_support phi S _ _ hjq).trans ((upper_nonincrease phi S b hb j).trans
      (right_support phi S _ _ hpb))⟩

theorem mass_nonincrease (phi : Constraints arity n) (S : Data arity n D) {p q : Pair S.size}
    (hm : Move (S.program phi) p q) : mass S q ≤ mass S p :=
  Nat.add_le_add (move_nonincrease phi S hm).1 (move_nonincrease phi S hm).2

theorem same_mass_original (phi : Constraints arity n) (S : Data arity n D) {p q : Pair S.size}
    (hm : Move (S.program phi) p q) (he : mass S q = mass S p) :
    ∃ u v : Pair n, p = (S.old u.1,S.old u.2) ∧ q = (S.old v.1,S.old v.2) ∧ Move phi u v := by
  have hq := target_support (S.program phi) hm
  have ⟨hl,hu⟩ := move_nonincrease phi S hm
  obtain ⟨hp,a,ha,b,hb,hap,hpb,i,j,hh,hij,hqi,hjq⟩ := hm
  have hpa := left_support phi S _ _ hap
  have haq := left_support phi S _ _ hqi
  have hpb' := right_support phi S _ _ hpb
  have hbq := right_support phi S _ _ hjq
  have hel : left S q.1 = left S p.1 := by unfold mass at he; omega
  have heu : right S q.2 = right S p.2 := by unfold mass at he; omega
  rcases lower_origin phi S a ha i with ⟨a,hao,rfl⟩ | hs
  swap
  · omega
  rcases upper_origin phi S b hb j with ⟨b,hbo,rfl⟩ | hs
  swap
  · omega
  change left S (S.old a.parent) ≤ left S p.1 at hpa
  change right S (S.old b.parent) ≤ right S p.2 at hpb'
  rw [left_old] at hpa
  rw [right_old] at hpb'
  have hpl : left S p.1 = S.word.length+1 := le_antisymm (left_bound S p.1) hpa
  have hpu : right S p.2 = S.word.length+1 := le_antisymm (right_bound S p.2) hpb'
  obtain ⟨u1,u2,hu1,hu2⟩ := maximal_original phi S _ _ hp hpl hpu
  obtain ⟨v1,v2,hv1,hv2⟩ := maximal_original phi S _ _ hq (hel.trans hpl) (heu.trans hpu)
  have hep : p = (S.old u1,S.old u2) := Prod.ext hu1 hu2
  have heq : q = (S.old v1,S.old v2) := Prod.ext hv1 hv2
  refine ⟨(u1,u2),(v1,v2),hep,heq,?_,a,hao,b,hbo,?_,?_,i,j,hh,hij,?_,?_⟩
  · exact MultiConstructorSpineClosure.old_support phi S _ _ (by simpa only [hu1,hu2] using hp)
  · exact MultiConstructorSpineClosure.old_support phi S _ _ (by simpa only [hu1] using hap)
  · exact MultiConstructorSpineClosure.old_support phi S _ _ (by simpa only [hu2] using hpb)
  · exact MultiConstructorSpineClosure.old_support phi S _ _ (by simpa only [hv1] using hqi)
  · exact MultiConstructorSpineClosure.old_support phi S _ _ (by simpa only [hv2] using hjq)

end NSSE.MultiConstructorSpineDescent
