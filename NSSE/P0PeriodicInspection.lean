import NSSE.P0PeriodicDriver

/-! Uniform ADDITIONAL inspection of an arbitrary history followed by a
fixed literal period. This is x749 Lemma 2 on the proper-machine semantics;
the old history is neither bounded nor forgotten. -/
namespace NSSE.P0PeriodicInspection
open P0ProperMachine P0PeriodicDriver
variable {Q A H : Type*} [Fintype Q]

def horizon (N r : Nat) : Nat := N*r+N*N*r+r

theorem horizon_eq (N r : Nat) : horizon N r = (N^2+N+1)*r := by
  simp only [horizon,pow_two,Nat.add_mul,Nat.one_mul]
  omega

theorem match_shift (z : Nat → A) (a b l s : Nat) (hs : s ≤ l)
    (hm : Match z a b l) : Match z (a+s) (b+s) (l-s) := by
  intro k hk
  simpa only [Nat.add_assoc] using hm (s+k) (by omega)

omit [Fintype Q] in
theorem ray_equal_of_goodUpTo (M : Machine Q A H) (z : Nat → A) (n a b l : Nat)
    (hg : GoodUpTo M z n) (ha : a+l ≤ n) (hb : b+l ≤ n)
    (hborn : M.birth (run M z a) (run M z b)) (hm : Match z a b l) :
    M.head (run M z (a+l)) = M.head (run M z (b+l)) :=
  hg.2 a (by omega) b (by omega) l (by omega) ha hb hborn hm

theorem good_of_inspected (M : Machine Q A H) (z : Nat → A) (m r : Nat)
    (hr : 0 < r) (cycle : Fin r → A) (hp : PeriodicFrom z m r hr cycle)
    (hg : GoodUpTo M z (m+horizon (Fintype.card Q) r)) : Good M z := by
  apply (good_iff M z).mpr
  constructor
  · intro k
    by_cases hk : k ≤ m
    · exact hg.1 k (by unfold horizon; omega)
    · obtain ⟨i,hi,_,hq,_⟩ := state_representative M z m r hr cycle hp (k-m)
      have hek : m+(k-m) = k := by omega
      rw [hek] at hq
      rw [← hq]
      exact hg.1 (m+i) (by unfold horizon; omega)
  · intro a b l hborn hm
    by_cases htail : m ≤ a ∨ m ≤ b
    · obtain ⟨a',ha',_,hta',hfa⟩ := origin_representative M z m r hr cycle hp a
      obtain ⟨b',hb',_,htb',hfb⟩ := origin_representative M z m r hr cycle hp b
      have hqa : run M z a' = run M z a := by simpa using (hfa 0).1
      have hqb : run M z b' = run M z b := by simpa using (hfb 0).1
      have hborn' : M.birth (run M z a') (run M z b') := by rwa [hqa,hqb]
      have hm' : Match z a' b' l := by
        intro k hk
        rw [(hfa k).2,(hfb k).2]
        exact hm k hk
      have ht' : m ≤ a' ∨ m ≤ b' := htail.imp hta' htb'
      obtain ⟨j,hj,hjl,hja,hjb⟩ := pair_representative_either M z m r hr cycle hp a' b' l ht' hm'
      have he := ray_equal_of_goodUpTo M z (m+horizon (Fintype.card Q) r) a' b' j hg
        (by unfold horizon; omega) (by unfold horizon; omega) hborn'
        (match_mono z a' b' l j hjl hm')
      rw [hja,hjb,(hfa l).1,(hfb l).1] at he
      exact he
    · have ha : a < m := by omega
      have hb : b < m := by omega
      by_cases hend : a+l ≤ m ∧ b+l ≤ m
      · exact ray_equal_of_goodUpTo M z (m+horizon (Fintype.card Q) r) a b l hg
          (by unfold horizon; omega) (by unfold horizon; omega) hborn hm
      · let s := m-max a b
        have hs : s ≤ l := by dsimp [s]; omega
        have hsa : a+s ≤ m := by dsimp [s]; omega
        have hsb : b+s ≤ m := by dsimp [s]; omega
        have hperiod : m ≤ a+s ∨ m ≤ b+s := by dsimp [s]; omega
        obtain ⟨j,hj,hjl,hja,hjb⟩ := pair_representative_either M z m r hr cycle hp
          (a+s) (b+s) (l-s) hperiod (match_shift z a b l s hs hm)
        have hsplit : s+(l-s) = l := by omega
        have hja' : run M z (a+(s+j)) = run M z (a+l) := by
          simpa only [Nat.add_assoc,hsplit] using hja
        have hjb' : run M z (b+(s+j)) = run M z (b+l) := by
          simpa only [Nat.add_assoc,hsplit] using hjb
        have he := ray_equal_of_goodUpTo M z (m+horizon (Fintype.card Q) r) a b (s+j) hg
          (by unfold horizon; omega) (by unfold horizon; omega) hborn
          (match_mono z a b l (s+j) (by omega) hm)
        rwa [hja',hjb'] at he

theorem good_iff_inspected (M : Machine Q A H) (z : Nat → A) (m r : Nat)
    (hr : 0 < r) (cycle : Fin r → A) (hp : PeriodicFrom z m r hr cycle) :
    Good M z ↔ GoodUpTo M z (m+horizon (Fintype.card Q) r) :=
  ⟨fun h => h _,good_of_inspected M z m r hr cycle hp⟩

end NSSE.P0PeriodicInspection
