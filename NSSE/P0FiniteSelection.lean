import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Explicit finite selection for ordered pair colors. The greedy bound
T(0)=1, T(r+1)=1+c*T(r) builds a left-homogeneous increasing sequence,
retaining a final vertex. This is the selection mechanism of x731/x734. -/
namespace NSSE.P0FiniteSelection

def threshold (c : Nat) : Nat → Nat
  | 0 => 1
  | r+1 => 1 + c * threshold c r

theorem threshold_pos (c r : Nat) : 0 < threshold c r := by
  cases r <;> simp [threshold]

def Forward {c : Nat} (edge : Nat → Nat → Fin c) (x y : Nat × Fin c) : Prop :=
  x.1 < y.1 ∧ edge x.1 y.1 = x.2

theorem greedy (c : Nat) (hc : 0 < c) (edge : Nat → Nat → Fin c) (r : Nat)
    (S : Finset Nat) (hsize : threshold c r ≤ S.card) :
    ∃ L : List (Nat × Fin c), L.length = r+1 ∧
      (∀ x ∈ L, x.1 ∈ S) ∧ L.Pairwise (Forward edge) := by
  classical
  induction r generalizing S with
  | zero =>
    have hne : S.Nonempty := Finset.card_pos.mp (by simpa [threshold] using hsize)
    obtain ⟨a,ha⟩ := hne
    exact ⟨[(a,edge a a)],rfl,by simpa using ha,List.pairwise_singleton _ _⟩
  | succ r ih =>
    have hne : S.Nonempty := Finset.card_pos.mp ((threshold_pos c (r+1)).trans_le hsize)
    let a := S.min' hne
    have ha : a ∈ S := S.min'_mem hne
    have hcard : c * threshold c r ≤ (S.erase a).card := by
      rw [Finset.card_erase_of_mem ha]
      simp only [threshold] at hsize
      omega
    obtain ⟨v,_,hv⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := S.erase a) (t := Finset.univ) (f := edge a) (n := threshold c r)
      (fun _ _ => Finset.mem_univ _) ⟨⟨0,hc⟩,Finset.mem_univ _⟩ (by simpa using hcard)
    obtain ⟨L,hlen,hmem,hpair⟩ := ih ((S.erase a).filter (fun b => edge a b = v)) hv
    have htail (x : Nat × Fin c) (hx : x ∈ L) : x.1 ∈ S ∧ a < x.1 ∧ edge a x.1 = v := by
      have hh := Finset.mem_filter.mp (hmem x hx)
      have hz := Finset.mem_erase.mp hh.1
      have hlo := S.min'_le x.1 hz.2
      exact ⟨hz.2,lt_of_le_of_ne hlo (Ne.symm hz.1),hh.2⟩
    refine ⟨(a,v)::L,by simp [hlen],?_,?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact (htail x hx).1
    · exact List.pairwise_cons.mpr ⟨fun x hx => (htail x hx).2,hpair⟩

theorem three_ordered {V : Type*} [LinearOrder V] (S : Finset V) (hs : 3 ≤ S.card) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ d ∈ S, a < b ∧ b < d := by
  classical
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  let a := S.min' hne
  let d := S.max' hne
  have ha : a ∈ S := S.min'_mem hne
  have hd : d ∈ S := S.max'_mem hne
  have hb : ∃ b ∈ S, b ≠ a ∧ b ≠ d := by
    by_contra h
    have hsub : S ⊆ {a,d} := by
      intro b hb
      by_cases hba : b = a
      · simp [hba]
      · have hbd : b = d := by by_contra hbd; exact h ⟨b,hb,hba,hbd⟩
        simp [hbd]
    have hcard := Finset.card_le_card hsub
    have htwo : ({a,d} : Finset V).card ≤ 2 :=
      (Finset.card_insert_le a {d}).trans (by simp)
    omega
  obtain ⟨b,hb,hba,hbd⟩ := hb
  exact ⟨a,ha,b,hb,d,hd,lt_of_le_of_ne (S.min'_le b hb) (Ne.symm hba),
    lt_of_le_of_ne (S.le_max' b hb) hbd⟩

theorem threshold_sum (c r : Nat) : threshold c r = ∑ j ∈ Finset.range (r+1), c^j := by
  induction r with
  | zero => simp [threshold]
  | succ r ih =>
    calc
      threshold c (r+1) = 1 + c * ∑ j ∈ Finset.range (r+1), c^j := by rw [threshold,ih]
      _ = 1 + ∑ j ∈ Finset.range (r+1), c^(j+1) := by
        rw [Finset.mul_sum]
        simp only [pow_succ']
      _ = ∑ j ∈ Finset.range (r+1+1), c^j := by
        conv_rhs => rw [Finset.sum_range_succ']
        simp only [pow_zero,Nat.add_comm]

def bound (c : Nat) : Nat := threshold c (3*c)

theorem bound_eq (c : Nat) : bound c = ∑ j ∈ Finset.range (3*c+1), c^j := threshold_sum c (3*c)

/-- All six FORWARD colors agree; the edge function need not be symmetric. -/
theorem four (c : Nat) (hc : 0 < c) (edge : Nat → Nat → Fin c)
    (S : Finset Nat) (hsize : bound c ≤ S.card) :
    ∃ a b d e v, a ∈ S ∧ b ∈ S ∧ d ∈ S ∧ e ∈ S ∧ a < b ∧ b < d ∧ d < e ∧
      edge a b = v ∧ edge a d = v ∧ edge a e = v ∧
      edge b d = v ∧ edge b e = v ∧ edge d e = v := by
  classical
  obtain ⟨L,hlen,hmem,hpair⟩ := greedy c hc edge (3*c) S hsize
  let f : Fin (3*c) → Fin c := fun i => (L[i.val]'(by rw [hlen]; omega)).2
  obtain ⟨v,_,hv⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (f := f) (n := 3)
    (fun _ _ => Finset.mem_univ _) ⟨⟨0,hc⟩,Finset.mem_univ _⟩ (by simp [Nat.mul_comm])
  obtain ⟨i,hi,j,hj,k,hk,hij,hjk⟩ := three_ordered (Finset.univ.filter (fun i => f i = v)) hv
  have hiL : i.val < L.length := by rw [hlen]; omega
  have hjL : j.val < L.length := by rw [hlen]; omega
  have hkL : k.val < L.length := by rw [hlen]; omega
  have heL : 3*c < L.length := by rw [hlen]; omega
  have hci : (L[i.val]'hiL).2 = v := (Finset.mem_filter.mp hi).2
  have hcj : (L[j.val]'hjL).2 = v := (Finset.mem_filter.mp hj).2
  have hck : (L[k.val]'hkL).2 = v := (Finset.mem_filter.mp hk).2
  have hp := List.pairwise_iff_getElem.mp hpair
  have pij := hp i.val j.val hiL hjL hij
  have pik := hp i.val k.val hiL hkL (lt_trans hij hjk)
  have pie := hp i.val (3*c) hiL heL i.isLt
  have pjk := hp j.val k.val hjL hkL hjk
  have pje := hp j.val (3*c) hjL heL j.isLt
  have pke := hp k.val (3*c) hkL heL k.isLt
  exact ⟨(L[i.val]'hiL).1,(L[j.val]'hjL).1,(L[k.val]'hkL).1,(L[3*c]'heL).1,v,
    hmem _ (List.getElem_mem hiL),hmem _ (List.getElem_mem hjL),
    hmem _ (List.getElem_mem hkL),hmem _ (List.getElem_mem heL),
    pij.1,pjk.1,pke.1,pij.2.trans hci,pik.2.trans hci,pie.2.trans hci,
    pjk.2.trans hcj,pje.2.trans hcj,pke.2.trans hck⟩

end NSSE.P0FiniteSelection
