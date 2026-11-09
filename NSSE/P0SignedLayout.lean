import NSSE.P0HomogeneousOrder

/-! The homogeneous four-list order is a finite sequence of consecutive
signed blocks. The boundaries are actual coordinates, not guessed layout
data; they are obtained from the last coordinate tied to the first one. -/
namespace NSSE.P0SignedLayout
open P0HomogeneousOrder
variable {m : Nat}

def BeforeTail (G : Grid m) (lo mid hi : Nat) : Prop :=
  ∀ i j, lo ≤ i → i < mid → mid ≤ j → j < hi → Separated G i j

theorem first_block (G : Grid m) (lo hi : Nat) (hlo : lo < hi) (hhi : hi ≤ m) :
    ∃ mid positive, lo < mid ∧ mid ≤ hi ∧ Block G lo mid positive ∧ BeforeTail G lo mid hi := by
  classical
  let S := (Finset.range hi).filter (fun i => lo ≤ i ∧ Tied G lo i)
  have hmem : lo ∈ S := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr hlo,le_rfl,tied_refl G lo (by omega)⟩
  have hne : S.Nonempty := ⟨lo,hmem⟩
  let last := S.max' hne
  have hlast := Finset.mem_filter.mp (S.max'_mem hne)
  have hlast_hi : last < hi := Finset.mem_range.mp hlast.1
  have hlo_last : lo ≤ last := hlast.2.1
  have htied : Tied G lo last := hlast.2.2
  have hbefore : BeforeTail G lo (last+1) hi := by
    intro i j hloi hi_last hlastj hjhi
    apply separated_of_not_tied G i j (by omega) (by omega)
    intro ht
    have hloi_tied := tied_shrink G lo last lo i (by omega) hloi (by omega) (by omega) htied
    have hloj_tied := tied_trans G lo i j hloi (by omega) (by omega) hloi_tied ht
    have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjhi,by omega,hloj_tied⟩
    have hjlast : j ≤ last := S.le_max' j hjS
    omega
  rcases htied with hp | hn
  · exact ⟨last+1,true,by omega,by omega,plus_block G lo last (by omega) hp,hbefore⟩
  · exact ⟨last+1,false,by omega,by omega,minus_block G lo last (by omega) hn,hbefore⟩

/-- Each list entry stores the exclusive upper boundary and the sign of
one block; the lower boundary is the previous upper boundary. -/
inductive Layout (G : Grid m) : Nat → Nat → List (Nat × Bool) → Prop where
  | nil (k) : Layout G k k []
  | cons {lo mid hi positive tail} (hlo : lo < mid) (hhi : mid ≤ hi)
      (block : Block G lo mid positive) (before : BeforeTail G lo mid hi)
      (rest : Layout G mid hi tail) : Layout G lo hi ((mid,positive)::tail)

theorem exists_layout_aux (G : Grid m) (n : Nat) :
    ∀ lo hi, lo ≤ hi → hi ≤ m → hi-lo ≤ n → ∃ L, Layout G lo hi L := by
  induction n with
  | zero =>
    intro lo hi hle _ hlen
    have he : lo = hi := by omega
    subst hi
    exact ⟨[],.nil lo⟩
  | succ n ih =>
    intro lo hi hle hhi hlen
    by_cases he : lo = hi
    · subst hi
      exact ⟨[],.nil lo⟩
    · obtain ⟨mid,s,hlom,hmid,hs,hbefore⟩ := first_block G lo hi (by omega) hhi
      obtain ⟨L,hL⟩ := ih mid hi hmid hhi (by omega)
      exact ⟨(mid,s)::L,.cons hlom hmid hs hbefore hL⟩

theorem exists_layout (G : Grid m) (lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ m) :
    ∃ L, Layout G lo hi L := exists_layout_aux G (hi-lo) lo hi hlo hhi le_rfl

theorem layout_length (G : Grid m) {lo hi : Nat} {L : List (Nat × Bool)}
    (h : Layout G lo hi L) : L.length ≤ hi-lo := by
  induction h with
  | nil => simp
  | cons hlo hhi hb hbefore hrest ih =>
    simp only [List.length_cons]
    omega

theorem layout_empty_iff (G : Grid m) {lo hi : Nat} {L : List (Nat × Bool)}
    (h : Layout G lo hi L) : L = [] ↔ lo = hi := by
  cases h with
  | nil => simp
  | cons hlo hhi =>
    have hn : lo ≠ hi := by omega
    simp [hn]

theorem whole_layout (G : Grid m) : ∃ L, Layout G 0 m L ∧ L.length ≤ m ∧ (L = [] ↔ m = 0) := by
  obtain ⟨L,hL⟩ := exists_layout G 0 m (by omega) le_rfl
  refine ⟨L,hL,?_,?_⟩
  · simpa only [Nat.sub_zero] using layout_length G hL
  · simpa only [eq_comm] using layout_empty_iff G hL

end NSSE.P0SignedLayout
