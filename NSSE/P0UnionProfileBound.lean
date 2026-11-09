import NSSE.P0ChildProfiles

/-! An explicit bound on equally sized normalized union children in an
actual shortest accepted word. This is the larger square-matrix bound,
not the optimized numerical mu recurrence of the paper. -/
namespace NSSE.P0UnionProfileBound
open scoped BigOperators
open P0Cotree P0CotreeNormalize P0CotreeColors P0ChildProfiles
open P0DDeadReader P0DDeadColor P0FourChildCut P0FourGroupEntry
variable {Q A H : Type*}

def capacity (k s : Nat) : Nat :=
  k^s * 2^(s*s) * (P0FiniteSelection.bound (2^(s*s))-1)

def unionBound (k B : Nat) : Nat := B * ∑ s ∈ Finset.range (B+1), capacity k s

theorem size_class_zero (L : List (Tree Nat)) : sizeClass L 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro i hi
  have hz := ((class_mem L 0 i).mp hi).2
  have hp := Finset.card_pos.mpr (leaves_nonempty (child L i))
  omega

theorem size_class_bound (J : Reader Q A H) (w : List A) (t l r : Tree Nat)
    (ht : Valid (Adjacent J w) t) (hleaves : leaves t = Finset.range (w.length+1))
    (hnode : Below (.fork false l r) t) (k s : Nat) (hs : 0 < s)
    [DecidableEq Q] (hk : (palette (color J w) (.fork false l r)).card ≤ k)
    (hends : J.endX ≠ J.endY) (hw : Accepted J w)
    (hmin : ∀ v, Accepted J v → w.length ≤ v.length) :
    (sizeClass (children (.fork false l r)) s).card ≤ capacity k s := by
  classical
  by_contra hlarge
  let U := leaves (.fork false l r)
  let L := children (.fork false l r)
  let I := sizeClass L s
  have hkpos : 0 < k := (Finset.card_pos.mpr (palette_nonempty (color J w) (.fork false l r))).trans_le hk
  obtain ⟨code,hcode⟩ := color_code (color J w) U k hkpos hk
  have hcard (i : Nat) (hi : i ∈ I) : (leaves (child L i)).card = s :=
    ((class_mem L s i).mp hi).2
  have hindex (i : Nat) (hi : i ∈ I) : i < L.length := ((class_mem L s i).mp hi).1
  obtain ⟨pick,G,hmem,_,hrows,hu,he⟩ := P0ProfileConfiguration.configuration J w U k s code
    (fun a ha b hb he => (hcode a ha b hb).mp he) (fun i => leaves (child L i)) I
    (fun i hi => children_inside false l r i (hindex i hi)) hcard
    (fun i hi j hj hne => children_disjoint (Adjacent J w) false l r (below_valid _ hnode ht)
      i j (hindex i hi) (hindex j hj) hne)
    (Nat.lt_of_not_ge hlarge)
  exact shortest_excludes J w t l r ht hleaves hnode G hs (fun q => child L (pick q))
    (fun q => child_mem L _ (hindex _ (hmem q))) hrows hends hw hmin ⟨hu,he⟩

theorem union_size_bound (J : Reader Q A H) (w : List A) (t l r : Tree Nat)
    (ht : Valid (Adjacent J w) t) (hleaves : leaves t = Finset.range (w.length+1))
    (hnode : Below (.fork false l r) t) (k B : Nat)
    [DecidableEq Q] (hk : (palette (color J w) (.fork false l r)).card ≤ k)
    (hB : ∀ u ∈ children (.fork false l r), (leaves u).card ≤ B)
    (hends : J.endX ≠ J.endY) (hw : Accepted J w)
    (hmin : ∀ v, Accepted J v → w.length ≤ v.length) :
    (leaves (.fork false l r)).card ≤ unionBound k B := by
  classical
  let L := children (.fork false l r)
  have hcover : Finset.range L.length ⊆ (Finset.range (B+1)).biUnion (sizeClass L) := by
    intro i hi
    have hib : i < L.length := Finset.mem_range.mp hi
    have hsize := hB (child L i) (child_mem L i hib)
    exact Finset.mem_biUnion.mpr ⟨(leaves (child L i)).card,Finset.mem_range.mpr (by omega),
      (class_mem L _ i).mpr ⟨hib,rfl⟩⟩
  have hlen : L.length ≤ ∑ s ∈ Finset.range (B+1), (sizeClass L s).card := by
    calc
      L.length = (Finset.range L.length).card := (Finset.card_range _).symm
      _ ≤ ((Finset.range (B+1)).biUnion (sizeClass L)).card := Finset.card_le_card hcover
      _ ≤ ∑ s ∈ Finset.range (B+1), (sizeClass L s).card := Finset.card_biUnion_le
  have hclasses : ∀ s, (sizeClass L s).card ≤ capacity k s := by
    intro s
    by_cases hs : 0 < s
    · exact size_class_bound J w t l r ht hleaves hnode k s hs hk hends hw hmin
    · have he : s = 0 := by omega
      rw [he,size_class_zero,Finset.card_empty]
      exact Nat.zero_le _
  have hcount : L.length ≤ ∑ s ∈ Finset.range (B+1), capacity k s :=
    hlen.trans (Finset.sum_le_sum (fun s _ => hclasses s))
  rw [← children_card (Adjacent J w) false l r (below_valid _ hnode ht)]
  have hh := (sum_bound L B (fun u => (leaves u).card) hB).trans (Nat.mul_le_mul_right B hcount)
  simpa only [unionBound,Nat.mul_comm] using hh

end NSSE.P0UnionProfileBound
