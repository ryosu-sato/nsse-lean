import Mathlib.Data.Finset.Card

/-! Finite binary union/join trees with actual vertex leaves. Validity
records both cross-edge orientations and disjoint leaf sets. Trees may
still have consecutive nodes of the same kind; normalization is separate. -/
namespace NSSE.P0Cotree
variable {V : Type*} [DecidableEq V]

inductive Tree (V : Type*) where
  | leaf : V → Tree V
  | fork : Bool → Tree V → Tree V → Tree V

def leaves : Tree V → Finset V
  | .leaf v => {v}
  | .fork _ l r => leaves l ∪ leaves r

theorem leaves_nonempty (t : Tree V) : (leaves t).Nonempty := by
  induction t with
  | leaf v => exact ⟨v,Finset.mem_singleton_self v⟩
  | fork j l r ih _ => exact ih.mono Finset.subset_union_left

def Valid (edge : V → V → Prop) : Tree V → Prop
  | .leaf _ => True
  | .fork j l r => Valid edge l ∧ Valid edge r ∧ Disjoint (leaves l) (leaves r) ∧
      ∀ a ∈ leaves l, ∀ b ∈ leaves r,
        (edge a b ↔ j = true) ∧ (edge b a ↔ j = true)

def HasCotree (edge : V → V → Prop) (S : Finset V) : Prop :=
  ∃ t : Tree V, leaves t = S ∧ Valid edge t

theorem singleton (edge : V → V → Prop) (v : V) : HasCotree edge {v} :=
  ⟨.leaf v,rfl,True.intro⟩

theorem combine (edge : V → V → Prop) (j : Bool) (S T : Finset V)
    (hs : HasCotree edge S) (ht : HasCotree edge T) (hd : Disjoint S T)
    (hc : ∀ a ∈ S, ∀ b ∈ T, (edge a b ↔ j = true) ∧ (edge b a ↔ j = true)) :
    HasCotree edge (S ∪ T) := by
  obtain ⟨l,rfl,hl⟩ := hs
  obtain ⟨r,rfl,hr⟩ := ht
  exact ⟨.fork j l r,rfl,hl,hr,hd,hc⟩

theorem valid_congr (edge edge' : V → V → Prop) (t : Tree V) (ht : Valid edge t)
    (he : ∀ a ∈ leaves t, ∀ b ∈ leaves t, edge a b ↔ edge' a b) : Valid edge' t := by
  induction t with
  | leaf v => trivial
  | fork j l r ihl ihr =>
    rcases ht with ⟨hl,hr,hd,hcross⟩
    refine ⟨ihl hl (fun a ha b hb => he a (Finset.mem_union_left _ ha) b
      (Finset.mem_union_left _ hb)),ihr hr (fun a ha b hb =>
      he a (Finset.mem_union_right _ ha) b (Finset.mem_union_right _ hb)),hd,?_⟩
    intro a ha b hb
    have hh := hcross a ha b hb
    exact ⟨(he a (Finset.mem_union_left _ ha) b (Finset.mem_union_right _ hb)).symm.trans hh.1,
      (he b (Finset.mem_union_right _ hb) a (Finset.mem_union_left _ ha)).symm.trans hh.2⟩

theorem congr (edge edge' : V → V → Prop) (S : Finset V) (hs : HasCotree edge S)
    (he : ∀ a ∈ S, ∀ b ∈ S, edge a b ↔ edge' a b) : HasCotree edge' S := by
  obtain ⟨t,rfl,ht⟩ := hs
  exact ⟨t,rfl,valid_congr edge edge' t ht he⟩

theorem partition (edge : V → V → Prop) (j : Bool) (S : Finset V) (p : V → Prop)
    [DecidablePred p] (hp : ∃ a ∈ S, p a) (hn : ∃ b ∈ S, ¬ p b)
    (hi : ∀ T, T ⊂ S → T.Nonempty → HasCotree edge T)
    (hc : ∀ a ∈ S, p a → ∀ b ∈ S, ¬ p b →
      (edge a b ↔ j = true) ∧ (edge b a ↔ j = true)) : HasCotree edge S := by
  classical
  let L := S.filter p
  let R := S.filter (fun v => ¬ p v)
  have hL : L ⊂ S := Finset.filter_ssubset.mpr hn
  have hR : R ⊂ S := Finset.filter_ssubset.mpr (by simpa using hp)
  obtain ⟨a,ha,hpa⟩ := hp
  obtain ⟨b,hb,hpb⟩ := hn
  have hl := hi L hL ⟨a,Finset.mem_filter.mpr ⟨ha,hpa⟩⟩
  have hr := hi R hR ⟨b,Finset.mem_filter.mpr ⟨hb,hpb⟩⟩
  have he : L ∪ R = S := Finset.filter_union_filter_neg_eq p S
  rw [← he]
  apply combine edge j L R hl hr
  · exact Finset.disjoint_filter_filter_neg _ _ _
  · intro x hx y hy
    exact hc x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
      y (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2

theorem constant (edge : V → V → Prop) (j : Bool) (S : Finset V) (hs : S.Nonempty)
    (hc : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      (edge a b ↔ j = true) ∧ (edge b a ↔ j = true)) : HasCotree edge S := by
  revert hs hc
  refine Finset.strongInductionOn S ?_
  intro S ih hs hc
  obtain ⟨a,ha⟩ := hs
  by_cases hsingle : S = {a}
  · rw [hsingle]; exact singleton edge a
  · have hn : ∃ b ∈ S, b ≠ a := by
      by_contra h
      push_neg at h
      exact hsingle (Finset.eq_singleton_iff_unique_mem.mpr ⟨ha,h⟩)
    apply partition edge j S (· = a) ⟨a,ha,rfl⟩ hn
    · intro T hT hne
      exact ih T hT hne (fun x hx y hy hxy => hc x (hT.1 hx) y (hT.1 hy) hxy)
    · intro x hx hxa y hy hya
      exact hc x hx y hy (by intro he; exact hya (he.symm.trans hxa))

end NSSE.P0Cotree
