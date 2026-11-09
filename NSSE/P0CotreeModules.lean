import NSSE.P0SuffixOrientation
import NSSE.P0ModuleCut

/-! Every node of the actual suffix cotree satisfies the external-color
rule. Consequently every one-color node of a shortest accepted word has
at most one vertex. Both claims use the actual constructed cotree. -/
namespace NSSE.P0Cotree
variable {V : Type*} [DecidableEq V]

inductive Below : Tree V → Tree V → Prop where
  | refl (t) : Below t t
  | left {u l r} (j) : Below u l → Below u (.fork j l r)
  | right {u l r} (j) : Below u r → Below u (.fork j l r)

theorem below_subset {u t : Tree V} (h : Below u t) : leaves u ⊆ leaves t := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | left j h ih => exact Finset.Subset.trans ih Finset.subset_union_left
  | right j h ih => exact Finset.Subset.trans ih Finset.subset_union_right

theorem below_valid (edge : V → V → Prop) {u t : Tree V} (h : Below u t)
    (ht : Valid edge t) : Valid edge u := by
  induction h with
  | refl => exact ht
  | left j h ih => exact ih ht.1
  | right j h ih => exact ih ht.2.1

theorem below_external (edge : V → V → Prop) {u t : Tree V} (h : Below u t)
    (ht : Valid edge t) (a b z : V) (ha : a ∈ leaves u) (hb : b ∈ leaves u)
    (hz : z ∈ leaves t) (hzu : z ∉ leaves u) :
    (edge a z ↔ edge b z) ∧ (edge z a ↔ edge z b) := by
  induction h with
  | refl => exact False.elim (hzu hz)
  | @left l r j h ih =>
    by_cases hzl : z ∈ leaves l
    · exact ih ht.1 hzl
    · have hzr : z ∈ leaves r := (Finset.mem_union.mp hz).resolve_left hzl
      have ha' := below_subset h ha
      have hb' := below_subset h hb
      have h1 := ht.2.2.2 a ha' z hzr
      have h2 := ht.2.2.2 b hb' z hzr
      exact ⟨h1.1.trans h2.1.symm,h1.2.trans h2.2.symm⟩
  | @right l r j h ih =>
    by_cases hzr : z ∈ leaves r
    · exact ih ht.2.1 hzr
    · have hzl : z ∈ leaves l := (Finset.mem_union.mp hz).resolve_right hzr
      have ha' := below_subset h ha
      have hb' := below_subset h hb
      have h1 := ht.2.2.2 z hzl a ha'
      have h2 := ht.2.2.2 z hzl b hb'
      exact ⟨h1.2.trans h2.2.symm,h1.1.trans h2.1.symm⟩

end NSSE.P0Cotree

namespace NSSE.P0ActualCotree
open P0DDeadReader P0DDeadColor P0SuffixWords P0SuffixCotree P0SuffixOrientation
open P0Cotree P0ModuleCut P0CutComparison
variable {Q A H : Type*}

theorem edge_exact (J : Reader Q A H) (w : List A) (hc : Complete J w)
    (a b : Nat) (ha : a ≤ w.length) (hb : b ≤ w.length) :
    Adjacent J w a b ↔ Edge J.endX J.endY ((decorate J w).drop a) ((decorate J w).drop b) := by
  simp only [Adjacent,Edge,suffix_exact J w hc a b ha hb,suffix_exact J w hc b a hb ha]

theorem exists_tree (J : Reader Q A H) (w : List A) (hc : Complete J w)
    (hne : J.endX ≠ J.endY) : HasCotree (Adjacent J w) (Finset.range (w.length+1)) := by
  have ht := bounded_family J.endX J.endY hne w.length (Finset.range (w.length+1))
    (fun k => (decorate J w).drop k) ⟨0,Finset.mem_range.mpr (by omega)⟩ (by
      intro k _
      simp only [List.length_drop,decorate_length]
      omega)
  apply congr _ _ _ ht
  intro a ha b hb
  exact (edge_exact J w hc a b (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using ha)
    (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hb)).symm

theorem node_module (J : Reader Q A H) (w : List A) (hc : Complete J w)
    (hne : J.endX ≠ J.endY) (t u : Tree Nat)
    (hleaf : leaves t = Finset.range (w.length+1)) (ht : Valid (Adjacent J w) t)
    (hu : Below u t) : ColoredModule J w (leaves u) := by
  have hbnd (v : Nat) (hv : v ∈ leaves u) : v ≤ w.length := by
    have hh := below_subset hu hv
    rw [hleaf,Finset.mem_range] at hh
    omega
  intro a ha b hb hcol z hz hzu
  by_cases hab : a = b
  · subst b; exact ⟨Iff.rfl,Iff.rfl⟩
  have hn : ¬ Edge J.endX J.endY ((decorate J w).drop a) ((decorate J w).drop b) :=
    fun h => proper_coloring J w hc a b hab hcol
      ((edge_exact J w hc a b (hbnd a ha) (hbnd b hb)).mpr h)
  have hzt : z ∈ leaves t := by rw [hleaf,Finset.mem_range]; omega
  have he := (below_external (Adjacent J w) hu ht a b z ha hb hzt hzu).1
  rw [edge_exact J w hc a z (hbnd a ha) hz,edge_exact J w hc b z (hbnd b hb) hz] at he
  have hh := uniform J.endX J.endY hne _ _ _ hn he
  simpa only [suffix_exact J w hc a z (hbnd a ha) hz,
    suffix_exact J w hc b z (hbnd b hb) hz,suffix_exact J w hc z a hz (hbnd a ha),
    suffix_exact J w hc z b hz (hbnd b hb)] using hh

theorem shortest_tree (J : Reader Q A H) (w : List A) (hw : Accepted J w)
    (hne : J.endX ≠ J.endY) (hmin : ∀ v, Accepted J v → w.length ≤ v.length) :
    ∃ t : Tree Nat, leaves t = Finset.range (w.length+1) ∧ Valid (Adjacent J w) t ∧
      ∀ u, Below u t → ColoredModule J w (leaves u) ∧
        ((∀ a ∈ leaves u, ∀ b ∈ leaves u, color J w a = color J w b) → (leaves u).card ≤ 1) := by
  obtain ⟨t,hleaf,ht⟩ := exists_tree J w hw.1 hne
  refine ⟨t,hleaf,ht,?_⟩
  intro u hu
  have hm := node_module J w hw.1 hne t u hleaf ht hu
  refine ⟨hm,fun hone => shortest_one_color J w (leaves u) hm ?_ hone hne hw hmin⟩
  intro z hz
  have hh := below_subset hu hz
  rw [hleaf,Finset.mem_range] at hh
  omega

end NSSE.P0ActualCotree
