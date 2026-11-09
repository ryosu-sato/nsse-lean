import NSSE.P0DZRankColor
import NSSE.P0CotreeModules

/-! The cotree is constructed from the actual D/Z suffixes. Every node
obeys the external refined-color rule simultaneously for all rail pairs.
Neither a supplied cotree nor a supplied orientation property is assumed. -/
namespace NSSE.P0DZCotree
open P0DZBranch P0DZTrace P0DZRelations P0DZSuffixWords P0DZRankColor
open P0SuffixWords P0SuffixCotree P0Cotree
variable {Q Z A H : Type*} [DecidableEq Q] [DecidableEq A]

omit [DecidableEq Q] [DecidableEq A] in
theorem exists_tree (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (hne : J.endX ≠ J.endY) : HasCotree (Adjacent J w) (Finset.range (w.length+1)) := by
  have ht := bounded_family J.endX J.endY hne w.length (Finset.range (w.length+1))
    (fun k => (P0DZSuffixWords.decorate J w).drop k) ⟨0,Finset.mem_range.mpr (by omega)⟩ (by
      intro k _
      simp only [List.length_drop,P0DZSuffixWords.decorate_length]
      omega)
  apply congr _ _ _ ht
  intro a ha b hb
  exact (edge_exact J w hc hne a b (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using ha)
    (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hb)).symm

def ColoredModule (J : Branch Q Z A H) (w : List A) (S : Finset Nat) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, color J w a = color J w b → ∀ z, z ≤ w.length → z ∉ S → ∀ s t,
    (Compatible J w a s z t ↔ Compatible J w b s z t) ∧
    (Compatible J w z s a t ↔ Compatible J w z s b t)

theorem node_module (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (hne : J.endX ≠ J.endY) (t u : P0Cotree.Tree Nat)
    (hleaf : leaves t = Finset.range (w.length+1)) (ht : Valid (Adjacent J w) t)
    (hu : Below u t) : ColoredModule J w (leaves u) := by
  have hbnd (v : Nat) (hv : v ∈ leaves u) : v ≤ w.length := by
    have hh := below_subset hu hv
    rw [hleaf,Finset.mem_range] at hh
    omega
  intro a ha b hb hcol z hz hzu s r
  by_cases hab : a = b
  · subst b; exact ⟨Iff.rfl,Iff.rfl⟩
  have hn : ¬ Edge J.endX J.endY ((P0DZSuffixWords.decorate J w).drop a)
      ((P0DZSuffixWords.decorate J w).drop b) :=
    fun h => proper_coloring J w hc hne a b (hbnd a ha) (hbnd b hb) hab hcol
      ((edge_exact J w hc hne a b (hbnd a ha) (hbnd b hb)).mpr h)
  have hzt : z ∈ leaves t := by rw [hleaf,Finset.mem_range]; omega
  have he := (below_external (Adjacent J w) hu ht a b z ha hb hzt hzu).1
  rw [edge_exact J w hc hne a z (hbnd a ha) hz,edge_exact J w hc hne b z (hbnd b hb) hz] at he
  have hh := P0FourRailOrientation.uniform J.endX J.endY hne _ _ _ hn he (endpoint J s) (endpoint J r)
  have haz : a ≠ z := fun h => hzu (h ▸ ha)
  have hbz : b ≠ z := fun h => hzu (h ▸ hb)
  simpa only [P0DZSuffixWords.suffix_exact J w hc a z (hbnd a ha) hz haz,
    P0DZSuffixWords.suffix_exact J w hc b z (hbnd b hb) hz hbz,
    P0DZSuffixWords.suffix_exact J w hc z a hz (hbnd a ha) (Ne.symm haz),
    P0DZSuffixWords.suffix_exact J w hc z b hz (hbnd b hb) (Ne.symm hbz)] using hh

theorem actual_modules (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (hne : J.endX ≠ J.endY) :
    ∃ t : P0Cotree.Tree Nat, leaves t = Finset.range (w.length+1) ∧ Valid (Adjacent J w) t ∧
      ∀ u, Below u t → ColoredModule J w (leaves u) := by
  obtain ⟨t,hleaf,ht⟩ := exists_tree J w hc hne
  exact ⟨t,hleaf,ht,fun u hu => node_module J w hc hne t u hleaf ht hu⟩

end NSSE.P0DZCotree
