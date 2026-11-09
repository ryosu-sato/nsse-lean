import NSSE.P0CotreeColors

/-! Direct connection of the normalized n-ary view to actual word
positions, ordered modules, and the finite reader-state color bound. -/
namespace NSSE.P0NormalizedActual
open P0Cotree P0CotreeNormalize P0CotreeColors P0ActualCotree
open P0DDeadReader P0DDeadColor P0ModuleCut
variable {Q A H V : Type*}

theorem below_trans {u v t : Tree V} (h : Below u v) (h' : Below v t) : Below u t := by
  induction h' with
  | refl => exact h
  | left j h' ih => exact .left j ih
  | right j h' ih => exact .right j ih

theorem actual_proper (J : Reader Q A H) (w : List A) (hc : Complete J w) (t : Tree Nat) :
    Proper (Adjacent J w) (color J w) t := by
  intro a _ b _ hne he
  exact proper_coloring J w hc a b hne he

theorem actual_join_count [Fintype Q] [DecidableEq Q]
    (J : Reader Q A H) (w : List A) (hc : Complete J w) (l r : Tree Nat)
    (ht : Valid (Adjacent J w) (.fork true l r)) :
    (children (.fork true l r)).length ≤ Fintype.card Q + 1 := by
  have hh := join_children_count (Adjacent J w) (color J w) l r ht
    (actual_proper J w hc (.fork true l r))
  have hb : (palette (color J w) (.fork true l r)).card ≤ Fintype.card Q + 1 := by
    simpa using Finset.card_le_univ (palette (color J w) (.fork true l r))
  exact hh.trans hb

theorem exists_normalized_view (J : Reader Q A H) (w : List A) (hc : Complete J w)
    (hne : J.endX ≠ J.endY) :
    ∃ t : Tree Nat, leaves t = Finset.range (w.length+1) ∧ Valid (Adjacent J w) t ∧
      ∀ j l r, Below (.fork j l r) t →
        2 ≤ (children (.fork j l r)).length ∧
        (children (.fork j l r)).Nodup ∧
        (children (.fork j l r)).Pairwise (Cross (Adjacent J w) j) ∧
        ((children (.fork j l r)).map (fun u => (leaves u).card)).sum =
          (leaves (.fork j l r)).card ∧
        ∀ u ∈ children (.fork j l r), Below u t ∧ kind u ≠ some j ∧
          ColoredModule J w (leaves u) ∧ (leaves u).card < (leaves (.fork j l r)).card := by
  obtain ⟨t,hleaf,ht⟩ := exists_tree J w hc hne
  refine ⟨t,hleaf,ht,?_⟩
  intro j l r hv
  have ht' := below_valid (Adjacent J w) hv ht
  refine ⟨children_length j l r,children_nodup (Adjacent J w) j l r ht',
    children_pairwise (Adjacent J w) j l r ht',children_card (Adjacent J w) j l r ht',?_⟩
  intro u hu
  have hut := below_trans (children_below j l r u hu) hv
  exact ⟨hut,children_kind j l r u hu,node_module J w hc hne t u hleaf ht hut,
    children_smaller (Adjacent J w) j l r u ht' hu⟩

end NSSE.P0NormalizedActual
