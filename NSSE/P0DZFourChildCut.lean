import NSSE.P0DZFourGroupEntry
import NSSE.P0DZMinimal
import NSSE.P0CotreeNormalize

/-! Actual D/Z union children supply the full cross-zero comparisons and
external module condition. Four equal profiles then give a shorter
accepted word of no larger rank, excluding them from a minimal word. -/
namespace NSSE.P0DZFourChildCut
open P0Cotree P0CotreeNormalize P0HomogeneousOrder
open P0DZBranch P0DZRelations P0DZSuffixWords P0DZCotree P0DZLayout P0DZFourGroupEntry
open P0DZModuleCut P0SuffixRank P0SuffixConflict
open P0FourGroupEntry (InRow)
variable {Q Z A H : Type*} [DecidableEq Q] [DecidableEq A] {m : Nat}

omit [DecidableEq Q] [DecidableEq A] in
theorem union_zero (J : Branch Q Z A H) (w : List A) (l r u : P0Cotree.Tree Nat)
    (ht : Valid (Adjacent J w) (.fork false l r))
    (hu : u ∈ children (.fork false l r)) (a : Nat) (ha : a ∈ leaves u)
    (p : Nat) (hp : p ∈ leaves (.fork false l r)) (hpu : p ∉ leaves u) : AllCompatible J w a p := by
  classical
  obtain ⟨v,hv,hpv⟩ := (children_cover false l r p).mp hp
  have hne : u ≠ v := by intro he; subst v; exact hpu hpv
  have hn : ¬ Adjacent J w a p := by
    intro he
    rcases P0IntervalFamily.pair_cases _ _ (children_pairwise _ false l r ht) u v hu hv with
      h | h | h
    · exact hne h
    · exact Bool.false_ne_true ((h.2 a ha p hpv).1.mp he)
    · exact Bool.false_ne_true ((h.2 p hpv a ha).2.mp he)
  simpa only [Adjacent,not_not] using hn

theorem shorten_in_tree (J : Branch Q Z A H) (w : List A) (t l r : P0Cotree.Tree Nat)
    (ht : Valid (Adjacent J w) t) (hleaves : leaves t = Finset.range (w.length+1))
    (hnode : Below (.fork false l r) t) (G : Grid m) (hpos : 0 < m)
    (selected : Fin 4 → P0Cotree.Tree Nat) (hselected : ∀ q, selected q ∈ children (.fork false l r))
    (hrows : ∀ q p, p ∈ leaves (selected q) ↔ InRow G q p)
    (hu : UniformColors J w G) (he : EqualMatrices J w G)
    (hends : J.endX ≠ J.endY) (hw : Accepted J w) :
    ∃ v, Accepted J v ∧ v.length < w.length ∧ maxRank J v ≤ maxRank J w := by
  have hin (q : Fin 4) (i : Nat) (hi : i < m) : G.pos q i ∈ leaves (.fork false l r) :=
    below_subset (children_below false l r (selected q) (hselected q))
      ((hrows q _).mpr ⟨i,hi,rfl⟩)
  have hb (q : Fin 4) (i : Nat) (hi : i < m) : G.pos q i ≤ w.length := by
    have hh := below_subset hnode (hin q i hi)
    rw [hleaves,Finset.mem_range] at hh
    omega
  have hc : UnionSeparated J w (leaves (.fork false l r)) G := by
    intro q i hi p hp hnot x y
    have hh := union_zero J w l r (selected q) (below_valid _ hnode ht) (hselected q)
      (G.pos q i) ((hrows q _).mpr ⟨i,hi,rfl⟩) p hp (fun hmem => hnot ((hrows q p).mp hmem))
    exact ⟨hh x y,all_symm J w (G.pos q i) p hh x y⟩
  exact shorten J w (leaves (.fork false l r)) G hpos hb hin hu
    (node_module J w hw.1 hends t (.fork false l r) hleaves ht hnode) he hc hends hw

theorem minimal_excludes (J : Branch Q Z A H) (w : List A) (t l r : P0Cotree.Tree Nat)
    (ht : Valid (Adjacent J w) t) (hleaves : leaves t = Finset.range (w.length+1))
    (hnode : Below (.fork false l r) t) (G : Grid m) (hpos : 0 < m)
    (selected : Fin 4 → P0Cotree.Tree Nat) (hselected : ∀ q, selected q ∈ children (.fork false l r))
    (hrows : ∀ q p, p ∈ leaves (selected q) ↔ InRow G q p)
    (hends : J.endX ≠ J.endY) (hw : Accepted J w) (hmin : RankMinimal J w) :
    ¬ (UniformColors J w G ∧ EqualMatrices J w G) := by
  rintro ⟨hu,he⟩
  obtain ⟨v,hv,hvlen,hrank⟩ := shorten_in_tree J w t l r ht hleaves hnode G hpos
    selected hselected hrows hu he hends hw
  have := hmin v hv hrank
  omega

theorem exists_excluding_tree (J : Branch Q Z A H) (w : List A) (hends : J.endX ≠ J.endY)
    (hw : Accepted J w) (hmin : RankMinimal J w) :
    ∃ t : P0Cotree.Tree Nat, leaves t = Finset.range (w.length+1) ∧ Valid (Adjacent J w) t ∧
      ∀ l r, Below (.fork false l r) t → ∀ m (G : Grid m), 0 < m →
        ∀ selected : Fin 4 → P0Cotree.Tree Nat, (∀ q, selected q ∈ children (.fork false l r)) →
          (∀ q p, p ∈ leaves (selected q) ↔ InRow G q p) →
            ¬ (UniformColors J w G ∧ EqualMatrices J w G) := by
  obtain ⟨t,hleaves,ht⟩ := exists_tree J w hw.1 hends
  exact ⟨t,hleaves,ht,fun l r hn _ G hp selected hs hr =>
    minimal_excludes J w t l r ht hleaves hn G hp selected hs hr hends hw hmin⟩

end NSSE.P0DZFourChildCut
