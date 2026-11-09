import NSSE.P0FourGroupEntry
import NSSE.P0NormalizedActual

/-! Actual normalized union children supply the cross-zero and module
premises of the four-group cut. In a shortest accepted word no four
equal-profile children with homogeneous shuffles can occur. -/
namespace NSSE.P0FourChildCut
open P0Cotree P0CotreeNormalize P0NormalizedActual P0ActualCotree
open P0DDeadReader P0DDeadColor P0CutComparison P0FourGroupEntry
open P0HomogeneousOrder P0LayoutReader
variable {Q A H : Type*} {m : Nat}

theorem union_zero (J : Reader Q A H) (w : List A) (l r u : Tree Nat)
    (ht : Valid (Adjacent J w) (.fork false l r))
    (hu : u ∈ children (.fork false l r)) (a : Nat) (ha : a ∈ leaves u)
    (p : Nat) (hp : p ∈ leaves (.fork false l r)) (hpu : p ∉ leaves u) :
    Compatible w (leftAt J w) (rightAt J w) a p ∧
      Compatible w (leftAt J w) (rightAt J w) p a := by
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
  simpa only [Adjacent,not_or,not_not] using hn

theorem shorten_in_tree (J : Reader Q A H) (w : List A) (t l r : Tree Nat)
    (ht : Valid (Adjacent J w) t) (hleaves : leaves t = Finset.range (w.length+1))
    (hnode : Below (.fork false l r) t) (G : Grid m) (hpos : 0 < m)
    (selected : Fin 4 → Tree Nat) (hselected : ∀ q, selected q ∈ children (.fork false l r))
    (hrows : ∀ q p, p ∈ leaves (selected q) ↔ InRow G q p)
    (hu : UniformStates J w G) (he : EqualMatrices J w G)
    (hends : J.endX ≠ J.endY) (hw : Accepted J w) :
    ∃ v, Accepted J v ∧ v.length < w.length := by
  have hin (q : Fin 4) (i : Nat) (hi : i < m) : G.pos q i ∈ leaves (.fork false l r) :=
    below_subset (children_below false l r (selected q) (hselected q))
      ((hrows q _).mpr ⟨i,hi,rfl⟩)
  have hb (q : Fin 4) (i : Nat) (hi : i < m) : G.pos q i ≤ w.length := by
    have hh := below_subset hnode (hin q i hi)
    rw [hleaves,Finset.mem_range] at hh
    omega
  have hc : UnionSeparated J w (leaves (.fork false l r)) G := by
    intro q i hi p hp hnot
    exact union_zero J w l r (selected q) (below_valid _ hnode ht) (hselected q)
      (G.pos q i) ((hrows q _).mpr ⟨i,hi,rfl⟩) p hp (fun hmem => hnot ((hrows q p).mp hmem))
  exact shorten J w (leaves (.fork false l r)) G hpos hb hin hu
    (node_module J w hw.1 hends t (.fork false l r) hleaves ht hnode) he hc hends hw

theorem shortest_excludes (J : Reader Q A H) (w : List A) (t l r : Tree Nat)
    (ht : Valid (Adjacent J w) t) (hleaves : leaves t = Finset.range (w.length+1))
    (hnode : Below (.fork false l r) t) (G : Grid m) (hpos : 0 < m)
    (selected : Fin 4 → Tree Nat) (hselected : ∀ q, selected q ∈ children (.fork false l r))
    (hrows : ∀ q p, p ∈ leaves (selected q) ↔ InRow G q p)
    (hends : J.endX ≠ J.endY) (hw : Accepted J w)
    (hmin : ∀ v, Accepted J v → w.length ≤ v.length) :
    ¬ (UniformStates J w G ∧ EqualMatrices J w G) := by
  rintro ⟨hu,he⟩
  obtain ⟨v,hv,hvlen⟩ := shorten_in_tree J w t l r ht hleaves hnode G hpos
    selected hselected hrows hu he hends hw
  have := hmin v hv
  omega

theorem exists_excluding_tree (J : Reader Q A H) (w : List A) (hends : J.endX ≠ J.endY)
    (hw : Accepted J w) (hmin : ∀ v, Accepted J v → w.length ≤ v.length) :
    ∃ t : Tree Nat, leaves t = Finset.range (w.length+1) ∧ Valid (Adjacent J w) t ∧
      ∀ l r, Below (.fork false l r) t → ∀ m (G : Grid m), 0 < m →
        ∀ selected : Fin 4 → Tree Nat, (∀ q, selected q ∈ children (.fork false l r)) →
          (∀ q p, p ∈ leaves (selected q) ↔ InRow G q p) →
            ¬ (UniformStates J w G ∧ EqualMatrices J w G) := by
  obtain ⟨t,hleaves,ht⟩ := exists_tree J w hw.1 hends
  exact ⟨t,hleaves,ht,fun l r hn _ G hp selected hs hr =>
    shortest_excludes J w t l r ht hleaves hn G hp selected hs hr hends hw hmin⟩

end NSSE.P0FourChildCut
