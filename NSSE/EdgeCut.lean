import NSSE

/-!
# Edge-disjoint paths force large cuts

Graph-independent list formulation of the cut argument in v398.
-/

namespace NSSE

universe u

def PairwiseEdgeDisjoint (paths : List (List ε)) : Prop :=
  ∀ p ∈ paths, ∀ q ∈ paths, p ≠ q →
    ∀ e, e ∈ p → e ∈ q → False

inductive AlignedEdgeChoice : List (List ε) → List ε → Prop
  | nil : AlignedEdgeChoice [] []
  | cons {path paths chosen} (edge : ε)
      (hedge : edge ∈ path)
      (tail : AlignedEdgeChoice paths chosen) :
      AlignedEdgeChoice (path :: paths) (edge :: chosen)

namespace AlignedEdgeChoice

theorem lengths {paths : List (List ε)} {chosen : List ε}
    (h : AlignedEdgeChoice paths chosen) :
    chosen.length = paths.length := by
  induction h with
  | nil => rfl
  | cons edge hedge tail ih => simp [ih]

theorem mem_has_path
    {paths : List (List ε)} {chosen : List ε}
    (h : AlignedEdgeChoice paths chosen)
    {edge : ε} (hmem : edge ∈ chosen) :
    ∃ path ∈ paths, edge ∈ path := by
  induction h with
  | nil => simp at hmem
  | @cons path paths chosen first hfirst tail ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact ⟨path, by simp, hfirst⟩
      · obtain ⟨p, hp, hedge⟩ := ih hmem
        exact ⟨p, by simp [hp], hedge⟩

theorem nodup_of_disjoint
    {paths : List (List ε)} {chosen : List ε}
    (hchoice : AlignedEdgeChoice paths chosen)
    (hpaths : paths.Nodup)
    (hdisjoint : PairwiseEdgeDisjoint paths) :
    chosen.Nodup := by
  induction hchoice with
  | nil => exact List.nodup_nil
  | @cons path paths chosen edge hedge tail ih =>
      have hpath_not_mem : path ∉ paths := (List.nodup_cons.mp hpaths).1
      have htail_nodup : paths.Nodup := (List.nodup_cons.mp hpaths).2
      have htail_disjoint : PairwiseEdgeDisjoint paths := by
        intro p hp q hq hpq e hep heq
        exact hdisjoint p (by simp [hp]) q (by simp [hq]) hpq e hep heq
      apply List.nodup_cons.mpr
      constructor
      · intro hedge_chosen
        obtain ⟨q, hq, hedgeq⟩ :=
          tail.mem_has_path hedge_chosen
        have hpq : path ≠ q := by
          intro heq
          subst q
          exact hpath_not_mem hq
        exact hdisjoint path (by simp) q (by simp [hq])
          hpq edge hedge hedgeq
      · exact ih htail_nodup htail_disjoint

end AlignedEdgeChoice

def HitsEveryPath (cut : ε → Prop) (paths : List (List ε)) : Prop :=
  ∀ path ∈ paths, ∃ edge ∈ path, cut edge

def HasAtLeast (cut : ε → Prop) (n : Nat) : Prop :=
  ∃ edges : List ε,
    edges.length = n ∧ edges.Nodup ∧ ∀ edge ∈ edges, cut edge

theorem aligned_choice_of_hits
    (cut : ε → Prop) (paths : List (List ε))
    (hhit : HitsEveryPath cut paths) :
    ∃ chosen,
      AlignedEdgeChoice paths chosen ∧
      ∀ edge ∈ chosen, cut edge := by
  classical
  induction paths with
  | nil =>
      exact ⟨[], AlignedEdgeChoice.nil, by simp⟩
  | cons path paths ih =>
      obtain ⟨edge, hedge, hcut⟩ := hhit path (by simp)
      have htail : HitsEveryPath cut paths := by
        intro p hp
        exact hhit p (by simp [hp])
      obtain ⟨chosen, hchoice, hall⟩ := ih htail
      refine ⟨edge :: chosen,
        AlignedEdgeChoice.cons edge hedge hchoice, ?_⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hcut
      · exact hall e he

/--
If `d` pairwise edge-disjoint paths are all hit by a cut, the cut contains
at least `d` distinct edges.
-/
theorem edge_disjoint_paths_cut_bound
    (cut : ε → Prop) (paths : List (List ε))
    (hnodup : paths.Nodup)
    (hdisjoint : PairwiseEdgeDisjoint paths)
    (hhit : HitsEveryPath cut paths) :
    HasAtLeast cut paths.length := by
  obtain ⟨chosen, hchoice, hcut⟩ :=
    aligned_choice_of_hits cut paths hhit
  exact ⟨chosen, hchoice.lengths, hchoice.nodup_of_disjoint
    hnodup hdisjoint, hcut⟩

end NSSE

