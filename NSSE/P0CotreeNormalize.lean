import NSSE.P0CotreeModules

/-! A normalized n-ary view of a binary cotree. Equal-kind consecutive
nodes are flattened by `frontier`; every exposed node is still an actual
subtree, so its ordered external-color module proof is retained. -/
namespace NSSE.P0CotreeNormalize
open P0Cotree
variable {V : Type*} [DecidableEq V]

deriving instance DecidableEq for Tree

def kind : Tree V → Option Bool
  | .leaf _ => none
  | .fork j _ _ => some j

def frontier (j : Bool) : Tree V → List (Tree V)
  | .leaf v => [.leaf v]
  | .fork k l r => if k = j then frontier j l ++ frontier j r else [.fork k l r]

def children : Tree V → List (Tree V)
  | .leaf _ => []
  | .fork j l r => frontier j l ++ frontier j r

omit [DecidableEq V] in
theorem frontier_nonempty (j : Bool) (t : Tree V) : 0 < (frontier j t).length := by
  induction t with
  | leaf v => simp [frontier]
  | fork k l r ihl ihr =>
    simp only [frontier]
    split_ifs <;> simp only [List.length_append,List.length_singleton] <;> omega

omit [DecidableEq V] in
theorem frontier_below (j : Bool) (t u : Tree V) (hu : u ∈ frontier j t) : Below u t := by
  induction t with
  | leaf v => simp only [frontier,List.mem_singleton] at hu; subst u; exact .refl _
  | fork k l r ihl ihr =>
    simp only [frontier] at hu
    split_ifs at hu with hk
    · rcases List.mem_append.mp hu with hu | hu
      · exact .left k (ihl hu)
      · exact .right k (ihr hu)
    · simp only [List.mem_singleton] at hu
      subst u
      exact .refl _

omit [DecidableEq V] in
theorem frontier_kind (j : Bool) (t u : Tree V) (hu : u ∈ frontier j t) : kind u ≠ some j := by
  induction t with
  | leaf v => simp only [frontier,List.mem_singleton] at hu; subst u; simp [kind]
  | fork k l r ihl ihr =>
    simp only [frontier] at hu
    split_ifs at hu with hk
    · rcases List.mem_append.mp hu with hu | hu
      · exact ihl hu
      · exact ihr hu
    · simp only [List.mem_singleton] at hu
      subst u
      intro he
      exact hk (Option.some.inj he)

theorem frontier_cover (j : Bool) (t : Tree V) (v : V) :
    v ∈ leaves t ↔ ∃ u ∈ frontier j t, v ∈ leaves u := by
  induction t with
  | leaf a => simp only [frontier,List.mem_singleton,exists_eq_left]
  | fork k l r ihl ihr =>
    by_cases hk : k = j
    · simp only [frontier,if_pos hk,leaves,Finset.mem_union,ihl,ihr,List.mem_append]
      constructor
      · rintro (⟨u,hu,hv⟩ | ⟨u,hu,hv⟩)
        · exact ⟨u,Or.inl hu,hv⟩
        · exact ⟨u,Or.inr hu,hv⟩
      · rintro ⟨u,hu,hv⟩
        rcases hu with hu | hu
        · exact Or.inl ⟨u,hu,hv⟩
        · exact Or.inr ⟨u,hu,hv⟩
    · simp only [frontier,if_neg hk,List.mem_singleton,exists_eq_left]

def Cross (edge : V → V → Prop) (j : Bool) (l r : Tree V) : Prop :=
  Disjoint (leaves l) (leaves r) ∧ ∀ a ∈ leaves l, ∀ b ∈ leaves r,
    (edge a b ↔ j = true) ∧ (edge b a ↔ j = true)

theorem cross_subtrees (edge : V → V → Prop) (j : Bool) (l r u v : Tree V)
    (ht : Valid edge (.fork j l r)) (hu : Below u l) (hv : Below v r) : Cross edge j u v := by
  refine ⟨Finset.disjoint_left.mpr ?_,?_⟩
  · intro x hx hy
    exact Finset.disjoint_left.mp ht.2.2.1 (below_subset hu hx) (below_subset hv hy)
  · intro a ha b hb
    exact ht.2.2.2 a (below_subset hu ha) b (below_subset hv hb)

theorem frontier_pairwise (edge : V → V → Prop) (j : Bool) (t : Tree V) (ht : Valid edge t) :
    (frontier j t).Pairwise (Cross edge j) := by
  induction t with
  | leaf v => simp only [frontier,List.pairwise_singleton]
  | fork k l r ihl ihr =>
    by_cases hk : k = j
    · subst k
      rw [frontier,if_pos rfl,List.pairwise_append]
      refine ⟨ihl ht.1,ihr ht.2.1,?_⟩
      intro u hu v hv
      exact cross_subtrees edge j l r u v ht (frontier_below j l u hu) (frontier_below j r v hv)
    · simp only [frontier,if_neg hk,List.pairwise_singleton]

theorem frontier_card (edge : V → V → Prop) (j : Bool) (t : Tree V) (ht : Valid edge t) :
    ((frontier j t).map (fun u => (leaves u).card)).sum = (leaves t).card := by
  induction t with
  | leaf v => simp [frontier]
  | fork k l r ihl ihr =>
    by_cases hk : k = j
    · rw [frontier,if_pos hk,List.map_append,List.sum_append,ihl ht.1,ihr ht.2.1]
      exact (Finset.card_union_of_disjoint ht.2.2.1).symm
    · simp only [frontier,if_neg hk,List.map_singleton,List.sum_singleton]

omit [DecidableEq V] in
theorem children_length (j : Bool) (l r : Tree V) : 2 ≤ (children (.fork j l r)).length := by
  have hl := frontier_nonempty j l
  have hr := frontier_nonempty j r
  simp only [children,List.length_append]
  omega

omit [DecidableEq V] in
theorem children_below (j : Bool) (l r u : Tree V) (hu : u ∈ children (.fork j l r)) :
    Below u (.fork j l r) := by
  rcases List.mem_append.mp hu with hu | hu
  · exact .left j (frontier_below j l u hu)
  · exact .right j (frontier_below j r u hu)

omit [DecidableEq V] in
theorem children_kind (j : Bool) (l r u : Tree V) (hu : u ∈ children (.fork j l r)) :
    kind u ≠ some j := by
  rcases List.mem_append.mp hu with hu | hu
  · exact frontier_kind j l u hu
  · exact frontier_kind j r u hu

theorem children_pairwise (edge : V → V → Prop) (j : Bool) (l r : Tree V)
    (ht : Valid edge (.fork j l r)) : (children (.fork j l r)).Pairwise (Cross edge j) := by
  simpa only [frontier,if_pos rfl,children] using frontier_pairwise edge j (.fork j l r) ht

theorem children_card (edge : V → V → Prop) (j : Bool) (l r : Tree V)
    (ht : Valid edge (.fork j l r)) :
    ((children (.fork j l r)).map (fun u => (leaves u).card)).sum = (leaves (.fork j l r)).card := by
  simpa only [frontier,if_pos rfl,children] using frontier_card edge j (.fork j l r) ht

theorem children_cover (j : Bool) (l r : Tree V) (v : V) :
    v ∈ leaves (.fork j l r) ↔ ∃ u ∈ children (.fork j l r), v ∈ leaves u := by
  simpa only [frontier,if_pos rfl,children] using frontier_cover j (.fork j l r) v

theorem children_smaller (edge : V → V → Prop) (j : Bool) (l r u : Tree V)
    (ht : Valid edge (.fork j l r)) (hu : u ∈ children (.fork j l r)) :
    (leaves u).card < (leaves (.fork j l r)).card := by
  have hsum : (leaves (.fork j l r)).card = (leaves l).card + (leaves r).card :=
    Finset.card_union_of_disjoint ht.2.2.1
  have hl := Finset.card_pos.mpr (leaves_nonempty l)
  have hr := Finset.card_pos.mpr (leaves_nonempty r)
  rcases List.mem_append.mp hu with hu | hu
  · have hsub := Finset.card_le_card (below_subset (frontier_below j l u hu))
    omega
  · have hsub := Finset.card_le_card (below_subset (frontier_below j r u hu))
    omega

theorem children_nodup (edge : V → V → Prop) (j : Bool) (l r : Tree V)
    (ht : Valid edge (.fork j l r)) : (children (.fork j l r)).Nodup := by
  have hp := children_pairwise edge j l r ht
  apply List.Pairwise.imp (fun {u v} h => ?_) hp
  intro he
  subst v
  obtain ⟨x,hx⟩ := leaves_nonempty u
  exact Finset.disjoint_left.mp h.1 hx hx

end NSSE.P0CotreeNormalize
