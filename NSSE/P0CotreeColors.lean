import NSSE.P0CotreeNormalize

/-! Quantitative facts of the normalized view: join children have disjoint
nonempty palettes, their number is at most the parent palette size, and
each uses strictly fewer colors. A union child is a leaf or a join. -/
namespace NSSE.P0CotreeColors
open P0Cotree P0CotreeNormalize
variable {V C : Type*} [DecidableEq V] [DecidableEq C]

def palette (col : V → C) (t : Tree V) : Finset C := (leaves t).image col

def Proper (edge : V → V → Prop) (col : V → C) (t : Tree V) : Prop :=
  ∀ a ∈ leaves t, ∀ b ∈ leaves t, a ≠ b → col a = col b → ¬ edge a b

theorem palette_nonempty (col : V → C) (t : Tree V) : (palette col t).Nonempty :=
  (leaves_nonempty t).image col

theorem palette_below (col : V → C) {u t : Tree V} (h : Below u t) :
    palette col u ⊆ palette col t := Finset.image_subset_image (below_subset h)

omit [DecidableEq C] in
theorem proper_below (edge : V → V → Prop) (col : V → C) {u t : Tree V}
    (h : Below u t) (hp : Proper edge col t) : Proper edge col u := by
  intro a ha b hb hne he
  exact hp a (below_subset h ha) b (below_subset h hb) hne he

theorem join_disjoint (edge : V → V → Prop) (col : V → C) (l r : Tree V)
    (ht : Valid edge (.fork true l r)) (hp : Proper edge col (.fork true l r)) :
    Disjoint (palette col l) (palette col r) := by
  apply Finset.disjoint_left.mpr
  intro c hc hd
  obtain ⟨a,ha,hac⟩ := Finset.mem_image.mp hc
  obtain ⟨b,hb,hbc⟩ := Finset.mem_image.mp hd
  have hne : a ≠ b := by
    intro he
    subst b
    exact Finset.disjoint_left.mp ht.2.2.1 ha hb
  have he := (ht.2.2.2 a ha b hb).1.mpr rfl
  exact hp a (Finset.mem_union_left _ ha) b (Finset.mem_union_right _ hb) hne
    (hac.trans hbc.symm) he

theorem join_palette_card (edge : V → V → Prop) (col : V → C) (l r : Tree V)
    (ht : Valid edge (.fork true l r)) (hp : Proper edge col (.fork true l r)) :
    (palette col (.fork true l r)).card = (palette col l).card + (palette col r).card := by
  simp only [palette,leaves,Finset.image_union]
  exact Finset.card_union_of_disjoint (join_disjoint edge col l r ht hp)

theorem frontier_palette_card (edge : V → V → Prop) (col : V → C) (t : Tree V)
    (ht : Valid edge t) (hp : Proper edge col t) :
    ((frontier true t).map (fun u => (palette col u).card)).sum = (palette col t).card := by
  induction t with
  | leaf v => simp [frontier]
  | fork j l r ihl ihr =>
    cases j with
    | false => simp [frontier]
    | true =>
      rw [frontier,if_pos rfl,List.map_append,List.sum_append,
        ihl ht.1 (proper_below edge col (.left true (.refl l)) hp),
        ihr ht.2.1 (proper_below edge col (.right true (.refl r)) hp)]
      exact (join_palette_card edge col l r ht hp).symm

theorem frontier_palette_disjoint (edge : V → V → Prop) (col : V → C) (t : Tree V)
    (ht : Valid edge t) (hp : Proper edge col t) :
    (frontier true t).Pairwise (fun u v => Disjoint (palette col u) (palette col v)) := by
  induction t with
  | leaf v => simp only [frontier,List.pairwise_singleton]
  | fork j l r ihl ihr =>
    cases j with
    | false => simp [frontier]
    | true =>
      rw [frontier,if_pos rfl,List.pairwise_append]
      refine ⟨ihl ht.1 (proper_below edge col (.left true (.refl l)) hp),
        ihr ht.2.1 (proper_below edge col (.right true (.refl r)) hp),?_⟩
      intro u hu v hv
      exact (join_disjoint edge col l r ht hp).mono
        (palette_below col (frontier_below true l u hu))
        (palette_below col (frontier_below true r v hv))

theorem join_children_disjoint (edge : V → V → Prop) (col : V → C) (l r : Tree V)
    (ht : Valid edge (.fork true l r)) (hp : Proper edge col (.fork true l r)) :
    (children (.fork true l r)).Pairwise (fun u v => Disjoint (palette col u) (palette col v)) := by
  simpa only [frontier,if_pos rfl,children] using frontier_palette_disjoint edge col (.fork true l r) ht hp

theorem palette_length_le (col : V → C) (L : List (Tree V)) :
    L.length ≤ (L.map (fun t => (palette col t).card)).sum := by
  induction L with
  | nil => simp
  | cons t L ih =>
    have ht := Finset.card_pos.mpr (palette_nonempty col t)
    simp only [List.length_cons,List.map_cons,List.sum_cons]
    omega

theorem join_children_count (edge : V → V → Prop) (col : V → C) (l r : Tree V)
    (ht : Valid edge (.fork true l r)) (hp : Proper edge col (.fork true l r)) :
    (children (.fork true l r)).length ≤ (palette col (.fork true l r)).card := by
  have hsum := frontier_palette_card edge col (.fork true l r) ht hp
  simp only [frontier,if_pos rfl] at hsum
  rw [← hsum]
  exact palette_length_le col (children (.fork true l r))

theorem join_child_fewer (edge : V → V → Prop) (col : V → C) (l r u : Tree V)
    (ht : Valid edge (.fork true l r)) (hp : Proper edge col (.fork true l r))
    (hu : u ∈ children (.fork true l r)) :
    (palette col u).card < (palette col (.fork true l r)).card := by
  have hsum := join_palette_card edge col l r ht hp
  have hl := Finset.card_pos.mpr (palette_nonempty col l)
  have hr := Finset.card_pos.mpr (palette_nonempty col r)
  rcases List.mem_append.mp hu with hu | hu
  · have hsub := Finset.card_le_card (palette_below col (frontier_below true l u hu))
    omega
  · have hsub := Finset.card_le_card (palette_below col (frontier_below true r u hu))
    omega

omit [DecidableEq V] in
theorem union_child_leaf_or_join (l r u : Tree V) (hu : u ∈ children (.fork false l r)) :
    (∃ v, u = .leaf v) ∨ ∃ a b, u = .fork true a b := by
  have hk := children_kind false l r u hu
  cases u with
  | leaf v => exact Or.inl ⟨v,rfl⟩
  | fork j a b =>
    cases j with
    | false => exact False.elim (hk rfl)
    | true => exact Or.inr ⟨a,b,rfl⟩

omit [DecidableEq V] in
theorem sum_bound (L : List (Tree V)) (B : Nat) (f : Tree V → Nat)
    (hf : ∀ u ∈ L, f u ≤ B) : (L.map f).sum ≤ L.length * B := by
  induction L with
  | nil => simp
  | cons t L ih =>
    have ht := hf t (List.mem_cons_self ..)
    have hL := ih (fun u hu => hf u (List.mem_cons_of_mem _ hu))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem join_size_le (edge : V → V → Prop) (col : V → C) (l r : Tree V) (B : Nat)
    (ht : Valid edge (.fork true l r)) (hp : Proper edge col (.fork true l r))
    (hB : ∀ u ∈ children (.fork true l r), (leaves u).card ≤ B) :
    (leaves (.fork true l r)).card ≤ (palette col (.fork true l r)).card * B := by
  rw [← children_card edge true l r ht]
  exact (sum_bound (children (.fork true l r)) B _ hB).trans
    (Nat.mul_le_mul_right B (join_children_count edge col l r ht hp))

end NSSE.P0CotreeColors
