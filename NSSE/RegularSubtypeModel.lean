import NSSE.RegularSubtypeTrees
import NSSE.SubtypeShapeGrammar
import NSSE.SubtypeLabelClashes

/-! # A computed regular model for every label-consistent original system

The SAME actual finite Support/down/lowStep computation is reused, but
this graph has only a lower set. Its absorbing, possibly infinite trees
are proved to satisfy ALL original literals. No finite model is assumed.
-/

namespace NSSE.RegularSubtypeModel

open AbsorbingSubtypeTrees RegularSubtypeTrees SubtypeConstraints
open SubtypeShapeGrammar SubtypeLabelClashes

variable {n d : Nat}

def HasTop (φ : Constraints n d) (L : Finset (Fin n)) : Prop := ∃ x ∈ φ.top, x ∈ L

instance (φ : Constraints n d) (L : Finset (Fin n)) : Decidable (HasTop φ L) := by
  unfold HasTop; infer_instance

def label (φ : Constraints n d) (L : Finset (Fin n)) : Label :=
  if HasTop φ L then 2 else if LowF φ L then 1 else 0

def graph (φ : Constraints n d) : Graph (Finset (Fin n)) d := ⟨label φ,lowStep φ⟩

def model (φ : Constraints n d) (x : Fin n) : Tree d := (graph φ).tree (down φ x)

theorem hasTop_mono (φ : Constraints n d) {L K : Finset (Fin n)} (h : L ⊆ K) :
    HasTop φ L → HasTop φ K := by
  rintro ⟨x,hx,hm⟩; exact ⟨x,hx,h hm⟩

theorem label_mono (φ : Constraints n d) {L K : Finset (Fin n)} (h : L ⊆ K) : label φ L ≤ label φ K := by
  have ht := hasTop_mono φ h
  have hf := lowF_mono φ h
  by_cases hL : HasTop φ L <;> by_cases hK : HasTop φ K <;>
    by_cases hLF : LowF φ L <;> by_cases hKF : LowF φ K <;> simp_all [label]

theorem tree_mono (φ : Constraints n d) {L K : Finset (Fin n)} (h : L ⊆ K) :
    (graph φ).tree L ≤ (graph φ).tree K := by
  apply Graph.compare (graph φ) (graph φ) (fun L K => L ⊆ K) ?_ ?_ h
  · exact fun _ _ h => label_mono φ h
  · exact fun _ _ h _ _ i => lowStep_mono φ h i

theorem model_regular (φ : Constraints n d) (x : Fin n) : Regular (model φ x) :=
  (graph φ).regular (down φ x)

theorem state_count : Fintype.card (Finset (Fin n)) = 2 ^ n := by simp

theorem model_satisfies (φ : Constraints n d) (hc : ¬ LabelClash φ) :
    Satisfies (constructor d) φ (model φ) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro a ha
    have hnt : ¬ HasTop φ (down φ a.1) := by
      rintro ⟨x,hx,hm⟩
      exact hc (Or.inr (Or.inl ⟨x,hx,a,ha,(mem_down φ _ _).mp hm⟩))
    by_cases hf : LowF φ (down φ a.1)
    · have hl : (graph φ).label (down φ a.1) = 1 := by simp [graph, label, hnt, hf]
      change (graph φ).tree (down φ a.1) ≤ node (fun i => model φ (a.2 i))
      rw [Graph.tree_node _ _ hl]
      apply (node_le_node _ _).mpr
      intro i
      exact tree_mono φ (upper_next_refines φ a ha i).1
    · have hl : (graph φ).label (down φ a.1) = 0 := by simp [graph, label, hnt, hf]
      change (graph φ).tree (down φ a.1) ≤ _
      rw [Graph.tree_bot _ _ hl]
      exact bot_le
  · intro a ha
    by_cases ht : HasTop φ (down φ a.1)
    · have hl : (graph φ).label (down φ a.1) = 2 := by simp [graph, label, ht]
      change _ ≤ (graph φ).tree (down φ a.1)
      rw [Graph.tree_top _ _ hl]
      exact le_top
    · have hf : LowF φ (down φ a.1) := ⟨a,ha,(mem_down φ _ _).mpr (.refl _)⟩
      have hl : (graph φ).label (down φ a.1) = 1 := by simp [graph, label, ht, hf]
      change node (fun i => model φ (a.2 i)) ≤ (graph φ).tree (down φ a.1)
      rw [Graph.tree_node _ _ hl]
      apply (node_le_node _ _).mpr
      intro i
      exact tree_mono φ (lower_next_refines φ a ha i).1
  · intro x hx
    have hnt : ¬ HasTop φ (down φ x) := by
      rintro ⟨y,hy,hm⟩
      exact hc (Or.inl ⟨y,hy,x,hx,(mem_down φ _ _).mp hm⟩)
    have hnf : ¬ LowF φ (down φ x) := by
      rintro ⟨a,ha,hm⟩
      exact hc (Or.inr (Or.inr ⟨a,ha,x,hx,(mem_down φ _ _).mp hm⟩))
    exact Graph.tree_bot (graph φ) (down φ x) (by simp [graph, label, hnt, hnf])
  · intro x hx
    have ht : HasTop φ (down φ x) := ⟨x,hx,(mem_down φ _ _).mpr (.refl _)⟩
    exact Graph.tree_top (graph φ) (down φ x) (by simp [graph, label, ht])

theorem bounded_label (φ : Constraints n d) (ρ : Fin n → Tree d)
    (hρ : Satisfies (constructor d) φ ρ) (L : Finset (Fin n)) (t : Tree d)
    (hb : ∀ x ∈ L, ρ x ≤ t) : label φ L ≤ t.label [] := by
  by_cases ht : HasTop φ L
  · simp only [label, if_pos ht]
    obtain ⟨x,hx,hm⟩ := ht
    have he := hb x hm
    rw [hρ.2.2.2 x hx] at he
    exact he []
  · by_cases hf : LowF φ L
    · simp only [label, if_neg ht, if_pos hf]
      obtain ⟨a,ha,hm⟩ := hf
      have he := (hρ.2.1 a ha).trans (hb a.1 hm)
      exact he []
    · simp only [label, if_neg ht, if_neg hf]
      exact Nat.zero_le _

/-- The source graph is below ANY tree bounding all its required original
variables. The target tree need not be regular, let alone finite. -/
theorem bounded_tree (φ : Constraints n d) (ρ : Fin n → Tree d)
    (hρ : Satisfies (constructor d) φ ρ) (L : Finset (Fin n)) (t : Tree d)
    (hb : ∀ x ∈ L, ρ x ≤ t) : (graph φ).tree L ≤ t := by
  apply AbsorbingSubtypeTrees.compare
    (fun a b => ∃ K, (graph φ).tree K = a ∧ ∀ x ∈ K, ρ x ≤ b) ?_ ?_ ⟨L,rfl,hb⟩
  · rintro a b ⟨K,rfl,hK⟩
    exact bounded_label φ ρ hρ K b hK
  · rintro a b ⟨K,rfl,hK⟩ hnode _ i
    change (graph φ).label K = 1 at hnode
    refine ⟨lowStep φ K i, ?_, ?_⟩
    · simp only [Graph.project_tree, Graph.step, if_pos hnode]
      rfl
    · intro z hz
      obtain ⟨a,ha,hm,hs⟩ := (mem_lowStep φ K i z).mp hz
      apply (support_sound (constructor d) φ ρ hρ hs).trans
      have he := project_mono ((hρ.2.1 a ha).trans (hK a.1 hm)) [i]
      simpa only [constructor, project_node, project_nil] using he

theorem model_least (φ : Constraints n d) (ρ : Fin n → Tree d)
    (hρ : Satisfies (constructor d) φ ρ) (x : Fin n) : model φ x ≤ ρ x := by
  apply bounded_tree φ ρ hρ (down φ x) (ρ x)
  intro z hz
  exact support_sound (constructor d) φ ρ hρ ((mem_down φ x z).mp hz)

theorem solution_no_clash (φ : Constraints n d) (ρ : Fin n → Tree d)
    (hρ : Satisfies (constructor d) φ ρ) : ¬ LabelClash φ := by
  rintro (⟨x,hx,y,hy,hs⟩ | ⟨x,hx,a,ha,hs⟩ | ⟨a,ha,y,hy,hs⟩)
  · have he := support_sound (constructor d) φ ρ hρ hs
    rw [hρ.2.2.2 x hx,hρ.2.2.1 y hy] at he
    have hroot := he []
    exact (by decide : ¬ (2 : Label) ≤ 0) hroot
  · have he := (support_sound (constructor d) φ ρ hρ hs).trans (hρ.1 a ha)
    rw [hρ.2.2.2 x hx] at he
    have hroot := he []
    exact (by decide : ¬ (2 : Label) ≤ 1) hroot
  · have he := (hρ.2.1 a ha).trans (support_sound (constructor d) φ ρ hρ hs)
    rw [hρ.2.2.1 y hy] at he
    have hroot := he []
    exact (by decide : ¬ (1 : Label) ≤ 0) hroot

theorem satisfiable_iff (φ : Constraints n d) : Satisfiable (constructor d) φ ↔ ¬ LabelClash φ := by
  constructor
  · rintro ⟨ρ,hρ⟩; exact solution_no_clash φ ρ hρ
  · intro h; exact ⟨model φ, model_satisfies φ h⟩

theorem regular_satisfiable_iff (φ : Constraints n d) : RegularSatisfiable φ ↔ ¬ LabelClash φ := by
  constructor
  · rintro ⟨ρ,_,hρ⟩; exact solution_no_clash φ ρ hρ
  · intro h; exact ⟨model φ,model_regular φ,model_satisfies φ h⟩

def decideSatisfiable (φ : Constraints n d) : Bool := !labelClashBool φ

theorem decideSatisfiable_correct (φ : Constraints n d) :
    decideSatisfiable φ = true ↔ Satisfiable (constructor d) φ := by
  rw [satisfiable_iff, ← labelClashBool_correct]
  unfold decideSatisfiable
  cases labelClashBool φ <;> simp

theorem decideRegularSatisfiable_correct (φ : Constraints n d) :
    decideSatisfiable φ = true ↔ RegularSatisfiable φ :=
  (decideSatisfiable_correct φ).trans ((satisfiable_iff φ).trans (regular_satisfiable_iff φ).symm)

end NSSE.RegularSubtypeModel
