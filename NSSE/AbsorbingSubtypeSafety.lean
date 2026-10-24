import NSSE.RegularSubtypeTrees

/-! # Actual finite-word safety for arbitrary subtype trees

Safety is a label comparison, not an automaton predicate. Both-side safety
characterizes pointwise order. Periodic soundness uses absorption, never
finite height, and therefore applies to genuine infinite trees.
-/

namespace NSSE.AbsorbingSubtypeSafety

open AbsorbingSubtypeTrees RegularSubtypeTrees SubtypeConstraints ForwardTableAutomaton

variable {n d : Nat}

def Safe (s : Side) (a b : Tree d) (w : List (Fin d)) : Prop :=
  match s with
  | .left => a.label w = 2 → b.label w = 2
  | .right => b.label w = 0 → a.label w = 0

def RootSafe (s : Side) (a b : Tree d) : Prop :=
  match s with | .left => a = ⊤ → b = ⊤ | .right => b = ⊥ → a = ⊥

theorem safe_iff_project (s : Side) (a b : Tree d) (w : List (Fin d)) :
    Safe s a b w ↔ RootSafe s (project a w) (project b w) := by
  cases s <;> simp only [Safe, RootSafe, eq_bot_iff_root, eq_top_iff_root, project_label, List.append_nil]

theorem label_order (a b : Label) :
    a ≤ b ↔ (a = 2 → b = 2) ∧ (b = 0 → a = 0) := by
  fin_cases a <;> fin_cases b <;> simp

theorem below_safe {a b : Tree d} (h : a ≤ b) (s : Side) (w : List (Fin d)) : Safe s a b w := by
  have hs := (label_order _ _).mp (h w)
  cases s with | left => exact hs.1 | right => exact hs.2

theorem below_iff_all_safe (a b : Tree d) : a ≤ b ↔ ∀ s w, Safe s a b w := by
  constructor
  · exact fun h => below_safe h
  · intro h w; exact (label_order _ _).mpr ⟨h .left w,h .right w⟩

theorem rootSafe_of_le {a b : Tree d} (h : a ≤ b) (s : Side) : RootSafe s a b := by
  cases s with
  | left => intro he; subst a; exact le_antisymm le_top h
  | right => intro he; subst b; exact le_antisymm h bot_le

theorem rootSafe_mono (s : Side) {a a' b b' : Tree d}
    (ha : a ≤ a') (hb : b' ≤ b) (h : RootSafe s a' b') : RootSafe s a b := by
  cases s with
  | left => intro he; exact rootSafe_of_le hb .left (h (rootSafe_of_le ha .left he))
  | right => intro he; exact rootSafe_of_le ha .right (h (rootSafe_of_le hb .right he))

theorem safe_mono (s : Side) {a a' b b' : Tree d} (ha : a ≤ a') (hb : b' ≤ b)
    {w : List (Fin d)} (h : Safe s a' b' w) : Safe s a b w :=
  (safe_iff_project s a b w).mpr (rootSafe_mono s (project_mono ha w) (project_mono hb w)
    ((safe_iff_project s a' b' w).mp h))

theorem safe_append (s : Side) (a b : Tree d) (p q : List (Fin d)) :
    Safe s a b (p ++ q) ↔ Safe s (project a p) (project b p) q := by cases s <;> rfl

theorem project_absorbing {t leaf : Tree d} (hleaf : leaf = ⊥ ∨ leaf = ⊤)
    {p q : List (Fin d)} (hp : p <+: q) (he : project t p = leaf) : project t q = leaf := by
  obtain ⟨r,rfl⟩ := hp
  rw [← project_append, he]
  rcases hleaf with rfl | rfl <;> simp

theorem periodic_left (a b : Tree d) (root tail : List (Fin d))
    (h : project a root ≤ b) (hp : tail <+: root ++ tail) : Safe .left a b tail := by
  apply (safe_iff_project .left a b tail).mpr
  intro ht
  have he := project_absorbing (t := a) (Or.inr rfl) hp ht
  have hh := project_mono h tail
  rw [project_append, he] at hh
  exact le_antisymm le_top hh

theorem periodic_right (a b : Tree d) (root tail : List (Fin d))
    (h : a ≤ project b root) (hp : tail <+: root ++ tail) : Safe .right a b tail := by
  apply (safe_iff_project .right a b tail).mpr
  intro hb
  have he := project_absorbing (t := b) (Or.inl rfl) hp hb
  have hh := project_mono h tail
  rw [project_append, he] at hh
  exact le_antisymm hh bot_le

def QuerySafe (Q : Query n d) (s : Side) (w : List (Fin d)) : Prop :=
  ∀ ρ, Satisfies (constructor d) Q.constraints ρ → Safe s (ρ Q.left) (ρ Q.right) w

def RegularQuerySafe (Q : Query n d) (s : Side) (w : List (Fin d)) : Prop :=
  ∀ ρ, (∀ x, Regular (ρ x)) → Satisfies (constructor d) Q.constraints ρ →
    Safe s (ρ Q.left) (ρ Q.right) w

theorem entails_iff_all_safe (Q : Query n d) : Entails (constructor d) Q ↔ ∀ s w, QuerySafe Q s w := by
  constructor
  · intro h s w ρ hρ; exact below_safe (h ρ hρ) s w
  · intro h ρ hρ; exact (below_iff_all_safe _ _).mpr (fun s w => h s w ρ hρ)

theorem entails_iff_both_safe (Q : Query n d) : Entails (constructor d) Q ↔
    (∀ w, QuerySafe Q .left w) ∧ (∀ w, QuerySafe Q .right w) := by
  rw [entails_iff_all_safe]
  constructor
  · intro h; exact ⟨h .left,h .right⟩
  · rintro ⟨hl,hr⟩ s; cases s with | left => exact hl | right => exact hr

theorem regular_entails_iff_all_safe (Q : Query n d) : RegularEntails Q ↔ ∀ s w, RegularQuerySafe Q s w := by
  constructor
  · intro h s w ρ hr hρ; exact below_safe (h ρ hr hρ) s w
  · intro h ρ hr hρ; exact (below_iff_all_safe _ _).mpr (fun s w => h s w ρ hr hρ)

end NSSE.AbsorbingSubtypeSafety
