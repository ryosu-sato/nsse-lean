import NSSE.FiniteSubtypeTrees

/-! # Literal path safety characterizes finite-tree subtype entailment

Safety has the published meaning: the selected side has a constructor at
the path, or a bottom prefix on the left or a top prefix on the right has
already made all extensions safe. No automaton language is used to define it.
-/

namespace NSSE.FiniteSubtypeSafety

open FiniteSubtypeTrees ForwardTableAutomaton SubtypeConstraints

variable {d n : Nat}

def atPath : Tree d → List (Fin d) → Option (Tree d)
  | t, [] => some t
  | .node children, i :: path => atPath (children i) path
  | .bot, _ :: _ => none
  | .top, _ :: _ => none

def HasNode (t : Tree d) (path : List (Fin d)) : Prop :=
  ∃ children, atPath t path = some (.node children)

def Hits (t target : Tree d) (path : List (Fin d)) : Prop :=
  ∃ pref, pref <+: path ∧ atPath t pref = some target

@[simp] theorem hits_nil (t target : Tree d) : Hits t target [] ↔ t = target := by
  simp [Hits, atPath]

theorem hits_cons_node (children : Fin d → Tree d) (target : Tree d)
    (hne : Tree.node children ≠ target) (i : Fin d) (path : List (Fin d)) :
    Hits (.node children) target (i :: path) ↔ Hits (children i) target path := by
  constructor
  · rintro ⟨pref, ⟨rest, he⟩, hat⟩
    cases pref with
    | nil => exact False.elim (hne (Option.some.inj hat))
    | cons j pref =>
        obtain ⟨rfl, he'⟩ := List.cons.inj he
        exact ⟨pref, ⟨rest, he'⟩, hat⟩
  · rintro ⟨pref, ⟨rest, he⟩, hat⟩
    exact ⟨i :: pref, ⟨rest, by simp only [List.cons_append, he]⟩, hat⟩

def Safe (side : Side) (left right : Tree d) (path : List (Fin d)) : Prop :=
  (match side with | .left => HasNode left path | .right => HasNode right path) ∨
    Hits left .bot path ∨ Hits right .top path

theorem safe_cons_nodes (side : Side) (left right : Fin d → Tree d)
    (i : Fin d) (path : List (Fin d)) :
    Safe side (.node left) (.node right) (i :: path) ↔ Safe side (left i) (right i) path := by
  have hb := hits_cons_node left .bot (by intro h; cases h) i path
  have ht := hits_cons_node right .top (by intro h; cases h) i path
  cases side <;> simp only [Safe, HasNode, atPath, hb, ht]

theorem below_safe {left right : Tree d} (h : left ≤ right)
    (side : Side) (path : List (Fin d)) : Safe side left right path := by
  change Below left right at h
  induction h generalizing side path with
  | bot right => exact Or.inr (Or.inl ⟨[], List.nil_prefix, rfl⟩)
  | top left => exact Or.inr (Or.inr ⟨[], List.nil_prefix, rfl⟩)
  | @node left right h ih =>
      cases path with
      | nil => cases side <;> exact Or.inl ⟨_, rfl⟩
      | cons i path => exact (safe_cons_nodes side left right i path).mpr (ih i side path)

theorem below_of_all_safe (left right : Tree d)
    (h : ∀ side path, Safe side left right path) : left ≤ right := by
  induction left generalizing right with
  | bot => exact bot_le
  | top =>
      cases right with
      | bot =>
          have hf := h .left []
          simp [Safe, HasNode, atPath] at hf
      | top => exact le_rfl
      | node right =>
          have hf := h .left []
          simp [Safe, HasNode, atPath] at hf
  | node left ih =>
      cases right with
      | bot =>
          have hf := h .right []
          simp [Safe, HasNode, atPath] at hf
      | top => exact le_top
      | node right =>
          apply Below.node
          intro i
          apply ih i (right i)
          intro side path
          exact (safe_cons_nodes side left right i path).mp (h side (i :: path))

theorem below_iff_all_safe (left right : Tree d) :
    left ≤ right ↔ ∀ side path, Safe side left right path :=
  ⟨fun h => below_safe h, below_of_all_safe left right⟩

/-- Semantic query safety quantifies the original constraint solutions,
not runs of the constructed side automaton. -/
def QuerySafe (Q : Query n d) (side : Side) (path : List (Fin d)) : Prop :=
  ∀ ρ, Satisfies (constructor d) Q.constraints ρ → Safe side (ρ Q.left) (ρ Q.right) path

theorem entails_iff_all_safe (Q : Query n d) :
    Entails (constructor d) Q ↔ ∀ side path, QuerySafe Q side path := by
  constructor
  · intro h side path ρ hρ
    exact below_safe (h ρ hρ) side path
  · intro h ρ hρ
    apply below_of_all_safe
    intro side path
    exact h side path ρ hρ

theorem entails_iff_both_safe (Q : Query n d) : Entails (constructor d) Q ↔
    (∀ path, QuerySafe Q .left path) ∧ (∀ path, QuerySafe Q .right path) := by
  rw [entails_iff_all_safe]
  constructor
  · intro h; exact ⟨h .left, h .right⟩
  · rintro ⟨hl,hr⟩ side
    cases side with
    | left => exact hl
    | right => exact hr

end NSSE.FiniteSubtypeSafety
