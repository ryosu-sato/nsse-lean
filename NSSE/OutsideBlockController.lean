import NSSE.BlockRelationPresentation
import NSSE.TerminalBorderRank

/-! # Exact outside control: skip precisely the two predecessor blocks -/

namespace NSSE.OutsideBlockController

open GuardedBlockRelation

universe u v
variable {B : Type u} {Q : Type v}

inductive State (Q : Type v)
  | before (firstAvailable : Bool) (q : Q)
  | waitLeft
  | middle (q : Q)
  | waitRight
  | after (q : Q)

theorem exists_state (P : State Q → Prop) : (∃ s, P s) ↔
    (∃ b q, P (.before b q)) ∨ P .waitLeft ∨ (∃ q, P (.middle q)) ∨
      P .waitRight ∨ (∃ q, P (.after q)) := by
  constructor
  · rintro ⟨s, hs⟩
    cases s with
    | before b q => exact Or.inl ⟨b, q, hs⟩
    | waitLeft => exact Or.inr (Or.inl hs)
    | middle q => exact Or.inr (Or.inr (Or.inl ⟨q, hs⟩))
    | waitRight => exact Or.inr (Or.inr (Or.inr (Or.inl hs)))
    | after q => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨q, hs⟩)))
  · rintro (⟨b, q, h⟩ | h | ⟨q, h⟩ | h | ⟨q, h⟩)
    · exact ⟨.before b q, h⟩
    · exact ⟨.waitLeft, h⟩
    · exact ⟨.middle q, h⟩
    · exact ⟨.waitRight, h⟩
    · exact ⟨.after q, h⟩

structure Data (B : Type u) (Q : Type v) where
  block : NSSE.NFA B Q
  r0 : Q
  r1 : Q
  t0 : Q
  t1 : Q
  first : Bool

namespace Data

def automaton (G : Data B Q) : NSSE.NFA (B ⊕ Bool) (State Q) where
  start s := match s with
    | .before b q => b = true ∧ G.block.start q
    | _ => False
  accept s := match s with
    | .after q => G.block.accept q
    | _ => False
  step s x t := match s, x, t with
    | .before _ q, .inl U, .before b' r => b' = false ∧ G.block.step q U r
    | .before b q, .inl _, .waitLeft => q = G.r0 ∧ b = G.first
    | .waitLeft, .inr false, .middle r => r = G.r1
    | .middle q, .inl U, .middle r => G.block.step q U r
    | .middle q, .inl _, .waitRight => q = G.t0
    | .waitRight, .inr true, .after r => r = G.t1
    | .after q, .inl U, .after r => G.block.step q U r
    | _, _, _ => False

theorem before_data (G : Data B Q) (b : Bool) (q : Q) (U : B) (w : List (B ⊕ Bool)) :
    AcceptFrom G.automaton (.before b q) (.inl U :: w) ↔
      (∃ r, G.block.step q U r ∧ AcceptFrom G.automaton (.before false r) w) ∨
      (q = G.r0 ∧ b = G.first ∧ AcceptFrom G.automaton .waitLeft w) := by
  simp [acceptFrom_cons, exists_state, automaton, and_assoc]

theorem middle_data (G : Data B Q) (q : Q) (U : B) (w : List (B ⊕ Bool)) :
    AcceptFrom G.automaton (.middle q) (.inl U :: w) ↔
      (∃ r, G.block.step q U r ∧ AcceptFrom G.automaton (.middle r) w) ∨
      (q = G.t0 ∧ AcceptFrom G.automaton .waitRight w) := by
  simp [acceptFrom_cons, exists_state, automaton]

theorem after_data (G : Data B Q) (q : Q) (U : B) (w : List (B ⊕ Bool)) :
    AcceptFrom G.automaton (.after q) (.inl U :: w) ↔
      ∃ r, G.block.step q U r ∧ AcceptFrom G.automaton (.after r) w := by
  simp [acceptFrom_cons, exists_state, automaton]

theorem waitLeft_data (G : Data B Q) (U : B) (w : List (B ⊕ Bool)) :
    ¬ AcceptFrom G.automaton .waitLeft (.inl U :: w) := by
  simp [acceptFrom_cons, exists_state, automaton]

theorem waitRight_data (G : Data B Q) (U : B) (w : List (B ⊕ Bool)) :
    ¬ AcceptFrom G.automaton .waitRight (.inl U :: w) := by
  simp [acceptFrom_cons, exists_state, automaton]

theorem before_marker (G : Data B Q) (b : Bool) (q : Q) (m : Bool) (w : List (B ⊕ Bool)) :
    ¬ AcceptFrom G.automaton (.before b q) (.inr m :: w) := by
  cases m <;> simp [acceptFrom_cons, exists_state, automaton]

theorem middle_marker (G : Data B Q) (q : Q) (m : Bool) (w : List (B ⊕ Bool)) :
    ¬ AcceptFrom G.automaton (.middle q) (.inr m :: w) := by
  cases m <;> simp [acceptFrom_cons, exists_state, automaton]

theorem waitLeft_marker (G : Data B Q) (w : List (B ⊕ Bool)) :
    AcceptFrom G.automaton .waitLeft (.inr false :: w) ↔
      AcceptFrom G.automaton (.middle G.r1) w := by
  simp [acceptFrom_cons, exists_state, automaton]

theorem waitRight_marker (G : Data B Q) (w : List (B ⊕ Bool)) :
    AcceptFrom G.automaton .waitRight (.inr true :: w) ↔
      AcceptFrom G.automaton (.after G.t1) w := by
  simp [acceptFrom_cons, exists_state, automaton]

theorem before_next_data (G : Data B Q) (b : Bool) (q : Q) (U V : B) (w : List (B ⊕ Bool)) :
    AcceptFrom G.automaton (.before b q) (.inl U :: .inl V :: w) ↔
      ∃ r, G.block.step q U r ∧ AcceptFrom G.automaton (.before false r) (.inl V :: w) := by
  rw [G.before_data]
  simp only [G.waitLeft_data, and_false, or_false]

theorem middle_next_data (G : Data B Q) (q : Q) (U V : B) (w : List (B ⊕ Bool)) :
    AcceptFrom G.automaton (.middle q) (.inl U :: .inl V :: w) ↔
      ∃ r, G.block.step q U r ∧ AcceptFrom G.automaton (.middle r) (.inl V :: w) := by
  rw [G.middle_data]
  simp only [G.waitRight_data, and_false, or_false]

theorem before_last_data (G : Data B Q) (b : Bool) (q : Q) (U : B) (w : List (B ⊕ Bool)) :
    AcceptFrom G.automaton (.before b q) (.inl U :: .inr false :: w) ↔
      q = G.r0 ∧ b = G.first ∧ AcceptFrom G.automaton (.middle G.r1) w := by
  rw [G.before_data, G.waitLeft_marker]
  simp [G.before_marker]

theorem middle_last_data (G : Data B Q) (q : Q) (U : B) (w : List (B ⊕ Bool)) :
    AcceptFrom G.automaton (.middle q) (.inl U :: .inr true :: w) ↔
      q = G.t0 ∧ AcceptFrom G.automaton (.after G.t1) w := by
  rw [G.middle_data, G.waitRight_marker]
  simp [G.middle_marker]

theorem runs_cons_iff (T : NSSE.NFA B Q) (q r : Q) (U : B) (w : List B) :
    T.Runs q (U :: w) r ↔ ∃ s, T.step q U s ∧ T.Runs s w r := by
  constructor
  · intro h
    cases h with
    | cons hs ht => exact ⟨_, hs, ht⟩
  · rintro ⟨s, hs, ht⟩
    exact .cons hs ht

theorem before_segment (G : Data B Q) (pre : List B) (U : B) (w : List (B ⊕ Bool))
    (b : Bool) (q : Q) :
    AcceptFrom G.automaton (.before b q) ((pre ++ [U]).map Sum.inl ++ .inr false :: w) ↔
      (b && pre.isEmpty) = G.first ∧ G.block.Runs q pre G.r0 ∧
        AcceptFrom G.automaton (.middle G.r1) w := by
  induction pre generalizing b q with
  | nil =>
      simp only [List.nil_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        G.before_last_data, List.isEmpty_nil, Bool.and_true, runs_nil_iff]
      exact ⟨fun ⟨hq, hb, h⟩ => ⟨hb, hq, h⟩, fun ⟨hb, hq, h⟩ => ⟨hq, hb, h⟩⟩
  | cons V pre ih =>
      have hnonempty : ∃ W ws, (pre ++ [U]).map Sum.inl ++ Sum.inr false :: w = Sum.inl W :: ws := by
        cases pre with
        | nil => exact ⟨U, _, rfl⟩
        | cons W pre => exact ⟨W, _, rfl⟩
      obtain ⟨W, ws, he⟩ := hnonempty
      change AcceptFrom G.automaton (.before b q)
        (Sum.inl V :: ((pre ++ [U]).map Sum.inl ++ Sum.inr false :: w)) ↔ _
      rw [he, G.before_next_data, ← he]
      simp only [ih, Bool.false_and, List.isEmpty_cons, Bool.and_false, runs_cons_iff]
      constructor
      · rintro ⟨r, hs, hb, hr, ht⟩
        exact ⟨hb, ⟨r, hs, hr⟩, ht⟩
      · rintro ⟨hb, ⟨r, hs, hr⟩, ht⟩
        exact ⟨r, hs, hb, hr, ht⟩

theorem middle_segment (G : Data B Q) (mid : List B) (V : B) (w : List (B ⊕ Bool)) (q : Q) :
    AcceptFrom G.automaton (.middle q) ((mid ++ [V]).map Sum.inl ++ .inr true :: w) ↔
      G.block.Runs q mid G.t0 ∧ AcceptFrom G.automaton (.after G.t1) w := by
  induction mid generalizing q with
  | nil =>
      simp only [List.nil_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        G.middle_last_data, runs_nil_iff]
  | cons U mid ih =>
      have hnonempty : ∃ W ws, (mid ++ [V]).map Sum.inl ++ Sum.inr true :: w = Sum.inl W :: ws := by
        cases mid with
        | nil => exact ⟨V, _, rfl⟩
        | cons W mid => exact ⟨W, _, rfl⟩
      obtain ⟨W, ws, he⟩ := hnonempty
      change AcceptFrom G.automaton (.middle q)
        (Sum.inl U :: ((mid ++ [V]).map Sum.inl ++ Sum.inr true :: w)) ↔ _
      rw [he, G.middle_next_data, ← he]
      simp only [ih, runs_cons_iff]
      constructor
      · rintro ⟨r, hs, hr, ht⟩
        exact ⟨⟨r, hs, hr⟩, ht⟩
      · rintro ⟨⟨r, hs, hr⟩, ht⟩
        exact ⟨r, hs, hr, ht⟩

theorem after_segment (G : Data B Q) (post : List B) (q : Q) :
    AcceptFrom G.automaton (.after q) (post.map Sum.inl) ↔ AcceptFrom G.block q post := by
  induction post generalizing q with
  | nil => simp [acceptFrom_nil, automaton]
  | cons U post ih =>
      simp only [List.map_cons, G.after_data, ih, acceptFrom_cons]

def input (pre : List B) (U : B) (mid : List B) (V : B) (post : List B) : List (B ⊕ Bool) :=
  (pre ++ [U]).map Sum.inl ++ .inr false :: ((mid ++ [V]).map Sum.inl ++ .inr true :: post.map Sum.inl)

/-- Exact acceptance on EVERY well-formed pair of marked cuts. Empty
outside sequences are genuine identity paths; the two skipped blocks
are distinct input positions, even when either block word is empty. -/
theorem accepts_input (G : Data B Q) (pre : List B) (U : B) (mid : List B) (V : B) (post : List B) :
    G.automaton.Accepts (input pre U mid V post) ↔
      pre.isEmpty = G.first ∧
      (∃ q, G.block.start q ∧ G.block.Runs q pre G.r0) ∧
      G.block.Runs G.r1 mid G.t0 ∧ AcceptFrom G.block G.t1 post := by
  have ha : G.automaton.Accepts (input pre U mid V post) ↔
      ∃ q, G.block.start q ∧ AcceptFrom G.automaton (.before true q) (input pre U mid V post) := by
    constructor
    · rintro ⟨s, r, hs, hrun, hr⟩
      cases s with
      | before b q =>
          obtain ⟨hb, hq⟩ := hs
          subst b
          exact ⟨q, hq, r, hrun, hr⟩
      | waitLeft => exact False.elim hs
      | middle q => exact False.elim hs
      | waitRight => exact False.elim hs
      | after q => exact False.elim hs
    · rintro ⟨q, hq, r, hrun, hr⟩
      exact ⟨.before true q, r, ⟨rfl, hq⟩, hrun, hr⟩
  rw [ha]
  simp only [input, G.before_segment, Bool.true_and, G.middle_segment, G.after_segment]
  constructor
  · rintro ⟨q, hq, hb, hp, hm, ht⟩
    exact ⟨hb, ⟨q, hq, hp⟩, hm, ht⟩
  · rintro ⟨hb, ⟨q, hq, hp⟩, hm, ht⟩
    exact ⟨q, hq, hb, hp, hm, ht⟩

end Data
end NSSE.OutsideBlockController
