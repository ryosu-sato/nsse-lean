import NSSE.PathBoundsToAutomaton

/-! # Actual forward acceptance certificates from original path bounds

All empty-anchor/root cases retain the real initial state and Support.
Positive roots return by the literal P-edge to a proved FINAL target.
-/

namespace NSSE.ForwardPeriodicCertificate

open SubtypeConstraints SubtypePathBounds ForwardTableAutomaton ConstraintForwardTables
open PathBoundsToAutomaton

variable {n d : Nat}

theorem raw_ordinary (Q : Query n d) (side : Side) {word : List (Fin d)} {q : State n}
    (hr : (rawNFA (tables Q) side).Runs (some (some Q.left,some Q.right)) word q)
    (hf : final (tables Q) side q) : ForwardCapAutomaton.Accepts (automaton Q side) word := by
  apply Or.inl
  refine ⟨_,stateEquiv n q,rfl,encode_run (tables Q) side hr,?_⟩
  change final (tables Q) side ((stateEquiv n).symm (stateEquiv n q))
  simpa only [Equiv.symm_apply_apply] using hf

theorem raw_capped (Q : Query n d) (side : Side) {word anchor tail root : List (Fin d)}
    {q source : State n} {power : Nat} (he : word = anchor ++ tail)
    (ha : (rawNFA (tables Q) side).Runs (some (some Q.left,some Q.right)) anchor q)
    (hf : final (tables Q) side q) (hr : (rawNFA (tables Q) side).Runs q root source)
    (hp : pedge side source q) (ht : tail <+: Language.wordPower root power) :
    ForwardCapAutomaton.Accepts (automaton Q side) word := by
  apply Or.inr
  refine ⟨anchor,tail,stateEquiv n q,stateEquiv n source,root,power,he,
    encode_run (tables Q) side ha,?_,encode_run (tables Q) side hr,?_,ht⟩
  · change final (tables Q) side ((stateEquiv n).symm (stateEquiv n q))
    simpa only [Equiv.symm_apply_apply] using hf
  · change pedge side ((stateEquiv n).symm (stateEquiv n source))
      ((stateEquiv n).symm (stateEquiv n q))
    simpa only [Equiv.symm_apply_apply] using hp

theorem raw_escape_prefix (Q : Query n d) (side : Side) {anchor word : List (Fin d)}
    (u v : Token n)
    (hr : (rawNFA (tables Q) side).Runs (some (some Q.left,some Q.right)) anchor (some (u,v)))
    (he : escape (tables Q) u v) (hp : anchor <+: word) :
    ForwardCapAutomaton.Accepts (automaton Q side) word := by
  obtain ⟨tail,rfl⟩ := hp
  obtain ⟨q,ht,hf⟩ := escape_universal (tables Q) side u v he tail
  exact raw_ordinary Q side (NFA.Runs.append _ hr ht) hf

theorem lower_path_final (Q : Query n d) {v z : Fin n} {word : List (Fin d)}
    (h : LowerPath Q.constraints v word z) (hne : word ≠ []) (u : Token n) :
    final (tables Q) .right (some (u,some v)) := by
  cases h with
  | nil _ => exact False.elim (hne rfl)
  | @cons _ a _ i _ hs _ =>
      exact Or.inr ⟨i,some a,(lower_correct Q _ _ _).mpr hs⟩

/-- The original path-bound periodic form supplies an actual acceptance
certificate, including epsilon anchor, epsilon difference, and every power. -/
theorem periodic_accepts (Q : Query n d) (word a s : List (Fin d)) (z : Fin n)
    (ha : a <+: word) (hu : UpperPath Q.constraints Q.left a z)
    (hl : LowerPath Q.constraints Q.right (a ++ s) z)
    (hper : s = [] ∨ ∃ power, word <+: a ++ Language.wordPower s power) :
    ForwardCapAutomaton.Accepts (automaton Q .right) word := by
  by_cases hs : s = []
  · subst s
    simp only [List.append_nil] at hl
    by_cases hae : a = []
    · subst a
      cases hu with
      | nil hx =>
          cases hl with
          | nil hy =>
              exact raw_escape_prefix Q .right (some Q.left) (some Q.right) (.nil _)
                (Or.inr (Or.inr ⟨Q.left,Q.right,rfl,rfl,(le_correct Q _ _).mpr (hx.trans hy)⟩)) ha
    · exact raw_escape_prefix Q .right (some z) (some z) (pair_raw Q .right hu hl hae)
        (Or.inr (Or.inr ⟨z,z,rfl,rfl,(le_correct Q _ _).mpr (.refl _)⟩)) ha
  · obtain ⟨power,hpow⟩ := hper.resolve_left hs
    obtain ⟨tail,rfl⟩ := ha
    have ht := (List.prefix_append_right_inj a).mp hpow
    by_cases hae : a = []
    · subst a
      simp only [List.nil_append] at hl ⊢
      cases hu with
      | nil hx =>
          have hl' := lower_post Q.constraints hl hx
          exact raw_capped Q .right (anchor := []) rfl (.nil _)
            (lower_path_final Q hl' hs (some Q.left))
            (lower_raw Q .right hl' hs (some Q.left)) rfl ht
    · obtain ⟨v,hla,hls⟩ := lower_split Q.constraints a hl
      exact raw_capped Q .right rfl (pair_raw Q .right hu hla hae)
        (lower_path_final Q hls hs (some z)) (lower_raw Q .right hls hs (some z)) rfl ht

theorem upper_bottom_accepts (Q : Query n d) (side : Side) {a word : List (Fin d)}
    {b : Fin n} (hu : UpperPath Q.constraints Q.left a b) (hb : b ∈ Q.constraints.bot)
    (ha : a <+: word) : ForwardCapAutomaton.Accepts (automaton Q side) word := by
  by_cases hae : a = []
  · subst a
    cases hu with
    | nil hs =>
        exact raw_escape_prefix Q side (some Q.left) (some Q.right) (.nil _)
          (Or.inl ⟨Q.left,rfl,(bot_correct Q _).mpr ⟨b,hb,hs⟩⟩) ha
  · exact raw_escape_prefix Q side (some b) none (upper_raw Q side hu hae (some Q.right))
      (Or.inl ⟨b,rfl,(bot_correct Q _).mpr ⟨b,hb,.refl _⟩⟩) ha

theorem lower_top_accepts (Q : Query n d) (side : Side) {a word : List (Fin d)}
    {b : Fin n} (hl : LowerPath Q.constraints Q.right a b) (hb : b ∈ Q.constraints.top)
    (ha : a <+: word) : ForwardCapAutomaton.Accepts (automaton Q side) word := by
  by_cases hae : a = []
  · subst a
    cases hl with
    | nil hs =>
        exact raw_escape_prefix Q side (some Q.left) (some Q.right) (.nil _)
          (Or.inr (Or.inl ⟨Q.right,rfl,(top_correct Q _).mpr ⟨b,hb,hs⟩⟩)) ha
  · exact raw_escape_prefix Q side none (some b) (lower_raw Q side hl hae (some Q.left))
      (Or.inr (Or.inl ⟨b,rfl,(top_correct Q _).mpr ⟨b,hb,.refl _⟩⟩)) ha

theorem lower_literal_final (Q : Query n d) (hd : 0 < d) (v : Fin n) (u : Token n)
    (l : BoundLiteral n d) (hl : l ∈ Q.constraints.lower) (hs : Support Q.constraints l.1 v) :
    final (tables Q) .right (some (u,some v)) := by
  let i : Fin d := ⟨0,hd⟩
  exact Or.inr ⟨i,some (l.2 i),(lower_correct Q _ _ _).mpr ⟨l,hl,.refl _,hs⟩⟩

theorem lower_node_accepts (Q : Query n d) (hd : 0 < d) (word : List (Fin d))
    (h : ∃ l ∈ Q.constraints.lower, LowerPath Q.constraints Q.right word l.1) :
    ForwardCapAutomaton.Accepts (automaton Q .right) word := by
  obtain ⟨l,hl,hp⟩ := h
  by_cases hw : word = []
  · subst word
    cases hp with
    | nil hs =>
        exact raw_ordinary Q .right (.nil _)
          (lower_literal_final Q hd Q.right (some Q.left) l hl hs)
  · exact raw_ordinary Q .right (lower_raw Q .right hp hw (some Q.left))
      (lower_literal_final Q hd l.1 none l hl (.refl _))

end NSSE.ForwardPeriodicCertificate
