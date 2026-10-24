import NSSE.SubtypeUpperExtension

/-! # Path conservation and ranked fresh paths in an upper extension -/

namespace NSSE.SubtypeUpperExtensionPaths

open SubtypeConstraints SubtypePathBounds SubtypeUpperExtension

variable {n d : Nat}
variable (φ : Constraints n d) (added : List (BoundLiteral n d))
variable (bots tops : List (Fin n)) (Base : Fin n → Prop)
variable (hc : Contained φ Base) (hf : FreshChildren added Base)
include hc hf

local notation "Ψ" => graft φ added bots tops

theorem lower_step_end_base {a b : Fin n} {i : Fin d} (h : SupportedLower Ψ a i b) : Base b := by
  obtain ⟨l,hl,hb,_⟩ := h
  change l ∈ φ.lower at hl
  by_contra hn
  exact no_fresh_base φ added bots tops Base hc hf hn ((hc.1 l hl).2 i) hb

theorem lower_step_from_base {a b : Fin n} {i : Fin d}
    (ha : Base a) (h : SupportedLower Ψ a i b) : Base b ∧ SupportedLower φ a i b := by
  have hb := lower_step_end_base φ added bots tops Base hc hf h
  obtain ⟨l,hl,hbl,hla⟩ := h
  change l ∈ φ.lower at hl
  exact ⟨hb,l,hl,
    (support_base_iff φ added bots tops Base hc hf hb ((hc.1 l hl).2 i)).mp hbl,
    (support_base_iff φ added bots tops Base hc hf (hc.1 l hl).1 ha).mp hla⟩

theorem upper_step_to_base {a b : Fin n} {i : Fin d}
    (hb : Base b) (h : SupportedUpper Ψ a i b) : Base a ∧ SupportedUpper φ a i b := by
  obtain ⟨l,hl,hal,hlb⟩ := h
  change l ∈ φ.upper ++ added at hl
  rcases List.mem_append.mp hl with hl | hl
  · have ha : Base a := by
      by_contra hn
      exact no_fresh_base φ added bots tops Base hc hf hn (hc.2 l hl).1 hal
    exact ⟨ha,l,hl,
      (support_base_iff φ added bots tops Base hc hf ha (hc.2 l hl).1).mp hal,
      (support_base_iff φ added bots tops Base hc hf ((hc.2 l hl).2 i) hb).mp hlb⟩
  · exact False.elim (no_fresh_base φ added bots tops Base hc hf (hf l hl i) hb hlb)

theorem lower_path_from_base (word : List (Fin d)) {a b : Fin n}
    (ha : Base a) (h : LowerPath Ψ a word b) : Base b ∧ LowerPath φ a word b := by
  induction word generalizing a b with
  | nil =>
      cases h with
      | nil hs =>
          have hb : Base b := by
            by_contra hn
            exact no_fresh_base φ added bots tops Base hc hf hn ha hs
          exact ⟨hb,.nil ((support_base_iff φ added bots tops Base hc hf hb ha).mp hs)⟩
  | cons i word ih =>
      cases h with
      | cons hs ht =>
          obtain ⟨hm,hmstep⟩ := lower_step_from_base φ added bots tops Base hc hf ha hs
          obtain ⟨hb,hp⟩ := ih hm ht
          exact ⟨hb,.cons hmstep hp⟩

theorem upper_path_to_base (word : List (Fin d)) {a b : Fin n}
    (hb : Base b) (h : UpperPath Ψ a word b) : Base a ∧ UpperPath φ a word b := by
  induction word generalizing a b with
  | nil =>
      cases h with
      | nil hs =>
          have ha : Base a := by
            by_contra hn
            exact no_fresh_base φ added bots tops Base hc hf hn hb hs
          exact ⟨ha,.nil ((support_base_iff φ added bots tops Base hc hf ha hb).mp hs)⟩
  | cons i word ih =>
      cases h with
      | cons hs ht =>
          obtain ⟨hm,hp⟩ := ih hb ht
          obtain ⟨ha,hmstep⟩ := upper_step_to_base φ added bots tops Base hc hf hm hs
          exact ⟨ha,.cons hmstep hp⟩

omit hc hf in
theorem upper_path_lift {a b : Fin n} {word : List (Fin d)} (h : UpperPath φ a word b) :
    UpperPath Ψ a word b := by
  apply upper_path_map φ Ψ id ?_ ?_ h
  · intro l hl; exact hl
  · intro l hl; exact List.mem_append_left _ hl

theorem lower_path_base_iff {a b : Fin n} (ha : Base a) (word : List (Fin d)) :
    LowerPath Ψ a word b ↔ LowerPath φ a word b :=
  ⟨fun h => (lower_path_from_base φ added bots tops Base hc hf word ha h).2,
    lower_path_lift φ added bots tops⟩

theorem upper_path_base_iff {a b : Fin n} (hb : Base b) (word : List (Fin d)) :
    UpperPath Ψ a word b ↔ UpperPath φ a word b :=
  ⟨fun h => (upper_path_to_base φ added bots tops Base hc hf word hb h).2,
    upper_path_lift φ added bots tops⟩

theorem lower_nonempty_end_base {a b : Fin n} {word : List (Fin d)}
    (hne : word ≠ []) (h : LowerPath Ψ a word b) : Base b := by
  cases h with
  | nil _ => exact False.elim (hne rfl)
  | cons hs ht =>
      exact (lower_path_from_base φ added bots tops Base hc hf _
        (lower_step_end_base φ added bots tops Base hc hf hs) ht).1

theorem fresh_upper_step {a b : Fin n} {i : Fin d} (ha : ¬ Base a)
    (h : SupportedUpper Ψ a i b) :
    ¬ Base b ∧ ∃ l ∈ added, l.1 = a ∧ l.2 i = b := by
  obtain ⟨l,hl,hal,hlb⟩ := h
  change l ∈ φ.upper ++ added at hl
  rcases List.mem_append.mp hl with hl | hl
  · exact False.elim (no_fresh_base φ added bots tops Base hc hf ha (hc.2 l hl).1 hal)
  · have hparent : ¬ Base l.1 := by
      intro hb
      exact no_fresh_base φ added bots tops Base hc hf ha hb hal
    have hb : ¬ Base b := by
      intro hb
      exact no_fresh_base φ added bots tops Base hc hf (hf l hl i) hb hlb
    exact ⟨hb,l,hl,(support_fresh_iff φ added bots tops Base hc hf ha hparent).mp hal |>.symm,
      (support_fresh_iff φ added bots tops Base hc hf (hf l hl i) hb).mp hlb⟩

/-- A fresh upper trace consists of literal added edges, so a rank on
those edges bounds the ACTUAL word length. -/
theorem fresh_upper_rank (μ : Fin n → Nat)
    (hinc : ∀ l ∈ added, ∀ i, μ l.1 < μ (l.2 i))
    (word : List (Fin d)) {a b : Fin n} (ha : ¬ Base a) (h : UpperPath Ψ a word b) :
    ¬ Base b ∧ μ a + word.length ≤ μ b := by
  induction word generalizing a b with
  | nil =>
      cases h with
      | nil hs =>
          have hb : ¬ Base b := fun hb => no_fresh_base φ added bots tops Base hc hf ha hb hs
          obtain rfl := (support_fresh_iff φ added bots tops Base hc hf ha hb).mp hs
          exact ⟨ha,by simp⟩
  | cons i word ih =>
      cases h with
      | cons hs ht =>
          obtain ⟨hm,l,hl,hp,hchild⟩ := fresh_upper_step φ added bots tops Base hc hf ha hs
          obtain ⟨hb,hh⟩ := ih hm ht
          have hi := hinc l hl i
          rw [hp,hchild] at hi
          refine ⟨hb,?_⟩
          simp only [List.length_cons]
          omega

end NSSE.SubtypeUpperExtensionPaths
