import NSSE.SubtypeCycleClashes
import NSSE.SubtypeLowerGraftSuffix
import NSSE.SubtypeUpperExtensionPaths

/-! # Ranked one-sided additions preserve the actual two-variable C4

Fresh same-direction paths are literal walks increasing rank. Nonempty
opposite-direction paths cannot end fresh. Both cycle variables are old.
-/

namespace NSSE.SubtypeGraftCycles

open SubtypeConstraints SubtypeConstraintOperations SubtypePathBounds SubtypeCycleClashes

variable {n m d : Nat}

theorem added_walk_rank (added : List (BoundLiteral (n + m) d)) (μ : Fin (n + m) → Nat)
    (hinc : ∀ l ∈ added, ∀ i, μ l.1 < μ (l.2 i))
    {u v word} (h : SubtypeLowerGraftSuffix.AddedWalk added u word v) :
    μ (Fin.natAdd n u) + word.length ≤ μ (Fin.natAdd n v) := by
  induction h with
  | nil u => simp
  | @cons l u v z i word hl hp hchild _ ih =>
      have hi := hinc l hl i
      rw [hp,hchild] at hi
      simp only [List.length_cons]
      omega

theorem no_lower_fresh_self (φ : Constraints n d) (added : List (BoundLiteral (n + m) d))
    (bots tops : List (Fin (n + m))) (hc : SubtypeLowerGraft.FreshChildren added)
    (μ : Fin (n + m) → Nat) (hinc : ∀ l ∈ added, ∀ i, μ l.1 < μ (l.2 i))
    (word : List (Fin d)) (hne : word ≠ []) (u : Fin m) :
    ¬ LowerPath (SubtypeLowerGraft.graft φ added bots tops) (Fin.natAdd n u) word (Fin.natAdd n u) := by
  intro h
  have hw := (SubtypeLowerGraftSuffix.fresh_path_iff φ added bots tops hc u u word).mp h
  have hh := added_walk_rank added μ hinc hw
  have hp := List.length_pos_iff.mpr hne
  omega

theorem no_upper_nonempty_fresh (φ : Constraints n d) (added : List (BoundLiteral (n + m) d))
    (bots tops : List (Fin (n + m))) (hc : SubtypeLowerGraft.FreshChildren added)
    (word : List (Fin d)) (hne : word ≠ []) (a : Fin (n + m)) (u : Fin m) :
    ¬ UpperPath (SubtypeLowerGraft.graft φ added bots tops) a word (Fin.natAdd n u) := by
  intro h
  cases h with
  | nil _ => exact hne rfl
  | cons hs ht =>
      obtain ⟨l,hl,_,hchild⟩ := hs
      change l ∈ φ.upper.map (renameBound (Fin.castAdd m)) at hl
      obtain ⟨l₀,_,rfl⟩ := List.mem_map.mp hl
      have hp := upper_pre (SubtypeLowerGraft.graft φ added bots tops) hchild ht
      obtain ⟨y,hy,_⟩ := SubtypeLowerGraftPaths.upper_path_from_old φ added bots tops hc _ (l₀.2 _) _ hp
      have hv := congrArg (fun z : Fin (n + m) => z.val) hy
      change n + u.val = y.val at hv
      have := y.isLt
      omega

theorem lower_cycle_iff (φ : Constraints n d) (added : List (BoundLiteral (n + m) d))
    (bots tops : List (Fin (n + m))) (hc : SubtypeLowerGraft.FreshChildren added)
    (μ : Fin (n + m) → Nat) (hinc : ∀ l ∈ added, ∀ i, μ l.1 < μ (l.2 i)) :
    CycleClash (SubtypeLowerGraft.graft φ added bots tops) ↔ CycleClash φ := by
  constructor
  · rintro ⟨a,b,word,hne,hs,hl,hu⟩
    induction a using Fin.addCases with
    | left a =>
        induction b using Fin.addCases with
        | left b =>
            exact ⟨a,b,word,hne,
              (SubtypeLowerGraft.support_old_iff φ added bots tops hc a b).mp hs,
              (SubtypeLowerGraftPaths.lower_path_old_iff φ added bots tops hc a a word).mp hl,
              (SubtypeLowerGraftPaths.upper_path_old_iff φ added bots tops hc b b word).mp hu⟩
        | right b => exact False.elim (no_upper_nonempty_fresh φ added bots tops hc word hne _ b hu)
    | right a => exact False.elim (no_lower_fresh_self φ added bots tops hc μ hinc word hne a hl)
  · rintro ⟨a,b,word,hne,hs,hl,hu⟩
    exact ⟨Fin.castAdd m a,Fin.castAdd m b,word,hne,
      (SubtypeLowerGraft.support_old_iff φ added bots tops hc a b).mpr hs,
      (SubtypeLowerGraftPaths.lower_path_old_iff φ added bots tops hc a a word).mpr hl,
      (SubtypeLowerGraftPaths.upper_path_old_iff φ added bots tops hc b b word).mpr hu⟩

theorem upper_cycle_iff (φ : Constraints n d) (added : List (BoundLiteral n d))
    (bots tops : List (Fin n)) (Base : Fin n → Prop)
    (hc : SubtypeUpperExtension.Contained φ Base)
    (hf : SubtypeUpperExtension.FreshChildren added Base)
    (μ : Fin n → Nat) (hinc : ∀ l ∈ added, ∀ i, μ l.1 < μ (l.2 i)) :
    CycleClash (SubtypeUpperExtension.graft φ added bots tops) ↔ CycleClash φ := by
  constructor
  · rintro ⟨a,b,word,hne,hs,hl,hu⟩
    have ha := SubtypeUpperExtensionPaths.lower_nonempty_end_base φ added bots tops Base hc hf hne hl
    have hb : Base b := by
      by_contra hn
      have hh := (SubtypeUpperExtensionPaths.fresh_upper_rank φ added bots tops Base hc hf μ hinc word hn hu).2
      have hp := List.length_pos_iff.mpr hne
      omega
    exact ⟨a,b,word,hne,
      (SubtypeUpperExtension.support_base_iff φ added bots tops Base hc hf ha hb).mp hs,
      (SubtypeUpperExtensionPaths.lower_path_base_iff φ added bots tops Base hc hf ha word).mp hl,
      (SubtypeUpperExtensionPaths.upper_path_base_iff φ added bots tops Base hc hf hb word).mp hu⟩
  · rintro ⟨a,b,word,hne,hs,hl,hu⟩
    exact ⟨a,b,word,hne,
      SubtypeUpperExtension.support_lift φ added bots tops hs,
      SubtypeUpperExtension.lower_path_lift φ added bots tops hl,
      SubtypeUpperExtensionPaths.upper_path_lift φ added bots tops hu⟩

end NSSE.SubtypeGraftCycles
