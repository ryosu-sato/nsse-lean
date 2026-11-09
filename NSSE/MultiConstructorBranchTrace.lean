import NSSE.MultiConstructorBranch

/-! The raw component of every complete compiled branch is the actual
original token fold, including the separately checked final Z state. -/
namespace NSSE.MultiConstructorBranchTrace
open MultiConstructorConstraints MultiConstructorTokens MultiConstructorRawTrace
open MultiConstructorBranch P0DZBranch P0DZTrace
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

def rawWord (C : Parameters arity n) (s : Row n) (w : List (Fin D)) : Row n :=
  w.foldl (fun s i => step C.input s i.val) s

theorem rawWord_cons (C : Parameters arity n) (s : Row n) (a : Fin D) (w : List (Fin D)) :
    rawWord C s (a::w) = rawWord C (step C.input s a.val) w := rfl

theorem rawWord_closed (C : Parameters arity n) (s : Row n) (w : List (Fin D))
    (hs : UpperClosed C.input s.1 ∧ LowerClosed C.input s.2) :
    UpperClosed C.input (rawWord C s w).1 ∧ LowerClosed C.input (rawWord C s w).2 := by
  induction w generalizing s with
  | nil => exact hs
  | cons a w ih => exact ih _ ⟨upperNext_closed _ _ _,lowerNext_closed _ _ _⟩

theorem proper_projection (C : Parameters arity n) (w : List (Fin D)) (s t : State n)
    (he : properFrom (branch C D) s w = some t) : t.1 = rawWord C s.1 w := by
  induction w generalizing s with
  | nil =>
    have heq : s = t := Option.some.inj he
    subst s
    rfl
  | cons a w ih =>
    rw [proper_cons] at he
    cases hn : (branch C D).next s a with
    | none => simp [hn] at he
    | some q =>
      have ht : properFrom (branch C D) q w = some t := by simpa [hn] using he
      rw [rawWord_cons,← MultiConstructorBranch.next_raw C D s q a hn]
      exact ih q ht

theorem finish_projection (C : Parameters arity n) (w : List (Fin D)) (s : State n) (t : Row n)
    (he : finishFrom (branch C D) s w = some t) : t = rawWord C s.1 w := by
  induction w generalizing s with
  | nil => cases he
  | cons a w ih =>
    cases w with
    | nil => exact final_raw C D s t a he
    | cons b w =>
      change ((branch C D).next s a).bind (fun q => finishFrom (branch C D) q (b::w)) = some t at he
      cases hn : (branch C D).next s a with
      | none => simp [hn] at he
      | some q =>
        have ht : finishFrom (branch C D) q (b::w) = some t := by simpa [hn] using he
        rw [rawWord_cons,← MultiConstructorBranch.next_raw C D s q a hn]
        exact ih q ht

theorem state_projection (C : Parameters arity n) (w : List (Fin D))
    (hc : Complete (branch C D) w) (k : Nat) (hk : k ≤ w.length) :
    ∃ q, stateAt (branch C D) w k = some q ∧
      raw q = rawWord C (initial C.input C.left C.right) (w.take k) := by
  by_cases hl : k < w.length
  · obtain ⟨q,hq⟩ := complete_prefix (branch C D) w hc k hl
    refine ⟨.inl q,?_,?_⟩
    · rw [proper_state _ _ _ hl]
      change (properAt (branch C D) w k).map Sum.inl = some (.inl q)
      rw [hq]
      rfl
    · exact proper_projection C (w.take k) (branch C D).initial q hq
  · have he : k = w.length := by omega
    subst k
    obtain ⟨t,ht⟩ := complete_terminal (branch C D) w hc
    refine ⟨.inr t,?_,?_⟩
    · rw [terminal_state,ht]
      rfl
    · rw [List.take_length]
      exact finish_projection C w (branch C D).initial t ht

theorem bornAt_exact (C : Parameters arity n) (w : List (Fin D))
    (hc : Complete (branch C D) w) (a b : Nat) (ha : a ≤ w.length) (hb : b ≤ w.length) :
    bornAt (branch C D) w a false b true ↔
      ∃ u ∈ (rawWord C (initial C.input C.left C.right) (w.take a)).1,
      ∃ v ∈ (rawWord C (initial C.input C.left C.right) (w.take b)).2, Support C.input u v := by
  obtain ⟨q,hq,hqa⟩ := state_projection C w hc a ha
  obtain ⟨t,ht,htb⟩ := state_projection C w hc b hb
  have hclosed := (rawWord_closed C (initial C.input C.left C.right) (w.take a)
    ⟨up_closed _ _,down_closed _ _⟩).1
  have hborn : bornAt (branch C D) w a false b true ↔ (branch C D).birth q false t true := by
    simp only [bornAt,hq,ht,Option.some.injEq]
    constructor
    · rintro ⟨q',t',rfl,rfl,h⟩
      exact h
    · intro h
      exact ⟨q,t,rfl,rfl,h⟩
  rw [hborn,branch_birth,hqa,htb,birth_iff_inter C.input _ _ hclosed]
  simp only [Finset.Nonempty,Finset.mem_inter]

end NSSE.MultiConstructorBranchTrace
