import NSSE.MultiConstructorBranchTrace

/-! Complete compiled paths are exactly the literal selected-head local
assignments, with terminal domains checked separately at the final row. -/
namespace NSSE.MultiConstructorBranchLocal
open MultiConstructorRawTrace MultiConstructorRawValidity MultiConstructorBranch
open MultiConstructorBranchTrace P0DZBranch
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

def EndValid (C : Parameters arity n) (t : Row n) : Prop :=
  Valid C.input t ∧ UpperDomain C.input t C.endX ∧
    LowerDomain C.input t C.endY ∧ C.endX ≠ C.endY

def LocalRun (C : Parameters arity n) (s : State n) : List (Fin D) → Prop
  | [] => False
  | [a] => StepGuard C s a.val ∧ EndValid C (step C.input s.1 a.val)
  | a::b::w => StepGuard C s a.val ∧ LocalRun C (successor C s a.val) (b::w)

theorem local_nonempty (C : Parameters arity n) (s : State n) (w : List (Fin D))
    (hl : LocalRun C s w) : w ≠ [] := by
  intro he
  subst w
  exact hl

theorem local_ready (C : Parameters arity n) (s : State n) (w : List (Fin D))
    (hl : LocalRun C s w) : Ready C s := by
  cases w with
  | nil => exact hl.elim
  | cons a w => cases w <;> exact hl.1.1

theorem finish_iff (C : Parameters arity n) (w : List (Fin D)) (s : State n) (t : Row n) :
    finishFrom (branch C D) s w = some t ↔ LocalRun C s w ∧ rawWord C s.1 w = t := by
  induction w generalizing s with
  | nil => simp [finishFrom,LocalRun]
  | cons a w ih =>
    cases w with
    | nil =>
      simpa only [finishFrom,LocalRun,ZGuard,EndValid,rawWord,List.foldl_cons,List.foldl_nil]
        using final_iff C D s t a
    | cons b w =>
      change ((branch C D).next s a).bind (fun q => finishFrom (branch C D) q (b::w)) = some t ↔ _
      constructor
      · intro he
        cases hn : (branch C D).next s a with
        | none => simp [hn] at he
        | some q =>
          have hf : finishFrom (branch C D) q (b::w) = some t := by simpa [hn] using he
          obtain ⟨hg,hq⟩ := (next_iff C D s q a).mp hn
          subst q
          obtain ⟨hl,ht⟩ := (ih _).mp hf
          exact ⟨⟨hg.1,hl⟩,ht⟩
      · rintro ⟨⟨hg,hl⟩,ht⟩
        have hn : (branch C D).next s a = some (successor C s a.val) :=
          (next_iff C D s _ a).mpr ⟨⟨hg,local_ready C _ _ hl⟩,rfl⟩
        rw [hn]
        exact (ih _).mpr ⟨hl,ht⟩

theorem complete_iff (C : Parameters arity n) (w : List (Fin D)) :
    Complete (branch C D) w ↔ LocalRun C (branch C D).initial w := by
  constructor
  · intro hc
    obtain ⟨t,ht⟩ := P0DZTrace.complete_terminal (branch C D) w hc
    exact ((finish_iff C w _ t).mp ht).1
  · intro hl
    have hf := (finish_iff C w (branch C D).initial _).mpr ⟨hl,rfl⟩
    change (finishFrom (branch C D) (branch C D).initial w).isSome = true
    rw [hf]
    rfl

def walk (C : Parameters arity n) (s : State n) (w : List (Fin D)) : State n :=
  w.foldl (fun s i => successor C s i.val) s

theorem proper_walk (C : Parameters arity n) (w : List (Fin D)) (s t : State n)
    (he : properFrom (branch C D) s w = some t) : t = walk C s w := by
  induction w generalizing s with
  | nil => exact (Option.some.inj he).symm
  | cons a w ih =>
    rw [proper_cons] at he
    cases hn : (branch C D).next s a with
    | none => simp [hn] at he
    | some q =>
      have hf : properFrom (branch C D) q w = some t := by simpa [hn] using he
      have hq := ((next_iff C D s q a).mp hn).2
      subst q
      exact ih _ hf

theorem local_end (C : Parameters arity n) (w : List (Fin D)) (s : State n)
    (hl : LocalRun C s w) : EndValid C (rawWord C s.1 w) := by
  induction w generalizing s with
  | nil => exact hl.elim
  | cons a w ih =>
    cases w with
    | nil => exact hl.2
    | cons b w => exact ih (successor C s a.val) hl.2

theorem local_guard (C : Parameters arity n) (w : List (Fin D)) (s : State n)
    (hl : LocalRun C s w) (k : Nat) (hk : k < w.length) :
    StepGuard C (walk C s (w.take k)) w[k].val := by
  induction w generalizing s k with
  | nil => simp at hk
  | cons a w ih =>
    cases k with
    | zero => cases w <;> exact hl.1
    | succ k =>
      cases w with
      | nil => simp at hk
      | cons b w => exact ih (successor C s a.val) hl.2 k (by simpa using hk)

theorem ends_distinct (C : Parameters arity n) (w : List (Fin D))
    (hc : Complete (branch C D) w) : C.endX ≠ C.endY :=
  (local_end C w _ ((complete_iff C w).mp hc)).2.2.2

theorem local_iff_pointwise (C : Parameters arity n) (w : List (Fin D)) (s : State n) :
    LocalRun C s w ↔ w ≠ [] ∧
      (∀ k, ∀ hk : k < w.length, StepGuard C (walk C s (w.take k)) w[k].val) ∧
      EndValid C (rawWord C s.1 w) := by
  constructor
  · intro hl
    exact ⟨local_nonempty C s w hl,local_guard C w s hl,local_end C w s hl⟩
  · induction w generalizing s with
    | nil => rintro ⟨h,_,_⟩; exact (h rfl).elim
    | cons a w ih =>
      rintro ⟨_,hg,he⟩
      cases w with
      | nil => exact ⟨hg 0 (by simp),he⟩
      | cons b w =>
        refine ⟨hg 0 (by simp),ih (successor C s a.val) ?_⟩
        refine ⟨by simp,?_,he⟩
        intro k hk
        exact hg (k+1) (by simpa using hk)

end NSSE.MultiConstructorBranchLocal
