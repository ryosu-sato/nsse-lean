import NSSE.MultiVarianceBranch

/-! Actual D/Z completion is exactly the selected-head local run. The
unconditional walk retains both frames; its final raw projection is the
actual Z identity, independently of the final selector's readiness. -/
namespace NSSE.MultiVarianceBranchLocal
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceBranch
open P0DZBranch P0DZTrace
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}
variable (pol : Polarity arity)

def walk (C : Parameters arity n) (s : State n) (w : List (Fin D)) : State n :=
  w.foldl (fun t i => successor pol C t i.val) s

def LocalRun (C : Parameters arity n) (s : State n) : List (Fin D) → Prop
  | [] => False
  | [a] => StepGuard C s a.val ∧ EndValid C (successor pol C s a.val).1
  | a::b::w => StepGuard C s a.val ∧ LocalRun C (successor pol C s a.val) (b::w)

theorem local_nonempty (C : Parameters arity n) (s : State n) (w : List (Fin D))
    (hl : LocalRun pol C s w) : w ≠ [] := by
  intro he
  subst w
  exact hl

theorem local_ready (C : Parameters arity n) (s : State n) (w : List (Fin D))
    (hl : LocalRun pol C s w) : Ready C s := by
  cases w with
  | nil => exact hl.elim
  | cons a w => cases w <;> exact hl.1.1

theorem finish_iff (C : Parameters arity n) (w : List (Fin D)) (s : State n) (t : Frame n) :
    finishFrom (branch pol C D) s w=some t ↔ LocalRun pol C s w ∧ (walk pol C s w).1=t := by
  induction w generalizing s with
  | nil => simp [finishFrom,LocalRun]
  | cons a w ih =>
    cases w with
    | nil =>
      simpa only [finishFrom,LocalRun,ZGuard,walk,List.foldl_cons,List.foldl_nil]
        using final_iff pol C D s t a
    | cons b w =>
      change ((branch pol C D).next s a).bind (fun q => finishFrom (branch pol C D) q (b::w))=some t ↔ _
      constructor
      · intro he
        cases hn : (branch pol C D).next s a with
        | none => simp [hn] at he
        | some q =>
          have hf : finishFrom (branch pol C D) q (b::w)=some t := by simpa [hn] using he
          obtain ⟨hg,hq⟩ := (next_iff pol C D s q a).mp hn
          subst q
          obtain ⟨hl,ht⟩ := (ih _).mp hf
          exact ⟨⟨hg.1,hl⟩,ht⟩
      · rintro ⟨⟨hg,hl⟩,ht⟩
        have hn : (branch pol C D).next s a=some (successor pol C s a.val) :=
          (next_iff pol C D s _ a).mpr ⟨⟨hg,local_ready pol C _ _ hl⟩,rfl⟩
        rw [hn]
        exact (ih _).mpr ⟨hl,ht⟩

theorem complete_iff (C : Parameters arity n) (w : List (Fin D)) :
    Complete (branch pol C D) w ↔ LocalRun pol C (branch pol C D).initial w := by
  constructor
  · intro hc
    obtain ⟨t,ht⟩ := complete_terminal (branch pol C D) w hc
    exact ((finish_iff pol C w _ t).mp ht).1
  · intro hl
    have hf := (finish_iff pol C w (branch pol C D).initial _).mpr ⟨hl,rfl⟩
    change (finishFrom (branch pol C D) (branch pol C D).initial w).isSome=true
    rw [hf]
    rfl

theorem proper_walk (C : Parameters arity n) (w : List (Fin D)) (s t : State n)
    (he : properFrom (branch pol C D) s w=some t) : t=walk pol C s w := by
  induction w generalizing s with
  | nil => exact (Option.some.inj he).symm
  | cons a w ih =>
    rw [proper_cons] at he
    cases hn : (branch pol C D).next s a with
    | none => simp [hn] at he
    | some q =>
      have hf : properFrom (branch pol C D) q w=some t := by simpa [hn] using he
      have hq := ((next_iff pol C D s q a).mp hn).2
      subst q
      exact ih _ hf

theorem local_end (C : Parameters arity n) (w : List (Fin D)) (s : State n)
    (hl : LocalRun pol C s w) : EndValid C (walk pol C s w).1 := by
  induction w generalizing s with
  | nil => exact hl.elim
  | cons a w ih =>
    cases w with
    | nil => exact hl.2
    | cons b w => exact ih (successor pol C s a.val) hl.2

theorem local_guard (C : Parameters arity n) (w : List (Fin D)) (s : State n)
    (hl : LocalRun pol C s w) (k : Nat) (hk : k<w.length) :
    StepGuard C (walk pol C s (w.take k)) w[k].val := by
  induction w generalizing s k with
  | nil => simp at hk
  | cons a w ih =>
    cases k with
    | zero => cases w <;> exact hl.1
    | succ k =>
      cases w with
      | nil => simp at hk
      | cons b w => exact ih (successor pol C s a.val) hl.2 k (by simpa using hk)

theorem local_iff_pointwise (C : Parameters arity n) (w : List (Fin D)) (s : State n) :
    LocalRun pol C s w ↔ w ≠ [] ∧
      (∀ k, ∀ hk : k<w.length, StepGuard C (walk pol C s (w.take k)) w[k].val) ∧
      EndValid C (walk pol C s w).1 := by
  constructor
  · intro hl
    exact ⟨local_nonempty pol C s w hl,local_guard pol C w s hl,local_end pol C w s hl⟩
  · induction w generalizing s with
    | nil => rintro ⟨h,_,_⟩; exact (h rfl).elim
    | cons a w ih =>
      rintro ⟨_,hg,he⟩
      cases w with
      | nil => exact ⟨hg 0 (by simp),he⟩
      | cons b w =>
        refine ⟨hg 0 (by simp),ih (successor pol C s a.val) ?_⟩
        exact ⟨by simp,(fun k hk => hg (k+1) (by simpa using hk)),he⟩

end NSSE.MultiVarianceBranchLocal
