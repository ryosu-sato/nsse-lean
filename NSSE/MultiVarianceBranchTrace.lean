import NSSE.MultiVarianceBranchLocal

/-! Every complete signed D/Z branch has the actual raw frame at each
position, including its final Z identity. All physical-side births are
retained, with their roles read from the raw signs at their own origins. -/
namespace NSSE.MultiVarianceBranchTrace
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceBranch
open MultiVarianceBranchLocal P0DZBranch P0DZTrace
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}
variable (pol : Polarity arity)

theorem state_projection (C : Parameters arity n) (w : List (Fin D))
    (hc : Complete (branch pol C D) w) (k : Nat) (hk : k ≤ w.length) :
    ∃ q, stateAt (branch pol C D) w k = some q ∧
      raw q = (walk pol C (branch pol C D).initial (w.take k)).1 := by
  by_cases hl : k < w.length
  · obtain ⟨q,hq⟩ := complete_prefix (branch pol C D) w hc k hl
    refine ⟨.inl q,?_,?_⟩
    · rw [proper_state _ _ _ hl]
      change (properAt (branch pol C D) w k).map Sum.inl = some (.inl q)
      rw [hq]
      rfl
    · exact congrArg Prod.fst (proper_walk pol C (w.take k) (branch pol C D).initial q hq)
  · have he : k = w.length := by omega
    subst k
    obtain ⟨t,ht⟩ := complete_terminal (branch pol C D) w hc
    refine ⟨.inr t,?_,?_⟩
    · rw [terminal_state,ht]
      rfl
    · rw [List.take_length]
      exact ((finish_iff pol C w (branch pol C D).initial t).mp ht).2.symm

theorem bornAt_exact (C : Parameters arity n) (w : List (Fin D))
    (hc : Complete (branch pol C D) w) (a b : Nat) (ha : a ≤ w.length) (hb : b ≤ w.length)
    (s t : Bool) : bornAt (branch pol C D) w a s b t ↔
      RawBirth (walk pol C (branch pol C D).initial (w.take a)).1 s
        (walk pol C (branch pol C D).initial (w.take b)).1 t := by
  obtain ⟨q,hq,hqa⟩ := state_projection pol C w hc a ha
  obtain ⟨r,hr,hrb⟩ := state_projection pol C w hc b hb
  have hh : bornAt (branch pol C D) w a s b t ↔ (branch pol C D).birth q s r t := by
    simp only [bornAt,hq,hr,Option.some.injEq]
    constructor
    · rintro ⟨q',r',rfl,rfl,h⟩
      exact h
    · intro h
      exact ⟨q,r,rfl,rfl,h⟩
  rw [hh]
  change RawBirth (raw q) s (raw r) t ↔ _
  rw [hqa,hrb]

end NSSE.MultiVarianceBranchTrace
