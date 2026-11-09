import NSSE.MultiConstructorCommonWord
import NSSE.P0DZProperMachine

/-! Actual all-D paths project to the same raw/reset walk as accepted
words. Every reached noninitial D target satisfies the real proper guard. -/
namespace NSSE.MultiConstructorProperTrace
open MultiConstructorBranch MultiConstructorBranchLocal MultiConstructorUnifiedWords
open MultiConstructorUnifiedBranch MultiConstructorUnifiedPrefix MultiConstructorRawValidity
open P0DZBranch P0DZTrace P0DZVirtualTrace P0DZFirstClash
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

theorem state_walk (C : Parameters arity n) (w : List (Fin D))
    (hc : DComplete (branch C D) w) (k : Nat) :
    dState (branch C D) w k = walk C (branch C D).initial (w.take k) :=
  proper_walk C _ _ _ (proper_eq_state (branch C D) w hc k)

theorem d_guard (C : Parameters arity n) (w : List (Fin D))
    (hc : DComplete (branch C D) w) (k : Nat) (hk : k < w.length) :
    StepGuard C (walk C (branch C D).initial (w.take k)) w[k].val ∧
      Ready C (walk C (branch C D).initial (w.take (k+1))) := by
  obtain ⟨q,hq⟩ := d_succ (branch C D) w hc k hk _ (proper_eq_state (branch C D) w hc k)
  obtain ⟨hg,he⟩ := (next_iff C D _ _ _).mp hq
  rw [state_walk C w hc k] at hg
  have hw : walk C (branch C D).initial (w.take (k+1)) =
      successor C (walk C (branch C D).initial (w.take k)) w[k].val := by
    simp only [walk,List.take_succ_eq_append_getElem hk,List.foldl_append,List.foldl_cons,List.foldl_nil]
  exact ⟨hg.1,by rw [hw]; exact hg.2⟩

theorem terminal_ready (C : Parameters arity n) (w : List (Fin D))
    (hw : w ≠ []) (hc : DComplete (branch C D) w) :
    Ready C (walk C (branch C D).initial w) := by
  have hn := List.length_pos_iff.mpr hw
  have h := (d_guard C w hc (w.length-1) (by omega)).2
  simpa only [show w.length-1+1 = w.length by omega,List.take_length] using h

theorem local_assignment (C : Parameters arity n) (w : List (Fin D))
    (hc : DComplete (branch C D) w) :
    Local C.input C.left C.right w (selectedHeads C w) := by
  intro k
  have hg := (d_guard C w hc k.val k.isLt).1
  have he : (walk C (branch C D).initial (w.take k.val)).1 = row C.input C.left C.right w k.val :=
    walk_raw C _ _
  exact ⟨he ▸ hg.1.1,he ▸ hg.1.2.2,hg.2⟩

end NSSE.MultiConstructorProperTrace
