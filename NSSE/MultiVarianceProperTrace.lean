import NSSE.MultiVarianceBranchAssignment
import NSSE.P0DZProperMachine

/-! Actual signed all-D traces, including the virtual proper terminal.
Full Good retains all physical rail pairs and both support directions. -/
namespace NSSE.MultiVarianceProperTrace
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceBranch MultiVarianceBranchLocal
open P0DZBranch P0DZTrace P0DZVirtualTrace P0DZFirstClash P0ProperWords
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}
variable (pol : Polarity arity)

def rawAt (C : Parameters arity n) (w : List (Fin D)) (k : Nat) : Frame n :=
  (walk pol C (branch pol C D).initial (w.take k)).1

def headAt (C : Parameters arity n) (w : List (Fin D)) (k : Nat) : H :=
  output C (walk pol C (branch pol C D).initial (w.take k))

theorem state_walk (C : Parameters arity n) (w : List (Fin D))
    (hc : DComplete (branch pol C D) w) (k : Nat) :
    dState (branch pol C D) w k=walk pol C (branch pol C D).initial (w.take k) :=
  proper_walk pol C _ _ _ (proper_eq_state (branch pol C D) w hc k)

theorem d_guard (C : Parameters arity n) (w : List (Fin D))
    (hc : DComplete (branch pol C D) w) (k : Nat) (hk : k<w.length) :
    StepGuard C (walk pol C (branch pol C D).initial (w.take k)) w[k].val ∧
      Ready C (walk pol C (branch pol C D).initial (w.take (k+1))) := by
  obtain ⟨q,hq⟩ := d_succ (branch pol C D) w hc k hk _ (proper_eq_state (branch pol C D) w hc k)
  obtain ⟨hg,_⟩ := (next_iff pol C D _ _ _).mp hq
  rw [state_walk pol C w hc k] at hg
  have hw : walk pol C (branch pol C D).initial (w.take (k+1)) =
      successor pol C (walk pol C (branch pol C D).initial (w.take k)) w[k].val := by
    simp only [walk,List.take_succ_eq_append_getElem hk,List.foldl_append,List.foldl_cons,List.foldl_nil]
  exact ⟨hg.1,by rw [hw]; exact hg.2⟩

theorem terminal_ready (C : Parameters arity n) (w : List (Fin D))
    (hw : w≠[]) (hc : DComplete (branch pol C D) w) :
    Ready C (walk pol C (branch pol C D).initial w) := by
  have hn := List.length_pos_iff.mpr hw
  have h := (d_guard pol C w hc (w.length-1) (by omega)).2
  simpa only [show w.length-1+1=w.length by omega,List.take_length] using h

def properBirthDecision (C : Parameters arity n) (D : Nat) :
    DecidableRel (P0DZProperMachine.machine (branch pol C D)).birth := by
  letI := birthDecision pol C D
  intro q r
  cases q <;> cases r <;> dsimp only [P0DZProperMachine.machine]
  · infer_instance
  · infer_instance
  · infer_instance
  · unfold P0DZFirstClash.Born
    infer_instance

def SymBirth (F : Frame n) (s : Bool) (G : Frame n) (t : Bool) : Prop :=
  RawBirth F s G t ∨ RawBirth G t F s

theorem symBirth_symm (F : Frame n) (s : Bool) (G : Frame n) (t : Bool) :
    SymBirth F s G t ↔ SymBirth G t F s := or_comm

theorem no_same_vertex_symBirth (F : Frame n) (s : Bool) : ¬SymBirth F s F s := by
  rintro (h | h) <;> exact no_same_vertex_birth F s h

theorem head_match (C : Parameters arity n) (w : List (Fin D))
    (hg : GoodWord (P0DZProperMachine.machine (branch pol C D)) w)
    (a b l : Nat) (s t : Bool) (hal : a+l≤w.length) (hbl : b+l≤w.length)
    (hb : SymBirth (rawAt pol C w a) s (rawAt pol C w b) t)
    (hm : WordMatch w a b l) : headAt pol C w (a+l)=headAt pol C w (b+l) := by
  have hc := ((P0DZProperMachine.good_iff (branch pol C D) w).mp hg).1
  have hborn : Born (branch pol C D) (dState (branch pol C D) w a) (dState (branch pol C D) w b) := by
    rw [state_walk pol C w hc a,state_walk pol C w hc b]
    rcases hb with hb | hb
    · exact Or.inl ⟨s,t,hb⟩
    · exact Or.inr ⟨t,s,hb⟩
  have he := hg.2 a (by omega) b (by omega) l (by omega) hal hbl
    ((P0DZProperMachine.birth_exact (branch pol C D) w hc a b).mpr hborn) hm
  rw [P0DZProperMachine.head_exact,P0DZProperMachine.head_exact,
    state_walk pol C w hc (a+l),state_walk pol C w hc (b+l)] at he
  exact he

end NSSE.MultiVarianceProperTrace
