import NSSE.MultiVarianceStreamIncidence
import NSSE.P0PeriodicMonitorInvariant

/-! A selected-side permanent-ray monitor shares the actual full-Good
control but keeps a DIFFERENT birth relation. Only full-to-selected
safety is asserted; all four rail pairs remain in the full machine. -/
namespace NSSE.MultiVarianceSelectedMachine
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceBranch MultiVarianceProperTrace
open MultiVarianceStreamTrace MultiVarianceStreamIncidence
open P0ProperMachine P0ProperWords
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}
variable (pol : Polarity arity)

def selectedBirth (side : Bool) : Option (State n) → Option (State n) → Prop
  | some q, some r => ∃ other, SymBirth q.1 other r.1 side
  | _, _ => False

def selected (C : Parameters arity n) (D : Nat) (side : Bool) : Machine (Option (State n)) (Fin D) H :=
  { P0DZProperMachine.machine (branch pol C D) with birth := selectedBirth side }

theorem state_eq (C : Parameters arity n) (side : Bool) (w : List (Fin D)) (k : Nat) :
    state (selected pol C D side) w k=state (P0DZProperMachine.machine (branch pol C D)) w k := rfl

theorem run_eq (C : Parameters arity n) (side : Bool) (z : Nat → Fin D) (k : Nat) :
    run (selected pol C D side) z k=run (P0DZProperMachine.machine (branch pol C D)) z k := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [run_succ,selected] using congrArg (fun q =>
      (P0DZProperMachine.machine (branch pol C D)).step q (z k)) ih

theorem birth_full (C : Parameters arity n) (side : Bool) (q r : Option (State n))
    (hb : (selected pol C D side).birth q r) : (P0DZProperMachine.machine (branch pol C D)).birth q r := by
  cases q with
  | none => exact hb.elim
  | some q =>
    cases r with
    | none => exact hb.elim
    | some r =>
      obtain ⟨other,h⟩ := hb
      rcases h with h | h
      · exact Or.inl ⟨other,side,h⟩
      · exact Or.inr ⟨side,other,h⟩

theorem goodWord_of_full (C : Parameters arity n) (side : Bool) (w : List (Fin D))
    (hg : GoodWord (P0DZProperMachine.machine (branch pol C D)) w) : GoodWord (selected pol C D side) w := by
  refine ⟨hg.1,?_⟩
  intro a ha b hb l hl hal hbl hborn hm
  exact hg.2 a ha b hb l hl hal hbl (birth_full pol C side _ _ hborn) hm

theorem good_of_full (C : Parameters arity n) (side : Bool) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch pol C D)) z) : Good (selected pol C D side) z := by
  intro k
  exact (goodWord_prefix _ z k).mp (goodWord_of_full pol C side _ (good_prefix pol C z hg k))

def selectedBirthDecision (C : Parameters arity n) (D : Nat) (side : Bool) :
    DecidableRel (selected pol C D side).birth := by
  intro q r
  cases q <;> cases r <;> dsimp only [selected,selectedBirth]
  · infer_instance
  · infer_instance
  · infer_instance
  · unfold SymBirth RawBirth
    infer_instance

def selectedValidDecision (C : Parameters arity n) (D : Nat) (side : Bool) :
    DecidablePred (selected pol C D side).valid := P0DZProperMachine.validDecision (branch pol C D)

theorem birth_exact (C : Parameters arity n) (side : Bool) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch pol C D)) z) (a b : Nat) :
    (selected pol C D side).birth (run (selected pol C D side) z a) (run (selected pol C D side) z b) ↔
      ∃ other, SymBirth (rawFrame pol C z a) other (rawFrame pol C z b) side := by
  rw [run_eq,run_eq,run_control pol C z hg a,run_control pol C z hg b]
  rfl

theorem permanent_incident (C : Parameters arity n) (side : Bool) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch pol C D)) z) (k t : Nat) (hkt : k≤t)
    (hp : P0PeriodicMonitorInvariant.Permanent (selected pol C D side) z k) : Incident pol C z side t := by
  obtain ⟨a,b,hab,hbk,hborn,hm⟩ := hp
  obtain ⟨other,hb⟩ := (birth_exact pol C side z hg a b).mp hborn
  exact ⟨a,b,t-b,other,by omega,by omega,hb,fun i _ => hm i⟩

theorem accepted_continuation (C : Parameters arity n) (w : List (Fin D))
    (ha : P0DZBranch.Accepted (branch pol C D) w) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch pol C D)) z) (hz : Spells z w) :
    ∃ side, ∀ t, w.length<t → MultiVarianceTokenExact.tokensOf (rawFrame pol C z t) side=∅ ∧
      ¬Incident pol C z side t ∧ ¬P0PeriodicMonitorInvariant.Permanent (selected pol C D side) z t := by
  obtain ⟨side,he,hi⟩ := accepted_isolation pol C w ha z hg hz
  refine ⟨side,?_⟩
  intro t ht
  have hn := hi t (by omega)
  exact ⟨he t ht,hn,fun hp => hn (permanent_incident pol C side z hg t t le_rfl hp)⟩

end NSSE.MultiVarianceSelectedMachine
