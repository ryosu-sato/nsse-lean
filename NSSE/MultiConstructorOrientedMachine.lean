import NSSE.MultiConstructorGoodCommon

/-! Side-oriented births preserve proper Good while retaining the physical
orientation required by the periodic permanent-comparison monitor. -/
namespace NSSE.MultiConstructorOrientedMachine
open MultiConstructorBranch P0ProperMachine P0ProperWords
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

def forward (C : Parameters arity n) (D : Nat) : Option (State n) → Option (State n) → Prop
  | some q, some r => (branch C D).birth (.inl q) false (.inl r) true
  | _, _ => False

def oriented (C : Parameters arity n) (D : Nat) (side : Bool) : Machine (Option (State n)) (Fin D) H :=
  { P0DZProperMachine.machine (branch C D) with
    birth := fun q r => if side then forward C D q r else forward C D r q }

theorem birth_union (C : Parameters arity n) (D : Nat) (side : Bool) (q r : Option (State n)) :
    (P0DZProperMachine.machine (branch C D)).birth q r ↔
      (oriented C D side).birth q r ∨ (oriented C D side).birth r q := by
  cases side <;> cases q <;> cases r <;>
    simp [P0DZProperMachine.machine,P0DZFirstClash.Born,oriented,forward,branch,or_comm]

theorem state_eq (C : Parameters arity n) (side : Bool) (w : List (Fin D)) (k : Nat) :
    state (oriented C D side) w k = state (P0DZProperMachine.machine (branch C D)) w k := rfl

theorem run_eq (C : Parameters arity n) (side : Bool) (z : Nat → Fin D) (k : Nat) :
    run (oriented C D side) z k = run (P0DZProperMachine.machine (branch C D)) z k := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [run_succ,oriented] using congrArg (fun q =>
      (P0DZProperMachine.machine (branch C D)).step q (z k)) ih

theorem goodWord_iff (C : Parameters arity n) (side : Bool) (w : List (Fin D)) :
    GoodWord (oriented C D side) w ↔ GoodWord (P0DZProperMachine.machine (branch C D)) w := by
  constructor
  · intro hg
    refine ⟨hg.1,?_⟩
    intro a ha b hb l hl hal hbl hborn hm
    rcases (birth_union C D side _ _).mp hborn with hf | hr
    · exact hg.2 a ha b hb l hl hal hbl hf hm
    · exact (hg.2 b hb a ha l hl hbl hal hr (fun i hi => (hm i hi).symm)).symm
  · intro hg
    refine ⟨hg.1,?_⟩
    intro a ha b hb l hl hal hbl hborn hm
    exact hg.2 a ha b hb l hl hal hbl ((birth_union C D side _ _).mpr (Or.inl hborn)) hm

theorem good_iff (C : Parameters arity n) (side : Bool) (z : Nat → Fin D) :
    Good (oriented C D side) z ↔ Good (P0DZProperMachine.machine (branch C D)) z := by
  have he (k : Nat) := (goodWord_iff C side (prefixWord z k))
  simpa only [Good,goodWord_prefix] using (forall_congr' he)

def orientedBirthDecision (C : Parameters arity n) (D : Nat) (side : Bool) :
    DecidableRel (oriented C D side).birth := by
  letI := birthDecision C D
  intro q r
  cases side <;> cases q <;> cases r <;> dsimp only [oriented,forward] <;> infer_instance

def orientedValidDecision (C : Parameters arity n) (D : Nat) (side : Bool) :
    DecidablePred (oriented C D side).valid := P0DZProperMachine.validDecision (branch C D)

end NSSE.MultiConstructorOrientedMachine
