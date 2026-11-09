import NSSE.MultiConstructorProperTrace
import NSSE.MultiConstructorTerminalIsolation

/-! Good proper branch words give actual common-terminal assignments.
Together with Z acceptance, this discharges the changed-side isolation claim. -/
namespace NSSE.MultiConstructorGoodCommon
open MultiConstructorTokens MultiConstructorRawValidity MultiConstructorUnifiedWords
open MultiConstructorBranch MultiConstructorBranchLocal MultiConstructorUnifiedBranch
open MultiConstructorUnifiedPrefix MultiConstructorCommonWord MultiConstructorProperTrace
open MultiConstructorTrees P0DZVirtualTrace P0DZFirstClash
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

def headAt (C : Parameters arity n) (w : List (Fin D)) (k : Nat) : H :=
  output C (walk C (branch C D).initial (w.take k))

def properBirthDecision (C : Parameters arity n) (D : Nat) :
    DecidableRel (P0DZProperMachine.machine (branch C D)).birth := by
  letI := birthDecision C D
  intro q r
  cases q <;> cases r <;> dsimp only [P0DZProperMachine.machine]
  · infer_instance
  · infer_instance
  · infer_instance
  · unfold P0DZFirstClash.Born
    infer_instance

theorem virtual_birth (C : Parameters arity n) (w : List (Fin D))
    (hc : DComplete (branch C D) w) (a b : Nat)
    (hb : MultiConstructorUnifiedWords.Born C.input C.left C.right w a b) :
    P0DZFirstClash.Born (branch C D) (dState (branch C D) w a) (dState (branch C D) w b) := by
  refine Or.inl ⟨false,true,?_⟩
  rw [state_walk C w hc a,state_walk C w hc b]
  change false = false ∧ true = true ∧
    ((walk C (branch C D).initial (w.take a)).1.1 ∩
      (walk C (branch C D).initial (w.take b)).1.2).Nonempty
  refine ⟨rfl,rfl,?_⟩
  rw [walk_raw,walk_raw]
  exact (birth_iff_inter C.input _ _ (row_closed C.input C.left C.right w a).1).mp hb

theorem head_match (C : Parameters arity n) (w : List (Fin D))
    (hg : P0ProperWords.GoodWord (P0DZProperMachine.machine (branch C D)) w)
    (a b l : Nat) (hal : a+l ≤ w.length) (hbl : b+l ≤ w.length)
    (hb : MultiConstructorUnifiedWords.Born C.input C.left C.right w a b)
    (hm : P0ProperWords.WordMatch w a b l) : headAt C w (a+l) = headAt C w (b+l) := by
  obtain ⟨hc,hn⟩ := (P0DZProperMachine.good_iff (branch C D) w).mp hg
  by_contra he
  apply hn a b l
  refine ⟨hal,hbl,virtual_birth C w hc a b hb,hm,?_⟩
  rw [state_walk C w hc (a+l),state_walk C w hc (b+l)]
  exact he

theorem common_value (C : Parameters arity n) (w : List (Fin D)) (s : Bool)
    (k : Nat) (hk : k ≤ w.length) :
    value w (selectedHeads C w) (.node (headAt C w w.length)) (.node (headAt C w w.length)) s k =
      .node (headAt C w k) := by
  by_cases hlt : k < w.length
  · rw [value,dif_pos hlt]
    rfl
  · have he : k = w.length := by omega
    subst k
    rw [value_terminal]
    cases s <;> rfl

theorem good_common (C : Parameters arity n) (w : List (Fin D)) (hw : w ≠ [])
    (hg : P0ProperWords.GoodWord (P0DZProperMachine.machine (branch C D)) w) :
    Common C.input C.left C.right w (selectedHeads C w) (headAt C w w.length) := by
  have hc := ((P0DZProperMachine.good_iff (branch C D) w).mp hg).1
  have ht := terminal_ready C w hw hc
  have he : (walk C (branch C D).initial w).1 = row C.input C.left C.right w w.length := by
    simpa only [row,List.take_length] using walk_raw C (branch C D).initial w
  refine ⟨local_assignment C w hc,he ▸ ht.1,?_,?_⟩
  · change Compatible C.input (row C.input C.left C.right w w.length)
      (output C (walk C (branch C D).initial (w.take w.length)))
    rw [List.take_length,← he]
    exact ht.2.2
  · intro a b l hb hal hbl hm
    rw [common_value C w false _ hal,common_value C w true _ hbl]
    exact head_match C w hg a.val b.val l.val hal hbl hb hm

theorem accepted_good_isolated (C : Parameters arity n) (w : List (Fin D))
    (ha : P0DZBranch.Accepted (branch C D) w)
    (hg : P0ProperWords.GoodWord (P0DZProperMachine.machine (branch C D)) w) :
    (upperPins C.input (row C.input C.left C.right w w.length).1 = ∅ ∧
      ¬MultiConstructorUnifiedRays.IncidentX C.input C.left C.right w w.length) ∨
    (lowerPins C.input (row C.input C.left C.right w w.length).2 = ∅ ∧
      ¬MultiConstructorUnifiedRays.IncidentY C.input C.left C.right w w.length) := by
  have hl := (MultiConstructorBranchAssignment.accepted_iff C w).mp ha
  have hw := local_nonempty C (branch C D).initial w hl.1
  exact MultiConstructorTerminalIsolation.changed_side C.input C.left C.right w (selectedHeads C w)
    (headAt C w w.length) C.endX C.endY (good_common C w hw hg) (assignment_sound C w hl)

end NSSE.MultiConstructorGoodCommon
