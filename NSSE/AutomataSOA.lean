import NSSE.ConcreteSOA
import NSSE.TransitionMonoid
import NSSE.FactorForest
import NSSE.EventStream
import Lean.Elab.Tactic.Omega

/-!
# Automata-presented SOA instances

Connects concrete SOA semantics to DFA transition-monoid replacement.
-/

namespace NSSE

universe u vc vl vr

structure AutomataSOAInstance
    (α : Type u) (QC : Type vc) (QL : Type vl) (QR : Type vr) where
  candidate : DFA α QC
  rows : List (DFA α QL × DFA α QR)

namespace AutomataSOAInstance

def toSOA (I : AutomataSOAInstance α QC QL QR) : SOAInstance α where
  candidate := I.candidate.language
  rows := I.rows.map (fun row => CapComponent.ofDFA row.1 row.2)

@[simp] theorem toSOA_candidate
    (I : AutomataSOAInstance α QC QL QR) (w : Word α) :
    I.toSOA.candidate w ↔ I.candidate.Accepts w := by
  rfl

/--
Any contextual factor replacement preserving the candidate DFA's full
transition transformation preserves candidate membership.
-/
theorem candidate_context_replace
    (I : AutomataSOAInstance α QC QL QR)
    (left x y right : Word α)
    (hxy :
      I.candidate.transitionEval x =
        I.candidate.transitionEval y) :
    I.toSOA.candidate (left ++ x ++ right) ↔
      I.toSOA.candidate (left ++ y ++ right) := by
  exact I.candidate.accepts_context_replace left x y right hxy

theorem candidate_two_factor_replace
    (I : AutomataSOAInstance α QC QL QR)
    (left x middle z right x' z' : Word α)
    (hx :
      I.candidate.transitionEval x =
        I.candidate.transitionEval x')
    (hz :
      I.candidate.transitionEval z =
        I.candidate.transitionEval z') :
    I.toSOA.candidate (left ++ x ++ middle ++ z ++ right) ↔
      I.toSOA.candidate (left ++ x' ++ middle ++ z' ++ right) := by
  constructor
  · intro h
    have h₁ :=
      (I.candidate.accepts_context_replace left x x'
        (middle ++ z ++ right) hx).1
        (by simpa [List.append_assoc] using h)
    have h₂ :=
      (I.candidate.accepts_context_replace
        (left ++ x' ++ middle) z z' right hz).1
        (by simpa [List.append_assoc] using h₁)
    simpa [List.append_assoc] using h₂
  · intro h
    have h₁ :=
      (I.candidate.accepts_context_replace
        (left ++ x' ++ middle) z' z right hz.symm).1
        (by simpa [List.append_assoc] using h)
    have h₂ :=
      (I.candidate.accepts_context_replace left x' x
        (middle ++ z ++ right) hx.symm).1
        (by simpa [List.append_assoc] using h₁)
    simpa [List.append_assoc] using h₂

/--
Literal/control-blind prefix restoration for one selected row.  A loop
in the candidate automaton preserves candidate membership; a loop in
the row's left automaton transports the concrete marked occurrence.
-/
theorem candidate_rootCov_prefix_of_loops
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (hrow : (left, right) ∈ I.rows)
    (pre w : Word α)
    (hcandidateLoop : I.candidate.run pre = I.candidate.start)
    (hleftLoop : left.run pre = left.start)
    (hcandidate : I.toSOA.candidate w)
    (hrowCovers :
      SOAInstance.RowCovers (CapComponent.ofDFA left right) w) :
    I.toSOA.candidate (pre ++ w) ∧
      I.toSOA.RootCov (pre ++ w) := by
  constructor
  · exact I.candidate.accepts_prefix_of_loop pre w
      hcandidateLoop hcandidate
  · refine ⟨CapComponent.ofDFA left right, ?_, ?_⟩
    · simp only [toSOA, List.mem_map]
      exact ⟨(left, right), hrow, rfl⟩
    · exact markedOccurrence_prefix_shift_of_left_loop
        left right pre w hleftLoop hrowCovers

theorem prefix_loop_lift_contradicts_avoider
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (hrow : (left, right) ∈ I.rows)
    (pre w : Word α)
    (hcandidateLoop : I.candidate.run pre = I.candidate.start)
    (hleftLoop : left.run pre = left.start)
    (hbottomCandidate : I.toSOA.candidate w)
    (hrowCovers :
      SOAInstance.RowCovers (CapComponent.ofDFA left right) w) :
    ¬ I.toSOA.Avoider (pre ++ w) := by
  intro havoider
  have hlift := candidate_rootCov_prefix_of_loops I left right hrow
    pre w hcandidateLoop hleftLoop hbottomCandidate hrowCovers
  exact havoider.2 hlift.2

/--
Literal lift for an insertion at any slot before the selected source cut.
The loop states are occurrence-local states after the insertion prefix,
not necessarily the automata start states.
-/
theorem candidate_rootCov_insertAt_before_of_loops
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (hrow : (left, right) ∈ I.rows)
    (w payload : Word α) (slot j t : Nat)
    (hslot : slot ≤ j) (hjt : j < t) (ht : t < w.length)
    (hcandidate : I.toSOA.candidate w)
    (hleft : left.Accepts (w.take j))
    (hright : right.Accepts (Word.factor w j (t - j)))
    (hoccurs : OccursSuffixAt w j t)
    (hcandidateLoop :
      I.candidate.runFrom (I.candidate.run (w.take slot)) payload =
        I.candidate.run (w.take slot))
    (hleftLoop :
      left.runFrom (left.run (w.take slot)) payload =
        left.run (w.take slot)) :
    I.toSOA.candidate (Word.insertAt w payload slot) ∧
      I.toSOA.RootCov (Word.insertAt w payload slot) := by
  constructor
  · exact I.candidate.accepts_insertAt_of_loop
      w payload slot hcandidateLoop hcandidate
  · refine ⟨CapComponent.ofDFA left right, ?_, ?_⟩
    · simp only [toSOA, List.mem_map]
      exact ⟨(left, right), hrow, rfl⟩
    · exact markedOccurrence_insertAt_before_of_left_loop
        left right w payload slot j t hslot hjt ht
        hleft hright hoccurs hleftLoop

theorem insertAt_before_loop_lift_contradicts_avoider
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (hrow : (left, right) ∈ I.rows)
    (w payload : Word α) (slot j t : Nat)
    (hslot : slot ≤ j) (hjt : j < t) (ht : t < w.length)
    (hcandidate : I.toSOA.candidate w)
    (hleft : left.Accepts (w.take j))
    (hright : right.Accepts (Word.factor w j (t - j)))
    (hoccurs : OccursSuffixAt w j t)
    (hcandidateLoop :
      I.candidate.runFrom (I.candidate.run (w.take slot)) payload =
        I.candidate.run (w.take slot))
    (hleftLoop :
      left.runFrom (left.run (w.take slot)) payload =
        left.run (w.take slot)) :
    ¬ I.toSOA.Avoider (Word.insertAt w payload slot) := by
  intro havoider
  have hlift :=
    candidate_rootCov_insertAt_before_of_loops I left right hrow
      w payload slot j t hslot hjt ht hcandidate hleft hright
      hoccurs hcandidateLoop hleftLoop
  exact havoider.2 hlift.2

/--
Two consecutive before-source restoration edges transport the same
selected bottom witness all the way to the top.  The second edge uses
the explicitly shifted cuts and row factor produced by the first edge.
-/
theorem candidate_rootCov_two_insertAt_before_of_loops
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (hrow : (left, right) ∈ I.rows)
    (w first second : Word α)
    (slot₁ slot₂ j t : Nat)
    (hslot₁ : slot₁ ≤ j) (hjt : j < t) (ht : t < w.length)
    (hslot₂ : slot₂ ≤ j + first.length)
    (hcandidate : I.toSOA.candidate w)
    (hleft : left.Accepts (w.take j))
    (hright : right.Accepts (Word.factor w j (t - j)))
    (hoccurs : OccursSuffixAt w j t)
    (hcandidateLoop₁ :
      I.candidate.runFrom
          (I.candidate.run (w.take slot₁)) first =
        I.candidate.run (w.take slot₁))
    (hleftLoop₁ :
      left.runFrom (left.run (w.take slot₁)) first =
        left.run (w.take slot₁))
    (hcandidateLoop₂ :
      I.candidate.runFrom
          (I.candidate.run
            ((Word.insertAt w first slot₁).take slot₂)) second =
        I.candidate.run
          ((Word.insertAt w first slot₁).take slot₂))
    (hleftLoop₂ :
      left.runFrom
          (left.run ((Word.insertAt w first slot₁).take slot₂))
          second =
        left.run ((Word.insertAt w first slot₁).take slot₂)) :
    I.toSOA.candidate
        (Word.insertAt (Word.insertAt w first slot₁) second slot₂) ∧
      I.toSOA.RootCov
        (Word.insertAt (Word.insertAt w first slot₁) second slot₂) := by
  let w₁ := Word.insertAt w first slot₁
  let j₁ := j + first.length
  let t₁ := t + first.length
  have hslot₁len : slot₁ ≤ w.length := by omega
  have hw₁Candidate : I.toSOA.candidate w₁ :=
    I.candidate.accepts_insertAt_of_loop
      w first slot₁ hcandidateLoop₁ hcandidate
  have hj₁t₁ : j₁ < t₁ := by
    dsimp [j₁, t₁]
    omega
  have ht₁ : t₁ < w₁.length := by
    dsimp [t₁, w₁]
    rw [Word.insertAt_length w first hslot₁len]
    omega
  have hleft₁ : left.Accepts (w₁.take j₁) := by
    dsimp [w₁, j₁]
    exact left.accepts_take_insertAt_before_of_loop
      w first slot₁ j hslot₁ (by omega) hleftLoop₁ hleft
  have hright₁ :
      right.Accepts (Word.factor w₁ j₁ (t₁ - j₁)) := by
    have hdiff : t₁ - j₁ = t - j := by
      dsimp [t₁, j₁]
      omega
    rw [hdiff]
    dsimp [w₁, j₁]
    rw [Word.factor_insertAt_before w first slot₁ j
      (t - j) hslot₁ (by omega)]
    exact hright
  have hoccurs₁ : OccursSuffixAt w₁ j₁ t₁ := by
    dsimp [w₁, j₁, t₁]
    exact Word.occursSuffixAt_insertAt_before
      w first slot₁ j t hslot₁ hjt ht hoccurs
  exact candidate_rootCov_insertAt_before_of_loops
    I left right hrow w₁ second slot₂ j₁ t₁ hslot₂
    hj₁t₁ ht₁ hw₁Candidate hleft₁ hright₁ hoccurs₁
    hcandidateLoop₂ hleftLoop₂

theorem two_insertAt_loop_lift_contradicts_avoider
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (hrow : (left, right) ∈ I.rows)
    (w first second : Word α)
    (slot₁ slot₂ j t : Nat)
    (hslot₁ : slot₁ ≤ j) (hjt : j < t) (ht : t < w.length)
    (hslot₂ : slot₂ ≤ j + first.length)
    (hcandidate : I.toSOA.candidate w)
    (hleft : left.Accepts (w.take j))
    (hright : right.Accepts (Word.factor w j (t - j)))
    (hoccurs : OccursSuffixAt w j t)
    (hcandidateLoop₁ :
      I.candidate.runFrom
          (I.candidate.run (w.take slot₁)) first =
        I.candidate.run (w.take slot₁))
    (hleftLoop₁ :
      left.runFrom (left.run (w.take slot₁)) first =
        left.run (w.take slot₁))
    (hcandidateLoop₂ :
      I.candidate.runFrom
          (I.candidate.run
            ((Word.insertAt w first slot₁).take slot₂)) second =
        I.candidate.run
          ((Word.insertAt w first slot₁).take slot₂))
    (hleftLoop₂ :
      left.runFrom
          (left.run ((Word.insertAt w first slot₁).take slot₂))
          second =
        left.run ((Word.insertAt w first slot₁).take slot₂)) :
    ¬ I.toSOA.Avoider
      (Word.insertAt (Word.insertAt w first slot₁) second slot₂) := by
  intro havoider
  have hlift :=
    candidate_rootCov_two_insertAt_before_of_loops I left right hrow
      w first second slot₁ slot₂ j t hslot₁ hjt ht hslot₂
      hcandidate hleft hright hoccurs hcandidateLoop₁ hleftLoop₁
      hcandidateLoop₂ hleftLoop₂
  exact havoider.2 hlift.2

/--
A finite stream whose every insertion is before the currently shifted
source cut and loops both the candidate DFA and the selected row's left
DFA at the occurrence-local state.
-/
inductive BeforeSourceLoopStream
    (I : AutomataSOAInstance α QC QL QR) (left : DFA α QL) :
    List (InsertionEvent α) → Word α → Nat → Nat → Prop where
  | nil (w : Word α) (j t : Nat) :
      BeforeSourceLoopStream I left [] w j t
  | cons
      {events : List (InsertionEvent α)} {w : Word α} {j t : Nat}
      (event : InsertionEvent α)
      (hslot : event.slot ≤ j)
      (hcandidateLoop :
        I.candidate.runFrom
            (I.candidate.run (w.take event.slot)) event.payload =
          I.candidate.run (w.take event.slot))
      (hleftLoop :
        left.runFrom
            (left.run (w.take event.slot)) event.payload =
          left.run (w.take event.slot))
      (tail :
        BeforeSourceLoopStream I left events (event.apply w)
          (j + event.payload.length) (t + event.payload.length)) :
      BeforeSourceLoopStream I left (event :: events) w j t

/--
Every finite before-source loop stream transports one concrete selected
row witness to its final word.  Thus the final word is a candidate and
is covered by that same row.
-/
theorem candidate_rootCov_applyStream_of_beforeSourceLoops
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (hrow : (left, right) ∈ I.rows)
    (events : List (InsertionEvent α)) (w : Word α) (j t : Nat)
    (hstream : BeforeSourceLoopStream I left events w j t)
    (hjt : j < t) (ht : t < w.length)
    (hcandidate : I.toSOA.candidate w)
    (hleft : left.Accepts (w.take j))
    (hright : right.Accepts (Word.factor w j (t - j)))
    (hoccurs : OccursSuffixAt w j t) :
    I.toSOA.candidate (InsertionEvent.applyStream events w) ∧
      I.toSOA.RootCov (InsertionEvent.applyStream events w) := by
  induction hstream with
  | nil w j t =>
      constructor
      · exact hcandidate
      · refine ⟨CapComponent.ofDFA left right, ?_, ?_⟩
        · simp only [toSOA, List.mem_map]
          exact ⟨(left, right), hrow, rfl⟩
        · exact ⟨j, t, hjt, ht, hleft, hright, hoccurs⟩
  | @cons events w j t event hslot hcandidateLoop hleftLoop tail ih =>
      have hslotLength : event.slot ≤ w.length := by omega
      have hjt' :
          j + event.payload.length < t + event.payload.length := by
        omega
      have ht' :
          t + event.payload.length < (event.apply w).length := by
        rw [InsertionEvent.apply, Word.insertAt_length
          w event.payload hslotLength]
        omega
      have hcandidate' : I.toSOA.candidate (event.apply w) := by
        exact I.candidate.accepts_insertAt_of_loop
          w event.payload event.slot hcandidateLoop hcandidate
      have hleft' :
          left.Accepts
            ((event.apply w).take (j + event.payload.length)) := by
        exact left.accepts_take_insertAt_before_of_loop
          w event.payload event.slot j hslot (by omega)
          hleftLoop hleft
      have hright' :
          right.Accepts
            (Word.factor (event.apply w)
              (j + event.payload.length)
              ((t + event.payload.length) -
                (j + event.payload.length))) := by
        have hdiff :
            (t + event.payload.length) -
                (j + event.payload.length) = t - j := by
          omega
        rw [hdiff, InsertionEvent.apply,
          Word.factor_insertAt_before w event.payload event.slot j
            (t - j) hslot (by omega)]
        exact hright
      have hoccurs' :
          OccursSuffixAt (event.apply w)
            (j + event.payload.length) (t + event.payload.length) := by
        exact Word.occursSuffixAt_insertAt_before
          w event.payload event.slot j t hslot hjt ht hoccurs
      exact ih hjt' ht' hcandidate' hleft' hright' hoccurs'

theorem applyStream_beforeSourceLoops_contradicts_avoider
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (hrow : (left, right) ∈ I.rows)
    (events : List (InsertionEvent α)) (w : Word α) (j t : Nat)
    (hstream : BeforeSourceLoopStream I left events w j t)
    (hjt : j < t) (ht : t < w.length)
    (hcandidate : I.toSOA.candidate w)
    (hleft : left.Accepts (w.take j))
    (hright : right.Accepts (Word.factor w j (t - j)))
    (hoccurs : OccursSuffixAt w j t) :
    ¬ I.toSOA.Avoider (InsertionEvent.applyStream events w) := by
  intro havoider
  have hlift :=
    candidate_rootCov_applyStream_of_beforeSourceLoops
      I left right hrow events w j t hstream hjt ht
      hcandidate hleft hright hoccurs
  exact havoider.2 hlift.2

/--
The exact one-edge `betweenCuts` response.  Unlike the before-source
case, occurrence preservation is not automatic: the expanded right
factor must still be accepted and the new suffix-copy equality must
hold.  These are explicit response premises.
-/
theorem candidate_rootCov_insertAt_between_of_response
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (hrow : (left, right) ∈ I.rows)
    (w payload : Word α) (slot j t : Nat)
    (hjslot : j < slot) (hslott : slot ≤ t)
    (ht : t < w.length)
    (hcandidate : I.toSOA.candidate w)
    (hleft : left.Accepts (w.take j))
    (hcandidateLoop :
      I.candidate.runFrom
          (I.candidate.run (w.take slot)) payload =
        I.candidate.run (w.take slot))
    (hrightResponse :
      right.Accepts
        (Word.factor (Word.insertAt w payload slot) j
          ((t + payload.length) - j)))
    (hoccursResponse :
      OccursSuffixAt (Word.insertAt w payload slot)
        j (t + payload.length)) :
    I.toSOA.candidate (Word.insertAt w payload slot) ∧
      I.toSOA.RootCov (Word.insertAt w payload slot) := by
  have hslotLength : slot ≤ w.length := by omega
  constructor
  · exact I.candidate.accepts_insertAt_of_loop
      w payload slot hcandidateLoop hcandidate
  · refine ⟨CapComponent.ofDFA left right, ?_, ?_⟩
    · simp only [toSOA, List.mem_map]
      exact ⟨(left, right), hrow, rfl⟩
    · refine ⟨j, t + payload.length, by omega, ?_, ?_,
        hrightResponse, hoccursResponse⟩
      · rw [Word.insertAt_length w payload hslotLength]
        omega
      · rw [Word.take_insertAt_after w payload slot j
          (Nat.le_of_lt hjslot) hslotLength]
        exact hleft

theorem insertAt_between_response_contradicts_avoider
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (hrow : (left, right) ∈ I.rows)
    (w payload : Word α) (slot j t : Nat)
    (hjslot : j < slot) (hslott : slot ≤ t)
    (ht : t < w.length)
    (hcandidate : I.toSOA.candidate w)
    (hleft : left.Accepts (w.take j))
    (hcandidateLoop :
      I.candidate.runFrom
          (I.candidate.run (w.take slot)) payload =
        I.candidate.run (w.take slot))
    (hrightResponse :
      right.Accepts
        (Word.factor (Word.insertAt w payload slot) j
          ((t + payload.length) - j)))
    (hoccursResponse :
      OccursSuffixAt (Word.insertAt w payload slot)
        j (t + payload.length)) :
    ¬ I.toSOA.Avoider (Word.insertAt w payload slot) := by
  intro havoider
  have hlift :=
    candidate_rootCov_insertAt_between_of_response
      I left right hrow w payload slot j t hjslot hslott ht
      hcandidate hleft hcandidateLoop hrightResponse hoccursResponse
  exact havoider.2 hlift.2

/--
The exact one-edge `afterTarget` response.  Both selected row-language
factors remain literal; only the suffix-copy equality over the enlarged
suffix must be supplied as a new response.
-/
theorem candidate_rootCov_insertAt_after_of_response
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (hrow : (left, right) ∈ I.rows)
    (w payload : Word α) (slot j t : Nat)
    (hjt : j < t) (htslot : t < slot)
    (hslotLength : slot ≤ w.length)
    (hcandidate : I.toSOA.candidate w)
    (hleft : left.Accepts (w.take j))
    (hright : right.Accepts (Word.factor w j (t - j)))
    (hcandidateLoop :
      I.candidate.runFrom
          (I.candidate.run (w.take slot)) payload =
        I.candidate.run (w.take slot))
    (hoccursResponse :
      OccursSuffixAt (Word.insertAt w payload slot) j t) :
    I.toSOA.candidate (Word.insertAt w payload slot) ∧
      I.toSOA.RootCov (Word.insertAt w payload slot) := by
  constructor
  · exact I.candidate.accepts_insertAt_of_loop
      w payload slot hcandidateLoop hcandidate
  · refine ⟨CapComponent.ofDFA left right, ?_, ?_⟩
    · simp only [toSOA, List.mem_map]
      exact ⟨(left, right), hrow, rfl⟩
    · refine ⟨j, t, hjt, ?_, ?_, ?_, hoccursResponse⟩
      · rw [Word.insertAt_length w payload hslotLength]
        omega
      · rw [Word.take_insertAt_after w payload slot j
          (by omega) hslotLength]
        exact hleft
      · rw [Word.factor_insertAt_after w payload slot j (t - j)
          (by omega) hslotLength]
        exact hright

theorem insertAt_after_response_contradicts_avoider
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (hrow : (left, right) ∈ I.rows)
    (w payload : Word α) (slot j t : Nat)
    (hjt : j < t) (htslot : t < slot)
    (hslotLength : slot ≤ w.length)
    (hcandidate : I.toSOA.candidate w)
    (hleft : left.Accepts (w.take j))
    (hright : right.Accepts (Word.factor w j (t - j)))
    (hcandidateLoop :
      I.candidate.runFrom
          (I.candidate.run (w.take slot)) payload =
        I.candidate.run (w.take slot))
    (hoccursResponse :
      OccursSuffixAt (Word.insertAt w payload slot) j t) :
    ¬ I.toSOA.Avoider (Word.insertAt w payload slot) := by
  intro havoider
  have hlift :=
    candidate_rootCov_insertAt_after_of_response
      I left right hrow w payload slot j t hjt htslot hslotLength
      hcandidate hleft hright hcandidateLoop hoccursResponse
  exact havoider.2 hlift.2

/--
Deleting one idempotent forest child produces an admissible concrete SOA
deletion whenever at least one sibling remains.
-/
theorem idempotent_child_deletesTo
    (I : AutomataSOAInstance α QC QL QR)
    {before after : List (FactorTree α)}
    {deleted : FactorTree α} {e : QC → QC}
    (he : (transformationMonoid QC).Idempotent e)
    (hall :
      ∀ t ∈ before ++ deleted :: after,
        FactorTree.control (transformationMonoid QC)
          I.candidate.letterTransform t = e)
    (hretained : before ++ after ≠ [])
    (hdeleted : deleted.WellFormed)
    (left right : Word α)
    (hcandidate :
      I.toSOA.candidate
        (left ++ FactorTree.forestYield
          (before ++ deleted :: after) ++ right)) :
    I.toSOA.DeletesTo
      (left ++ FactorTree.forestYield (before ++ after) ++ right)
      (left ++ FactorTree.forestYield
        (before ++ deleted :: after) ++ right) := by
  let C := transformationMonoid QC
  let letter := I.candidate.letterTransform
  have hdelete :=
    FactorTree.delete_one_idempotent_child C letter he hall
      hretained hdeleted
  have hcandidate' :
      I.toSOA.candidate
        (left ++ FactorTree.forestYield (before ++ after) ++ right) := by
    apply (I.candidate.accepts_context_replace left
      (FactorTree.forestYield (before ++ deleted :: after))
      (FactorTree.forestYield (before ++ after)) right hdelete.1).1
    exact hcandidate
  let pre := left ++ FactorTree.forestYield before
  let post := FactorTree.forestYield after ++ right
  refine ⟨pre.length, deleted.yield.length,
    List.length_pos_iff.mpr (FactorTree.yield_ne_nil hdeleted), ?_, ?_,
    hcandidate'⟩
  · dsimp [pre]
    simp only [FactorTree.forestYield_split, List.length_append]
    omega
  · dsimp [pre, post]
    simpa [FactorTree.forestYield, List.flatMap_append,
      List.append_assoc] using
      (SOAInstance.eraseFactor_append
        (left ++ FactorTree.forestYield before) deleted.yield
        (FactorTree.forestYield after ++ right)).symm

/--
At a length-minimal avoider, every admissible idempotent-child contraction
is covered.  This is the concrete bridge from factor-forest pumping to the
`AllDel`/shortest-avoider argument.
-/
theorem idempotent_child_rootCov_of_minimal
    (I : AutomataSOAInstance α QC QL QR)
    {before after : List (FactorTree α)}
    {deleted : FactorTree α} {e : QC → QC}
    (he : (transformationMonoid QC).Idempotent e)
    (hall :
      ∀ t ∈ before ++ deleted :: after,
        FactorTree.control (transformationMonoid QC)
          I.candidate.letterTransform t = e)
    (hretained : before ++ after ≠ [])
    (hdeleted : deleted.WellFormed)
    (left right : Word α)
    (hminimal :
      I.toSOA.LengthMinimalAvoider
        (left ++ FactorTree.forestYield
          (before ++ deleted :: after) ++ right)) :
    I.toSOA.RootCov
      (left ++ FactorTree.forestYield (before ++ after) ++ right) := by
  let shortened :=
    left ++ FactorTree.forestYield (before ++ after) ++ right
  let original :=
    left ++ FactorTree.forestYield
      (before ++ deleted :: after) ++ right
  have hdelete : I.toSOA.DeletesTo shortened original := by
    exact idempotent_child_deletesTo I he hall hretained hdeleted
      left right hminimal.1.1
  exact SOAInstance.covered_of_candidate_shorter hminimal
    (SOAInstance.deletesTo_candidate hdelete)
    (SOAInstance.deletesTo_shorter hdelete)

end AutomataSOAInstance

end NSSE
