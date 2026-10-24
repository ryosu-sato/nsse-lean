import NSSE.Automata
import NSSE.BoundedWordEnumeration
import NSSE.FiniteRegisteredStructuralTrace
import NSSE.FiniteDFAUnion

/-!
# Finite monitor for one short border length

For fixed positive `e`, this deterministic monitor stores the first `e`
letters and a queue containing the most recent `e` letters. Whenever the
queue is full, its oldest letter is sent to the root-language DFA before
the new letter is appended. At end of input, that DFA has therefore read
exactly the prefix of length `|w| - e`.
-/

namespace NSSE

universe u v

structure ShortBorderMonitorState
    (α : Type u) (Q : Type v) (e : Nat) where
  first : BoundedWord α e
  queue : BoundedWord α e
  rootState : Q
  shifted : Bool

def shortBorderBoolEnumeration : Enumeration Bool where
  values := [false, true]
  complete := by intro b; cases b <;> simp

def shortBorderMonitorStateEnumeration
    (alphabet : Enumeration α) (states : Enumeration Q)
    (e : Nat) :
    Enumeration (ShortBorderMonitorState α Q e) :=
  (((boundedWordEnumeration alphabet e).product
      (boundedWordEnumeration alphabet e)).product states).product
      shortBorderBoolEnumeration |>
    fun source =>
      source.mapOnto
        (fun value =>
          {
            first := value.1.1.1
            queue := value.1.1.2
            rootState := value.1.2
            shifted := value.2
          })
        (fun state =>
          (((state.first, state.queue), state.rootState),
            state.shifted))
        (by intro state; cases state; rfl)

def shortBorderMonitorStep
    [DecidableEq α]
    (root : DFA α Q) {e : Nat} (he : 0 < e)
    (state : ShortBorderMonitorState α Q e) (letter : α) :
    ShortBorderMonitorState α Q e :=
  let nextFirst : BoundedWord α e :=
    if hfirst : state.first.word.length < e then
      ⟨state.first.word ++ [letter], by
        simp only [List.length_append, List.length_singleton]
        omega⟩
    else
      state.first
  if hqueue : state.queue.word.length < e then
    {
      first := nextFirst
      queue :=
        ⟨state.queue.word ++ [letter], by
          simp only [List.length_append, List.length_singleton]
          omega⟩
      rootState := state.rootState
      shifted := state.shifted
    }
  else
    have hqueueLength : state.queue.word.length = e := by
      have hle := state.queue.length_le
      omega
    have hqueueNonempty : 0 < state.queue.word.length := by
      rw [hqueueLength]
      exact he
    {
      first := nextFirst
      queue :=
        ⟨state.queue.word.drop 1 ++ [letter], by
          simp only [List.length_append, List.length_singleton,
            List.length_drop, hqueueLength]
          omega⟩
      rootState :=
        root.step state.rootState
          (state.queue.word.get ⟨0, hqueueNonempty⟩)
      shifted := true
    }

/-- The fixed-positive-border DFA from Lemma 2.1. -/
def shortBorderDFA
    [DecidableEq α]
    (root : DFA α Q) (e : Nat) (he : 0 < e) :
    DFA α (ShortBorderMonitorState α Q e) where
  start :=
    {
      first := ⟨[], by simp⟩
      queue := ⟨[], by simp⟩
      rootState := root.start
      shifted := false
    }
  step := shortBorderMonitorStep root he
  accept := fun state =>
    state.first.word.length = e ∧
    state.queue.word.length = e ∧
    state.shifted = true ∧
    state.first.word = state.queue.word ∧
    root.accept state.rootState

/-- Updating a positive-length suffix queue by one appended letter. -/
theorem Word.suffix_append_singleton
    (w : Word α) (letter : α) (e : Nat)
    (he : 0 < e) (hew : e ≤ w.length) :
    Word.suffix (w ++ [letter]) e =
      (Word.suffix w e).drop 1 ++ [letter] := by
  unfold Word.suffix
  simp only [List.length_append, List.length_singleton]
  have hindex :
      w.length + 1 - e = (w.length - e) + 1 := by omega
  rw [hindex, List.drop_append_of_le_length (by omega),
    List.drop_drop]

/--
The prefix delayed by a positive queue grows by the oldest queued letter.
-/
theorem Word.take_complement_append_singleton
    (w : Word α) (letter : α) (e : Nat)
    (he : 0 < e) (hew : e ≤ w.length) :
    (w ++ [letter]).take ((w ++ [letter]).length - e) =
      w.take (w.length - e) ++
        [(Word.suffix w e).get
          ⟨0, by
            unfold Word.suffix
            simp
            omega⟩] := by
  have hindex :
      (w ++ [letter]).length - e = (w.length - e) + 1 := by
    simp only [List.length_append, List.length_singleton]
    omega
  rw [hindex,
    List.take_append_of_le_length (by omega),
    List.take_succ_eq_append_getElem (by omega)]
  congr 2
  unfold Word.suffix
  simp [List.get_eq_getElem]

/-- Streaming meaning of every short-border monitor field. -/
def ShortBorderCoreInvariant
    (root : DFA α Q) (e : Nat)
    (read : Word α) (state : ShortBorderMonitorState α Q e) : Prop :=
  state.first.word = read.take e ∧
  state.queue.word = Word.suffix read e ∧
  state.rootState = root.run (read.take (read.length - e)) ∧
  state.shifted = decide (e < read.length)

theorem shortBorder_start_invariant
    [DecidableEq α]
    (root : DFA α Q) (e : Nat) (he : 0 < e) :
    ShortBorderCoreInvariant root e []
      (shortBorderDFA root e he).start := by
  simp [ShortBorderCoreInvariant, shortBorderDFA,
    Word.suffix, DFA.run]

theorem shortBorderStep_coreInvariant
    [DecidableEq α]
    (root : DFA α Q) {e : Nat} (he : 0 < e)
    (read : Word α) (state : ShortBorderMonitorState α Q e)
    (hinvariant : ShortBorderCoreInvariant root e read state)
    (letter : α) :
    ShortBorderCoreInvariant root e (read ++ [letter])
      (shortBorderMonitorStep root he state letter) := by
  rcases hinvariant with
    ⟨hfirst, hqueue, hroot, hshifted⟩
  by_cases hshort : read.length < e
  · have hfirstFill : state.first.word.length < e := by
      rw [hfirst]
      simp only [List.length_take]
      omega
    have hqueueFill : state.queue.word.length < e := by
      rw [hqueue]
      unfold Word.suffix
      simp
      omega
    simp only [shortBorderMonitorStep,
      dif_pos hfirstFill, dif_pos hqueueFill]
    have hnewLe : (read ++ [letter]).length ≤ e := by
      simp only [List.length_append, List.length_singleton]
      omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · change state.first.word ++ [letter] =
        (read ++ [letter]).take e
      rw [hfirst, List.take_of_length_le (Nat.le_of_lt hshort),
        List.take_of_length_le hnewLe]
    · change state.queue.word ++ [letter] =
        Word.suffix (read ++ [letter]) e
      rw [hqueue]
      unfold Word.suffix
      have hreadSub : read.length - e = 0 := by omega
      have hnewSub : (read ++ [letter]).length - e = 0 := by
        simp only [List.length_append, List.length_singleton]
        omega
      rw [hreadSub, hnewSub]
      simp
    · rw [hroot]
      have hreadSub : read.length - e = 0 := by omega
      have hnewSub : (read ++ [letter]).length - e = 0 := by
        simp only [List.length_append, List.length_singleton]
        omega
      rw [hreadSub, hnewSub]
      rfl
    · rw [hshifted]
      simp only [List.length_append, List.length_singleton]
      have hold : ¬e < read.length := by omega
      have hnew : ¬e < read.length + 1 := by omega
      simp [hold, hnew]
  · have hlong : e ≤ read.length := by omega
    have hfirstFull : ¬state.first.word.length < e := by
      rw [hfirst]
      simp [List.length_take, Nat.min_eq_left hlong]
    have hqueueLength : state.queue.word.length = e := by
      rw [hqueue]
      unfold Word.suffix
      simp
      omega
    have hqueueFull : ¬state.queue.word.length < e := by omega
    simp only [shortBorderMonitorStep,
      dif_neg hfirstFull, dif_neg hqueueFull]
    refine ⟨?_, ?_, ?_, ?_⟩
    · change state.first.word =
        (read ++ [letter]).take e
      rw [hfirst,
        List.take_append_of_le_length hlong]
    · change state.queue.word.drop 1 ++ [letter] =
        Word.suffix (read ++ [letter]) e
      rw [hqueue]
      exact (Word.suffix_append_singleton
        read letter e he hlong).symm
    · change
        root.step state.rootState
            (state.queue.word.get
              ⟨0, by rw [hqueueLength]; exact he⟩) =
          root.run
            ((read ++ [letter]).take
              ((read ++ [letter]).length - e))
      rw [hroot]
      have htake :=
        Word.take_complement_append_singleton
          read letter e he hlong
      rw [htake, root.run_append]
      congr 1
      have hopt :=
        congrArg (fun word => word[0]?) hqueue
      have hqueueNonempty : 0 < state.queue.word.length := by
        rw [hqueueLength]
        exact he
      have hsuffixNonempty : 0 < (Word.suffix read e).length := by
        unfold Word.suffix
        simp
        omega
      simp [hqueueNonempty, hsuffixNonempty] at hopt
      simpa using hopt
    · simp only [List.length_append, List.length_singleton]
      simp [show e < read.length + 1 by omega]

theorem shortBorderDFA_run_coreInvariant
    [DecidableEq α]
    (root : DFA α Q) (e : Nat) (he : 0 < e)
    (w : Word α) :
    ShortBorderCoreInvariant root e w
      ((shortBorderDFA root e he).run w) := by
  have aux :
      ∀ (read suffix : Word α)
        (state : ShortBorderMonitorState α Q e),
        ShortBorderCoreInvariant root e read state →
        ShortBorderCoreInvariant root e (read ++ suffix)
          ((shortBorderDFA root e he).runFrom state suffix) := by
    intro read suffix
    induction suffix generalizing read with
    | nil =>
        intro state hinvariant
        simpa using hinvariant
    | cons letter suffix ih =>
        intro state hinvariant
        rw [DFA.runFrom_cons]
        have hstep :=
          shortBorderStep_coreInvariant root he
            read state hinvariant letter
        simpa [List.append_assoc] using
          ih (read ++ [letter])
            (shortBorderMonitorStep root he state letter) hstep
  unfold DFA.run
  simpa using aux [] w (shortBorderDFA root e he).start
    (shortBorder_start_invariant root e he)

/-- Exact language theorem for one positive border length. -/
theorem shortBorderDFA_accepts_iff
    [DecidableEq α]
    (root : DFA α Q) (e : Nat) (he : 0 < e)
    (w : Word α) :
    (shortBorderDFA root e he).Accepts w ↔
      e < w.length ∧
      Word.BorderCopy w e ∧
      root.Accepts (w.take (w.length - e)) := by
  have hinvariant :=
    shortBorderDFA_run_coreInvariant root e he w
  rcases hinvariant with
    ⟨hfirst, hqueue, hroot, hshifted⟩
  constructor
  · intro haccept
    rcases haccept with
      ⟨hfirstLength, hqueueLength, hshiftedTrue,
        hborderState, hrootAccept⟩
    have helen : e < w.length := by
      rw [hshifted] at hshiftedTrue
      simpa using hshiftedTrue
    refine ⟨helen, ?_, ?_⟩
    · unfold Word.BorderCopy Word.prefix
      rw [← hfirst, ← hqueue]
      exact hborderState
    · unfold DFA.Accepts
      rw [← hroot]
      exact hrootAccept
  · rintro ⟨helen, hborder, hrootAccept⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hfirst]
      simp [Nat.min_eq_left (Nat.le_of_lt helen)]
    · rw [hqueue]
      unfold Word.suffix
      simp
      omega
    · rw [hshifted]
      simp [helen]
    · rw [hfirst, hqueue]
      exact hborder
    · unfold DFA.Accepts at hrootAccept
      rw [hroot]
      exact hrootAccept

def fixedShortBorderEnumeratedDFA
    [DecidableEq α]
    (alphabet : Enumeration α)
    (root : DFA α Q) (rootStates : Enumeration Q)
    (border : PositivePeriodUpTo c) :
    EnumeratedDFA.{u, max u v} α where
  State := ShortBorderMonitorState α Q border.value
  automaton :=
    shortBorderDFA root border.value border.positive
  states :=
    shortBorderMonitorStateEnumeration
      alphabet rootStates border.value

def shortBorderMonitorUnion
    [DecidableEq α]
    (alphabet : Enumeration α)
    (root : DFA α Q) (rootStates : Enumeration Q)
    {c : Nat} :
    List (PositivePeriodUpTo c) →
      EnumeratedDFA.{u, max u v} α
  | [] => EnumeratedDFA.rejectsAll α
  | border :: borders =>
      (fixedShortBorderEnumeratedDFA
        alphabet root rootStates border).union
        (shortBorderMonitorUnion
          alphabet root rootStates borders)

theorem shortBorderMonitorUnion_accepts_iff
    [DecidableEq α]
    (alphabet : Enumeration α)
    (root : DFA α Q) (rootStates : Enumeration Q)
    {c : Nat} (borders : List (PositivePeriodUpTo c))
    (w : Word α) :
    (shortBorderMonitorUnion
      alphabet root rootStates borders).automaton.Accepts w ↔
      ∃ border ∈ borders,
        (shortBorderDFA root border.value
          border.positive).Accepts w := by
  induction borders with
  | nil =>
      simp [shortBorderMonitorUnion,
        EnumeratedDFA.rejectsAll, DFA.Accepts, DFA.run]
  | cons border borders ih =>
      rw [shortBorderMonitorUnion,
        EnumeratedDFA.union_accepts_iff, ih]
      simp only [List.mem_cons]
      constructor
      · rintro (hborder | ⟨candidate, hmem, hc⟩)
        · exact ⟨border, Or.inl rfl, hborder⟩
        · exact ⟨candidate, Or.inr hmem, hc⟩
      · rintro ⟨candidate, hmem, hc⟩
        rcases hmem with rfl | htail
        · exact Or.inl hc
        · exact Or.inr ⟨candidate, htail, hc⟩

def shortBorderEnumeratedDFA
    [DecidableEq α]
    (alphabet : Enumeration α)
    (root : DFA α Q) (rootStates : Enumeration Q)
    (c : Nat) :
    EnumeratedDFA.{u, max u v} α :=
  shortBorderMonitorUnion alphabet root rootStates
    (positivePeriodsUpTo c)

/--
Lemma 2.1, short-border half: the constructed finite enumerated DFA
recognizes exactly `Bord_{≤c}`.
-/
theorem shortBorderEnumeratedDFA_language_iff
    [DecidableEq α]
    (alphabet : Enumeration α)
    (root : DFA α Q) (rootStates : Enumeration Q)
    (c : Nat) (w : Word α) :
    (shortBorderEnumeratedDFA
      alphabet root rootStates c).automaton.Accepts w ↔
      ShortBorderLanguage root.language c w := by
  rw [shortBorderEnumeratedDFA,
    shortBorderMonitorUnion_accepts_iff]
  constructor
  · rintro ⟨border, hmem, hmonitor⟩
    obtain ⟨helen, hborder, hroot⟩ :=
      (shortBorderDFA_accepts_iff root border.value
        border.positive w).1 hmonitor
    exact ⟨border.value, border.positive,
      border.le_bound, helen, hborder, hroot⟩
  · rintro ⟨e, he, hec, helen, hborder, hroot⟩
    let border : PositivePeriodUpTo c := ⟨e, he, hec⟩
    refine ⟨border, mem_positivePeriodsUpTo c border, ?_⟩
    apply (shortBorderDFA_accepts_iff
      root e he w).2
    exact ⟨helen, hborder, hroot⟩

end NSSE
