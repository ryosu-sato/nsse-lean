import NSSE.Automata
import NSSE.BoundedWordEnumeration
import NSSE.FiniteRegisteredStructuralTrace

/-!
# Finite monitor for one bounded period

For a fixed positive `p`, the monitor stores the first `p` letters, the
state reached by the root-language DFA, and a cyclic comparison offset.
After the root buffer is full, every new letter is checked against the
buffer.  This is the fixed-period automaton used in Lemma 2.1.
-/

namespace NSSE

universe u v

structure PeriodMonitorState
    (α : Type u) (Q : Type v) (p : Nat) where
  buffer : BoundedWord α p
  rootState : Q
  offset : Fin p
  valid : Bool
  pastRoot : Bool

def periodMonitorBoolEnumeration : Enumeration Bool where
  values := [false, true]
  complete := by intro b; cases b <;> simp

def periodMonitorStateEnumeration
    (alphabet : Enumeration α) (states : Enumeration Q)
    (p : Nat) :
    Enumeration (PeriodMonitorState α Q p) :=
  (((((boundedWordEnumeration alphabet p).product states).product
      (finEnumeration p)).product periodMonitorBoolEnumeration).product
      periodMonitorBoolEnumeration).mapOnto
    (fun value =>
      {
        buffer := value.1.1.1.1
        rootState := value.1.1.1.2
        offset := value.1.1.2
        valid := value.1.2
        pastRoot := value.2
      })
    (fun state =>
      ((((state.buffer, state.rootState), state.offset), state.valid),
        state.pastRoot))
    (by intro state; cases state; rfl)

def periodMonitorAdvanceOffset
    {p : Nat} (hp : 0 < p) (offset : Fin p) : Fin p :=
  ⟨(offset.1 + 1) % p, Nat.mod_lt _ hp⟩

def periodMonitorStep
    [DecidableEq α]
    (A : DFA α Q) {p : Nat} (hp : 0 < p)
    (state : PeriodMonitorState α Q p) (letter : α) :
    PeriodMonitorState α Q p :=
  if hfill : state.buffer.word.length < p then
    {
      buffer :=
        ⟨state.buffer.word ++ [letter], by
          simp only [List.length_append, List.length_singleton]
          omega⟩
      rootState := A.step state.rootState letter
      offset := state.offset
      valid := state.valid
      pastRoot := state.pastRoot
    }
  else
    have hlength : state.buffer.word.length = p := by
      have hle := state.buffer.length_le
      omega
    let index : Fin state.buffer.word.length :=
      ⟨state.offset.1, by rw [hlength]; exact state.offset.2⟩
    {
      buffer := state.buffer
      rootState := state.rootState
      offset := periodMonitorAdvanceOffset hp state.offset
      valid := state.valid && decide (letter = state.buffer.word.get index)
      pastRoot := true
    }

/-- The fixed-positive-period DFA from Lemma 2.1. -/
def boundedPeriodDFA
    [DecidableEq α]
    (root : DFA α Q) (p : Nat) (hp : 0 < p) :
    DFA α (PeriodMonitorState α Q p) where
  start :=
    {
      buffer := ⟨[], by simp⟩
      rootState := root.start
      offset := ⟨0, hp⟩
      valid := true
      pastRoot := false
    }
  step := periodMonitorStep root hp
  accept := fun state =>
    state.buffer.word.length = p ∧
    state.pastRoot = true ∧
    state.valid = true ∧
    root.accept state.rootState

/-- The structural part of the streaming run invariant. -/
def PeriodMonitorCoreInvariant
    (root : DFA α Q) (p : Nat)
    (read : Word α) (state : PeriodMonitorState α Q p) : Prop :=
  state.buffer.word = read.take p ∧
  state.rootState = root.run (read.take p) ∧
  state.pastRoot = decide (p < read.length)

theorem periodMonitor_start_invariant
    [DecidableEq α]
    (root : DFA α Q) (p : Nat) (hp : 0 < p) :
    PeriodMonitorCoreInvariant root p []
      (boundedPeriodDFA root p hp).start := by
  simp [PeriodMonitorCoreInvariant, boundedPeriodDFA, DFA.run]

theorem periodMonitorStep_coreInvariant
    [DecidableEq α]
    (root : DFA α Q) {p : Nat} (hp : 0 < p)
    (read : Word α) (state : PeriodMonitorState α Q p)
    (hinvariant : PeriodMonitorCoreInvariant root p read state)
    (letter : α) :
    PeriodMonitorCoreInvariant root p (read ++ [letter])
      (periodMonitorStep root hp state letter) := by
  rcases hinvariant with ⟨hbuffer, hroot, hpast⟩
  unfold periodMonitorStep
  split
  · rename_i hfill
    have hread : read.length < p := by
      rw [hbuffer] at hfill
      simp only [List.length_take] at hfill
      omega
    have htake :
        (read ++ [letter]).take p = read.take p ++ [letter] := by
      have hreadle : read.length ≤ p := Nat.le_of_lt hread
      have happendle : (read ++ [letter]).length ≤ p := by
        simp only [List.length_append, List.length_singleton]
        omega
      rw [List.take_of_length_le happendle,
        List.take_of_length_le hreadle]
    refine ⟨?_, ?_, ?_⟩
    · simpa [hbuffer] using htake.symm
    · rw [htake, root.run_append, hroot]
      rfl
    · rw [hpast]
      simp only [List.length_append, List.length_singleton]
      have hnotPast : ¬p < read.length := by omega
      have hnew : ¬p < read.length + 1 := by omega
      simp [hnotPast, hnew]
  · rename_i hfull
    have hread : p ≤ read.length := by
      rw [hbuffer] at hfull
      simp only [List.length_take] at hfull
      omega
    have htake :
        (read ++ [letter]).take p = read.take p := by
      rw [List.take_append_of_le_length hread]
    refine ⟨?_, ?_, ?_⟩
    · simp [hbuffer, htake]
    · simp [hroot, htake]
    · simp only [List.length_append, List.length_singleton]
      simp [show p < read.length + 1 by omega]

/--
The core invariant holds after every run prefix.  This already proves that
the finite buffer and root-DFA state have their intended meanings.
-/
theorem boundedPeriodDFA_run_coreInvariant
    [DecidableEq α]
    (root : DFA α Q) (p : Nat) (hp : 0 < p)
    (w : Word α) :
    PeriodMonitorCoreInvariant root p w
      ((boundedPeriodDFA root p hp).run w) := by
  have aux :
      ∀ (read suffix : Word α) (state : PeriodMonitorState α Q p),
        PeriodMonitorCoreInvariant root p read state →
        PeriodMonitorCoreInvariant root p (read ++ suffix)
          ((boundedPeriodDFA root p hp).runFrom state suffix) := by
    intro read suffix
    induction suffix generalizing read with
    | nil =>
        intro state hinvariant
        simpa using hinvariant
    | cons letter suffix ih =>
        intro state hinvariant
        rw [DFA.runFrom_cons]
        have hstep :=
          periodMonitorStep_coreInvariant root hp
            read state hinvariant letter
        simpa [List.append_assoc] using
          ih (read ++ [letter])
            (periodMonitorStep root hp state letter) hstep
  unfold DFA.run
  simpa using aux [] w (boundedPeriodDFA root p hp).start
    (periodMonitor_start_invariant root p hp)

/-- Any accepted monitor word is longer than the root and its root is accepted. -/
theorem boundedPeriodDFA_accepts_root
    [DecidableEq α]
    (root : DFA α Q) (p : Nat) (hp : 0 < p)
    (w : Word α)
    (haccept : (boundedPeriodDFA root p hp).Accepts w) :
    p < w.length ∧ root.Accepts (w.take p) := by
  have hinvariant :=
    boundedPeriodDFA_run_coreInvariant root p hp w
  rcases hinvariant with ⟨hbuffer, hroot, hpast⟩
  rcases haccept with ⟨hfill, hpastTrue, hvalid, hrootAccept⟩
  constructor
  · rw [hpast] at hpastTrue
    simpa using hpastTrue
  · unfold DFA.Accepts
    rw [← hroot]
    exact hrootAccept

/--
When the validity bit is true, the consumed input is an exact number of
buffer powers followed by the buffer prefix ending at the cyclic offset.
-/
def PeriodMonitorPowerInvariant
    (root : DFA α Q) (p : Nat)
    (read : Word α) (state : PeriodMonitorState α Q p) : Prop :=
  PeriodMonitorCoreInvariant root p read state ∧
  (read.length ≤ p → state.offset.1 = 0) ∧
  (state.valid = true →
    ∃ k, read =
      Language.wordPower state.buffer.word k ++
        state.buffer.word.take state.offset.1)

theorem periodMonitor_start_powerInvariant
    [DecidableEq α]
    (root : DFA α Q) (p : Nat) (hp : 0 < p) :
    PeriodMonitorPowerInvariant root p []
      (boundedPeriodDFA root p hp).start := by
  refine ⟨periodMonitor_start_invariant root p hp, ?_, ?_⟩
  · intro
    rfl
  · intro
    exact ⟨0, rfl⟩

theorem periodMonitorStep_powerInvariant
    [DecidableEq α]
    (root : DFA α Q) {p : Nat} (hp : 0 < p)
    (read : Word α) (state : PeriodMonitorState α Q p)
    (hinvariant : PeriodMonitorPowerInvariant root p read state)
    (letter : α) :
    PeriodMonitorPowerInvariant root p (read ++ [letter])
      (periodMonitorStep root hp state letter) := by
  rcases hinvariant with ⟨hcore, hoffsetShort, hpower⟩
  have hcoreNext :=
    periodMonitorStep_coreInvariant root hp read state hcore letter
  refine ⟨hcoreNext, ?_, ?_⟩
  · intro hnewLength
    unfold periodMonitorStep
    split
    · rename_i hfill
      have hreadLength : read.length ≤ p := by
        simp only [List.length_append, List.length_singleton] at hnewLength
        omega
      exact hoffsetShort hreadLength
    · rename_i hfull
      have hreadLength : p ≤ read.length := by
        rcases hcore with ⟨hbuffer, -, -⟩
        rw [hbuffer] at hfull
        simp only [List.length_take] at hfull
        omega
      simp only [List.length_append, List.length_singleton] at hnewLength
      omega
  · intro hvalidNext
    unfold periodMonitorStep at hvalidNext ⊢
    split at hvalidNext
    · rename_i hfill
      simp only [dif_pos hfill]
      have hreadLength : read.length < p := by
        rcases hcore with ⟨hbuffer, -, -⟩
        rw [hbuffer] at hfill
        simp only [List.length_take] at hfill
        omega
      have hnewLength : (read ++ [letter]).length ≤ p := by
        simp only [List.length_append, List.length_singleton]
        omega
      have hbufferNext :
          state.buffer.word ++ [letter] = read ++ [letter] := by
        rcases hcore with ⟨hbuffer, -, -⟩
        rw [hbuffer, List.take_of_length_le (Nat.le_of_lt hreadLength)]
      have hoffset : state.offset.1 = 0 :=
        hoffsetShort (Nat.le_of_lt hreadLength)
      refine ⟨1, ?_⟩
      simp [Language.wordPower, hbufferNext, hoffset]
    · rename_i hfull
      simp only [dif_neg hfull]
      have hbufferLength : state.buffer.word.length = p := by
        have hle := state.buffer.length_le
        omega
      have holdValid : state.valid = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hvalidNext
        exact hvalidNext.1
      have hletter :
          letter =
            state.buffer.word.get
              ⟨state.offset.1, by
                rw [hbufferLength]
                exact state.offset.2⟩ := by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hvalidNext
        exact hvalidNext.2
      obtain ⟨k, hdecomp⟩ := hpower holdValid
      by_cases hnext : state.offset.1 + 1 < p
      · refine ⟨k, ?_⟩
        have hadvance :
            (periodMonitorAdvanceOffset hp state.offset).1 =
              state.offset.1 + 1 := by
          simp [periodMonitorAdvanceOffset,
            Nat.mod_eq_of_lt hnext]
        rw [hadvance]
        have htakeSucc :=
          List.take_succ_eq_append_getElem
            (l := state.buffer.word)
            (i := state.offset.1)
            (by simp [hbufferLength, state.offset.2])
        rw [hdecomp, List.append_assoc]
        apply congrArg
        calc
          state.buffer.word.take state.offset.1 ++ [letter] =
              state.buffer.word.take state.offset.1 ++
                [state.buffer.word.get
                  ⟨state.offset.1, by
                    rw [hbufferLength]
                    exact state.offset.2⟩] := by rw [hletter]
          _ = state.buffer.word.take (state.offset.1 + 1) := by
                exact htakeSucc.symm
      · have hboundary : state.offset.1 + 1 = p := by
          omega
        refine ⟨k + 1, ?_⟩
        have hadvance :
            (periodMonitorAdvanceOffset hp state.offset).1 = 0 := by
          simp [periodMonitorAdvanceOffset, hboundary]
        rw [hadvance, List.take_zero, List.append_nil,
          Language.wordPower_succ_right]
        have htakeSucc :=
          List.take_succ_eq_append_getElem
            (l := state.buffer.word)
            (i := state.offset.1)
            (by simp [hbufferLength, state.offset.2])
        calc
          read ++ [letter] =
              (Language.wordPower state.buffer.word k ++
                state.buffer.word.take state.offset.1) ++
                [letter] := by rw [hdecomp]
          _ = Language.wordPower state.buffer.word k ++
                (state.buffer.word.take state.offset.1 ++
                  [letter]) := by simp [List.append_assoc]
          _ = Language.wordPower state.buffer.word k ++
                state.buffer.word.take (state.offset.1 + 1) := by
                  apply congrArg
                  calc
                    state.buffer.word.take state.offset.1 ++ [letter] =
                        state.buffer.word.take state.offset.1 ++
                          [state.buffer.word.get
                            ⟨state.offset.1, by
                              rw [hbufferLength]
                              exact state.offset.2⟩] := by rw [hletter]
                    _ = state.buffer.word.take
                        (state.offset.1 + 1) := by
                          exact htakeSucc.symm
          _ = Language.wordPower state.buffer.word k ++
                state.buffer.word := by
                  rw [hboundary,
                    List.take_of_length_le (by
                      rw [hbufferLength]
                      exact Nat.le_refl p)]

/-- The power-decomposition invariant holds after every input word. -/
theorem boundedPeriodDFA_run_powerInvariant
    [DecidableEq α]
    (root : DFA α Q) (p : Nat) (hp : 0 < p)
    (w : Word α) :
    PeriodMonitorPowerInvariant root p w
      ((boundedPeriodDFA root p hp).run w) := by
  have aux :
      ∀ (read suffix : Word α) (state : PeriodMonitorState α Q p),
        PeriodMonitorPowerInvariant root p read state →
        PeriodMonitorPowerInvariant root p (read ++ suffix)
          ((boundedPeriodDFA root p hp).runFrom state suffix) := by
    intro read suffix
    induction suffix generalizing read with
    | nil =>
        intro state hinvariant
        simpa using hinvariant
    | cons letter suffix ih =>
        intro state hinvariant
        rw [DFA.runFrom_cons]
        have hstep :=
          periodMonitorStep_powerInvariant root hp
            read state hinvariant letter
        simpa [List.append_assoc] using
          ih (read ++ [letter])
            (periodMonitorStep root hp state letter) hstep
  unfold DFA.run
  simpa using aux [] w (boundedPeriodDFA root p hp).start
    (periodMonitor_start_powerInvariant root p hp)

/-- Soundness of the validity check: every accepted monitor word has period `p`. -/
theorem boundedPeriodDFA_accepts_hasPeriod
    [DecidableEq α]
    (root : DFA α Q) (p : Nat) (hp : 0 < p)
    (w : Word α)
    (haccept : (boundedPeriodDFA root p hp).Accepts w) :
    Word.HasPeriod w p := by
  have hinvariant :=
    boundedPeriodDFA_run_powerInvariant root p hp w
  have hpw :=
    (boundedPeriodDFA_accepts_root root p hp w haccept).1
  rcases hinvariant with ⟨hcore, hoffset, hpower⟩
  rcases hcore with ⟨hbuffer, hroot, hpast⟩
  rcases haccept with ⟨hfill, hpastTrue, hvalid, hrootAccept⟩
  obtain ⟨k, hdecomp⟩ := hpower hvalid
  have hprefix :
      ∃ repetitions tail,
        Language.wordPower (w.take p) repetitions = w ++ tail := by
    let monitor := (boundedPeriodDFA root p hp).run w
    let offset := monitor.offset.1
    have hpowMonitor :
        Language.wordPower monitor.buffer.word (k + 1) =
          w ++ monitor.buffer.word.drop offset := by
      calc
        Language.wordPower monitor.buffer.word (k + 1) =
            Language.wordPower monitor.buffer.word k ++
              monitor.buffer.word :=
                Language.wordPower_succ_right _ _
        _ = (Language.wordPower monitor.buffer.word k ++
              monitor.buffer.word.take offset) ++
              monitor.buffer.word.drop offset := by
                simp [List.append_assoc]
        _ = w ++ monitor.buffer.word.drop offset := by
                rw [← hdecomp]
    rw [hbuffer] at hpowMonitor
    refine ⟨k + 1, (w.take p).drop offset, ?_⟩
    exact hpowMonitor
  obtain ⟨repetitions, tail, hprefixPower⟩ := hprefix
  have hrootLength : (w.take p).length = p := by
    rw [← hbuffer]
    exact hfill
  have hresult := (Language.period_of_prefix_wordPower
    (w.take p) w tail repetitions
    (by rw [hrootLength]; exact hp)
    (by rw [hrootLength]; exact hpw)
    hprefixPower).2
  rw [hrootLength] at hresult
  exact hresult

/--
While the root buffer is still being filled, validity and the cyclic
offset are unchanged and the buffer length grows by the suffix length.
-/
theorem periodMonitor_runFrom_filling
    [DecidableEq α]
    (root : DFA α Q) {p : Nat} (hp : 0 < p)
    (state : PeriodMonitorState α Q p) (suffix : Word α)
    (hbound :
      state.buffer.word.length + suffix.length ≤ p) :
    let final :=
      (boundedPeriodDFA root p hp).runFrom state suffix
    final.buffer.word.length =
        state.buffer.word.length + suffix.length ∧
      final.valid = state.valid ∧
      final.offset = state.offset := by
  induction suffix generalizing state with
  | nil =>
      simp
  | cons letter suffix ih =>
      have hfill : state.buffer.word.length < p := by
        simp only [List.length_cons] at hbound
        omega
      rw [DFA.runFrom_cons]
      have hstep :
          periodMonitorStep root hp state letter =
            {
              buffer :=
                ⟨state.buffer.word ++ [letter], by
                  simp only [List.length_append,
                    List.length_singleton]
                  omega⟩
              rootState := root.step state.rootState letter
              offset := state.offset
              valid := state.valid
              pastRoot := state.pastRoot
            } := by
        simp [periodMonitorStep, hfill]
      have htailBound :
          (state.buffer.word ++ [letter]).length +
              suffix.length ≤ p := by
        simp at hbound ⊢
        omega
      simpa [boundedPeriodDFA, hstep,
        List.length_append, List.length_singleton,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih
          {
            buffer :=
              ⟨state.buffer.word ++ [letter], by
                simp only [List.length_append,
                  List.length_singleton]
                omega⟩
            rootState := root.step state.rootState letter
            offset := state.offset
            valid := state.valid
            pastRoot := state.pastRoot
          }
          htailBound

theorem boundedPeriodDFA_run_short_valid
    [DecidableEq α]
    (root : DFA α Q) (p : Nat) (hp : 0 < p)
    (w : Word α) (hw : w.length ≤ p) :
    let state := (boundedPeriodDFA root p hp).run w
    state.valid = true ∧ state.offset.1 = 0 := by
  have hfill :=
    periodMonitor_runFrom_filling root hp
      (boundedPeriodDFA root p hp).start w
        (by simpa [boundedPeriodDFA] using hw)
  exact ⟨hfill.2.1, congrArg Fin.val hfill.2.2⟩

/--
Once the buffer is full, reading the letter at the current cyclic offset
preserves validity and advances exactly to the next offset.
-/
theorem periodMonitorStep_expected
    [DecidableEq α]
    (root : DFA α Q) {p : Nat} (hp : 0 < p)
    (state : PeriodMonitorState α Q p)
    (hfull : state.buffer.word.length = p)
    (hvalid : state.valid = true) :
    let index : Fin state.buffer.word.length :=
      ⟨state.offset.1, by rw [hfull]; exact state.offset.2⟩
    let next :=
      periodMonitorStep root hp state
        (state.buffer.word.get index)
    next.buffer = state.buffer ∧
      next.valid = true ∧
      next.offset = periodMonitorAdvanceOffset hp state.offset := by
  simp [periodMonitorStep, hfull, hvalid]

/-- A full root buffer, used to define the canonical cyclic continuation. -/
structure FullPeriodRoot (α : Type u) (p : Nat) where
  word : Word α
  length_eq : word.length = p

def periodOffsetAfter
    {p : Nat} (hp : 0 < p) : Nat → Fin p → Fin p
  | 0, offset => offset
  | n + 1, offset =>
      periodOffsetAfter hp n (periodMonitorAdvanceOffset hp offset)

/-- The next `n` letters prescribed by a root and an initial cyclic offset. -/
def periodExpectedWord
    (root : FullPeriodRoot α p) (hp : 0 < p) :
    Fin p → Nat → Word α
  | _, 0 => []
  | offset, n + 1 =>
      let index : Fin root.word.length :=
        ⟨offset.1, by rw [root.length_eq]; exact offset.2⟩
      root.word.get index ::
        periodExpectedWord root hp
          (periodMonitorAdvanceOffset hp offset) n

@[simp] theorem periodExpectedWord_zero
    (root : FullPeriodRoot α p) (hp : 0 < p)
    (offset : Fin p) :
    periodExpectedWord root hp offset 0 = [] := rfl

@[simp] theorem periodExpectedWord_succ
    (root : FullPeriodRoot α p) (hp : 0 < p)
    (offset : Fin p) (n : Nat) :
    periodExpectedWord root hp offset (n + 1) =
      root.word.get
          ⟨offset.1, by rw [root.length_eq]; exact offset.2⟩ ::
        periodExpectedWord root hp
          (periodMonitorAdvanceOffset hp offset) n := rfl

@[simp] theorem periodExpectedWord_length
    (root : FullPeriodRoot α p) (hp : 0 < p) :
    ∀ (offset : Fin p) (n : Nat),
      (periodExpectedWord root hp offset n).length = n := by
  intro offset n
  induction n generalizing offset with
  | zero => rfl
  | succ n ih =>
      simp [periodExpectedWord_succ, ih]

/--
Reading the canonical expected trace from a full valid monitor preserves
the buffer and validity for any finite length.
-/
theorem periodMonitor_runFrom_expected
    [DecidableEq α]
    (automaton : DFA α Q)
    (root : FullPeriodRoot α p) (hp : 0 < p) :
    ∀ (n : Nat) (state : PeriodMonitorState α Q p)
      (offset : Fin p),
      state.buffer.word = root.word →
      state.valid = true →
      state.offset = offset →
      let final :=
        (boundedPeriodDFA automaton p hp).runFrom state
          (periodExpectedWord root hp offset n)
      final.buffer.word = root.word ∧
        final.valid = true ∧
        final.offset = periodOffsetAfter hp n offset := by
  intro n
  induction n with
  | zero =>
      intro state offset hbuffer hvalid hoffset
      simp [hbuffer, hvalid, hoffset, periodOffsetAfter]
  | succ n ih =>
      intro state offset hbuffer hvalid hoffset
      rw [periodExpectedWord_succ, DFA.runFrom_cons]
      let index : Fin root.word.length :=
        ⟨offset.1, by rw [root.length_eq]; exact offset.2⟩
      have hfull : state.buffer.word.length = p := by
        rw [hbuffer, root.length_eq]
      have hstep :=
        periodMonitorStep_expected automaton hp state hfull hvalid
      have hletter :
          root.word.get index =
            state.buffer.word.get
              ⟨state.offset.1, by rw [hfull]; exact state.offset.2⟩ := by
        subst offset
        have hopt :=
          congrArg (fun word => word[state.offset.1]?) hbuffer
        simp [hfull, root.length_eq, state.offset.2] at hopt
        simpa using hopt.symm
      rw [hletter]
      have hnextBuffer :
          (periodMonitorStep automaton hp state
            (state.buffer.word.get
              ⟨state.offset.1, by rw [hfull]; exact state.offset.2⟩)).buffer.word =
            root.word := by
        rw [hstep.1, hbuffer]
      have hnextValid :
          (periodMonitorStep automaton hp state
            (state.buffer.word.get
              ⟨state.offset.1, by rw [hfull]; exact state.offset.2⟩)).valid =
            true := hstep.2.1
      have hnextOffset :
          (periodMonitorStep automaton hp state
            (state.buffer.word.get
              ⟨state.offset.1, by rw [hfull]; exact state.offset.2⟩)).offset =
            periodMonitorAdvanceOffset hp offset := by
        rw [hstep.2.2, hoffset]
      simpa [periodOffsetAfter] using
        ih
          (periodMonitorStep automaton hp state
            (state.buffer.word.get
              ⟨state.offset.1, by rw [hfull]; exact state.offset.2⟩))
          (periodMonitorAdvanceOffset hp offset)
          hnextBuffer hnextValid hnextOffset

/--
Every nonempty canonical cyclic continuation of an accepted root is
accepted by the fixed-period monitor.
-/
theorem boundedPeriodDFA_accepts_expected
    [DecidableEq α]
    (automaton : DFA α Q)
    (root : FullPeriodRoot α p) (hp : 0 < p)
    (hrootAccept : automaton.Accepts root.word)
    (n : Nat) (hn : 0 < n) :
    (boundedPeriodDFA automaton p hp).Accepts
      (root.word ++
        periodExpectedWord root hp ⟨0, hp⟩ n) := by
  let monitor := boundedPeriodDFA automaton p hp
  let rootState := monitor.run root.word
  have hrootCore :=
    boundedPeriodDFA_run_coreInvariant automaton p hp root.word
  have hrootShort :=
    boundedPeriodDFA_run_short_valid automaton p hp root.word
      (by rw [root.length_eq]; exact Nat.le_refl p)
  have hrootBuffer : rootState.buffer.word = root.word := by
    dsimp [rootState, monitor]
    exact hrootCore.1.trans <| by
      rw [List.take_of_length_le (by
        rw [root.length_eq]
        exact Nat.le_refl p)]
  have hrootValid : rootState.valid = true := hrootShort.1
  have hrootOffset : rootState.offset = (⟨0, hp⟩ : Fin p) := by
    apply Fin.eq_of_val_eq
    exact hrootShort.2
  have htrace :=
    periodMonitor_runFrom_expected automaton root hp n rootState
      ⟨0, hp⟩ hrootBuffer hrootValid hrootOffset
  have hrun :
      monitor.run
          (root.word ++ periodExpectedWord root hp ⟨0, hp⟩ n) =
        monitor.runFrom rootState
          (periodExpectedWord root hp ⟨0, hp⟩ n) := by
    exact monitor.run_append _ _
  have hwholeCore :=
    boundedPeriodDFA_run_coreInvariant automaton p hp
      (root.word ++ periodExpectedWord root hp ⟨0, hp⟩ n)
  unfold DFA.Accepts
  rw [hrun]
  refine ⟨?_, ?_, htrace.2.1, ?_⟩
  · rw [htrace.1, root.length_eq]
  · have hpast := hwholeCore.2.2
    rw [hrun] at hpast
    rw [hpast]
    simp [root.length_eq, hn]
  · have hstoredRoot := hwholeCore.2.1
    rw [hrun] at hstoredRoot
    rw [hstoredRoot]
    have htake :
        (root.word ++
            periodExpectedWord root hp ⟨0, hp⟩ n).take p =
          root.word := by
      rw [List.take_append_of_le_length (by
        rw [root.length_eq]
        exact Nat.le_refl p),
        List.take_of_length_le (by
          rw [root.length_eq]
          exact Nat.le_refl p)]
    rw [htake]
    exact hrootAccept

/-- A period equality identifies the suffix after one root block. -/
theorem Word.drop_eq_take_of_hasPeriod
    (w : Word α) (p : Nat)
    (hperiod : Word.HasPeriod w p) :
    w.drop p = w.take (w.length - p) := by
  have heq := hperiod.2
  unfold Word.factor at heq
  have htakeDrop :
      (w.drop p).take (w.length - p) = w.drop p := by
    apply List.take_of_length_le
    simp
  rw [htakeDrop] at heq
  exact heq.symm

/--
A finite periodic word is uniquely determined by its length and its first
period block.
-/
theorem Word.eq_of_hasPeriod_of_length_eq_of_take_eq
    (p : Nat) (hp : 0 < p)
    (x y : Word α)
    (hxPeriod : Word.HasPeriod x p)
    (hyPeriod : Word.HasPeriod y p)
    (hlength : x.length = y.length)
    (hroot : x.take p = y.take p) :
    x = y := by
  suffices ∀ n, ∀ x y : Word α,
      x.length = n → y.length = n →
      Word.HasPeriod x p → Word.HasPeriod y p →
      x.take p = y.take p → x = y by
    exact this x.length x y rfl hlength.symm
      hxPeriod hyPeriod hroot
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro x y hxlen hylen hxPeriod hyPeriod hroot
      have hpn : p < n := by
        rw [← hxlen]
        exact hxPeriod.1
      have hxDrop :
          x.drop p = x.take (n - p) := by
        rw [← hxlen]
        exact Word.drop_eq_take_of_hasPeriod x p hxPeriod
      have hyDrop :
          y.drop p = y.take (n - p) := by
        rw [← hylen]
        exact Word.drop_eq_take_of_hasPeriod y p hyPeriod
      have hprefix :
          x.take (n - p) = y.take (n - p) := by
        by_cases hlong : p < n - p
        · have hxPrefixPeriod :
              Word.HasPeriod (x.take (n - p)) p := by
            apply Language.hasPeriod_take x hxPeriod hlong
            omega
          have hyPrefixPeriod :
              Word.HasPeriod (y.take (n - p)) p := by
            apply Language.hasPeriod_take y hyPeriod hlong
            omega
          have hxPrefixLen :
              (x.take (n - p)).length = n - p := by
            rw [List.length_take, hxlen,
              Nat.min_eq_left (Nat.sub_le n p)]
          have hyPrefixLen :
              (y.take (n - p)).length = n - p := by
            rw [List.length_take, hylen,
              Nat.min_eq_left (Nat.sub_le n p)]
          have hprefixRoot :
              (x.take (n - p)).take p =
                (y.take (n - p)).take p := by
            simpa [List.take_take,
              Nat.min_eq_left (Nat.le_of_lt hlong)] using hroot
          exact ih (n - p) (by omega)
            (x.take (n - p)) (y.take (n - p))
            hxPrefixLen hyPrefixLen
            hxPrefixPeriod hyPrefixPeriod hprefixRoot
        · have hshort : n - p ≤ p := by omega
          calc
            x.take (n - p) =
                (x.take p).take (n - p) := by
                  simp [List.take_take,
                    Nat.min_eq_left hshort]
            _ = (y.take p).take (n - p) := by rw [hroot]
            _ = y.take (n - p) := by
                  simp [List.take_take,
                    Nat.min_eq_left hshort]
      calc
        x = x.take p ++ x.drop p :=
          (List.take_append_drop p x).symm
        _ = x.take p ++ x.take (n - p) := by rw [hxDrop]
        _ = y.take p ++ y.take (n - p) := by rw [hroot, hprefix]
        _ = y.take p ++ y.drop p := by rw [hyDrop]
        _ = y := List.take_append_drop p y

/-- Completeness of the fixed-period monitor. -/
theorem boundedPeriodDFA_complete
    [DecidableEq α]
    (automaton : DFA α Q) (p : Nat) (hp : 0 < p)
    (w : Word α)
    (hperiod : Word.HasPeriod w p)
    (hrootAccept : automaton.Accepts (w.take p)) :
    (boundedPeriodDFA automaton p hp).Accepts w := by
  have hpw : p < w.length := hperiod.1
  let root : FullPeriodRoot α p :=
    {
      word := w.take p
      length_eq := by
        simp [Nat.min_eq_left (Nat.le_of_lt hpw)]
    }
  let continuation :=
    periodExpectedWord root hp ⟨0, hp⟩ (w.length - p)
  let canonical := root.word ++ continuation
  have hn : 0 < w.length - p := by omega
  have hcanonicalAccept :
      (boundedPeriodDFA automaton p hp).Accepts canonical := by
    exact boundedPeriodDFA_accepts_expected
      automaton root hp hrootAccept (w.length - p) hn
  have hcanonicalPeriod : Word.HasPeriod canonical p :=
    boundedPeriodDFA_accepts_hasPeriod
      automaton p hp canonical hcanonicalAccept
  have hcanonicalLength : canonical.length = w.length := by
    dsimp [canonical, continuation]
    simp [root.length_eq]
    omega
  have hcanonicalRoot : canonical.take p = w.take p := by
    dsimp [canonical]
    rw [List.take_append_of_le_length (by
      rw [root.length_eq]
      exact Nat.le_refl p)]
    dsimp [root]
    rw [List.take_of_length_le (by
      simp only [List.length_take]
      exact Nat.min_le_left p w.length)]
  have heq : w = canonical :=
    Word.eq_of_hasPeriod_of_length_eq_of_take_eq
      p hp w canonical hperiod hcanonicalPeriod
      hcanonicalLength.symm hcanonicalRoot.symm
  rw [heq]
  exact hcanonicalAccept

end NSSE
