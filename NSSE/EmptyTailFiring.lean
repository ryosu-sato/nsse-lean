import NSSE.EmptyTailAutomaton

/-! # Empty-tail recognition with the original markers, guard and cut semantics -/

namespace NSSE.EmptyTailFiring

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks GuardedBlockRelation
open GuardedRowFiring SymbolicReachability

universe u v w
variable {L : FirstOrder.Language.{u, v}} {P : Type w} {n : Nat}

def semantics (R : Row L P n) (last : P) {D : Type*} [L.Structure D] (p : P → D) :
    EmptyTailAutomaton.Data D (Fin n) where
  T := R.dataNFA p
  left q r := (R.left q r).Realize p
  right q r := (R.right q r).Realize p
  guard x := R.guard.Realize (Sum.elim p ![x, p last])

def terminalMarked {D : Type*} (pref tail : List D) : List (D ⊕ Bool) :=
  (pref.map Sum.inl ++ .inr false :: tail.map Sum.inl) ++ [.inr true]

theorem accepts_terminalMarked (R : Row L P n) (last : P) {D : Type*} [L.Structure D]
    (p : P → D) (pref tail : List D) :
    (R.markedNFA p).Accepts (terminalMarked pref tail) ↔
      ∃ q z r, (R.dataNFA p).start q ∧ (R.dataNFA p).Runs q pref z ∧
        (R.left z r).Realize p ∧ (semantics R last p).Ending r tail := by
  constructor
  · rintro ⟨q, f, hq, hrun, hf⟩
    obtain ⟨y, hp, hy⟩ := (runs_append_singleton (R.markedNFA p) q f _ (.inr true)).mp hrun
    obtain ⟨z, r, hpre, hl, htail⟩ := (R.marked_runs_iff p q y pref tail false).mp hp
    exact ⟨q, z, r, hq, hpre, hl, y, htail, f, hy, hf⟩
  · rintro ⟨q, z, r, hq, hpre, hl, y, htail, f, hy, hf⟩
    have hp := (R.marked_runs_iff p q y pref tail false).mpr ⟨z, r, hpre, hl, htail⟩
    exact ⟨q, f, hq, hp.append (R.markedNFA p) (.cons hy (.nil f)), hf⟩

def Witness (R : Row L P n) (last : P) {D : Type*} [L.Structure D] (p : P → D) (xs : List D) : Prop :=
  ∃ pref x tail, xs = pref ++ x :: tail ∧ tail ≠ [] ∧
    R.guard.Realize (Sum.elim p ![x, p last]) ∧
    (R.markedNFA p).Accepts (terminalMarked (pref ++ [x]) tail)

theorem semantic_witness (R : Row L P n) (last : P) {D : Type*} [L.Structure D]
    (p : P → D) (xs : List D) :
    (semantics R last p).automaton.Accepts xs ↔ Witness R last p xs := by
  rw [EmptyTailAutomaton.Data.accepts_correct]
  constructor
  · rintro ⟨q, hq, pref, x, tail, z, r, he, hpre, hg, hl, hne, hend⟩
    exact ⟨pref, x, tail, he, hne, hg,
      (accepts_terminalMarked R last p (pref ++ [x]) tail).mpr ⟨q, z, r, hq, hpre, hl, hend⟩⟩
  · rintro ⟨pref, x, tail, he, hne, hg, hacc⟩
    obtain ⟨q, z, r, hq, hpre, hl, hend⟩ := (accepts_terminalMarked R last p (pref ++ [x]) tail).mp hacc
    exact ⟨q, hq, pref, x, tail, z, r, he, hpre, hg, hl, hne, hend⟩

theorem markedOn_eof {D : Type*} (seed : D) (body : List D) (j : Nat) :
    markedOn (seed :: body) (j + 1) (body.length + 1) =
      terminalMarked (seed :: body.take j) (body.drop j) := by
  rw [markedOn_body]
  have ht : (body.drop j).take (body.length - j) = body.drop j := by
    apply List.take_of_length_le
    simp
  simp only [ht, List.drop_length, List.map_nil, terminalMarked]

theorem witness_iff_emptyTail (R : Row L P n) (last : P) {D : Type*} [L.Structure D]
    (p : P → D) (seed : D) (body : List D) (hLast : lastOr seed (seed :: body) = p last) :
    Witness R last p (seed :: body) ↔ EmptyTailFires R p seed body := by
  constructor
  · rintro ⟨pref, x, tail, he, hne, hg, hacc⟩
    have hlen := congrArg List.length he
    simp only [List.length_cons, List.length_append] at hlen
    have htailpos := List.length_pos_iff.mpr hne
    have hj : pref.length < body.length := by omega
    have hp : seed :: body.take pref.length = pref ++ [x] := by
      have hp' := congrArg (List.take (pref.length + 1)) he
      simpa [List.take_append] using hp'
    have ht : body.drop pref.length = tail := by
      have ht' := congrArg (List.drop (pref.length + 1)) he
      simpa [List.drop_append] using ht'
    refine ⟨pref.length, hj, le_refl _, ?_, ?_, ?_⟩
    · rw [markedOn_eof, hp, ht]
      exact hacc
    · have hwhole : (seed :: body).take (body.length + 1) = seed :: body := by simp
      simp only [List.take_succ_cons, hp, lastOr_append_singleton, hwhole, hLast]
      simpa only [List.take_length, hLast] using hg
    · simp [OccursSuffixAt, Word.factor]
  · rintro ⟨j, hj, _, hacc, hg, _⟩
    let pre := seed :: body.take j
    have hpre : pre ≠ [] := by simp [pre]
    let pref := pre.dropLast
    let x := pre.getLast hpre
    have hp : pre = pref ++ [x] := (List.dropLast_concat_getLast hpre).symm
    have he : seed :: body = pref ++ x :: body.drop j := by
      have he' : seed :: body = pre ++ body.drop j := by simp [pre]
      rw [he', hp]
      simp [List.append_assoc]
    have hne : body.drop j ≠ [] := by
      apply List.length_pos_iff.mp
      simp only [List.length_drop]
      omega
    refine ⟨pref, x, body.drop j, he, hne, ?_, ?_⟩
    · have hleft : lastOr seed ((seed :: body).take (j + 1)) = x := by
        change lastOr seed pre = x
        rw [hp, lastOr_append_singleton]
      have hright : lastOr seed ((seed :: body).take (body.length + 1)) = p last := by
        simpa using hLast
      simpa only [hleft, hright] using hg
    · rw [markedOn_eof] at hacc
      change (R.markedNFA p).Accepts (terminalMarked pre (body.drop j)) at hacc
      rwa [hp] at hacc

def states (n : Nat) : List (EmptyTailAutomaton.State (Fin n)) :=
  (List.finRange n).flatMap fun q => [.before q, .needAfter q, .after q]

def stateAt (n : Nat) (i : Fin (states n).length) : EmptyTailAutomaton.State (Fin n) := (states n).get i

theorem stateAt_surjective (n : Nat) : Function.Surjective (stateAt n) := by
  intro s
  have hmem : s ∈ states n := by cases s <;> simp [states]
  exact List.mem_iff_get.mp hmem

theorem length_states (n : Nat) : (states n).length = 3 * n := by
  simp [states, List.length_flatMap, Nat.mul_comm]

def initialGuard (R : Row L P n) : EmptyTailAutomaton.State (Fin n) → L.Formula P
  | .before q => R.initial q
  | _ => ⊥

def finalGuard (R : Row L P n) : EmptyTailAutomaton.State (Fin n) → L.Formula P
  | .after q => any n (fun r => R.right q r ⊓ R.final r)
  | _ => ⊥

def switchGuard (R : Row L P n) (last : P) (q r : Fin n) : L.Formula (P ⊕ Fin 1) :=
  guardAt R.guard Sum.inl (Sum.inr 0) (Sum.inl last) ⊓
    any n (fun z => R.data q z ⊓ (R.left z r).relabel Sum.inl)

def dataGuard (R : Row L P n) (last : P) :
    EmptyTailAutomaton.State (Fin n) → EmptyTailAutomaton.State (Fin n) → L.Formula (P ⊕ Fin 1)
  | .before q, .before r => R.data q r
  | .before q, .needAfter r => switchGuard R last q r
  | .needAfter q, .after r => R.data q r
  | .after q, .after r => R.data q r
  | _, _ => ⊥

/-- Pure finite syntax, with exactly 3*n states. The left predecessor guard
is checked on the SAME data letter that precedes the guessed marker. -/
def compile (R : Row L P n) (last : P) : Row L P (states n).length where
  initial q := initialGuard R (stateAt n q)
  final q := finalGuard R (stateAt n q)
  data q r := dataGuard R last (stateAt n q) (stateAt n r)
  left _ _ := ⊥
  right _ _ := ⊥
  guard := ⊥

theorem switchGuard_correct (R : Row L P n) (last : P) {D : Type*} [L.Structure D]
    (p : P → D) (q r : Fin n) (x : D) :
    (switchGuard R last q r).Realize (Sum.elim p (fun _ => x)) ↔
      (semantics R last p).guard x ∧ ∃ z,
        (R.dataNFA p).step q x z ∧ (R.left z r).Realize p := by
  simp only [switchGuard, Formula.realize_inf, realize_guardAt, realize_any,
    Formula.realize_relabel, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  rfl

theorem initialGuard_correct (R : Row L P n) (last : P) {D : Type*} [L.Structure D]
    (p : P → D) (q : EmptyTailAutomaton.State (Fin n)) :
    (initialGuard R q).Realize p ↔ (semantics R last p).automaton.start q := by
  cases q <;> rfl

theorem finalGuard_correct (R : Row L P n) (last : P) {D : Type*} [L.Structure D]
    (p : P → D) (q : EmptyTailAutomaton.State (Fin n)) :
    (finalGuard R q).Realize p ↔ (semantics R last p).automaton.accept q := by
  cases q <;> simp only [finalGuard, realize_any, Formula.realize_inf, Formula.realize_bot,
    EmptyTailAutomaton.Data.automaton, semantics, Row.dataNFA]

theorem dataGuard_correct (R : Row L P n) (last : P) {D : Type*} [L.Structure D]
    (p : P → D) (q r : EmptyTailAutomaton.State (Fin n)) (x : D) :
    (dataGuard R last q r).Realize (Sum.elim p (fun _ => x)) ↔
      (semantics R last p).automaton.step q x r := by
  cases q <;> cases r <;>
    simp only [dataGuard, switchGuard_correct, Formula.realize_bot,
      EmptyTailAutomaton.Data.automaton, semantics, Row.dataNFA]

theorem compile_interpret (R : Row L P n) (last : P) {D : Type*} [L.Structure D] (p : P → D) :
    (compile R last).dataNFA p =
      SymbolicComplement.pullback (semantics R last p).automaton (stateAt n) := by
  unfold Row.dataNFA compile SymbolicComplement.pullback
  congr 1
  · funext q
    exact propext (initialGuard_correct R last p _)
  · funext q x r
    exact propext (dataGuard_correct R last p _ _ x)
  · funext q
    exact propext (finalGuard_correct R last p _)

theorem compile_witness (R : Row L P n) (last : P) {D : Type*} [L.Structure D]
    (p : P → D) (xs : List D) :
    ((compile R last).dataNFA p).Accepts xs ↔ Witness R last p xs := by
  rw [compile_interpret, SymbolicComplement.pullback_accepts _ _ (stateAt_surjective n), semantic_witness]

/-- Exact empty-tail firing recognition on the fixed last-letter slice.
The seed is arbitrary; every old parameter is shared on every edge. -/
theorem compile_correct (R : Row L P n) (last : P) {D : Type*} [L.Structure D]
    (p : P → D) (seed : D) (w : List D) :
    ((compile R last).dataNFA p).Accepts (seed :: (w ++ [p last])) ↔
      EmptyTailFires R p seed (w ++ [p last]) := by
  rw [compile_witness]
  apply witness_iff_emptyTail
  change lastOr seed ((seed :: w) ++ [p last]) = p last
  exact lastOr_append_singleton seed (p last) (seed :: w)

end NSSE.EmptyTailFiring
