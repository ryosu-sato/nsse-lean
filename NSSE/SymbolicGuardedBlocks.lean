import NSSE.GuardedBlockRelation
import Mathlib.Tactic.FinCases

/-! # Actual finite symbolic presentation of the local guarded block relation H -/

namespace NSSE.SymbolicGuardedBlocks

open FirstOrder FirstOrder.Language SymbolicAutomata ConvolutionShapes
open GuardedBlockRelation SymbolicReachability

universe u v w
variable {L : FirstOrder.Language.{u, v}} {P : Type w} {n : Nat}

structure Row (L : FirstOrder.Language.{u, v}) (P : Type w) (n : Nat) where
  initial : Fin n → L.Formula P
  final : Fin n → L.Formula P
  data : Fin n → Fin n → L.Formula (P ⊕ Fin 1)
  left : Fin n → Fin n → L.Formula P
  right : Fin n → Fin n → L.Formula P
  guard : L.Formula (P ⊕ Fin 2)

structure Ends (n : Nat) where
  leftStart : Fin n
  leftEnd : Fin n
  rightStart : Fin n
  rightEnd : Fin n

def dataAt {X : Type*} (f : L.Formula (P ⊕ Fin 1)) (rename : P → X) (x : X) : L.Formula X :=
  f.relabel (Sum.elim rename (fun _ => x))

theorem realize_dataAt {D X : Type*} [L.Structure D] (f : L.Formula (P ⊕ Fin 1))
    (rename : P → X) (x : X) (v : X → D) :
    (dataAt f rename x).Realize v ↔ f.Realize (Sum.elim (v ∘ rename) (fun _ => v x)) := by
  rw [dataAt, Formula.realize_relabel]
  have he : v ∘ Sum.elim rename (fun _ : Fin 1 => x) =
      Sum.elim (v ∘ rename) (fun _ => v x) := by
    funext i
    cases i <;> rfl
  rw [he]

def guardAt {X : Type*} (f : L.Formula (P ⊕ Fin 2)) (rename : P → X) (x y : X) : L.Formula X :=
  f.relabel (Sum.elim rename ![x, y])

theorem realize_guardAt {D X : Type*} [L.Structure D] (f : L.Formula (P ⊕ Fin 2))
    (rename : P → X) (x y : X) (v : X → D) :
    (guardAt f rename x y).Realize v ↔ f.Realize (Sum.elim (v ∘ rename) ![v x, v y]) := by
  rw [guardAt, Formula.realize_relabel]
  have he : v ∘ Sum.elim rename ![x, y] = Sum.elim (v ∘ rename) ![v x, v y] := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => fin_cases i <;> rfl
  rw [he]

def fallback (seed last : P) (first : Bool) : P := if first then seed else last

namespace Row

def dataNFA (R : Row L P n) {D : Type*} [L.Structure D] (p : P → D) : NSSE.NFA D (Fin n) where
  start q := (R.initial q).Realize p
  accept q := (R.final q).Realize p
  step q x r := (R.data q r).Realize (Sum.elim p (fun _ => x))

def semantics (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) : GuardedBlockRelation.Data D (Fin n) where
  T := R.dataNFA p
  left q r := (R.left q r).Realize p
  right q r := (R.right q r).Realize p
  guard x y := R.guard.Realize (Sum.elim p ![x, y])
  leftDefault := p (fallback seed last first)
  rightDefault := p last
  leftStart := e.leftStart
  rightStart := e.rightStart
  finish q := (R.dataNFA p).step q.1 (p last) e.leftEnd ∧ (R.dataNFA p).step q.2 (p last) e.rightEnd

def valueIndex (s : Shape 2) (i : Fin 2) (defval : P) : P ⊕ Fin (arity 2 s) :=
  if hi : mask s i = true then .inr (slot (mask s) i hi) else .inl defval

theorem realize_valueIndex {D : Type*} (p : P → D) (c : Sparse D 2) (i : Fin 2) (defval : P) :
    Sum.elim p c.2 (valueIndex c.1 i defval) = (toDense c i).getD (p defval) := by
  by_cases hi : mask c.1 i = true <;> simp [valueIndex, hi, toDense, expand]

def backGuard (R : Row L P n) (s : Shape 2) (q r : Fin n) (i : Fin 2) :
    L.Formula (P ⊕ Fin (arity 2 s)) :=
  if hi : mask s i = true then dataAt (R.data r q) Sum.inl (Sum.inr (slot (mask s) i hi))
  else if r = q then ⊤ else ⊥

theorem realize_backGuard (R : Row L P n) {D : Type*} [L.Structure D]
    (p : P → D) (c : Sparse D 2) (q r : Fin n) (i : Fin 2) :
    (R.backGuard c.1 q r i).Realize (Sum.elim p c.2) ↔
      BackStep (R.dataNFA p) q (toDense c i) r := by
  by_cases hi : mask c.1 i = true
  · simp [backGuard, hi, realize_dataAt, BackStep, toDense, expand, dataNFA, Function.comp_def]
  · by_cases hqr : r = q <;> simp [backGuard, hi, hqr, BackStep, toDense, expand]

def pairBackGuard (R : Row L P n) (s : Shape 2) (q r : PairState (Fin n)) :
    L.Formula (P ⊕ Fin (arity 2 s)) := R.backGuard s q.1 r.1 0 ⊓ R.backGuard s q.2 r.2 1

theorem realize_pairBackGuard (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (c : Sparse D 2) (q r : PairState (Fin n)) :
    (R.pairBackGuard c.1 q r).Realize (Sum.elim p c.2) ↔
      (R.semantics e seed last first p).backward q (toDense c) r := by
  simp only [pairBackGuard, Formula.realize_inf, realize_backGuard, Data.backward, semantics]

def sharedGuard (R : Row L P n) (s : Shape 2) (q r : PairState (Fin n)) :
    L.Formula (P ⊕ Fin (arity 2 s)) :=
  if mask s 0 = true ∧ mask s 1 = true then
    WordEqualityAutomaton.equalityGuard 0 1 s ⊓ R.pairBackGuard s q r
  else ⊥

theorem realize_sharedGuard (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (c : Sparse D 2) (q r : PairState (Fin n)) :
    (R.sharedGuard c.1 q r).Realize (Sum.elim p c.2) ↔
      (R.semantics e seed last first p).sharedStep q (toDense c) r := by
  by_cases h₀ : mask c.1 0 = true <;> by_cases h₁ : mask c.1 1 = true <;>
    simp [sharedGuard, h₀, h₁, WordEqualityAutomaton.realize_equalityGuard,
      realize_pairBackGuard R e seed last first, Data.sharedStep, toDense, expand, eq_comm]

def switchGuard (R : Row L P n) (s : Shape 2) (q r : PairState (Fin n))
    (seed last : P) (first : Bool) : L.Formula (P ⊕ Fin (arity 2 s)) :=
  guardAt R.guard Sum.inl (valueIndex s 0 (fallback seed last first)) (valueIndex s 1 last) ⊓
    any n (fun z => any n (fun z' =>
      (R.left z q.1).relabel Sum.inl ⊓ ((R.right z' q.2).relabel Sum.inl ⊓
        R.pairBackGuard s (z, z') r)))

theorem realize_switchGuard (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (c : Sparse D 2) (q r : PairState (Fin n)) :
    (R.switchGuard c.1 q r seed last first).Realize (Sum.elim p c.2) ↔
      (R.semantics e seed last first p).switch q (toDense c) r := by
  simp only [switchGuard, Formula.realize_inf, realize_guardAt, realize_valueIndex,
    realize_any, Formula.realize_relabel, realize_pairBackGuard R e seed last first]
  change (_ ∧ ∃ z z', _ ∧ _ ∧ _) ↔ (_ ∧ ∃ z : PairState (Fin n), _ ∧ _ ∧ _)
  constructor
  · rintro ⟨hg, z, z', hl, hr, hb⟩
    exact ⟨hg, (z, z'), hl, hr, hb⟩
  · rintro ⟨hg, ⟨z, z'⟩, hl, hr, hb⟩
    exact ⟨hg, z, z', hl, hr, hb⟩

end Row

def states (n : Nat) : List (State (Fin n)) :=
  (SymbolicConjunction.pairs n n).flatMap (fun q => [(false, q), (true, q)])

def stateAt (n : Nat) (i : Fin (states n).length) : State (Fin n) := (states n).get i

theorem stateAt_surjective (n : Nat) : Function.Surjective (stateAt n) := by
  rintro ⟨b, q⟩
  apply List.mem_iff_get.mp
  apply List.mem_flatMap.mpr
  obtain ⟨i, hi⟩ := SymbolicConjunction.decode_surjective n n q
  refine ⟨q, ?_, ?_⟩
  · rw [← hi]
    exact List.get_mem _ _
  · cases b <;> simp

theorem length_states (n : Nat) : (states n).length = 2 * n * n := by
  simp [states, List.length_flatMap, SymbolicConjunction.length_pairs, Nat.mul_comm, Nat.mul_assoc]

namespace Row

def initialGuard (R : Row L P n) (e : Ends n) (last : P) (q : State (Fin n)) : L.Formula P :=
  if q.1 then ⊥ else dataAt (R.data q.2.1 e.leftEnd) id last ⊓ dataAt (R.data q.2.2 e.rightEnd) id last

def finalGuard (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    (q : State (Fin n)) : L.Formula P :=
  if q.1 then if q.2 = (e.leftStart, e.rightStart) then ⊤ else ⊥
  else R.left e.leftStart q.2.1 ⊓ (R.right e.rightStart q.2.2 ⊓
    guardAt R.guard id (fallback seed last first) last)

def stepGuard (R : Row L P n) (s : Shape 2) (seed last : P) (first : Bool)
    (q r : State (Fin n)) : L.Formula (P ⊕ Fin (arity 2 s)) :=
  match q.1, r.1 with
  | false, false => R.sharedGuard s q.2 r.2
  | false, true => R.switchGuard s q.2 r.2 seed last first
  | true, true => R.pairBackGuard s q.2 r.2
  | true, false => ⊥

theorem realize_initialGuard (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (q : State (Fin n)) :
    (R.initialGuard e last q).Realize p ↔ (R.semantics e seed last first p).automaton.start q := by
  rcases q with ⟨b, q⟩
  cases b <;> simp [initialGuard, realize_dataAt, Data.automaton, semantics, dataNFA, Function.comp_def]

theorem realize_finalGuard (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (q : State (Fin n)) :
    (R.finalGuard e seed last first q).Realize p ↔ (R.semantics e seed last first p).automaton.accept q := by
  rcases q with ⟨b, q⟩
  cases b
  · simp [finalGuard, realize_guardAt, Data.automaton, Data.endSwitch, semantics, Function.comp_def]
  · by_cases hq : q = (e.leftStart, e.rightStart) <;>
      simp [finalGuard, hq, Data.automaton, semantics]

theorem realize_stepGuard (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (c : Sparse D 2) (q r : State (Fin n)) :
    (R.stepGuard c.1 seed last first q r).Realize (Sum.elim p c.2) ↔
      (R.semantics e seed last first p).automaton.step q (toDense c) r := by
  rcases q with ⟨b, q⟩
  rcases r with ⟨b', r⟩
  cases b <;> cases b' <;>
    simp only [stepGuard, Data.automaton, realize_sharedGuard R e seed last first,
      realize_switchGuard R e seed last first, realize_pairBackGuard R e seed last first,
      Formula.realize_bot]

/-- 2*n*n explicit phase/state pairs. Padding is inserted in compileH. -/
def raw (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool) :
    WordAutomaton L P (states n).length 2 where
  initial i := R.initialGuard e last (stateAt n i)
  final i := R.finalGuard e seed last first (stateAt n i)
  silent _ _ := ⊥
  step s i j := R.stepGuard s seed last first (stateAt n i) (stateAt n j)

theorem raw_dataInterpret (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) :
    (R.raw e seed last first).dataInterpret p = SymbolicComplement.pullback
      (mapInput (R.semantics e seed last first p).automaton toDense) (stateAt n) := by
  unfold raw Automaton.dataInterpret SymbolicComplement.pullback mapInput
  congr 1
  · funext q
    exact propext (R.realize_initialGuard e seed last first p _)
  · funext q c r
    exact propext (R.realize_stepGuard e seed last first p c _ _)
  · funext q
    exact propext (R.realize_finalGuard e seed last first p _)

theorem raw_correct (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (w : List (Sparse D 2)) :
    (R.raw e seed last first).Accepts p w ↔
      (R.semantics e seed last first p).automaton.Accepts (w.map toDense) := by
  rw [(R.raw e seed last first).accepts_iff_data_of_noSilent p (by intro q r; simp [raw]) w,
    R.raw_dataInterpret, SymbolicComplement.pullback_accepts _ _ (stateAt_surjective n), mapInput_accepts]

def compileH (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool) :=
  enforcePadding (R.raw e seed last first)

theorem compile_core (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (t : CanonicalConvolution.Tuple D 2) :
    tupleAccepts (R.compileH e seed last first) p t ↔
      ∃ q, (R.semantics e seed last first p).finish q ∧
        (R.semantics e seed last first p).core q (t 0) (t 1) := by
  rw [compileH, enforcePadding_tuple]
  unfold tupleAccepts denseAccepts
  rw [R.raw_correct]
  simp only [List.map_map, Function.comp_def, toDense_fromDense, List.map_id']
  rw [(R.semantics e seed last first p).accepts_correct _ (CanonicalConvolution.canonical_encode t)]
  simp only [CanonicalConvolution.decode_encode]

/-- The literal local witness relation of v1317 (5), including the final
delimiter and the predecessor guard at its original left/right cut. -/
def H (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (U V : List D) : Prop :=
  let G := R.semantics e seed last first p
  ∃ px py shared : List D, U = px ++ shared ∧ V = py ++ shared ∧
    G.guard (px.reverse.head?.getD G.leftDefault) (py.reverse.head?.getD G.rightDefault) ∧
    (∃ z b, G.T.Runs G.leftStart px z ∧ G.left z b ∧ G.T.Runs b (shared ++ [p last]) e.leftEnd) ∧
    (∃ z b, G.T.Runs G.rightStart py z ∧ G.right z b ∧ G.T.Runs b (shared ++ [p last]) e.rightEnd)

theorem H_iff_core (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (U V : List D) :
    R.H e seed last first p U V ↔
      ∃ q, (R.semantics e seed last first p).finish q ∧
        (R.semantics e seed last first p).core q U.reverse V.reverse := by
  let G := R.semantics e seed last first p
  constructor
  · rintro ⟨px, py, shared, rfl, rfl, hg, ⟨z, b, hp, hm, hs⟩, ⟨z', b', hp', hm', hs'⟩⟩
    obtain ⟨q, hshared, hlast⟩ := (runs_append_singleton G.T _ _ shared (p last)).mp hs
    obtain ⟨q', hshared', hlast'⟩ := (runs_append_singleton G.T _ _ shared (p last)).mp hs'
    refine ⟨(q, q'), ⟨hlast, hlast'⟩, shared.reverse, px.reverse, py.reverse,
      List.reverse_append, List.reverse_append, hg, ?_, ?_⟩
    · exact ⟨z, b, by simpa only [List.reverse_reverse] using hp, hm,
        by simpa only [List.reverse_reverse] using hshared⟩
    · exact ⟨z', b', by simpa only [List.reverse_reverse] using hp', hm',
        by simpa only [List.reverse_reverse] using hshared'⟩
  · rintro ⟨q, hfinish, shared, px, py, hx, hy, hg, ⟨z, b, hp, hm, hs⟩, ⟨z', b', hp', hm', hs'⟩⟩
    refine ⟨px.reverse, py.reverse, shared.reverse, ?_, ?_, ?_,
      ⟨z, b, hp, hm, hs.append G.T (.cons hfinish.1 (.nil _))⟩,
      ⟨z', b', hp', hm', hs'.append G.T (.cons hfinish.2 (.nil _))⟩⟩
    · simpa only [List.reverse_reverse, List.reverse_append] using congrArg List.reverse hx
    · simpa only [List.reverse_reverse, List.reverse_append] using congrArg List.reverse hy
    · simpa only [List.reverse_reverse] using hg

/-- The actual finite symbolic compiler recognizes exactly H on reversed
word convolution, for every fixed valuation and every pair of block words. -/
theorem compileH_correct (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (U V : List D) :
    tupleAccepts (R.compileH e seed last first) p ![U.reverse, V.reverse] ↔
      R.H e seed last first p U V := by
  rw [R.compile_core]
  exact (R.H_iff_core e seed last first p U V).symm

/-- The original row NFA, with false/true denoting its left/right marker. -/
def markedNFA (R : Row L P n) {D : Type*} [L.Structure D] (p : P → D) :
    NSSE.NFA (D ⊕ Bool) (Fin n) where
  start q := (R.initial q).Realize p
  accept q := (R.final q).Realize p
  step q x r := match x with
    | .inl a => (R.dataNFA p).step q a r
    | .inr false => (R.left q r).Realize p
    | .inr true => (R.right q r).Realize p

theorem data_runs_marked (R : Row L P n) {D : Type*} [L.Structure D]
    (p : P → D) (q r : Fin n) (w : List D) :
    (R.dataNFA p).Runs q w r ↔ (R.markedNFA p).Runs q (w.map Sum.inl) r :=
  mapInput_runs (R.markedNFA p) Sum.inl w q r

theorem marked_runs_iff (R : Row L P n) {D : Type*} [L.Structure D]
    (p : P → D) (q r : Fin n) (pref tail : List D) (marker : Bool) :
    (R.markedNFA p).Runs q (pref.map Sum.inl ++ Sum.inr marker :: tail.map Sum.inl) r ↔
      ∃ z b, (R.dataNFA p).Runs q pref z ∧
        (if marker then R.right z b else R.left z b).Realize p ∧ (R.dataNFA p).Runs b tail r := by
  rw [runs_append_iff]
  constructor
  · rintro ⟨z, hp, ht⟩
    cases ht with
    | cons hmarker htail =>
        refine ⟨z, _, (R.data_runs_marked p _ _ _).mpr hp, ?_,
          (R.data_runs_marked p _ _ _).mpr htail⟩
        cases marker <;> exact hmarker
  · rintro ⟨z, b, hp, hm, ht⟩
    refine ⟨z, (R.data_runs_marked p _ _ _).mp hp,
      .cons ?_ ((R.data_runs_marked p _ _ _).mp ht)⟩
    cases marker <;> exact hm

/-- H stated directly on the original marked NFA's two finite paths. -/
def LiteralH (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (U V : List D) : Prop :=
  ∃ px py shared : List D, U = px ++ shared ∧ V = py ++ shared ∧
    R.guard.Realize (Sum.elim p ![px.reverse.head?.getD (p (fallback seed last first)),
      py.reverse.head?.getD (p last)]) ∧
    (R.markedNFA p).Runs e.leftStart
      (px.map Sum.inl ++ Sum.inr false :: (shared ++ [p last]).map Sum.inl) e.leftEnd ∧
    (R.markedNFA p).Runs e.rightStart
      (py.map Sum.inl ++ Sum.inr true :: (shared ++ [p last]).map Sum.inl) e.rightEnd

theorem H_iff_literal (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (U V : List D) :
    R.H e seed last first p U V ↔ R.LiteralH e seed last first p U V := by
  simp only [H, LiteralH, R.marked_runs_iff, Bool.false_eq_true, ↓reduceIte, semantics]

/-- End-to-end local-relation theorem: finite FO syntax -> reversed word
convolution -> exact original marked paths, uniformly in all parameters. -/
theorem compileH_marked_correct (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (U V : List D) :
    tupleAccepts (R.compileH e seed last first) p ![U.reverse, V.reverse] ↔
      R.LiteralH e seed last first p U V :=
  (R.compileH_correct e seed last first p U V).trans (R.H_iff_literal e seed last first p U V)

end Row

end NSSE.SymbolicGuardedBlocks
