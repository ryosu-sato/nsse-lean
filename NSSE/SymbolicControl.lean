import NSSE.SymbolicComplement

/-!
# Effective intersection with finite shape control

The control reads column SHAPES only. It is synchronized after proved
epsilon elimination, so original silent edges do not advance the control.
An explicit finite state list is reindexed into the same symbolic datatype.
-/

namespace NSSE.SymbolicControl

open FirstOrder FirstOrder.Language SymbolicAutomata

universe u v w
variable {L : FirstOrder.Language.{u, v}} {P : Type w}

section SemanticProduct

variable {α Q R : Type*}

def product (A : NSSE.NFA α Q) (B : NSSE.DFA α R) : NSSE.NFA α (Q × R) where
  start s := A.start s.1 ∧ s.2 = B.start
  accept s := A.accept s.1 ∧ B.accept s.2
  step s a t := A.step s.1 a t.1 ∧ t.2 = B.step s.2 a

theorem product_run (A : NSSE.NFA α Q) (B : NSSE.DFA α R)
    {q r : Q} {w : List α} (h : A.Runs q w r) (s : R) :
    (product A B).Runs (q, s) w (r, B.runFrom s w) := by
  induction h generalizing s with
  | nil q => exact .nil (q, s)
  | cons hstep _ ih => exact .cons ⟨hstep, rfl⟩ (ih _)

theorem of_product_run (A : NSSE.NFA α Q) (B : NSSE.DFA α R)
    {s t : Q × R} {w : List α} (h : (product A B).Runs s w t) :
    A.Runs s.1 w t.1 ∧ t.2 = B.runFrom s.2 w := by
  induction h with
  | nil s => exact ⟨.nil s.1, rfl⟩
  | @cons s t u a w hstep _ ih =>
      refine ⟨.cons hstep.1 ih.1, ?_⟩
      rw [NSSE.DFA.runFrom_cons, ← hstep.2]
      exact ih.2

theorem product_accepts (A : NSSE.NFA α Q) (B : NSSE.DFA α R) (w : List α) :
    (product A B).Accepts w ↔ A.Accepts w ∧ B.Accepts w := by
  constructor
  · rintro ⟨s, t, ⟨hs, hsB⟩, hrun, ⟨ht, htB⟩⟩
    obtain ⟨ha, hb⟩ := of_product_run A B hrun
    refine ⟨⟨s.1, t.1, hs, ha, ht⟩, ?_⟩
    simpa only [hb, hsB, NSSE.DFA.Accepts, NSSE.DFA.run] using htB
  · rintro ⟨⟨q, r, hq, hrun, hr⟩, hB⟩
    exact ⟨(q, B.start), (r, B.run w), ⟨hq, rfl⟩,
      product_run A B hrun B.start, hr, hB⟩

end SemanticProduct

/-- Control data with a concrete exhaustive list, not a semantic oracle. -/
structure Control (Q : Type*) (m : Nat) where
  states : List Q
  complete : ∀ q, q ∈ states
  start : Q
  step : Q → Fin m → Q
  final : Q → Bool

namespace Control

variable {Q : Type*} {m : Nat}

def toDFA (B : Control Q m) {arity : Fin m → Nat} (D : Type*) :
    NSSE.DFA (Column D arity) Q where
  start := B.start
  step q c := B.step q c.1
  accept q := B.final q = true

def pairs (B : Control Q m) (n : Nat) : List (Fin n × Q) :=
  (List.finRange n).flatMap (fun q => B.states.map (fun r => (q, r)))

theorem mem_pairs (B : Control Q m) (n : Nat) (s : Fin n × Q) : s ∈ B.pairs n := by
  exact List.mem_flatMap.mpr ⟨s.1, List.mem_finRange _,
    List.mem_map.mpr ⟨s.2, B.complete _, Prod.mk.eta⟩⟩

def decode (B : Control Q m) (n : Nat) (i : Fin (B.pairs n).length) : Fin n × Q :=
  (B.pairs n).get i

theorem decode_surjective (B : Control Q m) (n : Nat) : Function.Surjective (B.decode n) := by
  intro s
  exact List.mem_iff_get.mp (B.mem_pairs n s)

theorem length_pairs (B : Control Q m) (n : Nat) : (B.pairs n).length = n * B.states.length := by
  simp [pairs, List.length_flatMap]

end Control

variable {n m : Nat} {arity : Fin m → Nat} {Q : Type*} [DecidableEq Q]

def flag (b : Bool) : L.Formula P := if b then ⊤ else ⊥

@[simp] theorem realize_flag {D : Type*} [L.Structure D] (p : P → D) (b : Bool) :
    (flag b : L.Formula P).Realize p ↔ b = true := by
  cases b <;> simp [flag]

/-- The output has n * |control states| numbered states and no silent edges. -/
def compile (A : Automaton L P n m arity) (B : Control Q m) :
    Automaton L P (B.pairs n).length m arity where
  initial i := A.epsilonFree.initial (B.decode n i).1 ⊓
    flag (decide ((B.decode n i).2 = B.start))
  final i := A.epsilonFree.final (B.decode n i).1 ⊓ flag (B.final (B.decode n i).2)
  silent _ _ := ⊥
  step c i j := A.epsilonFree.step c (B.decode n i).1 (B.decode n j).1 ⊓
    flag (decide ((B.decode n j).2 = B.step (B.decode n i).2 c))

theorem compile_dataInterpret (A : Automaton L P n m arity) (B : Control Q m)
    {D : Type*} [L.Structure D] (p : P → D) :
    (compile A B).dataInterpret p =
      SymbolicComplement.pullback (product (A.epsilonFree.dataInterpret p) (B.toDFA D))
        (B.decode n) := by
  unfold Automaton.dataInterpret compile SymbolicComplement.pullback product Control.toDFA
  congr 1
  · funext q
    apply propext
    simp only [Formula.realize_inf, realize_flag, decide_eq_true_eq]
  · funext q a r
    apply propext
    simp only [Formula.realize_inf, realize_flag, decide_eq_true_eq]
  · funext q
    apply propext
    simp only [Formula.realize_inf, realize_flag]

/-- Exact intersection with the shape control for every word and valuation.
There is no bound on the input automaton's original silent runs. -/
theorem compile_correct (A : Automaton L P n m arity) (B : Control Q m)
    {D : Type*} [L.Structure D] (p : P → D) (w : List (Column D arity)) :
    (compile A B).Accepts p w ↔ A.Accepts p w ∧ (B.toDFA D).Accepts w := by
  rw [(compile A B).accepts_iff_data_of_noSilent p (by intro q r; simp [compile]) w,
    compile_dataInterpret, SymbolicComplement.pullback_accepts _ _ (B.decode_surjective n),
    product_accepts, A.epsilonFree_correct p w]

end NSSE.SymbolicControl
