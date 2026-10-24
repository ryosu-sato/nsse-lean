import NSSE.OutsideBlockController

/-! # The outside controller as actual row syntax in the block language -/

namespace NSSE.SymbolicOutsideController

open FirstOrder FirstOrder.Language SymbolicAutomata
open SymbolicGuardedBlocks BlockRelationPresentation GuardedBlockRelation

universe u v w
variable {L : FirstOrder.Language.{u, v}} {P : Type w} {n : Nat}

abbrev ControlState (n : Nat) := OutsideBlockController.State (Fin n)
abbrev BlockLanguage (n : Nat) := BlockRelationPresentation.language n

def states (n : Nat) : List (ControlState n) :=
  (List.finRange n).flatMap (fun q => [.before true q, .before false q, .middle q, .after q]) ++
    [.waitLeft, .waitRight]

def stateAt (n : Nat) (i : Fin (states n).length) : ControlState n := (states n).get i

theorem stateAt_surjective (n : Nat) : Function.Surjective (stateAt n) := by
  intro s
  apply List.mem_iff_get.mp
  cases s with
  | before b q => cases b <;> simp [states]
  | waitLeft => simp [states]
  | middle q => simp [states]
  | waitRight => simp [states]
  | after q => simp [states]

theorem length_states (n : Nat) : (states n).length = 4 * n + 2 := by
  simp [states, List.length_flatMap, Nat.mul_comm]

def test {X : Type*} (h : Prop) [Decidable h] : (BlockLanguage n).Formula X := if h then ⊤ else ⊥

theorem realize_test {X D : Type*} [(BlockLanguage n).Structure D]
    (v : X → D) (h : Prop) [Decidable h] :
    (test (n := n) (X := X) h).Realize v ↔ h := by
  by_cases hh : h <;> simp [test, hh]

def blockAtom (q r : Fin n) : (BlockLanguage n).Formula (Empty ⊕ Fin 1) :=
  Relations.formula₁ (L := BlockLanguage n) (.block q r) (.var (.inr 0))

def guardAtom (e : Ends n) (first : Bool) : (BlockLanguage n).Formula (Empty ⊕ Fin 2) :=
  Relations.formula₂ (L := BlockLanguage n) (.guarded e first) (.var (.inr 0)) (.var (.inr 1))

def initialAtom (q : Fin n) : (BlockLanguage n).Formula Empty :=
  Relations.formula (L := BlockLanguage n) (.initial q) Fin.elim0

def finalAtom (q : Fin n) : (BlockLanguage n).Formula Empty :=
  Relations.formula (L := BlockLanguage n) (.final q) Fin.elim0

def blockNFA (R : Row L P n) (seed last : P) {D : Type*} [L.Structure D] (p : P → D) :
    NSSE.NFA (List D) (Fin n) where
  start q := ∃ z, (R.dataNFA p).start z ∧ (R.dataNFA p).step z (p seed) q
  step q U r := (R.dataNFA p).Runs q (U ++ [p last]) r
  accept q := (R.dataNFA p).accept q

def semantics (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) : OutsideBlockController.Data (List D) (Fin n) where
  block := blockNFA R seed last p
  r0 := e.leftStart
  r1 := e.leftEnd
  t0 := e.rightStart
  t1 := e.rightEnd
  first := first

theorem realize_blockAtom (R : Row L P n) (seed last : P) {D : Type*} [L.Structure D]
    (p : P → D) (q r : Fin n) (v : Empty → List D) (U : List D) :
    letI := BlockRelationPresentation.model R seed last p
    (blockAtom q r).Realize (Sum.elim v (fun _ => U)) ↔ (blockNFA R seed last p).step q U r := by
  letI := BlockRelationPresentation.model R seed last p
  rw [blockAtom, Formula.realize_rel₁]
  exact block_interpret R seed last p q r U

theorem realize_guardAtom (R : Row L P n) (seed last : P) {D : Type*} [L.Structure D]
    (p : P → D) (e : Ends n) (first : Bool) (v : Empty → List D) (U V : List D) :
    letI := BlockRelationPresentation.model R seed last p
    (guardAtom e first).Realize (Sum.elim v ![U, V]) ↔ R.LiteralH e seed last first p U V := by
  letI := BlockRelationPresentation.model R seed last p
  rw [guardAtom, Formula.realize_rel₂]
  exact guarded_interpret R seed last p e first U V

theorem realize_initialAtom (R : Row L P n) (seed last : P) {D : Type*} [L.Structure D]
    (p : P → D) (q : Fin n) (v : Empty → List D) :
    letI := BlockRelationPresentation.model R seed last p
    (initialAtom q).Realize v ↔ (blockNFA R seed last p).start q := by
  letI := BlockRelationPresentation.model R seed last p
  rw [initialAtom, Formula.realize_rel]
  exact initial_interpret R seed last p q _

theorem realize_finalAtom (R : Row L P n) (seed last : P) {D : Type*} [L.Structure D]
    (p : P → D) (q : Fin n) (v : Empty → List D) :
    letI := BlockRelationPresentation.model R seed last p
    (finalAtom q).Realize v ↔ (blockNFA R seed last p).accept q := by
  letI := BlockRelationPresentation.model R seed last p
  rw [finalAtom, Formula.realize_rel]
  exact final_interpret R seed last p q _

def initialGuard (s : ControlState n) : (BlockLanguage n).Formula Empty :=
  match s with
  | .before b q => test (b = true) ⊓ initialAtom q
  | _ => ⊥

def finalGuard (s : ControlState n) : (BlockLanguage n).Formula Empty :=
  match s with
  | .after q => finalAtom q
  | _ => ⊥

def dataGuard (e : Ends n) (first : Bool) (s t : ControlState n) :
    (BlockLanguage n).Formula (Empty ⊕ Fin 1) :=
  match s, t with
  | .before _ q, .before b r => test (b = false) ⊓ blockAtom q r
  | .before b q, .waitLeft => test (q = e.leftStart ∧ b = first)
  | .middle q, .middle r => blockAtom q r
  | .middle q, .waitRight => test (q = e.rightStart)
  | .after q, .after r => blockAtom q r
  | _, _ => ⊥

def leftGuard (e : Ends n) (s t : ControlState n) : (BlockLanguage n).Formula Empty :=
  match s, t with
  | .waitLeft, .middle r => test (r = e.leftEnd)
  | _, _ => ⊥

def rightGuard (e : Ends n) (s t : ControlState n) : (BlockLanguage n).Formula Empty :=
  match s, t with
  | .waitRight, .after r => test (r = e.rightEnd)
  | _, _ => ⊥

/-- The output is an ordinary finite Row over the block relational language.
Its free parameter type is EMPTY: all old parameters stay in the model. -/
def compile (e : Ends n) (first : Bool) : Row (BlockLanguage n) Empty (states n).length where
  initial i := initialGuard (stateAt n i)
  final i := finalGuard (stateAt n i)
  data i j := dataGuard e first (stateAt n i) (stateAt n j)
  left i j := leftGuard e (stateAt n i) (stateAt n j)
  right i j := rightGuard e (stateAt n i) (stateAt n j)
  guard := guardAtom e first

theorem initialGuard_correct (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (v : Empty → List D) (s : ControlState n) :
    letI := BlockRelationPresentation.model R seed last p
    (initialGuard s).Realize v ↔ (semantics R e seed last first p).automaton.start s := by
  letI := BlockRelationPresentation.model R seed last p
  cases s <;> simp only [initialGuard, Formula.realize_inf, realize_test,
    realize_initialAtom R seed last p, Formula.realize_bot, OutsideBlockController.Data.automaton, semantics]

theorem finalGuard_correct (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (v : Empty → List D) (s : ControlState n) :
    letI := BlockRelationPresentation.model R seed last p
    (finalGuard s).Realize v ↔ (semantics R e seed last first p).automaton.accept s := by
  letI := BlockRelationPresentation.model R seed last p
  cases s <;> simp only [finalGuard, realize_finalAtom R seed last p,
    Formula.realize_bot, OutsideBlockController.Data.automaton, semantics]

theorem dataGuard_correct (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (v : Empty → List D)
    (s t : ControlState n) (U : List D) :
    letI := BlockRelationPresentation.model R seed last p
    (dataGuard e first s t).Realize (Sum.elim v (fun _ => U)) ↔
      (semantics R e seed last first p).automaton.step s (.inl U) t := by
  letI := BlockRelationPresentation.model R seed last p
  cases s <;> cases t <;> simp only [dataGuard, Formula.realize_inf, realize_test,
    realize_blockAtom R seed last p, Formula.realize_bot, OutsideBlockController.Data.automaton, semantics]

theorem leftGuard_correct (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (v : Empty → List D) (s t : ControlState n) :
    letI := BlockRelationPresentation.model R seed last p
    (leftGuard e s t).Realize v ↔ (semantics R e seed last first p).automaton.step s (.inr false) t := by
  letI := BlockRelationPresentation.model R seed last p
  cases s <;> cases t <;> simp only [leftGuard, realize_test, Formula.realize_bot,
    OutsideBlockController.Data.automaton, semantics]

theorem rightGuard_correct (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (v : Empty → List D) (s t : ControlState n) :
    letI := BlockRelationPresentation.model R seed last p
    (rightGuard e s t).Realize v ↔ (semantics R e seed last first p).automaton.step s (.inr true) t := by
  letI := BlockRelationPresentation.model R seed last p
  cases s <;> cases t <;> simp only [rightGuard, realize_test, Formula.realize_bot,
    OutsideBlockController.Data.automaton, semantics]

theorem compile_interpret (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (v : Empty → List D) :
    letI := BlockRelationPresentation.model R seed last p
    (compile e first).markedNFA v = SymbolicComplement.pullback
      (semantics R e seed last first p).automaton (stateAt n) := by
  letI := BlockRelationPresentation.model R seed last p
  unfold Row.markedNFA Row.dataNFA compile SymbolicComplement.pullback
  congr 1
  · funext s
    exact propext (initialGuard_correct R e seed last first p v _)
  · funext s x t
    cases x with
    | inl U => exact propext (dataGuard_correct R e seed last first p v _ _ U)
    | inr b =>
        cases b
        · exact propext (leftGuard_correct R e seed last first p v _ _)
        · exact propext (rightGuard_correct R e seed last first p v _ _)
  · funext s
    exact propext (finalGuard_correct R e seed last first p v _)

theorem compile_accepts (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (v : Empty → List D) (w : List (List D ⊕ Bool)) :
    letI := BlockRelationPresentation.model R seed last p
    (compile e first).markedNFA v |>.Accepts w ↔
      (semantics R e seed last first p).automaton.Accepts w := by
  letI := BlockRelationPresentation.model R seed last p
  rw [compile_interpret R e seed last first p v,
    SymbolicComplement.pullback_accepts _ _ (stateAt_surjective n)]

theorem compile_guard (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (v : Empty → List D) (U V : List D) :
    letI := BlockRelationPresentation.model R seed last p
    (compile e first).guard.Realize (Sum.elim v ![U, V]) ↔ R.LiteralH e seed last first p U V :=
  realize_guardAtom R seed last p e first v U V

end NSSE.SymbolicOutsideController
