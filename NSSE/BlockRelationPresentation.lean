import NSSE.SymbolicGuardedBlocks

/-! # Concrete atomic presentations for the outside block controller -/

namespace NSSE.BlockRelationPresentation

open FirstOrder FirstOrder.Language SymbolicAutomata ConvolutionShapes
open SymbolicGuardedBlocks GuardedBlockRelation SymbolicReachability

universe u v w
variable {L : FirstOrder.Language.{u, v}} {P : Type w} {n : Nat}

def identityGuard (q r : Fin n) : L.Formula P := if q = r then ⊤ else ⊥

theorem realize_identityGuard {D : Type*} [L.Structure D] (p : P → D) (q r : Fin n) :
    (identityGuard (L := L) (P := P) q r).Realize p ↔ q = r := by
  by_cases h : q = r <;> simp [identityGuard, h]

def identityMarkers (R : Row L P n) : Row L P n :=
  { R with left := identityGuard, right := identityGuard, guard := ⊤ }

theorem identity_marked_path (R : Row L P n) {D : Type*} [L.Structure D]
    (p : P → D) (start finish : Fin n) (pref tail : List D) :
    (∃ z b, ((identityMarkers R).dataNFA p).Runs start pref z ∧
      (identityGuard (L := L) (P := P) z b).Realize p ∧
      ((identityMarkers R).dataNFA p).Runs b tail finish) ↔
      (R.dataNFA p).Runs start (pref ++ tail) finish := by
  simp only [realize_identityGuard]
  rw [runs_append_iff]
  constructor
  · rintro ⟨z, b, hp, rfl, ht⟩
    exact ⟨z, hp, ht⟩
  · rintro ⟨z, hp, ht⟩
    exact ⟨z, z, hp, rfl, ht⟩

theorem identity_H (R : Row L P n) (e : Ends n) (last : P)
    {D : Type*} [L.Structure D] (p : P → D) (U V : List D) :
    (identityMarkers R).H e last last false p U V ↔
      (R.dataNFA p).Runs e.leftStart (U ++ [p last]) e.leftEnd ∧
      (R.dataNFA p).Runs e.rightStart (V ++ [p last]) e.rightEnd := by
  change (∃ px py shared, U = px ++ shared ∧ V = py ++ shared ∧
    (⊤ : L.Formula (P ⊕ Fin 2)).Realize _ ∧
    (∃ z b, ((identityMarkers R).dataNFA p).Runs e.leftStart px z ∧
      (identityGuard (L := L) (P := P) z b).Realize p ∧
      ((identityMarkers R).dataNFA p).Runs b (shared ++ [p last]) e.leftEnd) ∧
    (∃ z b, ((identityMarkers R).dataNFA p).Runs e.rightStart py z ∧
      (identityGuard (L := L) (P := P) z b).Realize p ∧
      ((identityMarkers R).dataNFA p).Runs b (shared ++ [p last]) e.rightEnd)) ↔ _
  simp only [Formula.realize_top, true_and, identity_marked_path]
  constructor
  · rintro ⟨px, py, shared, rfl, rfl, hl, hr⟩
    simpa only [List.append_assoc] using And.intro hl hr
  · rintro ⟨hl, hr⟩
    exact ⟨U, V, [], by simp, by simp, hl, hr⟩

def compileB (R : Row L P n) (last : P) (q r : Fin n) :=
  pullbackWords (fun _ : Fin 2 => (0 : Fin 1))
    ((identityMarkers R).compileH ⟨q, r, q, r⟩ last last false)

theorem compileB_correct (R : Row L P n) (last : P) (q r : Fin n)
    {D : Type*} [L.Structure D] (p : P → D) (U : List D) :
    tupleAccepts (compileB R last q r) p ![U.reverse] ↔
      (R.dataNFA p).Runs q (U ++ [p last]) r := by
  rw [compileB, pullbackWords_correct]
  have ht : ![U.reverse] ∘ (fun _ : Fin 2 => (0 : Fin 1)) = ![U.reverse, U.reverse] := by
    funext i
    fin_cases i <;> rfl
  rw [ht, Row.compileH_correct, identity_H]
  exact ⟨And.left, fun h => ⟨h, h⟩⟩

def paramAutomaton (f : L.Formula P) : WordAutomaton L P 1 0 where
  initial _ := f
  final _ := ⊤
  silent _ _ := ⊥
  step _ _ _ := ⊥

theorem paramAutomaton_correct (f : L.Formula P) {D : Type*} [L.Structure D]
    (p : P → D) (t : CanonicalConvolution.Tuple D 0) :
    tupleAccepts (paramAutomaton f) p t ↔ f.Realize p := by
  unfold tupleAccepts denseAccepts
  rw [UniformWordLowering.encode_zero]
  change (paramAutomaton f).Accepts p [] ↔ _
  rw [(paramAutomaton f).accepts_iff_data_of_noSilent p
    (by intro q r; simp [paramAutomaton]) ([] : List (Sparse D 0))]
  simp [NSSE.NFA.Accepts, runs_nil_iff, Automaton.dataInterpret, paramAutomaton]

def initialFormula (R : Row L P n) (seed : P) (q : Fin n) : L.Formula P :=
  any n (fun z => R.initial z ⊓ dataAt (R.data z q) id seed)

theorem initialFormula_correct (R : Row L P n) (seed : P) (q : Fin n)
    {D : Type*} [L.Structure D] (p : P → D) :
    (initialFormula R seed q).Realize p ↔
      ∃ z, (R.dataNFA p).start z ∧ (R.dataNFA p).step z (p seed) q := by
  simp [initialFormula, realize_any, realize_dataAt, Row.dataNFA, Function.comp_def]

inductive Rel (n : Nat) : Nat → Type
  | block (q r : Fin n) : Rel n 1
  | guarded (e : Ends n) (first : Bool) : Rel n 2
  | initial (q : Fin n) : Rel n 0
  | final (q : Fin n) : Rel n 0

abbrev language (n : Nat) := UniformWordLowering.wordLanguage (Rel n)

def relationAutomaton (R : Row L P n) (seed last : P) :
    {a : Nat} → Rel n a → UniformWordLowering.Compiled L P a
  | _, .block q r => ⟨_, compileB R last q r⟩
  | _, .guarded e first => ⟨_, R.compileH e seed last first⟩
  | _, .initial q => ⟨_, paramAutomaton (initialFormula R seed q)⟩
  | _, .final q => ⟨_, paramAutomaton (R.final q)⟩

def presentation (R : Row L P n) (seed last : P) :
    UniformWordLowering.Presentation L P (Rel n) where
  states s := (relationAutomaton R seed last s).1
  automaton s := (relationAutomaton R seed last s).2

def model (R : Row L P n) (seed last : P) {D : Type*} [L.Structure D] (p : P → D) :
    (language n).Structure (List D) :=
  UniformWordLowering.model (presentation R seed last) p (UniformWordLowering.reverseEquiv D)

theorem block_interpret (R : Row L P n) (seed last : P) {D : Type*} [L.Structure D]
    (p : P → D) (q r : Fin n) (U : List D) :
    letI := model R seed last p
    FirstOrder.Language.Structure.RelMap (L := language n) (.block q r) ![U] ↔
      (R.dataNFA p).Runs q (U ++ [p last]) r := by
  change tupleAccepts (compileB R last q r) p
    ((UniformWordLowering.reverseEquiv D) ∘ ![U]) ↔ _
  have ht : (UniformWordLowering.reverseEquiv D) ∘ ![U] = ![U.reverse] := by
    funext i
    fin_cases i
    rfl
  rw [ht, compileB_correct]

theorem guarded_interpret (R : Row L P n) (seed last : P) {D : Type*} [L.Structure D]
    (p : P → D) (e : Ends n) (first : Bool) (U V : List D) :
    letI := model R seed last p
    FirstOrder.Language.Structure.RelMap (L := language n) (.guarded e first) ![U, V] ↔
      R.LiteralH e seed last first p U V := by
  change tupleAccepts (R.compileH e seed last first) p
    ((UniformWordLowering.reverseEquiv D) ∘ ![U, V]) ↔ _
  have ht : (UniformWordLowering.reverseEquiv D) ∘ ![U, V] = ![U.reverse, V.reverse] := by
    funext i
    fin_cases i <;> rfl
  rw [ht, Row.compileH_marked_correct]

theorem initial_interpret (R : Row L P n) (seed last : P) {D : Type*} [L.Structure D]
    (p : P → D) (q : Fin n) (t : Fin 0 → List D) :
    letI := model R seed last p
    FirstOrder.Language.Structure.RelMap (L := language n) (.initial q) t ↔
      ∃ z, (R.dataNFA p).start z ∧ (R.dataNFA p).step z (p seed) q := by
  change tupleAccepts (paramAutomaton (initialFormula R seed q)) p _ ↔ _
  rw [paramAutomaton_correct, initialFormula_correct]

theorem final_interpret (R : Row L P n) (seed last : P) {D : Type*} [L.Structure D]
    (p : P → D) (q : Fin n) (t : Fin 0 → List D) :
    letI := model R seed last p
    FirstOrder.Language.Structure.RelMap (L := language n) (.final q) t ↔ (R.dataNFA p).accept q := by
  change tupleAccepts (paramAutomaton (R.final q)) p _ ↔ _
  rw [paramAutomaton_correct]
  rfl

end NSSE.BlockRelationPresentation
