import NSSE.FiniteRankDecision

/-! # Concrete alphabet tables as symbolic Row labels

For a finite base alphabet, a Boolean function on a finite tuple is an
actual atomic relation table. Interpretation evaluates that table, so the
base model requires no logical oracle. This embeds concrete marked NFAs
in the input class of the complete rank compiler.
-/

namespace NSSE.AlphabetTableRows

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks

def language (α : Type) : FirstOrder.Language.{0, 0} :=
  UniformWordLowering.wordLanguage (fun n => (Fin n → α) → Bool)

instance model (α : Type) : (language α).Structure α where
  funMap f := nomatch f
  RelMap r xs := r xs = true

def relationDecision (α : Type) : FiniteRankDecision.RelationDecision (language α) α :=
  fun r xs => inferInstanceAs (Decidable (r xs = true))

def truth {α P : Type} (b : Bool) : (language α).Formula P := if b then ⊤ else ⊥

@[simp] theorem realize_truth {α P : Type} (b : Bool) (p : P → α) :
    (truth (α := α) b).Realize p ↔ b = true := by cases b <;> simp [truth]

def unary {α P : Type} (f : α → Bool) : (language α).Formula (P ⊕ Fin 1) :=
  FirstOrder.Language.Relations.formula₁ (L := language α)
    (fun xs : Fin 1 → α => f (xs 0)) (.var (.inr 0))

@[simp] theorem realize_unary {α P : Type} (f : α → Bool) (p : P → α) (x : α) :
    (unary f).Realize (Sum.elim p (fun _ => x)) ↔ f x = true := by
  rfl

variable {α : Type} {n : Nat}

def compile (T : NSSE.NFA (α ⊕ Bool) (Fin n))
    [DecidablePred T.start] [DecidablePred T.accept]
    [∀ q x r, Decidable (T.step q x r)] : Row (language α) Empty n where
  initial q := truth (decide (T.start q))
  final q := truth (decide (T.accept q))
  data q r := unary (fun x => decide (T.step q (.inl x) r))
  left q r := truth (decide (T.step q (.inr false) r))
  right q r := truth (decide (T.step q (.inr true) r))
  guard := ⊤

theorem compile_markedNFA (T : NSSE.NFA (α ⊕ Bool) (Fin n))
    [DecidablePred T.start] [DecidablePred T.accept]
    [∀ q x r, Decidable (T.step q x r)] (p : Empty → α) :
    (compile T).markedNFA p = T := by
  unfold Row.markedNFA Row.dataNFA compile
  congr 1
  · funext q
    simp
  · funext q x r
    cases x with
    | inl x => simp
    | inr b => cases b <;> simp
  · funext q
    simp

def compileData (T : NSSE.NFA α (Fin n))
    [DecidablePred T.start] [DecidablePred T.accept]
    [∀ q x r, Decidable (T.step q x r)] : Row (language α) Empty n where
  initial q := truth (decide (T.start q))
  final q := truth (decide (T.accept q))
  data q r := unary (fun x => decide (T.step q x r))
  left _ _ := ⊥
  right _ _ := ⊥
  guard := ⊥

theorem compileData_dataNFA (T : NSSE.NFA α (Fin n))
    [DecidablePred T.start] [DecidablePred T.accept]
    [∀ q x r, Decidable (T.step q x r)] (p : Empty → α) :
    (compileData T).dataNFA p = T := by
  unfold Row.dataNFA compileData
  congr 1
  · funext q
    simp
  · funext q x r
    simp
  · funext q
    simp

end NSSE.AlphabetTableRows
