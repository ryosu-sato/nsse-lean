import NSSE.StoredAlphabetRowLabels

namespace NSSE.StoredUnaryLabel
variable {d : Nat}

inductive Atom where
  | constant (b : Bool)
  | unary (table : List Bool)
  deriving BEq

def evaluate (a : Atom) (i : Fin d) : Bool × Nat :=
  match a with
  | .constant b => (b,1)
  | .unary xs => let r := StoredForwardLookup.get false xs i.val; (r.1,1+r.2)

-- Semantic rendering; executable evaluation above charges table access.
def denote {P : Type} : Atom → (AlphabetTableRows.language (Fin d)).Formula (P ⊕ Fin 1)
  | .constant b => AlphabetTableRows.truth b
  | .unary xs => AlphabetTableRows.unary (fun i => (StoredForwardLookup.get false xs i.val).1)

theorem evaluate_correct {P : Type} (a : Atom) (p : P → Fin d) (i : Fin d) :
    (evaluate a i).1 = true ↔ (denote (d := d) a).Realize (Sum.elim p (fun _ => i)) := by
  cases a <;> simp only [evaluate,denote,AlphabetTableRows.realize_truth,AlphabetTableRows.realize_unary]

theorem evaluate_bound (a : Atom) (i : Fin d) : (evaluate a i).2 ≤ d+1 := by
  cases a with
  | constant b => simp only [evaluate]; omega
  | unary xs =>
    have h := (StoredForwardLookup.get_bound false xs i.val).trans i.isLt
    simp only [evaluate]; omega

def build (f : Fin d → Bool × Nat) : Atom × Nat :=
  let t := CountedFinEnumeration.tabulate d f
  (.unary t.1,1+t.2)

theorem value (f : Fin d → Bool × Nat) : (build f).1 = .unary (List.ofFn (fun i => (f i).1)) := by
  simp only [build,CountedFinEnumeration.tabulate_value]

theorem bound (f : Fin d → Bool × Nat) (c : Nat) (h : ∀ i, (f i).2 ≤ c) :
    (build f).2 ≤ 1+StoredForwardTableBuild.tabBudget d c :=
  Nat.add_le_add_left (CountedFinEnumeration.tabulate_bound d f c h) 1

theorem denote_value {P : Type} (f : Fin d → Bool × Nat) :
    denote (d := d) (P := P) (build f).1 = AlphabetTableRows.unary (fun i => (f i).1) := by
  simp only [value,denote]
  apply congrArg AlphabetTableRows.unary
  funext i
  exact StoredForwardLookup.get_ofFn false _ i
end NSSE.StoredUnaryLabel
