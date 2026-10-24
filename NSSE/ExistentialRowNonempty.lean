import NSSE.DirectRankExistentialStep

/-! # Actual seed-only and nonempty row formulas as existential packages -/

namespace NSSE.ExistentialRowNonempty

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks ExistentialFormulaPackage
open ArrayAtomExistentialPackages SymbolicReachability

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {n : Nat}

def anyPackage (m : Nat) (f : Fin m → Package L P) : Package L P :=
  ((List.finRange m).map f).foldr Package.disj (Package.atom ⊥ BoundedFormula.isQF_bot)

theorem anyPackage_correct {D : Type*} [L.Structure D] [Nonempty D] (p : P → D)
    (m : Nat) (f : Fin m → Package L P) :
    (anyPackage m f).toFormula.Realize p ↔ ∃ i, (f i).toFormula.Realize p := by
  have hl (as : List (Package L P)) :
      (as.foldr Package.disj (Package.atom ⊥ BoundedFormula.isQF_bot)).toFormula.Realize p ↔
        ∃ A ∈ as, A.toFormula.Realize p := by
    induction as with
    | nil => simp [Package.atom_correct]
    | cons A as ih => simp only [List.foldr_cons, Package.disj_correct, ih, List.mem_cons]; aesop
  rw [anyPackage, hl]
  simp

def eliminate (W : Fin n → Fin n → Package L P) : List (Fin n) → Fin n → Fin n → Package L P
  | [], a, b => W a b
  | t::ts, a, b => Package.disj (eliminate W ts a b)
      (Package.conj (eliminate W ts a t) (eliminate W ts t b))

theorem eliminate_correct {D : Type*} [L.Structure D] [Nonempty D] (p : P → D)
    (W : Fin n → Fin n → Package L P) (V : Fin n → Fin n → L.Formula P)
    (hv : ∀ a b, (W a b).toFormula.Realize p ↔ (V a b).Realize p) (ts : List (Fin n)) (a b : Fin n) :
    (eliminate W ts a b).toFormula.Realize p ↔ (SymbolicReachability.eliminate V ts a b).Realize p := by
  induction ts generalizing a b with
  | nil => exact hv a b
  | cons t ts ih =>
    simp only [eliminate, SymbolicReachability.eliminate, via, Package.disj_correct, Package.conj_correct,
      Formula.realize_sup, Formula.realize_inf, ih]

def reachPackage (W : Fin n → Fin n → Package L P) (a b : Fin n) : Package L P :=
  eliminate (fun a b => Package.disj
    (Package.atom (if a=b then ⊤ else ⊥) (by split; exact BoundedFormula.IsQF.top; exact BoundedFormula.isQF_bot))
    (W a b)) (List.finRange n) a b

theorem reachPackage_correct {D : Type*} [L.Structure D] [Nonempty D] (p : P → D)
    (W : Fin n → Fin n → Package L P) (V : Fin n → Fin n → L.Formula P)
    (hv : ∀ a b, (W a b).toFormula.Realize p ↔ (V a b).Realize p) (a b : Fin n) :
    (reachPackage W a b).toFormula.Realize p ↔ (reach V a b).Realize p := by
  apply eliminate_correct
  intro q r
  simp only [Package.disj_correct, Package.atom_correct, reflexiveEdges, Formula.realize_sup, hv]

def dataPackage (R : Row L P n) (h : RowQF R) (q r : Fin n) : Package L P :=
  Package.bind 1 (Package.atom (R.data q r) (h.data q r))

def edgePackage (R : Row L P n) (h : RowQF R) (q r : Fin n) : Package L P :=
  Package.disj (Package.atom ⊥ BoundedFormula.isQF_bot) (anyPackage 1 (fun _ => dataPackage R h q r))

def seedOnly (R : Row L P n) (h : RowQF R) : Package L P :=
  anyPackage n (fun q => anyPackage n (fun r => Package.conj (Package.atom (R.initial q) (h.initial q))
    (Package.conj (dataPackage R h q r) (Package.atom (R.final r) (h.final r)))))

def nonempty (R : Row L P n) (h : RowQF R) : Package L P :=
  anyPackage n (fun q => anyPackage n (fun r => Package.conj (Package.atom (R.initial q) (h.initial q))
    (Package.conj (reachPackage (edgePackage R h) q r) (Package.atom (R.final r) (h.final r)))))

theorem dataPackage_correct (R : Row L P n) (h : RowQF R) {D : Type*} [L.Structure D]
    (p : P → D) (q r : Fin n) :
    (dataPackage R h q r).toFormula.Realize p ↔ (closeColumn (R.data q r)).Realize p := by
  simp only [dataPackage, Package.bind_correct, Package.atom_correct, realize_closeColumn]

theorem edgePackage_correct (R : Row L P n) (h : RowQF R) {D : Type*} [L.Structure D] [Nonempty D]
    (p : P → D) (q r : Fin n) :
    (edgePackage R h q r).toFormula.Realize p ↔ ((RowRegularOperations.toAutomaton R).edge q r).Realize p := by
  simp only [edgePackage, Package.disj_correct, Package.atom_correct, anyPackage_correct,
    SymbolicAutomata.Automaton.edge, Formula.realize_sup, realize_any, dataPackage_correct]
  rfl

theorem seedOnly_correct (R : Row L P n) (h : RowQF R) {D : Type*} [L.Structure D] [Nonempty D]
    (p : P → D) : (seedOnly R h).toFormula.Realize p ↔ ∃ x, (R.dataNFA p).Accepts [x] := by
  rw [← RowRegularOperations.seedOnlyFormula_correct]
  simp only [seedOnly, anyPackage_correct, Package.conj_correct, Package.atom_correct, dataPackage_correct,
    RowRegularOperations.seedOnlyFormula, realize_any, Formula.realize_inf]

theorem nonempty_correct (R : Row L P n) (h : RowQF R) {D : Type*} [L.Structure D] [Nonempty D]
    (p : P → D) : (nonempty R h).toFormula.Realize p ↔ ∃ xs, (R.dataNFA p).Accepts xs := by
  rw [← RowRegularOperations.nonemptyFormula_correct]
  simp only [nonempty, anyPackage_correct, Package.conj_correct, Package.atom_correct,
    RowRegularOperations.nonemptyFormula, SymbolicAutomata.Automaton.nonemptyFormula, realize_any, Formula.realize_inf]
  simp only [reachPackage_correct p _ _ (edgePackage_correct R h p)]
  rfl

end NSSE.ExistentialRowNonempty
