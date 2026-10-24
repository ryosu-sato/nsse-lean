import NSSE.StoredRelationalReachability

/-! Rows with actual stored formula tables, including counted field lookup. -/
namespace NSSE.StoredRelationalRow
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalClosure
variable {R : Nat → Type} {P : Type} {n : Nat}
structure QF (R : Nat → Type) (P : Type) where
  formula : Data R P 0
  qfree : (denote formula).IsQF
abbrev Vector (α : Type) (n : Nat) := StoredRelationTuple.Data α n
structure Row (R : Nat → Type) (P : Type) (n : Nat) where
  initial : Vector (QF R P) n
  final : Vector (QF R P) n
  data : Vector (Vector (QF R (P ⊕ Fin 1)) n) n
  left : Vector (Vector (QF R P) n) n
  right : Vector (Vector (QF R P) n) n
  guard : QF R (P ⊕ Fin 2)

def readPair {α : Type} (a : Vector (Vector α n) n) (q r : Fin n) : α × Nat :=
  let x := StoredRelationTuple.read a q
  let y := StoredRelationTuple.read x.1 r
  (y.1,1+x.2+y.2)
theorem readPair_bound {α : Type} (a : Vector (Vector α n) n) (q r : Fin n) :
    (readPair a q r).2 ≤ 1+2*n := by
  have h₁ := StoredRelationTuple.read_bound a q
  have h₂ := StoredRelationTuple.read_bound (StoredRelationTuple.read a q).1 r
  simp only [readPair]; omega

def Row.original (A : Row R P n) : SymbolicGuardedBlocks.Row (UniformWordLowering.wordLanguage R) P n where
  initial q := denote (StoredRelationTuple.read A.initial q).1.formula
  final q := denote (StoredRelationTuple.read A.final q).1.formula
  data q r := denote (readPair A.data q r).1.formula
  left q r := denote (readPair A.left q r).1.formula
  right q r := denote (readPair A.right q r).1.formula
  guard := denote A.guard.formula

theorem Row.qfree (A : Row R P n) : ArrayAtomExistentialPackages.RowQF A.original where
  initial q := (StoredRelationTuple.read A.initial q).1.qfree
  final q := (StoredRelationTuple.read A.final q).1.qfree
  data q r := (readPair A.data q r).1.qfree
  left q r := (readPair A.left q r).1.qfree
  right q r := (readPair A.right q r).1.qfree
  guard := A.guard.qfree

def data (A : Row R P n) (q r : Fin n) : Package R P × Nat :=
  let f := readPair A.data q r
  let a := StoredRelationalPackages.atom f.1.formula f.1.qfree
  let b := StoredRelationalPackages.bind 1 a.1
  (b.1,2+f.2+a.2+b.2)
theorem data_value (A : Row R P n) (q r : Fin n) :
    (data A q r).1.original = ExistentialRowNonempty.dataPackage A.original A.qfree q r := by
  simp only [data,StoredRelationalPackages.bind_original,StoredRelationalPackages.atom_original,
    ExistentialRowNonempty.dataPackage,Row.original]

theorem data_shape (A : Row R P n) (q r : Fin n) :
    (data A q r).1.vars = 1 ∧ nodes (data A q r).1.body = nodes (readPair A.data q r).1.formula ∧
    arity (data A q r).1.body = arity (readPair A.data q r).1.formula := by
  dsimp only [data]
  have ha := StoredRelationalPackages.atom_shape (readPair A.data q r).1.formula (readPair A.data q r).1.qfree
  have hb := StoredRelationalPackages.bind_shape 1
    (StoredRelationalPackages.atom (readPair A.data q r).1.formula (readPair A.data q r).1.qfree).1
  exact ⟨by omega,hb.2.1.trans ha.2.1,hb.2.2.trans ha.2.2⟩
def dataBudget (n B K : Nat) := 2*n+7+(weight K 1+weight K 5)*B

theorem data_bound (A : Row R P n) (B K : Nat)
    (hb : ∀ q r, nodes (readPair A.data q r).1.formula ≤ B)
    (hk : ∀ q r, arity (readPair A.data q r).1.formula ≤ K) (q r : Fin n) :
    (data A q r).2 ≤ dataBudget n B K := by
  let f := readPair A.data q r
  let a := StoredRelationalPackages.atom f.1.formula f.1.qfree
  have hf := readPair_bound A.data q r
  have ha := StoredRelationalPackages.atom_bound f.1.formula f.1.qfree K (hk q r)
  have hs := StoredRelationalPackages.atom_shape f.1.formula f.1.qfree
  have hka : arity a.1.body ≤ K := by rw [hs.2.2]; exact hk q r
  have hba : nodes a.1.body ≤ B := by rw [hs.2.1]; exact hb q r
  have hbind := StoredRelationalPackages.bind_bound 1 a.1 K hka
  have hb' := hb q r
  change f.2 ≤ _ at hf
  change a.2 ≤ _ at ha
  change 2+f.2+a.2+(StoredRelationalPackages.bind 1 a.1).2 ≤ _
  unfold dataBudget
  nlinarith

theorem data_size (A : Row R P n) (B : Nat)
    (hb : ∀ q r, nodes (readPair A.data q r).1.formula ≤ B) (q r : Fin n) :
    StoredRelationalElimination.size (data A q r).1 ≤ B+5 := by
  unfold StoredRelationalElimination.size
  rw [(data_shape A q r).2.1,(data_shape A q r).1]
  have h := hb q r; omega
end NSSE.StoredRelationalRow
