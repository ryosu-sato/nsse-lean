import NSSE.StoredClosedLabel

namespace NSSE.StoredSymbolicRow
variable {d : Nat}

structure Data where
  count : Nat
  initial : List StoredClosedLabel.Atom
  final : List StoredClosedLabel.Atom
  data : List (List StoredUnaryLabel.Atom)
  left : List (List StoredClosedLabel.Atom)
  right : List (List StoredClosedLabel.Atom)
  guard : StoredClosedLabel.Atom
  deriving BEq

-- Semantic rendering only; later consumers must charge reads and syntax operations.
def denote (A : Data) : SymbolicGuardedBlocks.Row (AlphabetTableRows.language (Fin d)) Empty A.count where
  initial q := StoredClosedLabel.denote (StoredForwardLookup.get (.constant false) A.initial q.val).1
  final q := StoredClosedLabel.denote (StoredForwardLookup.get (.constant false) A.final q.val).1
  data q r := StoredUnaryLabel.denote (StoredForwardLookup.get (.constant false)
    (StoredForwardLookup.get [] A.data q.val).1 r.val).1
  left q r := StoredClosedLabel.denote (StoredForwardLookup.get (.constant false)
    (StoredForwardLookup.get [] A.left q.val).1 r.val).1
  right q r := StoredClosedLabel.denote (StoredForwardLookup.get (.constant false)
    (StoredForwardLookup.get [] A.right q.val).1 r.val).1
  guard := StoredClosedLabel.denote A.guard

def marked (A : StoredCapRowNFABuild.Data) : Data × Nat :=
  let s := StoredClosedLabel.vector A.count (StoredMarkedNFAAccess.start A)
  let f := StoredClosedLabel.vector A.count (StoredMarkedNFAAccess.final A)
  let t := StoredDataLabels.buildMarked (d := d) A
  let l := StoredClosedLabel.matrix A.count (fun q r => StoredMarkedNFAAccess.step (d := d) A q r (.inr false))
  let r := StoredClosedLabel.matrix A.count (fun q r => StoredMarkedNFAAccess.step (d := d) A q r (.inr true))
  (⟨A.count,s.1,f.1,t.1,l.1,r.1,.constant true⟩,6+s.2+f.2+t.2+l.2+r.2)

def plain (A : StoredRightIdealNFABuild.Data) : Data × Nat :=
  let s := StoredClosedLabel.vector A.count (StoredPlainNFAAccess.start A)
  let f := StoredClosedLabel.vector A.count (StoredPlainNFAAccess.final A)
  let t := StoredDataLabels.buildPlain (d := d) A
  let l := StoredClosedLabel.matrix A.count (fun _ _ => (false,1))
  let r := StoredClosedLabel.matrix A.count (fun _ _ => (false,1))
  (⟨A.count,s.1,f.1,t.1,l.1,r.1,.constant false⟩,6+s.2+f.2+t.2+l.2+r.2)

open StoredForwardTableBuild in
def markedBudget (n d : Nat) := 6+2*tabBudget n (1+n)+
  tabBudget n (tabBudget n (1+tabBudget d (2*n+d+3)))+
  2*tabBudget n (tabBudget n (1+(2*n+d+3)))
open StoredForwardTableBuild in
def plainBudget (n d : Nat) := 6+2*tabBudget n (1+n)+
  tabBudget n (tabBudget n (1+tabBudget d (2*n+d+2)))+
  2*tabBudget n (tabBudget n 2)

theorem marked_bound (A : StoredCapRowNFABuild.Data) : (marked (d := d) A).2 ≤ markedBudget A.count d := by
  have hs := StoredClosedLabel.vector_bound A.count A.count (StoredMarkedNFAAccess.start A) (StoredMarkedNFAAccess.start_bound A)
  have hf := StoredClosedLabel.vector_bound A.count A.count (StoredMarkedNFAAccess.final A) (StoredMarkedNFAAccess.final_bound A)
  have ht := StoredDataLabels.buildMarked_bound (d := d) A
  have hm (b : Bool) := StoredClosedLabel.matrix_bound A.count (2*A.count+d+3)
    (fun q r => StoredMarkedNFAAccess.step (d := d) A q r (.inr b))
    (fun q r => StoredMarkedNFAAccess.step_bound (d := d) A q r (.inr b))
  have hl := hm false
  have hr := hm true
  simp only [marked,markedBudget]; omega

theorem plain_bound (A : StoredRightIdealNFABuild.Data) : (plain (d := d) A).2 ≤ plainBudget A.count d := by
  have hs := StoredClosedLabel.vector_bound A.count A.count (StoredPlainNFAAccess.start A) (StoredPlainNFAAccess.start_bound A)
  have hf := StoredClosedLabel.vector_bound A.count A.count (StoredPlainNFAAccess.final A) (StoredPlainNFAAccess.final_bound A)
  have ht := StoredDataLabels.buildPlain_bound (d := d) A
  have hm := StoredClosedLabel.matrix_bound A.count 1 (fun _ _ => (false,1)) (fun _ _ => le_rfl)
  change _ ≤ StoredForwardTableBuild.tabBudget A.count (StoredForwardTableBuild.tabBudget A.count 2) at hm
  simp only [plain,plainBudget]; omega

theorem marked_value (A : StoredCapRowNFABuild.Data) :
    denote (d := d) (marked (d := d) A).1 = AlphabetTableRows.compile (StoredMarkedNFAAccess.input (d := d) A) := by
  simp only [marked,denote,StoredClosedLabel.vector_value,StoredClosedLabel.matrix_value,
    StoredDataLabels.buildMarked,StoredDataLabels.table_value,StoredForwardLookup.get_ofFn,
    StoredDataLabels.marked_value,StoredClosedLabel.denote,AlphabetTableRows.compile,
    StoredMarkedNFAAccess.input,Bool.decide_coe,AlphabetTableRows.truth]
  simp

theorem plain_value (A : StoredRightIdealNFABuild.Data) :
    denote (d := d) (plain (d := d) A).1 = AlphabetTableRows.compileData (StoredPlainNFAAccess.input (d := d) A) := by
  simp only [plain,denote,StoredClosedLabel.vector_value,StoredClosedLabel.matrix_value,
    StoredDataLabels.buildPlain,StoredDataLabels.table_value,StoredForwardLookup.get_ofFn,
    StoredDataLabels.plain_value,StoredClosedLabel.denote,AlphabetTableRows.compileData,
    StoredPlainNFAAccess.input,Bool.decide_coe,AlphabetTableRows.truth]
  simp
end NSSE.StoredSymbolicRow
