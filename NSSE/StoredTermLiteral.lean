import NSSE.StoredTermReference
import NSSE.StoredSubtypeInput

/-! Materialize constructor literals by counted traversal of stored children.
Term packing and construction of the layout/pair count remain separate. -/
namespace NSSE.StoredTermLiteral
open StoredSubtypeTerm
variable {n d : Nat}

def children (ts : List (Term n)) (pairs : Nat) (cs : List (Term n)) :
    List (Fin (n+(ts.length+(pairs+1)))) × Nat :=
  CountedListConstruction.map (StoredTermReference.resolve ts pairs) cs

theorem children_value (ts : List (Term n)) (pairs : Nat) (cs : List (Term n)) :
    (children ts pairs cs).1 = cs.map (fun t => (StoredTermReference.resolve ts pairs t).1) :=
  CountedListConstruction.map_value _ _

theorem children_length (ts : List (Term n)) (pairs : Nat) (cs : List (Term n)) :
    (children ts pairs cs).1.length = cs.length := by
  simp only [children_value,List.length_map]

theorem children_bound (ts : List (Term n)) (pairs : Nat) (cs : List (Term n))
    (W : Nat) (hw : ∀ t ∈ cs, weight t ≤ W) :
    (children ts pairs cs).2 ≤ 1+cs.length*(1+(n+2*ts.length+8+ts.length*(1+2*W))) := by
  apply CountedListConstruction.map_bound
  intro t ht
  exact StoredTermReference.uniform_bound ts pairs t n ts.length W (by rfl) (by rfl) (hw t ht)

def literal (ts : List (Term n)) (pairs : Nat) (head : Term n)
    (cs : List (Term n)) (h : cs.length = d) :
    StoredSubtypeInput.Bound (n+(ts.length+(pairs+1))) d × Nat :=
  let a := StoredTermReference.resolve ts pairs head
  let b := children ts pairs cs
  (⟨a.1,b.1,(children_length ts pairs cs).trans h⟩,1+a.2+b.2)

theorem literal_bound (ts : List (Term n)) (pairs : Nat) (head : Term n)
    (cs : List (Term n)) (h : cs.length = d) (W : Nat)
    (hh : weight head ≤ W) (hc : ∀ t ∈ cs, weight t ≤ W) :
    (literal ts pairs head cs h).2 ≤
      2+(n+2*ts.length+8+ts.length*(1+2*W))+
        d*(1+(n+2*ts.length+8+ts.length*(1+2*W))) := by
  have ha := StoredTermReference.uniform_bound ts pairs head n ts.length W (by rfl) (by rfl) hh
  have hb := children_bound ts pairs cs W hc
  simp only [literal]
  rw [h] at hb
  omega

theorem packed_children_value (L : SubtypeTermLayout.Layout n d)
    (cs : List (SubtypeTerms.Term n d)) :
    ((children (L.terms.map pack) L.pairs.length (cs.map pack)).1.map Fin.val) =
      cs.map (fun t => (L.ref t).val) := by
  simp only [children_value,List.map_map]
  apply List.map_congr_left
  intro t _
  exact StoredTermReference.packed_value L t

theorem packed_head_value (L : SubtypeTermLayout.Layout n d)
    (head : SubtypeTerms.Term n d) (c : Fin d → SubtypeTerms.Term n d) :
    (literal (L.terms.map pack) L.pairs.length (pack head)
      (List.ofFn (fun i => pack (c i))) List.length_ofFn).1.head.val = (L.ref head).val :=
  StoredTermReference.packed_value L head

theorem packed_literal_children (L : SubtypeTermLayout.Layout n d)
    (head : SubtypeTerms.Term n d) (c : Fin d → SubtypeTerms.Term n d) :
    (literal (L.terms.map pack) L.pairs.length (pack head)
      (List.ofFn (fun i => pack (c i))) List.length_ofFn).1.children.map Fin.val =
      List.ofFn (fun i => (L.ref (c i)).val) := by
  simpa only [literal,List.map_ofFn] using packed_children_value L (List.ofFn c)

-- A proof-only reindexing lets the materialized literal be compared directly
-- with the original callback specification; it is not part of execution.
def transport {a b : Nat} (h : a=b) (x : StoredSubtypeInput.Bound a d) :
    SubtypeConstraints.BoundLiteral b d :=
  (Fin.cast h x.head,fun i => Fin.cast h (x.denote.2 i))

theorem packed_literal_value (L : SubtypeTermLayout.Layout n d)
    (head : SubtypeTerms.Term n d) (c : Fin d → SubtypeTerms.Term n d) :
    transport (by simp [SubtypeTermLayout.Layout.count])
      (literal (L.terms.map pack) L.pairs.length (pack head)
        (List.ofFn (fun i => pack (c i))) List.length_ofFn).1 =
      (L.ref head,fun i => L.ref (c i)) := by
  apply Prod.ext
  · apply Fin.ext
    exact packed_head_value L head c
  · funext i
    apply Fin.ext
    simp only [transport,StoredSubtypeInput.Bound.denote,Fin.coe_cast,literal,
      children_value,List.getElem_map,List.getElem_ofFn]
    exact StoredTermReference.packed_value L (c i)
end NSSE.StoredTermLiteral
