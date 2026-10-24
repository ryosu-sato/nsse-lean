import NSSE.StoredPaddedLiteral
import NSSE.StoredTermClause
import NSSE.SubtypeTermFlattening

namespace NSSE.StoredEdgeClause
open StoredSubtypeTerm
variable {n d : Nat}

def slot (ts : List (Term n)) (pairs : Nat) (j : Fin pairs) :
    Fin (n+(ts.length+(pairs+1))) × Nat :=
  let r := StoredTermReference.padding ts j.val
  (⟨r.1,by rw [StoredTermReference.padding_value]; omega⟩,r.2)

def padding (ts : List (Term n)) (pairs : Nat) :
    Fin (n+(ts.length+(pairs+1))) × Nat :=
  let r := StoredTermReference.padding ts pairs
  (⟨r.1,by rw [StoredTermReference.padding_value]; omega⟩,r.2)

def clause (ts : List (Term n)) (pairs : Nat) (i : Fin d) (j : Fin pairs)
    (left right : Term n) : StoredSubtypeInput.Input (n+(ts.length+(pairs+1))) d × Nat :=
  let s := slot ts pairs j
  let e := padding ts pairs
  let a := StoredTermReference.resolve ts pairs left
  let b := StoredTermReference.resolve ts pairs right
  let u := StoredPaddedLiteral.literal i s.1 b.1 e.1
  let l := StoredPaddedLiteral.literal i s.1 a.1 e.1
  (⟨[u.1],[l.1],[],[]⟩,3+s.2+e.2+a.2+b.2+u.2+l.2)

def budget (n m d W : Nat) :=
  3+2*(n+2*m+5)+2*(n+2*m+8+m*(1+2*W))+2*StoredPaddedLiteral.budget d

theorem bound (ts : List (Term n)) (pairs : Nat) (i : Fin d) (j : Fin pairs)
    (left right : Term n) (W : Nat) (hl : weight left ≤ W) (hr : weight right ≤ W) :
    (clause ts pairs i j left right).2 ≤ budget n ts.length d W := by
  have ha := StoredTermReference.uniform_bound ts pairs left n ts.length W (by rfl) (by rfl) hl
  have hb := StoredTermReference.uniform_bound ts pairs right n ts.length W (by rfl) (by rfl) hr
  have hu := StoredPaddedLiteral.bound i (slot ts pairs j).1 (StoredTermReference.resolve ts pairs right).1 (padding ts pairs).1
  have hv := StoredPaddedLiteral.bound i (slot ts pairs j).1 (StoredTermReference.resolve ts pairs left).1 (padding ts pairs).1
  simp only [clause,budget,slot,padding,StoredTermReference.padding_cost] at *
  omega

theorem slot_packed (L : SubtypeTermLayout.Layout n d) (j : Fin L.pairs.length) :
    Fin.cast (by simp [SubtypeTermLayout.Layout.count]) (slot (L.terms.map pack) L.pairs.length j).1 = L.edgeSlot j := by
  apply Fin.ext
  simp only [slot,Fin.coe_cast,StoredTermReference.padding_value,List.length_map,
    SubtypeTermLayout.Layout.edgeSlot,Fin.coe_natAdd,Fin.coe_castAdd]

theorem padding_packed (L : SubtypeTermLayout.Layout n d) :
    Fin.cast (by simp [SubtypeTermLayout.Layout.count]) (padding (L.terms.map pack) L.pairs.length).1 = L.padding := by
  apply Fin.ext
  simp [padding,StoredTermReference.padding_value,SubtypeTermLayout.Layout.padding]

theorem ref_packed (L : SubtypeTermLayout.Layout n d) (t : SubtypeTerms.Term n d) :
    Fin.cast (by simp [SubtypeTermLayout.Layout.count])
      (StoredTermReference.resolve (L.terms.map pack) L.pairs.length (pack t)).1 = L.ref t :=
  Fin.ext (StoredTermReference.packed_value L t)

theorem packed_value (L : SubtypeTermLayout.Layout n d) (i : Fin d) (j : Fin L.pairs.length) :
    StoredTermClause.transport (by simp [SubtypeTermLayout.Layout.count])
      (clause (L.terms.map pack) L.pairs.length i j (pack L.pairs[j.val].1) (pack L.pairs[j.val].2)).1 =
      SubtypeTermFlattening.edgeClause L i j := by
  simp only [clause,StoredTermClause.transport,List.map_cons,List.map_nil,
    StoredPaddedLiteral.transport_value,slot_packed,padding_packed,ref_packed,
    SubtypeTermFlattening.edgeClause]
end NSSE.StoredEdgeClause
