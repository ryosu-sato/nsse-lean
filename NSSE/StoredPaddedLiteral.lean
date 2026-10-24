import NSSE.StoredTermLiteral
import NSSE.SubtypeTermLayout

namespace NSSE.StoredPaddedLiteral
variable {n d : Nat}

def cell (i : Fin d) (a e : Fin n) (j : Fin d) : Fin n × Nat :=
  let r := FiniteValuationLookup.equalNat j.val i.val
  (if r.1 then a else e,1+r.2)

theorem cell_value (i : Fin d) (a e : Fin n) (j : Fin d) :
    (cell i a e j).1 = SubtypeTermLayout.padded i a e j := by
  have h : (FiniteValuationLookup.equalNat j.val i.val).1 = true ↔ j=i := by
    rw [FiniteValuationLookup.equalNat_correct,Fin.ext_iff]
  simp only [cell,SubtypeTermLayout.padded,h]

theorem cell_bound (i : Fin d) (a e : Fin n) (j : Fin d) :
    (cell i a e j).2 ≤ 1+d := by
  have h := FiniteValuationLookup.equalFin_bound j i
  simp only [cell]; omega

def literal (i : Fin d) (head a e : Fin n) : StoredSubtypeInput.Bound n d × Nat :=
  let cs := CountedFinEnumeration.tabulate d (cell i a e)
  (⟨head,cs.1,by change (CountedFinEnumeration.tabulate d (cell i a e)).1.length = d; simp only [CountedFinEnumeration.tabulate_value,List.length_ofFn]⟩,1+cs.2)

theorem value (i : Fin d) (head a e : Fin n) :
    (literal i head a e).1.denote = (head,SubtypeTermLayout.padded i a e) := by
  apply Prod.ext
  · rfl
  · funext j
    simp only [literal,StoredSubtypeInput.Bound.denote,CountedFinEnumeration.tabulate_value,
      List.getElem_ofFn,cell_value]

def budget (d : Nat) := 3+(d+1)^2+d*(2+d)

theorem bound (i : Fin d) (head a e : Fin n) : (literal i head a e).2 ≤ budget d := by
  have h := CountedFinEnumeration.tabulate_bound d (cell i a e) (1+d) (cell_bound i a e)
  simp only [←Nat.add_assoc] at h; norm_num only at h
  simp only [literal,budget]; omega

theorem transport_value {m : Nat} (h : n=m) (i : Fin d) (head a e : Fin n) :
    StoredTermLiteral.transport h (literal i head a e).1 =
      (Fin.cast h head,SubtypeTermLayout.padded i (Fin.cast h a) (Fin.cast h e)) := by
  subst m
  simpa only [StoredTermLiteral.transport,Fin.cast_refl] using value i head a e
end NSSE.StoredPaddedLiteral
