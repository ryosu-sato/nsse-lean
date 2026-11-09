import NSSE.MultiVarianceTerms

/-! Actual old/subterm/edge slots, with signed comparison copies. Every
negative child reverses the two premise endpoints in the edge gadget. -/
namespace NSSE.MultiVarianceTermLayout
open MultiConstructorTerms (Term Query)
open MultiConstructorTermLayout (Layout layout)
open MultiVarianceEncoding MultiVarianceTrees MultiVarianceTerms
variable {H : Type*} {arity : H → Nat} {n : Nat} (pol : Polarity arity)

def copyChildren (h : H) (a b : Tree pol) (j : Fin (arity h)) : Tree pol := if pol h j then b else a

theorem copy_order (h : H) (i : Fin (arity h)) (a b : Tree pol) :
    node h (copyChildren pol h a b)≤node h (copyChildren pol h b a) ↔ a≤b := by
  rw [node_le_node]
  constructor
  · intro hh
    have hc := hh i
    cases hp : pol h i <;> simpa only [copyChildren,hp,Bool.false_eq_true,if_false,if_true] using hc
  · intro hh j
    cases hp : pol h j <;> simpa only [copyChildren,hp,Bool.false_eq_true,if_false,if_true] using hh

def extend (L : Layout arity n) (h : H) (rho : Fin n → Tree pol) : Fin L.count → Tree pol :=
  Fin.addCases rho (Fin.addCases (fun j => eval pol rho L.terms[j.val])
    (Fin.addCases (fun j => node h (copyChildren pol h (eval pol rho L.pairs[j.val].1)
      (eval pol rho L.pairs[j.val].2))) (fun _ => ⊥)))

@[simp] theorem extend_old (L : Layout arity n) (h : H) (rho : Fin n → Tree pol) (x : Fin n) :
    extend pol L h rho (L.old x)=rho x := by simp [extend,Layout.old]
@[simp] theorem restrict_extend (L : Layout arity n) (h : H) (rho : Fin n → Tree pol) :
    L.restrict (extend pol L h rho)=rho := by funext x; exact extend_old pol L h rho x
@[simp] theorem extend_termSlot (L : Layout arity n) (h : H) (rho : Fin n → Tree pol) (j : Fin L.terms.length) :
    extend pol L h rho (L.termSlot j)=eval pol rho L.terms[j.val] := by
  simp [extend,Layout.termSlot,Fin.addCases_right]
@[simp] theorem extend_edgeSlot (L : Layout arity n) (h : H) (rho : Fin n → Tree pol) (j : Fin L.pairs.length) :
    extend pol L h rho (L.edgeSlot j)=node h (copyChildren pol h (eval pol rho L.pairs[j.val].1)
      (eval pol rho L.pairs[j.val].2)) := by simp [extend,Layout.edgeSlot,Fin.addCases_right]
@[simp] theorem extend_padding (L : Layout arity n) (h : H) (rho : Fin n → Tree pol) :
    extend pol L h rho L.padding=⊥ := by simp [extend,Layout.padding,Fin.addCases_right]

theorem extend_ref [DecidableEq H] (L : Layout arity n) (h : H) (rho : Fin n → Tree pol)
    (t : Term arity n) (ht : t∈L.terms) : extend pol L h rho (L.ref t)=eval pol rho t := by
  cases t with
  | var x => exact extend_old pol L h rho x
  | bot => simp only [Layout.ref,dif_pos ht,extend_termSlot,List.getElem_idxOf]
  | top => simp only [Layout.ref,dif_pos ht,extend_termSlot,List.getElem_idxOf]
  | node g c => simp only [Layout.ref,dif_pos ht,extend_termSlot,List.getElem_idxOf]

theorem extend_closed (L : Layout arity n) (h : H) (P : Tree pol → Prop) (hb : P ⊥) (ht : P ⊤)
    (hn : ∀ g c, (∀ i, P (c i)) → P (node g c)) (rho : Fin n → Tree pol) (hr : ∀ x, P (rho x)) :
    ∀ x, P (extend pol L h rho x) := by
  apply Fin.addCases
  · intro x
    simp only [extend,Fin.addCases_left]
    exact hr x
  · apply Fin.addCases
    · intro j
      simp only [extend,Fin.addCases_right,Fin.addCases_left]
      exact eval_closed pol P hb ht hn rho hr L.terms[j.val]
    · apply Fin.addCases
      · intro j
        simp only [extend,Fin.addCases_right,Fin.addCases_left]
        apply hn
        intro i
        unfold copyChildren
        split_ifs <;> exact eval_closed pol P hb ht hn rho hr _
      · intro j
        simp only [extend,Fin.addCases_right]
        exact hb

end NSSE.MultiVarianceTermLayout
