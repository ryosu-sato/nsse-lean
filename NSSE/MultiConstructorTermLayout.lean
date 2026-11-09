import NSSE.MultiConstructorTerms

/-! Computable slots for old variables, subterms and premise edges.
Each edge uses a chosen constructor on constant tuples of child values. -/
namespace NSSE.MultiConstructorTermLayout
open MultiConstructorTerms
open MultiConstructorConstraints (Algebra)

structure Layout {H : Type*} (arity : H → Nat) (n : Nat) where
  terms : List (Term arity n)
  pairs : List (Term arity n × Term arity n)

variable {H : Type*} {arity : H → Nat} {n : Nat}

def layout (Q : Query arity n) : Layout arity n := ⟨MultiConstructorTerms.terms Q,expanded Q⟩
def Layout.count (L : Layout arity n) : Nat := n+(L.terms.length+(L.pairs.length+1))
def Layout.old (L : Layout arity n) (x : Fin n) : Fin L.count := Fin.castAdd _ x
def Layout.termSlot (L : Layout arity n) (j : Fin L.terms.length) : Fin L.count := Fin.natAdd n (Fin.castAdd _ j)
def Layout.edgeSlot (L : Layout arity n) (j : Fin L.pairs.length) : Fin L.count :=
  Fin.natAdd n (Fin.natAdd L.terms.length (Fin.castAdd 1 j))
def Layout.padding (L : Layout arity n) : Fin L.count :=
  Fin.natAdd n (Fin.natAdd L.terms.length (Fin.natAdd L.pairs.length (0 : Fin 1)))

def Layout.ref [DecidableEq H] (L : Layout arity n) (t : Term arity n) : Fin L.count :=
  match t with
  | .var x => L.old x
  | t => if ht : t ∈ L.terms then L.termSlot ⟨L.terms.idxOf t,List.idxOf_lt_length_iff.mpr ht⟩ else L.padding

section Semantics
variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

def Layout.restrict (L : Layout arity n) (sigma : Fin L.count → T) (x : Fin n) : T := sigma (L.old x)

def Layout.extend (L : Layout arity n) (h : H) (F : Algebra (arity := arity) T) (rho : Fin n → T) : Fin L.count → T :=
  Fin.addCases rho (Fin.addCases (fun j => eval F rho L.terms[j.val])
    (Fin.addCases (fun j => F.node h (fun _ => eval F rho L.pairs[j.val].1)) (fun _ => ⊥)))

@[simp] theorem extend_old (L : Layout arity n) (h : H) (F : Algebra (arity := arity) T)
    (rho : Fin n → T) (x : Fin n) : L.extend h F rho (L.old x) = rho x := by
  simp [Layout.extend,Layout.old]

@[simp] theorem restrict_extend (L : Layout arity n) (h : H) (F : Algebra (arity := arity) T) (rho : Fin n → T) :
    L.restrict (L.extend h F rho) = rho := by funext x; exact extend_old L h F rho x

@[simp] theorem extend_termSlot (L : Layout arity n) (h : H) (F : Algebra (arity := arity) T)
    (rho : Fin n → T) (j : Fin L.terms.length) : L.extend h F rho (L.termSlot j) = eval F rho L.terms[j.val] := by
  simp [Layout.extend,Layout.termSlot,Fin.addCases_right]

@[simp] theorem extend_edgeSlot (L : Layout arity n) (h : H) (F : Algebra (arity := arity) T)
    (rho : Fin n → T) (j : Fin L.pairs.length) :
    L.extend h F rho (L.edgeSlot j) = F.node h (fun _ => eval F rho L.pairs[j.val].1) := by
  simp [Layout.extend,Layout.edgeSlot,Fin.addCases_right]

@[simp] theorem extend_padding (L : Layout arity n) (h : H) (F : Algebra (arity := arity) T)
    (rho : Fin n → T) : L.extend h F rho L.padding = ⊥ := by
  simp [Layout.extend,Layout.padding,Fin.addCases_right]

theorem extend_ref [DecidableEq H] (L : Layout arity n) (h : H) (F : Algebra (arity := arity) T)
    (rho : Fin n → T) (t : Term arity n) (ht : t ∈ L.terms) : L.extend h F rho (L.ref t) = eval F rho t := by
  cases t with
  | var x => exact extend_old L h F rho x
  | bot => simp only [Layout.ref,dif_pos ht,extend_termSlot,List.getElem_idxOf]
  | top => simp only [Layout.ref,dif_pos ht,extend_termSlot,List.getElem_idxOf]
  | node g c => simp only [Layout.ref,dif_pos ht,extend_termSlot,List.getElem_idxOf]

theorem copy_order (F : Algebra (arity := arity) T) (h : H) (i : Fin (arity h)) (a b : T) :
    F.node h (fun _ => a) ≤ F.node h (fun _ => b) ↔ a ≤ b := by
  rw [F.node_le_node]
  exact ⟨fun hh => hh i,fun hh _ => hh⟩

theorem extend_closed (L : Layout arity n) (h : H) (F : Algebra (arity := arity) T) (P : T → Prop)
    (hb : P ⊥) (ht : P ⊤) (hn : ∀ g c, (∀ i, P (c i)) → P (F.node g c))
    (rho : Fin n → T) (hr : ∀ x, P (rho x)) : ∀ x, P (L.extend h F rho x) := by
  apply Fin.addCases
  · intro x
    simp only [Layout.extend,Fin.addCases_left]
    exact hr x
  · apply Fin.addCases
    · intro j
      simp only [Layout.extend,Fin.addCases_right,Fin.addCases_left]
      exact eval_closed F P hb ht hn rho hr L.terms[j.val]
    · apply Fin.addCases
      · intro j
        simp only [Layout.extend,Fin.addCases_right,Fin.addCases_left]
        exact hn h _ (fun _ => eval_closed F P hb ht hn rho hr L.pairs[j.val].1)
      · intro j
        simp only [Layout.extend,Fin.addCases_right]
        exact hb

end Semantics
end NSSE.MultiConstructorTermLayout
