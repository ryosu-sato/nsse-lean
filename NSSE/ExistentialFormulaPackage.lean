import NSSE.BoundedExistentialScalarLowering

/-! # Executable existential-prefix packages with capture-free composition

An explicit finite witness count and an actual quantifier-free matrix are
maintained together. Conjunction/disjunction add witness counts, and binding
concatenates them; no Boolean distribution or duplicated matrices are used.
-/

namespace NSSE.ExistentialFormulaPackage

open FirstOrder FirstOrder.Language ExactReachabilityTable SymbolicReachability ExactReachabilitySize

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w}

structure Package (L : FirstOrder.Language.{u,v}) (P : Type w) where
  vars : Nat
  body : L.Formula (P ⊕ Fin vars)
  qfree : body.IsQF

namespace Package

def toFormula (A : Package L P) : L.Formula P := closeColumn A.body

def atom (f : L.Formula P) (hf : f.IsQF) : Package L P :=
  ⟨0, f.relabel Sum.inl, relabel_qf f hf _⟩

def conj (A B : Package L P) : Package L P :=
  ⟨A.vars+B.vars,
    A.body.relabel (Sum.map id (Fin.castAdd B.vars)) ⊓
      B.body.relabel (Sum.map id (Fin.natAdd A.vars)),
    (relabel_qf _ A.qfree _).inf (relabel_qf _ B.qfree _)⟩

def disj (A B : Package L P) : Package L P :=
  ⟨A.vars+B.vars,
    A.body.relabel (Sum.map id (Fin.castAdd B.vars)) ⊔
      B.body.relabel (Sum.map id (Fin.natAdd A.vars)),
    (relabel_qf _ A.qfree _).sup (relabel_qf _ B.qfree _)⟩

def joinNames (m n : Nat) : (P ⊕ Fin m) ⊕ Fin n → P ⊕ Fin (m+n)
  | .inl (.inl p) => .inl p
  | .inl (.inr i) => .inr (Fin.castAdd n i)
  | .inr j => .inr (Fin.natAdd m j)

def bind (m : Nat) (A : Package L (P ⊕ Fin m)) : Package L P :=
  ⟨m+A.vars, A.body.relabel (joinNames m A.vars), relabel_qf _ A.qfree _⟩

theorem exists_append {D : Type*} (m n : Nat) (Φ : (Fin (m+n) → D) → Prop) :
    (∃ z, Φ z) ↔ ∃ x y, Φ (Fin.append x y) := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨(fun i => z (Fin.castAdd n i)), (fun j => z (Fin.natAdd m j)), ?_⟩
    have he : Fin.append (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j)) = z := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    rwa [he]
  · rintro ⟨x,y,h⟩
    exact ⟨Fin.append x y,h⟩

theorem left_values {D : Type*} (p : P → D) {m n : Nat} (x : Fin m → D) (y : Fin n → D) :
    Sum.elim p (Fin.append x y) ∘ Sum.map id (Fin.castAdd n) = Sum.elim p x := by
  funext a
  cases a <;> simp [Function.comp_def]

theorem right_values {D : Type*} (p : P → D) {m n : Nat} (x : Fin m → D) (y : Fin n → D) :
    Sum.elim p (Fin.append x y) ∘ Sum.map id (Fin.natAdd m) = Sum.elim p y := by
  funext a
  cases a <;> simp [Function.comp_def]

theorem joined_values {D : Type*} (p : P → D) {m n : Nat} (x : Fin m → D) (y : Fin n → D) :
    Sum.elim p (Fin.append x y) ∘ joinNames m n = Sum.elim (Sum.elim p x) y := by
  funext a
  cases a with
  | inl a => cases a <;> simp [joinNames, Function.comp_def]
  | inr i => simp [joinNames, Function.comp_def]

theorem atom_correct {D : Type*} [L.Structure D] (p : P → D) (f : L.Formula P) (hf : f.IsQF) :
    (atom f hf).toFormula.Realize p ↔ f.Realize p := by
  simp [toFormula, atom, Formula.realize_relabel, Function.comp_def]

theorem conj_correct {D : Type*} [L.Structure D] (p : P → D) (A B : Package L P) :
    (conj A B).toFormula.Realize p ↔ A.toFormula.Realize p ∧ B.toFormula.Realize p := by
  simp only [toFormula, conj, realize_closeColumn]
  rw [exists_append A.vars B.vars]
  simp only [Formula.realize_inf, Formula.realize_relabel, left_values, right_values]
  constructor
  · rintro ⟨x,y,hx,hy⟩
    exact ⟨⟨x,hx⟩,⟨y,hy⟩⟩
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    exact ⟨x,y,hx,hy⟩

theorem disj_correct {D : Type*} [L.Structure D] [Nonempty D] (p : P → D) (A B : Package L P) :
    (disj A B).toFormula.Realize p ↔ A.toFormula.Realize p ∨ B.toFormula.Realize p := by
  simp only [toFormula, disj, realize_closeColumn]
  rw [exists_append A.vars B.vars]
  simp only [Formula.realize_sup, Formula.realize_relabel, left_values, right_values]
  constructor
  · rintro ⟨x,y,h⟩
    exact h.elim (fun hx => Or.inl ⟨x,hx⟩) (fun hy => Or.inr ⟨y,hy⟩)
  · classical
    rintro (⟨x,hx⟩ | ⟨y,hy⟩)
    · exact ⟨x, (fun _ => Classical.ofNonempty), Or.inl hx⟩
    · exact ⟨(fun _ => Classical.ofNonempty), y, Or.inr hy⟩

theorem bind_correct {D : Type*} [L.Structure D] (p : P → D) (m : Nat) (A : Package L (P ⊕ Fin m)) :
    (bind m A).toFormula.Realize p ↔ ∃ x : Fin m → D, A.toFormula.Realize (Sum.elim p x) := by
  simp only [toFormula, bind, realize_closeColumn]
  rw [exists_append m A.vars]
  simp only [Formula.realize_relabel, joined_values]

def boundedBody (A : Package L P) : L.BoundedFormula P A.vars :=
  BoundedFormula.relabel id A.body

theorem boundedBody_qf (A : Package L P) : A.boundedBody.IsQF := A.qfree.relabel id

theorem toFormula_eq_exs (A : Package L P) : A.toFormula = A.boundedBody.exs := rfl

theorem nodes_atom (f : L.Formula P) (hf : f.IsQF) : nodes (atom f hf).toFormula = nodes f := by
  simp [toFormula, atom]

theorem nodes_conj (A B : Package L P) :
    nodes (conj A B).toFormula = 5+nodes A.toFormula+nodes B.toFormula := by
  simp [toFormula, conj]
  ring

theorem nodes_disj (A B : Package L P) :
    nodes (disj A B).toFormula = 3+nodes A.toFormula+nodes B.toFormula := by
  simp [toFormula, disj]
  ring

theorem nodes_bind (m : Nat) (A : Package L (P ⊕ Fin m)) :
    nodes (bind m A).toFormula = nodes A.toFormula+5*m := by
  simp [toFormula, bind]
  ring

end Package
end NSSE.ExistentialFormulaPackage
