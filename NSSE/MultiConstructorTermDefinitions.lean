import NSSE.MultiConstructorTermLayout

/-! Each named constructor subterm gets both original bounds. Every
valuation satisfying these definitions evaluates its references exactly. -/
namespace NSSE.MultiConstructorTermDefinitions
open MultiConstructorTerms MultiConstructorTermLayout
open MultiConstructorConstraints (Constraints Algebra)
open MultiConstructorInputMap
variable {H : Type*} {arity : H → Nat} {n m : Nat}

def empty : Constraints arity m := ⟨[],[],[],[]⟩
def join (xs : List (Constraints arity m)) : Constraints arity m := xs.foldr append empty

def termClause [DecidableEq H] (L : Layout arity n) : Term arity n → Constraints arity L.count
  | .var _ => empty
  | .bot => ⟨[],[],[L.ref .bot],[]⟩
  | .top => ⟨[],[],[],[L.ref .top]⟩
  | .node h c => ⟨[⟨L.ref (.node h c),h,fun i => L.ref (c i)⟩],
      [⟨L.ref (.node h c),h,fun i => L.ref (c i)⟩],[],[]⟩

def definitions [DecidableEq H] (L : Layout arity n) : Constraints arity L.count :=
  join (L.terms.map (termClause L))

def Closed (L : Layout arity n) : Prop := ∀ h c, Term.node h c ∈ L.terms → ∀ i, c i ∈ L.terms
theorem layout_closed (Q : Query arity n) : Closed (layout Q) := terms_closed Q

section Semantics
variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

theorem satisfies_join (F : Algebra (arity := arity) T) (xs : List (Constraints arity m)) (sigma : Fin m → T) :
    MultiConstructorConstraints.Satisfies F (join xs) sigma ↔
      ∀ phi ∈ xs, MultiConstructorConstraints.Satisfies F phi sigma := by
  induction xs with
  | nil => simp [join,empty,MultiConstructorConstraints.Satisfies]
  | cons x xs ih =>
    change MultiConstructorConstraints.Satisfies F (append x (join xs)) sigma ↔ _
    rw [append_iff,ih]
    simp

variable [DecidableEq H]

def Equation (F : Algebra (arity := arity) T) (L : Layout arity n) (sigma : Fin L.count → T) : Term arity n → Prop
  | .var _ => True
  | .bot => sigma (L.ref .bot) = ⊥
  | .top => sigma (L.ref .top) = ⊤
  | .node h c => sigma (L.ref (.node h c)) = F.node h (fun i => sigma (L.ref (c i)))

theorem termClause_correct (F : Algebra (arity := arity) T) (L : Layout arity n) (sigma : Fin L.count → T)
    (t : Term arity n) : MultiConstructorConstraints.Satisfies F (termClause L t) sigma ↔ Equation F L sigma t := by
  have heq (a b : T) : a ≤ b ∧ b ≤ a ↔ a = b :=
    ⟨fun h => le_antisymm h.1 h.2,fun h => ⟨le_of_eq h,le_of_eq h.symm⟩⟩
  cases t <;> simp [termClause,empty,Equation,MultiConstructorConstraints.Satisfies,heq]

theorem definitions_correct (F : Algebra (arity := arity) T) (L : Layout arity n) (sigma : Fin L.count → T) :
    MultiConstructorConstraints.Satisfies F (definitions L) sigma ↔ ∀ t ∈ L.terms, Equation F L sigma t := by
  simp only [definitions,satisfies_join,List.forall_mem_map,termClause_correct]

theorem term_value (F : Algebra (arity := arity) T) (L : Layout arity n) (hc : Closed L)
    (sigma : Fin L.count → T) (hs : MultiConstructorConstraints.Satisfies F (definitions L) sigma)
    (t : Term arity n) (ht : t ∈ L.terms) : sigma (L.ref t) = eval F (L.restrict sigma) t := by
  have he := (definitions_correct F L sigma).mp hs
  induction t with
  | var x => rfl
  | bot => exact he .bot ht
  | top => exact he .top ht
  | node h c ih =>
    have hn := he (.node h c) ht
    change sigma (L.ref (.node h c)) = F.node h (fun i => sigma (L.ref (c i))) at hn
    rw [hn]
    exact congrArg (F.node h) (funext (fun i => ih i (hc h c ht i)))

theorem extend_definitions (F : Algebra (arity := arity) T) (L : Layout arity n) (hc : Closed L)
    (h : H) (rho : Fin n → T) : MultiConstructorConstraints.Satisfies F (definitions L) (L.extend h F rho) := by
  apply (definitions_correct F L _).mpr
  intro t ht
  cases t with
  | var x => trivial
  | bot => exact extend_ref L h F rho .bot ht
  | top => exact extend_ref L h F rho .top ht
  | node g c =>
    change L.extend h F rho (L.ref (.node g c)) = F.node g (fun i => L.extend h F rho (L.ref (c i)))
    rw [extend_ref L h F rho (.node g c) ht]
    exact congrArg (F.node g) (funext (fun i => (extend_ref L h F rho (c i) (hc g c ht i)).symm))

end Semantics
end NSSE.MultiConstructorTermDefinitions
