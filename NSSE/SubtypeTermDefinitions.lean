import NSSE.SubtypeTermLayout

/-! # Exact flat definitions for all finite subterms

The definitions force each nonvariable reference to its actual term value.
Both inequalities are emitted for a constructor, so antisymmetry applies.
-/

namespace NSSE.SubtypeTermDefinitions

open SubtypeTerms SubtypeTermLayout
open SubtypeConstraints (Constraints Constructor)
open SubtypeConstraintOperations

variable {n d m : Nat}

def empty : Constraints m d := ⟨[],[],[],[]⟩

def join (xs : List (Constraints m d)) : Constraints m d := xs.foldr combine empty

def termClause (L : Layout n d) : Term n d → Constraints L.count d
  | .var _ => empty
  | .bot => ⟨[],[],[L.ref .bot],[]⟩
  | .top => ⟨[],[],[],[L.ref .top]⟩
  | .node c => ⟨[(L.ref (.node c),fun i => L.ref (c i))],
      [(L.ref (.node c),fun i => L.ref (c i))],[],[]⟩

def definitions (L : Layout n d) : Constraints L.count d := join (L.terms.map (termClause L))

def Closed (L : Layout n d) : Prop :=
  ∀ c, Term.node c ∈ L.terms → ∀ i, c i ∈ L.terms

theorem layout_closed (Q : Query n d) : Closed (layout Q) := terms_closed Q

section Semantics

variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

theorem satisfies_join (F : Constructor T d) (xs : List (Constraints m d)) (σ : Fin m → T) :
    SubtypeConstraints.Satisfies F (join xs) σ ↔ ∀ φ ∈ xs, SubtypeConstraints.Satisfies F φ σ := by
  induction xs with
  | nil => simp [join, empty, SubtypeConstraints.Satisfies]
  | cons x xs ih =>
      change SubtypeConstraints.Satisfies F (combine x (join xs)) σ ↔ _
      rw [satisfies_combine, ih]
      simp

def Equation (F : Constructor T d) (L : Layout n d) (σ : Fin L.count → T) : Term n d → Prop
  | .var _ => True
  | .bot => σ (L.ref .bot) = ⊥
  | .top => σ (L.ref .top) = ⊤
  | .node c => σ (L.ref (.node c)) = F.node (fun i => σ (L.ref (c i)))

theorem termClause_correct (F : Constructor T d) (L : Layout n d) (σ : Fin L.count → T)
    (t : Term n d) : SubtypeConstraints.Satisfies F (termClause L t) σ ↔ Equation F L σ t := by
  have heq (a b : T) : a ≤ b ∧ b ≤ a ↔ a = b :=
    ⟨fun h => le_antisymm h.1 h.2,fun h => ⟨le_of_eq h,le_of_eq h.symm⟩⟩
  cases t <;> simp [termClause, empty, Equation, SubtypeConstraints.Satisfies, heq]

theorem definitions_correct (F : Constructor T d) (L : Layout n d) (σ : Fin L.count → T) :
    SubtypeConstraints.Satisfies F (definitions L) σ ↔ ∀ t ∈ L.terms, Equation F L σ t := by
  simp only [definitions, satisfies_join, List.forall_mem_map, termClause_correct]

theorem term_value (F : Constructor T d) (L : Layout n d) (hc : Closed L)
    (σ : Fin L.count → T) (hσ : SubtypeConstraints.Satisfies F (definitions L) σ)
    (t : Term n d) (hm : t ∈ L.terms) : σ (L.ref t) = eval F (L.restrict σ) t := by
  have he := (definitions_correct F L σ).mp hσ
  induction t with
  | var x => rfl
  | bot => exact he .bot hm
  | top => exact he .top hm
  | node c ih =>
      have hn := he (.node c) hm
      change σ (L.ref (.node c)) = F.node (fun i => σ (L.ref (c i))) at hn
      rw [hn]
      exact congrArg F.node (funext (fun i => ih i (hc c hm i)))

theorem extend_definitions (F : Constructor T d) (L : Layout n d) (hc : Closed L)
    (i : Fin d) (ρ : Fin n → T) : SubtypeConstraints.Satisfies F (definitions L) (L.extend i F ρ) := by
  apply (definitions_correct F L _).mpr
  intro t hm
  cases t with
  | var x => trivial
  | bot => exact extend_ref L i F ρ .bot hm
  | top => exact extend_ref L i F ρ .top hm
  | node c =>
      change L.extend i F ρ (L.ref (.node c)) = F.node (fun j => L.extend i F ρ (L.ref (c j)))
      rw [extend_ref L i F ρ (.node c) hm]
      exact congrArg F.node (funext (fun j => (extend_ref L i F ρ (c j) (hc c hm j)).symm))

end Semantics

end NSSE.SubtypeTermDefinitions
