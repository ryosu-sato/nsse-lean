import NSSE.TermCountermodelExtraction

/-! # Non-vacuous term-input families, including zero original variables

These are general semantic theorems, not bounded empirical claims.
-/

namespace NSSE.TermDecisionExamples

open SubtypeTerms TermEntailmentDecision TermCountermodelExtraction

variable {d : Nat}

def closedNegative (d : Nat) : Query 0 d := ⟨[],.node (fun _ => .bot),.bot⟩

theorem closedNegative_finite_false (hd : 0 < d) : decideFinite (closedNegative d) hd = false := by
  apply (decideFinite_false _ hd).mpr
  refine ⟨Fin.elim0,?_,?_⟩
  · simp [Satisfies,closedNegative]
  · intro h
    change FiniteSubtypeTrees.Below (.node (fun _ => .bot)) .bot at h
    cases h

theorem closedNegative_all_false (hd : 0 < d) : decideAll (closedNegative d) hd = false := by
  apply (decideAll_false _ hd).mpr
  refine ⟨Fin.elim0,?_,?_⟩
  · simp [Satisfies,closedNegative]
  · intro h
    exact (by decide : ¬ (1 : AbsorbingSubtypeTrees.Label) ≤ 0) (h [])

theorem closedNegative_finite_output (hd : 0 < d) :
    ∃ c, extractFinite (closedNegative d) hd = some c :=
  (extractFinite_exists_iff_false _ hd).mpr (closedNegative_finite_false hd)

theorem closedNegative_regular_output (hd : 0 < d) :
    ∃ c, extractRegular (closedNegative d) hd = some c :=
  (extractRegular_exists_iff_false _ hd).mpr (closedNegative_all_false hd)

def nested {n : Nat} (t : Term n d) : Term n d := .node (fun _ => .node (fun _ => t))

def equalityQuery (d : Nat) : Query 2 d :=
  ⟨[.eq (.var 0) (nested (.var 1))],.var 0,nested (.var 1)⟩

theorem equalityQuery_entails {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]
    (F : SubtypeConstraints.Constructor T d) : Entails F (equalityQuery d) := by
  intro ρ hρ
  exact le_of_eq (hρ (.eq (.var 0) (nested (.var 1))) (by simp [equalityQuery]))

theorem equalityQuery_satisfiable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]
    (F : SubtypeConstraints.Constructor T d) : Satisfiable F (equalityQuery d) := by
  refine ⟨fun x => if x = 0 then F.node (fun _ => F.node (fun _ => ⊥)) else ⊥,?_⟩
  simp [Satisfies,Holds,equalityQuery,nested,eval]

theorem equalityQuery_finite_true (hd : 0 < d) : decideFinite (equalityQuery d) hd = true :=
  (decideFinite_correct _ hd).mpr (equalityQuery_entails (FiniteSubtypeTrees.constructor d))

theorem equalityQuery_all_true (hd : 0 < d) : decideAll (equalityQuery d) hd = true :=
  (decideAll_correct _ hd).mpr (equalityQuery_entails (AbsorbingSubtypeTrees.constructor d))

theorem equalityQuery_finite_sat (hd : 0 < d) : decideFiniteSatisfiable (equalityQuery d) hd = true :=
  (decideFiniteSatisfiable_correct _ hd).mpr (equalityQuery_satisfiable (FiniteSubtypeTrees.constructor d))

theorem equalityQuery_all_sat (hd : 0 < d) : decideAllSatisfiable (equalityQuery d) hd = true :=
  (decideAllSatisfiable_correct _ hd).mpr (equalityQuery_satisfiable (AbsorbingSubtypeTrees.constructor d))

end NSSE.TermDecisionExamples
