import NSSE.NatPresburgerStandardization

/-!
# Substitution in Presburger formulas

Linear expressions may be substituted for all free variables at once.
Under a quantifier, the new bound variable is fixed while every free
replacement is weakened.  Evaluation is proved to commute with
substitution for expressions and complete formulas.
-/

namespace NSSE

namespace NatLinearExpr

def linearCombination
    (coefficient : Fin sourceArity → Nat)
    (terms : Fin sourceArity → NatLinearExpr targetArity) :
    NatLinearExpr targetArity :=
  (List.finRange sourceArity).foldr
    (fun index accumulated =>
      add (scale (coefficient index) (terms index))
        accumulated)
    (const 0)

theorem eval_linearCombination
    (coefficient : Fin sourceArity → Nat)
    (terms : Fin sourceArity → NatLinearExpr targetArity)
    (valuation : Fin targetArity → Nat) :
    (linearCombination coefficient terms).Eval valuation =
      ∑ index,
        coefficient index * (terms index).Eval valuation := by
  classical
  have hlist :
      ∀ indices : List (Fin sourceArity),
        (indices.foldr
          (fun index accumulated =>
            add (scale (coefficient index) (terms index))
              accumulated)
          (const 0)).Eval valuation =
        (indices.map fun index =>
          coefficient index *
            (terms index).Eval valuation).sum := by
    intro indices
    induction indices with
    | nil => simp
    | cons index rest ih =>
        simp [ih, Nat.add_comm]
  rw [linearCombination, hlist]
  rw [← List.sum_toFinset
    (fun index =>
      coefficient index * (terms index).Eval valuation)
    (List.nodup_finRange sourceArity),
    List.toFinset_finRange]

def substitute
    (expression : NatLinearExpr sourceArity)
    (replacement :
      Fin sourceArity → NatLinearExpr targetArity) :
    NatLinearExpr targetArity :=
  add (const expression.constant)
    (linearCombination expression.coefficient replacement)

@[simp] theorem eval_substitute
    (expression : NatLinearExpr sourceArity)
    (replacement :
      Fin sourceArity → NatLinearExpr targetArity)
    (valuation : Fin targetArity → Nat) :
    (expression.substitute replacement).Eval valuation =
      expression.Eval
        (fun index => (replacement index).Eval valuation) := by
  rw [substitute, eval_add, eval_const,
    eval_linearCombination]
  rfl

end NatLinearExpr

namespace NatPresburger

def liftSubstitution
    (replacement :
      Fin sourceArity → NatLinearExpr targetArity) :
    Fin (sourceArity + 1) →
      NatLinearExpr (targetArity + 1) :=
  Fin.lastCases
    (.varExpr (Fin.last targetArity))
    (fun index => weakenExpr (replacement index))

@[simp] theorem eval_liftSubstitution_last
    (replacement :
      Fin sourceArity → NatLinearExpr targetArity)
    (valuation : Fin targetArity → Nat)
    (bound : Nat) :
    (liftSubstitution replacement
      (Fin.last sourceArity)).Eval
        (extendValuation valuation bound) =
      bound := by
  simp [liftSubstitution]

@[simp] theorem eval_liftSubstitution_castSucc
    (replacement :
      Fin sourceArity → NatLinearExpr targetArity)
    (valuation : Fin targetArity → Nat)
    (bound : Nat)
    (index : Fin sourceArity) :
    (liftSubstitution replacement index.castSucc).Eval
        (extendValuation valuation bound) =
      (replacement index).Eval valuation := by
  simp [liftSubstitution]

theorem eval_liftSubstitution
    (replacement :
      Fin sourceArity → NatLinearExpr targetArity)
    (valuation : Fin targetArity → Nat)
    (bound : Nat) :
    (fun index =>
      (liftSubstitution replacement index).Eval
        (extendValuation valuation bound)) =
      extendValuation
        (fun index => (replacement index).Eval valuation)
        bound := by
  funext index
  refine Fin.lastCases ?_ (fun earlier => ?_) index
  · simp
  · simp

def substitute
    (replacement :
      Fin sourceArity → NatLinearExpr targetArity) :
    NatPresburger sourceArity →
      NatPresburger targetArity
  | .falsum => .falsum
  | .equal left right =>
      .equal (left.substitute replacement)
        (right.substitute replacement)
  | .lessEqual left right =>
      .lessEqual (left.substitute replacement)
        (right.substitute replacement)
  | .congruent left right modulus =>
      .congruent (left.substitute replacement)
        (right.substitute replacement) modulus
  | .afterCongruent expression threshold modulus residue =>
      .afterCongruent
        (expression.substitute replacement)
        threshold modulus residue
  | .neg formula => .neg (formula.substitute replacement)
  | .conj left right =>
      .conj (left.substitute replacement)
        (right.substitute replacement)
  | .disj left right =>
      .disj (left.substitute replacement)
        (right.substitute replacement)
  | .existsQ formula =>
      .existsQ
        (formula.substitute
          (liftSubstitution replacement))

theorem eval_substitute_iff
    (formula : NatPresburger sourceArity)
    (replacement :
      Fin sourceArity → NatLinearExpr targetArity)
    (valuation : Fin targetArity → Nat) :
    (formula.substitute replacement).Eval valuation ↔
      formula.Eval
        (fun index => (replacement index).Eval valuation) := by
  induction formula generalizing targetArity with
  | falsum => rfl
  | equal left right =>
      simp [substitute, Eval]
  | lessEqual left right =>
      simp [substitute, Eval]
  | congruent left right modulus =>
      simp [substitute, Eval]
  | afterCongruent expression threshold modulus residue =>
      simp [substitute, Eval]
  | neg formula ih =>
      exact not_congr (ih replacement valuation)
  | conj left right ihLeft ihRight =>
      exact and_congr
        (ihLeft replacement valuation)
        (ihRight replacement valuation)
  | disj left right ihLeft ihRight =>
      exact or_congr
        (ihLeft replacement valuation)
        (ihRight replacement valuation)
  | existsQ formula ih =>
      simp only [substitute, Eval]
      constructor
      · rintro ⟨bound, heval⟩
        refine ⟨bound, ?_⟩
        rw [ih (liftSubstitution replacement)
          (extendValuation valuation bound),
          eval_liftSubstitution] at heval
        exact heval
      · rintro ⟨bound, heval⟩
        refine ⟨bound, ?_⟩
        rw [ih (liftSubstitution replacement)
          (extendValuation valuation bound),
          eval_liftSubstitution]
        exact heval

theorem eval_substitute_variables_iff
    (formula : NatPresburger arity)
    (valuation : Fin arity → Nat) :
    (formula.substitute NatLinearExpr.varExpr).Eval
        valuation ↔
      formula.Eval valuation := by
  rw [formula.eval_substitute_iff]
  simp

theorem eval_substitute_comp_iff
    (formula : NatPresburger sourceArity)
    (first :
      Fin sourceArity → NatLinearExpr middleArity)
    (second :
      Fin middleArity → NatLinearExpr targetArity)
    (valuation : Fin targetArity → Nat) :
    ((formula.substitute first).substitute second).Eval
        valuation ↔
      (formula.substitute
        (fun index =>
          (first index).substitute second)).Eval
        valuation := by
  rw [eval_substitute_iff, eval_substitute_iff,
    eval_substitute_iff]
  simp

def reindex
    (formula : NatPresburger sourceArity)
    (variableMap : Fin sourceArity → Fin targetArity) :
    NatPresburger targetArity :=
  formula.substitute
    (fun index => .varExpr (variableMap index))

theorem eval_reindex_iff
    (formula : NatPresburger sourceArity)
    (variableMap : Fin sourceArity → Fin targetArity)
    (valuation : Fin targetArity → Nat) :
    (formula.reindex variableMap).Eval valuation ↔
      formula.Eval (fun index => valuation (variableMap index)) := by
  rw [reindex, eval_substitute_iff]
  simp

theorem standard_substitute
    (formula : NatPresburger sourceArity)
    (hstandard : formula.Standard)
    (replacement :
      Fin sourceArity → NatLinearExpr targetArity) :
    (formula.substitute replacement).Standard := by
  induction formula generalizing targetArity with
  | falsum => trivial
  | equal left right => trivial
  | lessEqual left right => trivial
  | congruent left right modulus => trivial
  | afterCongruent expression threshold modulus residue =>
      exact False.elim hstandard
  | neg formula ih =>
      exact ih hstandard replacement
  | conj left right ihLeft ihRight =>
      exact ⟨ihLeft hstandard.1 replacement,
        ihRight hstandard.2 replacement⟩
  | disj left right ihLeft ihRight =>
      exact ⟨ihLeft hstandard.1 replacement,
        ihRight hstandard.2 replacement⟩
  | existsQ formula ih =>
      exact ih hstandard (liftSubstitution replacement)

theorem quantifierFree_substitute
    (formula : NatPresburger sourceArity)
    (hfree : formula.QuantifierFree)
    (replacement :
      Fin sourceArity → NatLinearExpr targetArity) :
    (formula.substitute replacement).QuantifierFree := by
  induction formula generalizing targetArity with
  | falsum => trivial
  | equal left right => trivial
  | lessEqual left right => trivial
  | congruent left right modulus => trivial
  | afterCongruent expression threshold modulus residue =>
      trivial
  | neg formula ih =>
      exact ih hfree replacement
  | conj left right ihLeft ihRight =>
      exact ⟨ihLeft hfree.1 replacement,
        ihRight hfree.2 replacement⟩
  | disj left right ihLeft ihRight =>
      exact ⟨ihLeft hfree.1 replacement,
        ihRight hfree.2 replacement⟩
  | existsQ formula =>
      exact False.elim hfree

end NatPresburger

end NSSE
