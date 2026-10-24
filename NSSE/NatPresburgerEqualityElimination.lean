import NSSE.NatPresburgerSubstitution

/-!
# Eliminating a defined existential variable

If the last existentially bound variable is constrained to equal a linear
term in the free variables, the quantifier is eliminated by substitution.
This is the basic equality-elimination rule used by Presburger
normalization and quantifier elimination.
-/

namespace NSSE

namespace NatPresburger

def substituteLast
    (term : NatLinearExpr arity) :
    Fin (arity + 1) → NatLinearExpr arity :=
  Fin.lastCases term NatLinearExpr.varExpr

@[simp] theorem eval_substituteLast_last
    (term : NatLinearExpr arity)
    (valuation : Fin arity → Nat) :
    (substituteLast term (Fin.last arity)).Eval valuation =
      term.Eval valuation := by
  simp [substituteLast]

@[simp] theorem eval_substituteLast_castSucc
    (term : NatLinearExpr arity)
    (valuation : Fin arity → Nat)
    (index : Fin arity) :
    (substituteLast term index.castSucc).Eval valuation =
      valuation index := by
  simp [substituteLast]

theorem eval_substituteLast
    (term : NatLinearExpr arity)
    (valuation : Fin arity → Nat) :
    (fun index =>
      (substituteLast term index).Eval valuation) =
      extendValuation valuation (term.Eval valuation) := by
  funext index
  refine Fin.lastCases ?_ (fun earlier => ?_) index
  · simp
  · simp

def eliminateDefinedLast
    (body : NatPresburger (arity + 1))
    (term : NatLinearExpr arity) :
    NatPresburger arity :=
  body.substitute (substituteLast term)

theorem eval_eliminateDefinedLast_iff
    (body : NatPresburger (arity + 1))
    (term : NatLinearExpr arity)
    (valuation : Fin arity → Nat) :
    (body.eliminateDefinedLast term).Eval valuation ↔
      body.Eval
        (extendValuation valuation
          (term.Eval valuation)) := by
  rw [eliminateDefinedLast, eval_substitute_iff,
    eval_substituteLast]

theorem standard_eliminateDefinedLast
    (body : NatPresburger (arity + 1))
    (hstandard : body.Standard)
    (term : NatLinearExpr arity) :
    (body.eliminateDefinedLast term).Standard :=
  body.standard_substitute hstandard (substituteLast term)

theorem eval_exists_eq_last_conj_iff
    (body : NatPresburger (arity + 1))
    (term : NatLinearExpr arity)
    (valuation : Fin arity → Nat) :
    (.existsQ
      (.conj
        (.equal
          (.varExpr (Fin.last arity))
          (weakenExpr term))
        body) : NatPresburger arity).Eval valuation ↔
      (body.eliminateDefinedLast term).Eval valuation := by
  simp only [Eval, NatLinearExpr.eval_variable,
    eval_weakenExpr]
  constructor
  · rintro ⟨bound, heq, heval⟩
    have hbound : bound = term.Eval valuation := by
      simpa using heq
    subst bound
    exact (body.eval_eliminateDefinedLast_iff
      term valuation).mpr heval
  · intro heval
    refine ⟨term.Eval valuation, by simp, ?_⟩
    exact (body.eval_eliminateDefinedLast_iff
      term valuation).mp heval

theorem eval_exists_last_eq_conj_iff
    (body : NatPresburger (arity + 1))
    (term : NatLinearExpr arity)
    (valuation : Fin arity → Nat) :
    (.existsQ
      (.conj
        (.equal
          (weakenExpr term)
          (.varExpr (Fin.last arity)))
        body) : NatPresburger arity).Eval valuation ↔
      (body.eliminateDefinedLast term).Eval valuation := by
  simp only [Eval, NatLinearExpr.eval_variable,
    eval_weakenExpr]
  constructor
  · rintro ⟨bound, heq, heval⟩
    have hbound : bound = term.Eval valuation := by
      simpa using heq.symm
    subst bound
    exact (body.eval_eliminateDefinedLast_iff
      term valuation).mpr heval
  · intro heval
    refine ⟨term.Eval valuation, by simp, ?_⟩
    exact (body.eval_eliminateDefinedLast_iff
      term valuation).mp heval

theorem eval_exists_conj_eq_last_iff
    (body : NatPresburger (arity + 1))
    (term : NatLinearExpr arity)
    (valuation : Fin arity → Nat) :
    (.existsQ
      (.conj body
        (.equal
          (.varExpr (Fin.last arity))
          (weakenExpr term))) :
        NatPresburger arity).Eval valuation ↔
      (body.eliminateDefinedLast term).Eval valuation := by
  simpa [Eval, and_comm] using
    body.eval_exists_eq_last_conj_iff term valuation

theorem eval_exists_conj_last_eq_iff
    (body : NatPresburger (arity + 1))
    (term : NatLinearExpr arity)
    (valuation : Fin arity → Nat) :
    (.existsQ
      (.conj body
        (.equal
          (weakenExpr term)
          (.varExpr (Fin.last arity)))) :
        NatPresburger arity).Eval valuation ↔
      (body.eliminateDefinedLast term).Eval valuation := by
  simpa [Eval, and_comm] using
    body.eval_exists_last_eq_conj_iff term valuation

end NatPresburger

end NSSE
