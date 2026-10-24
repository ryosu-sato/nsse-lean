import NSSE.RankNextQuantifierFree

/-! # Qfree closure of the actual epsilon, complement and product constructions -/

namespace NSSE.RowBooleanClosureQuantifierFree

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks SymbolicAutomata SymbolicReachability
open ExactReachabilityTable ArrayAtomExistentialPackages

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {n m r : Nat} {arity : Fin m → Nat}

structure AutomatonQF (A : Automaton L P n m arity) : Prop where
  initial : ∀ q, (A.initial q).IsQF
  final : ∀ q, (A.final q).IsQF
  silent : ∀ q r, (A.silent q r).IsQF
  step : ∀ s q r, (A.step s q r).IsQF

theorem reach_qf (W : Fin n → Fin n → L.Formula P) (h : ∀ a b, (W a b).IsQF) (a b : Fin n) :
    (reach W a b).IsQF := by
  have hr (a b : Fin n) : (reflexiveEdges W a b).IsQF := by
    unfold reflexiveEdges
    split
    · exact BoundedFormula.IsQF.top.sup (h a b)
    · exact BoundedFormula.isQF_bot.sup (h a b)
  have he (ks : List (Fin n)) (a b : Fin n) : (eliminate (reflexiveEdges W) ks a b).IsQF := by
    induction ks generalizing a b with
    | nil => exact hr a b
    | cons k ks ih => exact (ih a b).sup ((ih a k).inf (ih k b))
  exact he _ a b

theorem epsilon_qf (A : Automaton L P n m arity) (h : AutomatonQF A) : AutomatonQF A.epsilonFree where
  initial r := any_qf n _ (fun q => (h.initial q).inf (reach_qf A.silent h.silent q r))
  final := h.final
  silent _ _ := BoundedFormula.isQF_bot
  step s q r := any_qf n _ (fun t => (h.step s q t).inf
    (relabel_qf _ (reach_qf A.silent h.silent t r) _))

theorem cell_qf (S : SymbolicComplement.Mask n) (f : Fin n → L.Formula P)
    (h : ∀ q, (f q).IsQF) : (SymbolicComplement.cell S f).IsQF := by
  apply every_qf
  intro q
  dsimp only
  split
  · exact h q
  · exact (h q).not

theorem complement_qf (A : Automaton L P n m arity) (h : AutomatonQF A) :
    AutomatonQF (SymbolicComplement.compile A) := by
  have he := epsilon_qf A h
  have hi (s : SymbolicComplement.State n) : (SymbolicComplement.startGuard A.epsilonFree s).IsQF := by
    cases s
    · exact BoundedFormula.IsQF.top
    · exact BoundedFormula.isQF_bot
  have hf (s : SymbolicComplement.State n) : (SymbolicComplement.finalGuard A.epsilonFree s).IsQF := by
    cases s with
    | none => exact any_qf n _ (fun q => (he.initial q).inf (he.final q))
    | some S =>
      apply any_qf
      intro q
      dsimp only
      split
      · exact he.final q
      · exact BoundedFormula.isQF_bot
  have hd (a : Fin m) (s t : SymbolicComplement.State n) :
      (SymbolicComplement.stepGuard A.epsilonFree a s t).IsQF := by
    cases s <;> cases t
    · exact BoundedFormula.isQF_bot
    · apply cell_qf
      intro r
      exact any_qf n _ (fun q => (relabel_qf _ (he.initial q) _).inf (he.step a q r))
    · exact BoundedFormula.isQF_bot
    · apply cell_qf
      intro r
      apply any_qf
      intro q
      dsimp only
      split
      · exact he.step a q r
      · exact BoundedFormula.isQF_bot
  exact { initial := fun i => hi _
          final := fun i => (hf _).not
          silent := fun _ _ => BoundedFormula.isQF_bot
          step := fun a i j => hd a _ _ }

theorem product_qf (A : Automaton L P n m arity) (B : Automaton L P r m arity)
    (ha : AutomatonQF A) (hb : AutomatonQF B) : AutomatonQF (SymbolicConjunction.compile A B) := by
  have he := epsilon_qf A ha
  have hf := epsilon_qf B hb
  exact { initial := fun i => (he.initial _).inf (hf.initial _)
          final := fun i => (he.final _).inf (hf.final _)
          silent := fun _ _ => BoundedFormula.isQF_bot
          step := fun s i j => (he.step s _ _).inf (hf.step s _ _) }

theorem toAutomaton_qf (R : Row L P n) (h : RowQF R) : AutomatonQF (RowRegularOperations.toAutomaton R) where
  initial := h.initial
  final := h.final
  silent _ _ := BoundedFormula.isQF_bot
  step _ := h.data

theorem ofAutomaton_qf (A : RowRegularOperations.Single L P n) (h : AutomatonQF A) :
    RowQF (RowRegularOperations.ofAutomaton A) := by
  have he := epsilon_qf A h
  exact { data := he.step 0
          left := fun _ _ => BoundedFormula.isQF_bot
          right := fun _ _ => BoundedFormula.isQF_bot
          guard := BoundedFormula.isQF_bot
          initial := he.initial
          final := he.final }

theorem difference_qf (R : Row L P n) (S : Row L P r) (hr : RowQF R) (hs : RowQF S) :
    RowQF (RowRegularOperations.difference R S) :=
  ofAutomaton_qf _ (product_qf _ _ (toAutomaton_qf R hr)
    (toAutomaton_qf _ (ofAutomaton_qf _ (complement_qf _ (toAutomaton_qf S hs)))))

end NSSE.RowBooleanClosureQuantifierFree
