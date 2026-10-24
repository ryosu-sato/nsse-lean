import NSSE.LoopTransitionTaggedRules
import NSSE.SolverHornFamily

/-!
# Exact Horn terminal for a nonidentity loop update

The finite wire/counter nonidentity disposition is an exact solver and
therefore a reusable two-state Horn family.  Structural tagged derivability
is connected directly to this terminal family.
-/

namespace NSSE

universe u

def loopNonidentitySolver [DecidableEq Wire] :
    ExactSolver (LoopUpdate Wire) where
  formula := fun update => ¬ update.IsIdentity
  decide := LoopUpdate.nonidentityB
  correct := LoopUpdate.nonidentityB_correct

def loopNonidentityHornFamily [DecidableEq Wire]
    (update : LoopUpdate Wire) : HornFamily :=
  exactSolverHornFamily loopNonidentitySolver update

theorem loopNonidentityHornFamily_derives_iff
    [DecidableEq Wire] (update : LoopUpdate Wire) :
    HornDerives
        (loopNonidentityHornFamily update).compiler
        (loopNonidentityHornFamily update).root ↔
      ¬ update.IsIdentity := by
  exact exactSolverHornFamily_derives_iff
    loopNonidentitySolver update

theorem loopNonidentityHornFamily_decide_correct
    [DecidableEq Wire] (update : LoopUpdate Wire) :
    decideHornState
        (loopNonidentityHornFamily update).compiler
        (loopNonidentityHornFamily update).root = true ↔
      ¬ update.IsIdentity := by
  rw [decideHornState_correct
    (loopNonidentityHornFamily update).compiler
    (loopNonidentityHornFamily update).root
    (loopNonidentityHornFamily update).root_lt]
  exact loopNonidentityHornFamily_derives_iff update

theorem structuralTag_derives_iff_loopHorn
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq LCA] [DecidableEq Macro] [DecidableEq Wire]
    [DecidableEq Atom] [DecidableEq QClass]
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro) (wire : Enumeration (LoopUpdate Wire))
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (tag : LoopCompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass)
    (update : LoopUpdate Wire)
    (hupdate : tag.loopUpdate? = some update) :
    (loopTransitionRuleTests.ruleSystem
        ctl cut ori lca macros wire atom quotient).TaggedDerives tag ↔
      HornDerives
        (loopNonidentityHornFamily update).compiler
        (loopNonidentityHornFamily update).root := by
  rw [loop_taggedDerives_iff_nonidentity,
    loopNonidentityHornFamily_derives_iff]
  constructor
  · rintro ⟨found, hfound, hnonidentity⟩
    rw [hupdate] at hfound
    cases hfound
    exact hnonidentity
  · intro hnonidentity
    exact ⟨update, hupdate, hnonidentity⟩

end NSSE
