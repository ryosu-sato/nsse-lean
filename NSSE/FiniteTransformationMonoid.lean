import NSSE.FiniteFunctionEnumeration
import NSSE.TransitionMonoid
import NSSE.FactorForest

/-!
# Finite enumeration of DFA transformations

For an enumerated DFA state type, all transformations `Q → Q` form an
executable finite list.  The DFA start state supplies the fallback used
outside the value vector, although completeness ensures every state has
an in-range table entry.
-/

namespace NSSE

universe u v

def transformationEnumeration
    [DecidableEq Q]
    (states : Enumeration Q) (fallback : Q) :
    Enumeration (Q → Q) :=
  functionEnumeration states states fallback

def DFA.transformationEnumeration
    [DecidableEq Q]
    (A : DFA α Q) (states : Enumeration Q) :
    Enumeration (Q → Q) :=
  NSSE.transformationEnumeration states A.start

theorem DFA.transitionEval_mem_transformationEnumeration
    [DecidableEq Q]
    (A : DFA α Q) (states : Enumeration Q)
    (word : Word α) :
    A.transitionEval word ∈
      (A.transformationEnumeration states).values :=
  (A.transformationEnumeration states).complete _

theorem FactorTree.control_mem_transformationEnumeration
    [DecidableEq Q]
    (A : DFA α Q) (states : Enumeration Q)
    (tree : FactorTree α) :
    FactorTree.control (transformationMonoid Q)
        A.letterTransform tree ∈
      (A.transformationEnumeration states).values :=
  (A.transformationEnumeration states).complete _

end NSSE
