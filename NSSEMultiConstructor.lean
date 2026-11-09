import NSSE.MultiConstructorTermDecision
import NSSE.MultiVarianceTermDecision
import NSSE.MultiVarianceTermExtraction

/-!
# Several constructors

Entry point for the decision of non-structural subtype entailment with several constructors.

* `NSSE.MultiConstructorTermDecision`: every constructor covariant
  (`inspectAll_correct`, `inspectRegular_correct`, `inspectFinite_correct`).
* `NSSE.MultiVarianceTermDecision`: each argument of each constructor covariant or contravariant
  (`inspectAll_correct`, `inspectRegular_correct`, `inspectFinite_correct`).
* `NSSE.MultiVarianceTermExtraction`: countermodels for the same inputs
  (`all_none`, `all_some`, `finite_none`, `finite_some`, `regular_none`).
-/
