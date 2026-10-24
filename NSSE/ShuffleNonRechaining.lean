import NSSE.Cap

/-!
# Shuffle non-rechaining

`Cap.shuffle_non_rechaining` already proves Lemma 5.1's promotion to the
whole word. This file records the route-free consequence stated in the
manuscript.
-/

namespace NSSE

universe u

/-- A route-free word cannot have two same-component anchors separated by
an accepted right-language factor, provided the component's left language
is one of the expression's explicit routes. -/
theorem routeFree_no_sameComponent_rechaining
    (E : CapExpression α) (c : CapComponent α)
    (hcroute : c.left ∈ E.routes)
    (w : Word α) {j j' : Nat}
    (hfree : routeFree E w)
    (hshuffle : ShuffleCondition c)
    (hjj' : j ≤ j')
    (hleft : c.left (w.take j))
    (hleft' : c.left (w.take j'))
    (hright : c.right (Word.factor w j (j' - j))) :
    False := by
  have hwhole :=
    (shuffle_non_rechaining c w hshuffle hjj'
      hleft hleft' hright).1
  apply hfree
  refine ⟨c.left, hcroute, w, [], by simp, hwhole, trivial⟩

end NSSE
