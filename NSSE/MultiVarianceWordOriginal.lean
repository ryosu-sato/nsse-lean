import NSSE.MultiVarianceFirstTail

/-! Arbitrary original countermodels have an accepted current-head word
and hence a first accepted prefix. This exact semantics precedes selector
coverage and does not assume a witness bound or finite-memory head stream. -/
namespace NSSE.MultiVarianceWordOriginal
open MultiConstructorConstraints (Query)
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceTokenExact
open MultiVarianceSpineSeparation MultiVarianceSpineWords MultiVarianceSpineSuffixes MultiVarianceLiteralGeometry
open MultiVarianceWordReader MultiVarianceFirstPrefix
variable {H : Type*} {arity : H → Nat} {n : Nat}

theorem rebuild (s : Spine arity) :
    ofLetters (path s) (label (suffix s s.depth) false) (label (suffix s s.depth) true)=s := by
  induction s with
  | stop a b => rfl
  | step h i s ih =>
    change Spine.step h i (ofLetters (path s) (label (suffix s s.depth) false) (label (suffix s s.depth) true)) = _
    rw [ih]

variable [DecidableEq H] (pol : Polarity arity)

def terminalLabel (Q : Query arity n) (s : Spine arity) (side : Bool) : Label H :=
  label (suffix s s.depth) (roleOf (frame pol Q (path s) (path s).length).sign side)

theorem make_original (Q : Query arity n) (s : Spine arity) :
    make pol Q (path s) (terminalLabel pol Q s false) (terminalLabel pol Q s true)=s := by
  unfold make terminalLabel physical
  cases hs : (frame pol Q (path s) (path s).length).sign <;>
    simp only [roleOf,hs,Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true]
  all_goals exact rebuild s

theorem accepted_original (Q : Query arity n) (s : Spine arity) :
    Accepted pol Q (path s) (terminalLabel pol Q s false) (terminalLabel pol Q s true) ↔
      MultiVarianceRawSpine.inspectSpine pol Q s=true := by
  rw [accepted_iff_inspect,make_original]

theorem not_entails_iff_word (Q : Query arity n) :
    ¬MultiVarianceConstraints.Entails pol Q ↔ ∃ w : List (Letter arity), Witness pol Q w := by
  rw [MultiVarianceRawSpine.not_entails_iff_exists_inspectSpine]
  constructor
  · rintro ⟨s,hs⟩
    exact ⟨path s,_,_,(accepted_original pol Q s).mpr hs⟩
  · rintro ⟨w,ex,ey,ha⟩
    exact ⟨make pol Q w ex ey,(accepted_iff_inspect pol Q w ex ey).mp ha⟩

theorem not_entails_iff_first (Q : Query arity n) :
    ¬MultiVarianceConstraints.Entails pol Q ↔ ∃ w : List (Letter arity), First pol Q w := by
  rw [not_entails_iff_word]
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨m,_,hm⟩ := first_prefix pol Q w hw
    exact ⟨w.take m,hm⟩
  · rintro ⟨w,hw⟩
    exact ⟨w,hw.1⟩

end NSSE.MultiVarianceWordOriginal
