import NSSE.FactorForest
import Lean.Elab.Tactic.Omega

/-!
# Synchronized replacement of disjoint equal factors

This is the context algebra surrounding the transported common
factorization forest in v372/v413.
-/

namespace NSSE

universe u v

inductive Orientation
  | forward
  | theta
deriving DecidableEq

namespace Word

def thetaReverse (theta : α → α) (w : Word α) : Word α :=
  w.reverse.map theta

def orient (theta : α → α) : Orientation → Word α → Word α
  | .forward, w => w
  | .theta, w => thetaReverse theta w

@[simp] theorem thetaReverse_length (theta : α → α) (w : Word α) :
    (thetaReverse theta w).length = w.length := by
  simp [thetaReverse]

@[simp] theorem orient_length (theta : α → α)
    (o : Orientation) (w : Word α) :
    (orient theta o w).length = w.length := by
  cases o <;> simp [orient]

theorem thetaReverse_append (theta : α → α) (x y : Word α) :
    thetaReverse theta (x ++ y) =
      thetaReverse theta y ++ thetaReverse theta x := by
  simp [thetaReverse, List.reverse_append, List.map_append]

theorem orient_append (theta : α → α) (o : Orientation)
    (x y : Word α) :
    orient theta o (x ++ y) =
      match o with
      | .forward => orient theta o x ++ orient theta o y
      | .theta => orient theta o y ++ orient theta o x := by
  cases o
  · rfl
  · exact thetaReverse_append theta x y

end Word

namespace ControlMonoid

variable {M : Type v} (C : ControlMonoid M) (letter : α → M)

/-- Two disjoint factor replacements with preserved control values
preserve the full outer control value. -/
theorem eval_two_factor_replace
    (left source middle mate right source' mate' : Word α)
    (hsource : C.eval letter source = C.eval letter source')
    (hmate : C.eval letter mate = C.eval letter mate') :
    C.eval letter (left ++ source ++ middle ++ mate ++ right) =
      C.eval letter (left ++ source' ++ middle ++ mate' ++ right) := by
  calc
    C.eval letter (left ++ source ++ middle ++ mate ++ right) =
        C.eval letter (left ++ source' ++ middle ++ mate ++ right) := by
      have h := C.eval_context_replace letter left source source'
        (middle ++ mate ++ right) hsource
      simpa [List.append_assoc] using h
    _ = C.eval letter (left ++ source' ++ middle ++ mate' ++ right) := by
      have h := C.eval_context_replace letter
        (left ++ source' ++ middle) mate mate' right hmate
      simpa [List.append_assoc] using h

/--
The synchronized replacement used for forward or theta-oriented equal
occurrences.  The two post-replacement factors retain the same orientation
relation by construction.
-/
theorem eval_synchronized_oriented_replace
    (theta : α → α) (o : Orientation)
    (left source middle right source' : Word α)
    (hsource : C.eval letter source = C.eval letter source')
    (horiented :
      C.eval letter (Word.orient theta o source) =
        C.eval letter (Word.orient theta o source')) :
    C.eval letter
        (left ++ source ++ middle ++ Word.orient theta o source ++ right) =
      C.eval letter
        (left ++ source' ++ middle ++ Word.orient theta o source' ++ right) :=
  C.eval_two_factor_replace letter left source middle
    (Word.orient theta o source) right source'
    (Word.orient theta o source') hsource horiented

theorem synchronized_oriented_replace_shorter
    (theta : α → α) (o : Orientation)
    (left source middle right source' : Word α)
    (hshort : source'.length < source.length) :
    (left ++ source' ++ middle ++ Word.orient theta o source' ++ right).length <
      (left ++ source ++ middle ++ Word.orient theta o source ++ right).length := by
  simp only [List.length_append, Word.orient_length]
  omega

end ControlMonoid

end NSSE
