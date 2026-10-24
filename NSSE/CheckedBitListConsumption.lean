import NSSE.CheckedBitListBound

namespace NSSE.CheckedBitListConsumption
open CheckedBitListIndex (Index)

theorem children (limit count : List Bool) (tokens : List (List Bool))
    (xs : List (Index limit)) (rest : List (List Bool))
    (h : (CheckedBitListChildren.read limit count tokens).1 = some (xs,rest)) :
    rest.length + xs.length = tokens.length ∧
      (rest.map List.length).sum ≤ (tokens.map List.length).sum := by
  induction tokens generalizing count xs rest with
  | nil =>
    cases hc : (BitListCountdown.decrement count).1 with
    | none =>
      rw [CheckedBitListChildren.read] at h
      simp only [hc, Option.some.injEq] at h
      cases h
      simp
    | some next => rw [CheckedBitListChildren.read] at h; simp [hc] at h
  | cons digits tail ih =>
    cases hc : (BitListCountdown.decrement count).1 with
    | none =>
      rw [CheckedBitListChildren.read] at h
      simp only [hc, Option.some.injEq] at h
      cases h
      simp
    | some next =>
      rw [CheckedBitListChildren.read] at h
      simp only [hc] at h
      cases he : (CheckedBitListIndex.check limit digits).1 with
      | none => simp [he] at h
      | some x =>
        cases hr : (CheckedBitListChildren.read limit next tail).1 with
        | none => simp [he,hr] at h
        | some p =>
          obtain ⟨ys,rs⟩ := p
          have hh := ih next ys rs hr
          have hp : (x::ys,rs) = (xs,rest) := by simpa [he,hr] using h
          cases hp
          simp only [List.length_cons, List.map_cons, List.sum_cons]
          omega

theorem bound (limit arity : List Bool) (tokens : List (List Bool))
    (a : CheckedBitListBound.Bound limit arity) (rest : List (List Bool))
    (h : (CheckedBitListBound.read limit arity tokens).1 = some (a,rest)) :
    rest.length + a.children.length + 1 = tokens.length ∧
      (rest.map List.length).sum ≤ (tokens.map List.length).sum := by
  cases tokens with
  | nil => simp [CheckedBitListBound.read] at h
  | cons digits tail =>
    simp only [CheckedBitListBound.read] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i head he cs rs hr
        have hh := children limit arity tail cs rs hr
        have hp := Option.some.inj h
        cases hp
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        omega
end NSSE.CheckedBitListConsumption
