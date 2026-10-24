import NSSE.CheckedBitListBound

namespace NSSE.CheckedBitListWeight
open CheckedBitListIndex (Index)

def tokens (bs : List (List Bool)) := bs.length+(bs.map List.length).sum
def indices {limit : List Bool} (xs : List (Index limit)) :=
  (xs.map (fun x => 1+x.digits.length)).sum
def literal {limit arity : List Bool} (a : CheckedBitListBound.Bound limit arity) :=
  1+a.head.digits.length+indices a.children

theorem children (limit count : List Bool) (tokens : List (List Bool))
    (xs : List (Index limit)) (rest : List (List Bool))
    (h : (CheckedBitListChildren.read limit count tokens).1 = some (xs,rest)) :
    indices xs + CheckedBitListWeight.tokens rest = CheckedBitListWeight.tokens tokens := by
  induction tokens generalizing count xs rest with
  | nil =>
    cases hc : (BitListCountdown.decrement count).1 with
    | none =>
      rw [CheckedBitListChildren.read] at h
      simp only [hc, Option.some.injEq] at h
      cases h
      simp [indices,CheckedBitListWeight.tokens]
    | some next => rw [CheckedBitListChildren.read] at h; simp [hc] at h
  | cons digits tail ih =>
    cases hc : (BitListCountdown.decrement count).1 with
    | none =>
      rw [CheckedBitListChildren.read] at h
      simp only [hc, Option.some.injEq] at h
      cases h
      simp [indices,CheckedBitListWeight.tokens]
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
          have hd := CheckedBitListIndex.returned_digits limit digits x he
          have hh := ih next ys rs hr
          have hp : (x::ys,rs) = (xs,rest) := by simpa [he,hr] using h
          cases hp
          simp only [indices,CheckedBitListWeight.tokens,List.length_cons,List.map_cons,List.sum_cons,hd] at *
          omega

theorem bound (limit arity : List Bool) (tokens : List (List Bool))
    (a : CheckedBitListBound.Bound limit arity) (rest : List (List Bool))
    (h : (CheckedBitListBound.read limit arity tokens).1 = some (a,rest)) :
    literal a + CheckedBitListWeight.tokens rest = CheckedBitListWeight.tokens tokens := by
  cases tokens with
  | nil => simp [CheckedBitListBound.read] at h
  | cons digits tail =>
    simp only [CheckedBitListBound.read] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i head he cs rs hr
        have hd := CheckedBitListIndex.returned_digits limit digits head he
        have hh := children limit arity tail cs rs hr
        have hp := Option.some.inj h
        cases hp
        simp only [literal,CheckedBitListWeight.tokens,List.length_cons,List.map_cons,List.sum_cons,hd] at *
        omega
end NSSE.CheckedBitListWeight
