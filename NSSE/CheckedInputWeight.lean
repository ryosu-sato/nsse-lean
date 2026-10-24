import NSSE.CheckedBitListWeight
import NSSE.CheckedBitListInput

namespace NSSE.CheckedInputWeight
open CheckedBitListWeight

def literals {limit arity : List Bool} (xs : List (CheckedBitListBound.Bound limit arity)) :=
  (xs.map literal).sum

def input {limit arity : List Bool} (I : CheckedBitListInput.Input limit arity) :=
  literals I.upper+literals I.lower+indices I.bot+indices I.top

theorem bounds (limit arity count : List Bool) (bs : List (List Bool))
    (xs : List (CheckedBitListBound.Bound limit arity)) (rest : List (List Bool))
    (h : (CheckedBitListBounds.many limit arity count bs).1 = some (xs,rest)) :
    literals xs + tokens rest = tokens bs := by
  induction count, bs using CheckedBitListBounds.many.induct limit arity generalizing xs rest with
  | case1 count bs c hc =>
    dsimp only [c] at hc
    rw [CheckedBitListBounds.many] at h
    dsimp only at h
    simp only [hc, Option.some.injEq] at h
    cases h
    simp [literals]
  | case2 count bs c next hc r hr =>
    dsimp only [c] at hc
    dsimp only [r] at hr
    rw [CheckedBitListBounds.many] at h
    dsimp only at h
    simp only [hc] at h
    split at h
    · simp at h
    · rename_i a rs hh; rw [hr] at hh; cases hh
  | case3 count bs c next hc r a rs hr ih =>
    dsimp only [c] at hc
    dsimp only [r] at hr
    have hs := CheckedBitListWeight.bound limit arity bs a rs hr
    rw [CheckedBitListBounds.many] at h
    dsimp only at h
    simp only [hc] at h
    split at h
    · rename_i hh; rw [hr] at hh; cases hh
    · rename_i b ts hh
      have he := Option.some.inj (hr.symm.trans hh)
      cases he
      cases ht : (CheckedBitListBounds.many limit arity next rs).1 with
      | none => simp [ht] at h
      | some p =>
        obtain ⟨ys,us⟩ := p
        have hi := ih ys us ht
        have hp : (a::ys,us)=(xs,rest) := by simpa [ht] using h
        cases hp
        simp only [literals,List.map_cons,List.sum_cons] at *
        omega

theorem read_bounds (limit arity : List Bool) (bs : List (List Bool))
    (xs : List (CheckedBitListBound.Bound limit arity)) (rest : List (List Bool))
    (h : (CheckedBitListBounds.read limit arity bs).1 = some (xs,rest)) :
    literals xs + tokens rest ≤ tokens bs := by
  cases bs with
  | nil => simp [CheckedBitListBounds.read] at h
  | cons count tail =>
    have hh := bounds limit arity count tail xs rest h
    simp only [tokens,List.length_cons,List.map_cons,List.sum_cons] at *
    omega

theorem read_indices (limit : List Bool) (bs : List (List Bool))
    (xs : List (CheckedBitListIndex.Index limit)) (rest : List (List Bool))
    (h : (CheckedBitListIndices.read limit bs).1 = some (xs,rest)) :
    indices xs + tokens rest ≤ tokens bs := by
  cases bs with
  | nil => simp [CheckedBitListIndices.read] at h
  | cons count tail =>
    have hh := CheckedBitListWeight.children limit count tail xs rest h
    simp only [tokens,List.length_cons,List.map_cons,List.sum_cons] at *
    omega

theorem parse (limit arity : List Bool) (bs : List (List Bool))
    (I : CheckedBitListInput.Input limit arity) (rest : List (List Bool))
    (h : (CheckedBitListInput.parse limit arity bs).1 = some (I,rest)) :
    input I + tokens rest ≤ tokens bs := by
  simp only [CheckedBitListInput.parse] at h
  split at h
  · simp at h
  · rename_i upper us eu
    have hu := read_bounds limit arity bs upper us eu
    split at h
    · simp at h
    · rename_i lower ls el
      have hl := read_bounds limit arity us lower ls el
      split at h
      · simp at h
      · rename_i bot ts eb
        have hb := read_indices limit ls bot ts eb
        cases et : (CheckedBitListIndices.read limit ts).1 with
        | none => simp [et] at h
        | some p =>
          obtain ⟨top,rs⟩ := p
          have ht := read_indices limit ts top rs et
          have hp : (CheckedBitListInput.Input.mk upper lower bot top,rs) = (I,rest) := by
            simpa [et] using h
          cases hp
          simp only [input]
          omega

theorem decode (limit arity : List Bool) (bs : List (List Bool))
    (I : CheckedBitListInput.Input limit arity)
    (h : (CheckedBitListInput.decode limit arity bs).1 = some I) : input I ≤ tokens bs := by
  simp only [CheckedBitListInput.decode] at h
  cases hp : (CheckedBitListInput.parse limit arity bs).1 with
  | none => simp [hp] at h
  | some p =>
    obtain ⟨J,rest⟩ := p
    have hs := parse limit arity bs J rest hp
    cases rest with
    | nil => simp [hp] at h; cases h; simpa [tokens] using hs
    | cons b rs => simp [hp] at h
end NSSE.CheckedInputWeight
