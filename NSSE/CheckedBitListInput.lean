import NSSE.CheckedBitListIndices
import NSSE.CheckedBitListBounds

namespace NSSE.CheckedBitListInput
open BitListTokenReader (eval)
open CheckedBitListIndex (Index)
open CheckedBitListBound (Bound)

structure Input (limit arity : List Bool) where
  upper : List (Bound limit arity)
  lower : List (Bound limit arity)
  bot : List (Index limit)
  top : List (Index limit)

def Input.denote {limit arity : List Bool} (I : Input limit arity) :
    StoredSubtypeInput.Input (eval limit) (eval arity) :=
  ⟨I.upper.map Bound.denote,I.lower.map Bound.denote,I.bot.map Index.denote,I.top.map Index.denote⟩

def parse (limit arity : List Bool) (bs : List (List Bool)) :
    Option (Input limit arity × List (List Bool)) × Nat :=
  let u := CheckedBitListBounds.read limit arity bs
  match u.1 with
  | none => (none,1+u.2)
  | some (upper,us) =>
    let l := CheckedBitListBounds.read limit arity us
    match l.1 with
    | none => (none,2+u.2+l.2)
    | some (lower,ls) =>
      let b := CheckedBitListIndices.read limit ls
      match b.1 with
      | none => (none,3+u.2+l.2+b.2)
      | some (bot,ts) =>
        let t := CheckedBitListIndices.read limit ts
        (t.1.map (fun p => (⟨upper,lower,bot,p.1⟩,p.2)),4+u.2+l.2+b.2+t.2)

theorem value (limit arity : List Bool) (bs : List (List Bool)) :
    (parse limit arity bs).1.map (fun p => (p.1.denote,p.2.map eval)) =
      StoredInputCodec.parse (eval limit) (eval arity) (bs.map eval) := by
  have hu := CheckedBitListBounds.read_value limit arity bs
  cases eu : (CheckedBitListBounds.read limit arity bs).1 with
  | none =>
    simp only [eu,Option.map_none'] at hu
    simp [parse,eu,StoredInputCodec.parse,← hu]
  | some up =>
    obtain ⟨upper,us⟩ := up
    simp only [eu,Option.map_some'] at hu
    have hl := CheckedBitListBounds.read_value limit arity us
    cases el : (CheckedBitListBounds.read limit arity us).1 with
    | none =>
      simp only [el,Option.map_none'] at hl
      simp [parse,eu,el,StoredInputCodec.parse,← hu,← hl]
    | some lp =>
      obtain ⟨lower,ls⟩ := lp
      simp only [el,Option.map_some'] at hl
      have hb := CheckedBitListIndices.value limit ls
      cases eb : (CheckedBitListIndices.read limit ls).1 with
      | none =>
        simp only [eb,Option.map_none'] at hb
        simp [parse,eu,el,eb,StoredInputCodec.parse,← hu,← hl,← hb]
      | some bp =>
        obtain ⟨bot,ts⟩ := bp
        simp only [eb,Option.map_some'] at hb
        have ht := CheckedBitListIndices.value limit ts
        cases et : (CheckedBitListIndices.read limit ts).1 with
        | none =>
          simp only [et,Option.map_none'] at ht
          simp [parse,eu,el,eb,et,StoredInputCodec.parse,← hu,← hl,← hb,← ht]
        | some tp =>
          obtain ⟨top,rest⟩ := tp
          simp only [et,Option.map_some'] at ht
          simp [parse,eu,el,eb,et,StoredInputCodec.parse,← hu,← hl,← hb,← ht,Input.denote]

theorem bounds_mono (limit arity : List Bool) (xs ys : List (List Bool))
    (hl : xs.length ≤ ys.length) (hs : (xs.map List.length).sum ≤ (ys.map List.length).sum) :
    CheckedBitListBounds.readBudget limit arity xs ≤ CheckedBitListBounds.readBudget limit arity ys := by
  dsimp only [CheckedBitListBounds.readBudget, CheckedBitListBound.budget, CheckedBitListChildren.budget]
  gcongr

theorem indices_mono (limit : List Bool) (xs ys : List (List Bool))
    (hl : xs.length ≤ ys.length) (hs : (xs.map List.length).sum ≤ (ys.map List.length).sum) :
    CheckedBitListIndices.budget limit xs ≤ CheckedBitListIndices.budget limit ys := by
  dsimp only [CheckedBitListIndices.budget]
  gcongr

def budget (limit arity : List Bool) (bs : List (List Bool)) :=
  4+2*CheckedBitListBounds.readBudget limit arity bs+2*CheckedBitListIndices.budget limit bs

theorem bound (limit arity : List Bool) (bs : List (List Bool)) :
    (parse limit arity bs).2 ≤ budget limit arity bs := by
  have hu := CheckedBitListBounds.read_bound limit arity bs
  cases eu : (CheckedBitListBounds.read limit arity bs).1 with
  | none => simp only [parse,eu,budget]; omega
  | some up =>
    obtain ⟨upper,us⟩ := up
    have su := CheckedBitListBounds.read_consumption limit arity bs upper us eu
    have hl := (CheckedBitListBounds.read_bound limit arity us).trans
      (bounds_mono limit arity us bs (by omega) su.2)
    cases el : (CheckedBitListBounds.read limit arity us).1 with
    | none => simp only [parse,eu,el,budget]; omega
    | some lp =>
      obtain ⟨lower,ls⟩ := lp
      have sl := CheckedBitListBounds.read_consumption limit arity us lower ls el
      have hb := (CheckedBitListIndices.bound limit ls).trans
        (indices_mono limit ls bs (by omega) (sl.2.trans su.2))
      cases eb : (CheckedBitListIndices.read limit ls).1 with
      | none => simp only [parse,eu,el,eb,budget]; omega
      | some bp =>
        obtain ⟨bot,ts⟩ := bp
        have sb := CheckedBitListIndices.consumption limit ls bot ts eb
        have ht := (CheckedBitListIndices.bound limit ts).trans
          (indices_mono limit ts bs (by omega) (sb.2.trans (sl.2.trans su.2)))
        simp only [parse,eu,el,eb,budget]
        omega

def decode (limit arity : List Bool) (bs : List (List Bool)) : Option (Input limit arity) × Nat :=
  let r := parse limit arity bs
  (r.1.bind (fun p => if p.2.isEmpty then some p.1 else none),1+r.2)

theorem decode_value (limit arity : List Bool) (bs : List (List Bool)) :
    (decode limit arity bs).1.map Input.denote =
      StoredInputCodec.decode (eval limit) (eval arity) (bs.map eval) := by
  rw [StoredInputCodec.decode, ← value]
  simp only [decode]
  cases (parse limit arity bs).1 with
  | none => rfl
  | some p =>
    obtain ⟨I,rest⟩ := p
    cases rest <;> simp

theorem decode_bound (limit arity : List Bool) (bs : List (List Bool)) :
    (decode limit arity bs).2 ≤ 1+budget limit arity bs := by
  exact Nat.add_le_add_left (bound limit arity bs) 1

end NSSE.CheckedBitListInput
