import NSSE.CheckedBitListIndex
import NSSE.BitListCountdown

/-! Stored binary child lists checked against binary arity and limit.
Recursion follows the token tail; no numeric header conversion is executed. -/
namespace NSSE.CheckedBitListChildren
open BitListTokenReader (eval)
open CheckedBitListIndex (Index)

def read (limit count : List Bool) (tokens : List (List Bool)) :
    Option (List (Index limit) × List (List Bool)) × Nat :=
  let c := BitListCountdown.decrement count
  match c.1 with
  | none => (some ([],tokens),1+c.2)
  | some next => match tokens with
    | [] => (none,1+c.2)
    | digits::rest =>
      let i := CheckedBitListIndex.check limit digits
      match i.1 with
      | none => (none,2+c.2+i.2)
      | some x =>
        let r := read limit next rest
        (r.1.map (fun p => (x::p.1,p.2)),2+c.2+i.2+r.2)
termination_by tokens.length

theorem value (limit count : List Bool) (tokens : List (List Bool)) :
    (read limit count tokens).1.map (fun p => (p.1.map Index.denote,p.2.map eval)) =
      StoredInputCodec.many (StoredInputCodec.index (eval limit)) (eval count) (tokens.map eval) := by
  induction tokens generalizing count with
  | nil =>
    cases hc : (BitListCountdown.decrement count).1 with
    | none =>
      have hz := (BitListCountdown.none_iff count).mp hc
      rw [read]
      simp [hc, hz, StoredInputCodec.many]
    | some next =>
      have hs := (BitListCountdown.some_value count next hc).1
      rw [read]
      simp [hc, ← hs, StoredInputCodec.many, StoredInputCodec.index]
  | cons digits rest ih =>
    cases hc : (BitListCountdown.decrement count).1 with
    | none =>
      have hz := (BitListCountdown.none_iff count).mp hc
      rw [read]
      simp [hc, hz, StoredInputCodec.many]
    | some next =>
      have hs := (BitListCountdown.some_value count next hc).1
      have hi := CheckedBitListIndex.value limit digits (rest.map eval)
      rw [read]
      simp only [hc, List.map_cons]
      cases he : (CheckedBitListIndex.check limit digits).1 with
      | none =>
        simp only [he, Option.map_none'] at hi
        simp [he, ← hs, StoredInputCodec.many, ← hi]
      | some x =>
        simp only [he, Option.map_some'] at hi
        simp only [he, Option.map_map, Function.comp_def, List.map_cons]
        rw [← hs, StoredInputCodec.many, ← hi]
        change _ = (StoredInputCodec.many (StoredInputCodec.index (eval limit)) (eval next)
          (rest.map eval)).bind (fun p => some (x.denote::p.1,p.2))
        rw [← ih]
        cases (read limit next rest).1 <;> rfl

def budget (limit count : List Bool) (tokens : List (List Bool)) :=
  (tokens.length+1)*(2*count.length+3*limit.length+6)+3*(tokens.map List.length).sum

theorem bound (limit count : List Bool) (tokens : List (List Bool)) :
    (read limit count tokens).2 ≤ budget limit count tokens := by
  induction tokens generalizing count with
  | nil =>
    have h := BitListCountdown.bound count
    cases hc : (BitListCountdown.decrement count).1 <;> rw [read] <;>
      simp only [hc, budget, List.length_nil, List.map_nil, List.sum_nil] <;> nlinarith
  | cons digits rest ih =>
    have h := BitListCountdown.bound count
    cases hc : (BitListCountdown.decrement count).1 with
    | none =>
      have hm := Nat.mul_le_mul_right (2*count.length+3*limit.length+6)
        (show 1 ≤ rest.length+1+1 by omega)
      simp only [Nat.one_mul] at hm
      rw [read]
      simp only [hc, budget, List.length_cons, List.map_cons, List.sum_cons]
      omega
    | some next =>
      have hn := (BitListCountdown.some_value count next hc).2
      have hi := CheckedBitListIndex.bound limit digits
      have ht : (read limit next rest).2 ≤ budget limit count rest := by
        apply (ih next).trans
        dsimp only [budget]
        gcongr
      rw [read]
      simp only [hc]
      cases he : (CheckedBitListIndex.check limit digits).1 <;>
        simp only [he, budget, List.length_cons, List.map_cons, List.sum_cons] at * <;> nlinarith

/-- Success returns exactly the declared number of checked children. -/
theorem length (limit count : List Bool) (tokens : List (List Bool))
    (xs : List (Index limit)) (rest : List (List Bool))
    (h : (read limit count tokens).1 = some (xs,rest)) : xs.length = eval count := by
  induction tokens generalizing count xs rest with
  | nil =>
    cases hc : (BitListCountdown.decrement count).1 with
    | none =>
      have hz := (BitListCountdown.none_iff count).mp hc
      rw [read] at h
      simp only [hc, Option.some.injEq] at h
      cases h
      exact hz.symm
    | some next => rw [read] at h; simp [hc] at h
  | cons digits tail ih =>
    cases hc : (BitListCountdown.decrement count).1 with
    | none =>
      have hz := (BitListCountdown.none_iff count).mp hc
      rw [read] at h
      simp only [hc, Option.some.injEq] at h
      cases h
      exact hz.symm
    | some next =>
      have hn := (BitListCountdown.some_value count next hc).1
      rw [read] at h
      simp only [hc] at h
      cases he : (CheckedBitListIndex.check limit digits).1 with
      | none => simp [he] at h
      | some x =>
        cases hr : (read limit next tail).1 with
        | none => simp [he, hr] at h
        | some p =>
          obtain ⟨ys,rs⟩ := p
          have hh := ih next ys rs hr
          have hp : (x::ys,rs)=(xs,rest) := by simpa [he,hr] using h
          cases hp
          simp only [List.length_cons]
          omega
end NSSE.CheckedBitListChildren
