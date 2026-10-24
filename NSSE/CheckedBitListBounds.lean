import NSSE.CheckedBitListConsumption

namespace NSSE.CheckedBitListBounds
open BitListTokenReader (eval)

def many (limit arity count : List Bool) (bs : List (List Bool)) :
    Option (List (CheckedBitListBound.Bound limit arity) × List (List Bool)) × Nat :=
  let c := BitListCountdown.decrement count
  match c.1 with
  | none => (some ([],bs),1+c.2)
  | some next =>
    let r := CheckedBitListBound.read limit arity bs
    match hr : r.1 with
    | none => (none,2+c.2+r.2)
    | some (digits,rest) =>
      let t := many limit arity next rest
      (t.1.map (fun p => (digits::p.1,p.2)),2+c.2+r.2+t.2)
termination_by bs.length
decreasing_by
  have hs := CheckedBitListConsumption.bound limit arity bs digits rest hr
  omega

theorem value (limit arity count : List Bool) (bs : List (List Bool)) :
    (many limit arity count bs).1.map (fun p => (p.1.map CheckedBitListBound.Bound.denote,p.2.map eval)) =
      StoredInputCodec.many (StoredInputCodec.readBound (eval limit) (eval arity)) (eval count) (bs.map eval) := by
  induction count, bs using many.induct limit arity with
  | case1 count bs c hc =>
    dsimp only [c] at hc
    have hz := (BitListCountdown.none_iff count).mp hc
    rw [many]
    dsimp only
    simp only [ hc, hz, StoredInputCodec.many, Option.map_some', List.map_nil]
  | case2 count bs c next hc r hr =>
    dsimp only [c] at hc
    dsimp only [r] at hr
    have hs := BitListCountdown.some_value count next hc
    have hv := CheckedBitListBound.value limit arity bs
    simp only [hr, Option.map_none'] at hv
    rw [many]
    dsimp only
    simp only [ hc, hr, Option.map_none', ← hs.1, StoredInputCodec.many, ← hv]
    split
    · rfl
    · rename_i ds rs hh
      rw [hr] at hh
      cases hh
  | case3 count bs c next hc r digits rest hr ih =>
    dsimp only [c] at hc
    dsimp only [r] at hr
    have hs := BitListCountdown.some_value count next hc
    have hv := CheckedBitListBound.value limit arity bs
    simp only [hr, Option.map_some'] at hv
    rw [many]
    dsimp only
    simp only [hc, hr, Option.map_map, Function.comp_def, List.map_cons]
    split
    · rename_i hh; rw [hr] at hh; cases hh
    · rename_i ds rs hh
      have he : (digits,rest)=(ds,rs) := Option.some.inj (hr.symm.trans hh)
      cases he
      simp only [Option.map_map, Function.comp_def, List.map_cons]
      rw [← hs.1, StoredInputCodec.many, ← hv]
      change _ = (StoredInputCodec.many (StoredInputCodec.readBound (eval limit) (eval arity)) (eval next) (rest.map eval)).bind
        (fun p => some (digits.denote::p.1,p.2))
      rw [← ih]
      cases (many limit arity next rest).1 <;> rfl

def budget (limit arity count : List Bool) (bs : List (List Bool)) :=
  (bs.length+1)*(2*count.length+3+CheckedBitListBound.budget limit arity bs)

theorem bound (limit arity count : List Bool) (bs : List (List Bool)) :
    (many limit arity count bs).2 ≤ budget limit arity count bs := by
  induction count, bs using many.induct limit arity with
  | case1 count bs c hc =>
    dsimp only [c] at hc
    have h := BitListCountdown.bound count
    rw [many]
    dsimp only
    simp only [hc, budget]
    nlinarith
  | case2 count bs c next hc r hr =>
    dsimp only [c] at hc
    dsimp only [r] at hr
    have h := BitListCountdown.bound count
    have hread := CheckedBitListBound.bound limit arity bs
    rw [many]
    dsimp only
    simp only [hc, budget]
    split
    · nlinarith
    · rename_i ds rs hh; rw [hr] at hh; cases hh
  | case3 count bs c next hc r digits rest hr ih =>
    dsimp only [c] at hc
    dsimp only [r] at hr
    have h := BitListCountdown.bound count
    have hread := CheckedBitListBound.bound limit arity bs
    have hn := (BitListCountdown.some_value count next hc).2
    have hs := CheckedBitListConsumption.bound limit arity bs digits rest hr
    have hrest : rest.length+1 ≤ bs.length := by omega
    have hm : CheckedBitListBound.budget limit arity rest ≤
        CheckedBitListBound.budget limit arity bs := by
      dsimp only [CheckedBitListBound.budget, CheckedBitListChildren.budget]
      gcongr <;> omega
    have hi : (many limit arity next rest).2 ≤
        bs.length*(2*count.length+3+CheckedBitListBound.budget limit arity bs) := by
      apply ih.trans
      dsimp only [budget]
      exact Nat.mul_le_mul hrest (by omega)
    rw [many]
    dsimp only
    simp only [hc, budget]
    split
    · rename_i hh; rw [hr] at hh; cases hh
    · rename_i ds rs hh
      have he : (digits,rest)=(ds,rs) := Option.some.inj (hr.symm.trans hh)
      cases he
      nlinarith

theorem consumption (limit arity count : List Bool) (bs : List (List Bool))
    (xs : List (CheckedBitListBound.Bound limit arity)) (rest : List (List Bool))
    (h : (many limit arity count bs).1 = some (xs,rest)) :
    rest.length + xs.length ≤ bs.length ∧
      (rest.map List.length).sum ≤ (bs.map List.length).sum := by
  induction count, bs using many.induct limit arity generalizing xs rest with
  | case1 count bs c hc =>
    dsimp only [c] at hc
    rw [many] at h
    dsimp only at h
    simp only [hc, Option.some.injEq] at h
    cases h
    simp
  | case2 count bs c next hc r hr =>
    dsimp only [c] at hc
    dsimp only [r] at hr
    rw [many] at h
    dsimp only at h
    simp only [hc] at h
    split at h
    · simp at h
    · rename_i a rs hh; rw [hr] at hh; cases hh
  | case3 count bs c next hc r a rs hr ih =>
    dsimp only [c] at hc
    dsimp only [r] at hr
    have hs := CheckedBitListConsumption.bound limit arity bs a rs hr
    rw [many] at h
    dsimp only at h
    simp only [hc] at h
    split at h
    · rename_i hh; rw [hr] at hh; cases hh
    · rename_i b ts hh
      have he := Option.some.inj (hr.symm.trans hh)
      cases he
      cases ht : (many limit arity next rs).1 with
      | none => simp [ht] at h
      | some p =>
        obtain ⟨ys,us⟩ := p
        have hi := ih ys us ht
        have hp : (a::ys,us)=(xs,rest) := by simpa [ht] using h
        cases hp
        simp only [List.length_cons]
        omega

def read (limit arity : List Bool) : List (List Bool) →
    Option (List (CheckedBitListBound.Bound limit arity) × List (List Bool)) × Nat
  | [] => (none,1)
  | count::rest => let r := many limit arity count rest; (r.1,1+r.2)

theorem read_value (limit arity : List Bool) (bs : List (List Bool)) :
    (read limit arity bs).1.map (fun p => (p.1.map CheckedBitListBound.Bound.denote,p.2.map eval)) =
      StoredInputCodec.readList (StoredInputCodec.readBound (eval limit) (eval arity))
        (bs.map eval) := by
  cases bs with
  | nil => rfl
  | cons count rest => exact value limit arity count rest

def readBudget (limit arity : List Bool) (bs : List (List Bool)) :=
  1+(bs.length+1)*(2*(bs.map List.length).sum+3+CheckedBitListBound.budget limit arity bs)

theorem read_bound (limit arity : List Bool) (bs : List (List Bool)) :
    (read limit arity bs).2 ≤ readBudget limit arity bs := by
  cases bs with
  | nil => simp only [read,readBudget]; omega
  | cons count rest =>
    have h := bound limit arity count rest
    have hm : CheckedBitListBound.budget limit arity rest ≤
        CheckedBitListBound.budget limit arity (count::rest) := by
      dsimp only [CheckedBitListBound.budget, CheckedBitListChildren.budget,
        List.length_cons, List.map_cons, List.sum_cons]
      nlinarith
    have hh : (many limit arity count rest).2 ≤
        ((count::rest).length+1)*(2*((count::rest).map List.length).sum+3+
          CheckedBitListBound.budget limit arity (count::rest)) := by
      apply h.trans
      dsimp only [budget, List.length_cons, List.map_cons, List.sum_cons]
      exact Nat.mul_le_mul (by omega) (by omega)
    simpa only [read,readBudget] using Nat.add_le_add_left hh 1

theorem read_consumption (limit arity : List Bool) (bs : List (List Bool))
    (xs : List (CheckedBitListBound.Bound limit arity)) (rest : List (List Bool))
    (h : (read limit arity bs).1 = some (xs,rest)) :
    rest.length + xs.length < bs.length ∧
      (rest.map List.length).sum ≤ (bs.map List.length).sum := by
  cases bs with
  | nil => simp [read] at h
  | cons count tail =>
    have hh := consumption limit arity count tail xs rest h
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

end NSSE.CheckedBitListBounds
