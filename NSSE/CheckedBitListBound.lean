import NSSE.CheckedBitListChildren

/-! Checked binary bound-literal decoding. Arity validity is proof data,
not a second numeric scan in the executable constructor. -/
namespace NSSE.CheckedBitListBound
open BitListTokenReader (eval)
open CheckedBitListIndex (Index)

structure Bound (limit arity : List Bool) where
  head : Index limit
  children : List (Index limit)
  length_eq : children.length = eval arity

def Bound.denote {limit arity : List Bool} (a : Bound limit arity) :
    StoredSubtypeInput.Bound (eval limit) (eval arity) :=
  ⟨a.head.denote,a.children.map Index.denote,by simpa only [List.length_map] using a.length_eq⟩

def read (limit arity : List Bool) : List (List Bool) →
    Option (Bound limit arity × List (List Bool)) × Nat
  | [] => (none,1)
  | digits::tail =>
    let h := CheckedBitListIndex.check limit digits
    match h.1 with
    | none => (none,1+h.2)
    | some head =>
      let c := CheckedBitListChildren.read limit arity tail
      match hc : c.1 with
      | none => (none,2+h.2+c.2)
      | some (children,rest) =>
        (some (⟨head,children,CheckedBitListChildren.length limit arity tail children rest hc⟩,rest),
          2+h.2+c.2)

theorem value (limit arity : List Bool) (tokens : List (List Bool)) :
    (read limit arity tokens).1.map (fun p => (p.1.denote,p.2.map eval)) =
      StoredInputCodec.readBound (eval limit) (eval arity) (tokens.map eval) := by
  cases tokens with
  | nil => simp [read, StoredInputCodec.readBound, StoredInputCodec.index]
  | cons digits tail =>
    have hi := CheckedBitListIndex.value limit digits (tail.map eval)
    have hc := CheckedBitListChildren.value limit arity tail
    cases he : (CheckedBitListIndex.check limit digits).1 with
    | none =>
      simp only [he, Option.map_none'] at hi
      simp [read, he, StoredInputCodec.readBound, ← hi]
    | some head =>
      simp only [he, Option.map_some'] at hi
      cases hcs : (CheckedBitListChildren.read limit arity tail).1 with
      | none =>
        simp only [hcs, Option.map_none'] at hc
        simp [read, he, hcs, StoredInputCodec.readBound, ← hi, ← hc]
        split <;> rename_i hh
        · rfl
        · rw [hcs] at hh; cases hh
      | some p =>
        obtain ⟨children,rest⟩ := p
        have hl := CheckedBitListChildren.length limit arity tail children rest hcs
        simp only [hcs, Option.map_some'] at hc
        simp [read, he, hcs, StoredInputCodec.readBound, ← hi, ← hc, Bound.denote, hl]
        split
        · rename_i hh; rw [hcs] at hh; cases hh
        · rename_i cs rs hh
          have hp := Option.some.inj (hcs.symm.trans hh)
          cases hp
          exact ⟨_, _, rfl, ⟨rfl, rfl⟩, rfl⟩

def budget (limit arity : List Bool) (tokens : List (List Bool)) :=
  5+3*((tokens.map List.length).sum+limit.length)+CheckedBitListChildren.budget limit arity tokens

theorem bound (limit arity : List Bool) (tokens : List (List Bool)) :
    (read limit arity tokens).2 ≤ budget limit arity tokens := by
  cases tokens with
  | nil => simp only [read, budget]; omega
  | cons digits tail =>
    have hi := CheckedBitListIndex.bound limit digits
    have hc := CheckedBitListChildren.bound limit arity tail
    have hm : CheckedBitListChildren.budget limit arity tail ≤
        CheckedBitListChildren.budget limit arity (digits::tail) := by
      dsimp only [CheckedBitListChildren.budget, List.length_cons, List.map_cons, List.sum_cons]
      nlinarith
    have hcb := hc.trans hm
    cases he : (CheckedBitListIndex.check limit digits).1 with
    | none =>
      simp only [read, he, budget, List.map_cons, List.sum_cons]
      omega
    | some head =>
      simp only [read, he]
      split <;> simp only [budget, List.map_cons, List.sum_cons] <;> omega
end NSSE.CheckedBitListBound
