import NSSE.CountedSupportRules

/-! Flat inputs with stored child lists rather than executable callbacks.
Length proofs are erased. Serialization and bit encodings are not yet fixed. -/
namespace NSSE.StoredSubtypeInput

def lookup {α : Type*} : (xs : List α) → Fin xs.length → α × Nat
  | [], i => Fin.elim0 i
  | x::_, ⟨0,_⟩ => (x,1)
  | _::xs, ⟨k+1,h⟩ =>
    let r := lookup xs ⟨k,Nat.lt_of_succ_lt_succ h⟩
    (r.1,1+r.2)

theorem lookup_value {α : Type*} (xs : List α) (i : Fin xs.length) :
    (lookup xs i).1 = xs[i.val] := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
    rcases i with ⟨k,h⟩
    cases k with
    | zero => rfl
    | succ k => simpa only [lookup, List.getElem_cons_succ] using ih ⟨k,Nat.lt_of_succ_lt_succ h⟩

theorem lookup_cost {α : Type*} (xs : List α) (i : Fin xs.length) :
    (lookup xs i).2 = i.val+1 := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
    rcases i with ⟨k,h⟩
    cases k with
    | zero => rfl
    | succ k => simp [lookup, ih, Nat.add_comm]

structure Bound (n d : Nat) where
  head : Fin n
  children : List (Fin n)
  length_eq : children.length = d

variable {n d : Nat}

def Bound.child (a : Bound n d) (i : Fin d) : Fin n × Nat :=
  lookup a.children ⟨i.val,by rw [a.length_eq]; exact i.isLt⟩
def Bound.denote (a : Bound n d) : SubtypeConstraints.BoundLiteral n d :=
  (a.head,fun i => a.children[i.val]'(by rw [a.length_eq]; exact i.isLt))

theorem child_value (a : Bound n d) (i : Fin d) : (a.child i).1 = a.denote.2 i := lookup_value _ _
theorem child_bound (a : Bound n d) (i : Fin d) : (a.child i).2 ≤ d := by
  rw [Bound.child, lookup_cost]
  exact i.isLt

def packBound (a : SubtypeConstraints.BoundLiteral n d) : Bound n d :=
  ⟨a.1,List.ofFn a.2,List.length_ofFn⟩
theorem packBound_denote (a : SubtypeConstraints.BoundLiteral n d) : (packBound a).denote = a := by
  apply Prod.ext
  · rfl
  · funext i; simp [Bound.denote, packBound]

structure Input (n d : Nat) where
  upper : List (Bound n d)
  lower : List (Bound n d)
  bot : List (Fin n)
  top : List (Fin n)
def Input.denote (I : Input n d) : SubtypeConstraints.Constraints n d :=
  ⟨I.upper.map Bound.denote,I.lower.map Bound.denote,I.bot,I.top⟩
def pack (φ : SubtypeConstraints.Constraints n d) : Input n d :=
  ⟨φ.upper.map packBound,φ.lower.map packBound,φ.bot,φ.top⟩
theorem pack_denote (φ : SubtypeConstraints.Constraints n d) : (pack φ).denote = φ := by
  cases φ
  simp [pack, Input.denote, List.map_map, Function.comp_def, packBound_denote]
end NSSE.StoredSubtypeInput
