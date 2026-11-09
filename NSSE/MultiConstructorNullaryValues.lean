import NSSE.MultiConstructorRegularTrees
import NSSE.MultiConstructorLabelSup

/-! With only nullary heads, every actual tree is determined by its root
label and is the embedding of an explicit finite tree of height at most one. -/
namespace NSSE.MultiConstructorNullaryValues
open MultiConstructorTrees
variable {H : Type*} {arity : H → Nat}

def allValue (e : Label H) : Tree arity := ⟨fun _ => e,fun _ _ _ _ => rfl⟩

def finiteValue (hn : ∀ h, arity h = 0) : Label H → MultiConstructorFiniteTrees.Tree arity
  | .bot => .bot
  | .top => .top
  | .node h => .node h (fun i => Fin.elim0 (Fin.cast (hn h) i))

def finiteRoot : MultiConstructorFiniteTrees.Tree arity → Label H
  | .bot => .bot
  | .top => .top
  | .node h _ => .node h

theorem embed_root (t : MultiConstructorFiniteTrees.Tree arity) :
    (MultiConstructorFiniteTrees.embed t).label [] = finiteRoot t := by cases t <;> rfl

theorem all_stops (hn : ∀ h, arity h = 0) (e : Label H) (i : Nat) : Label.Stops arity e i := by
  cases e <;> simp [Label.Stops,hn]

theorem all_constant (hn : ∀ h, arity h = 0) (t : Tree arity) (w : List Nat) : t.label w = t.label [] := by
  cases w with
  | nil => rfl
  | cons i w => exact t.absorbs [] i w (all_stops hn _ i)

theorem all_value_root (e : Label H) : (allValue (arity := arity) e).label [] = e := rfl

theorem all_value_surjective (hn : ∀ h, arity h = 0) (t : Tree arity) : allValue (t.label []) = t := by
  apply MultiConstructorTrees.Tree.ext
  intro w
  exact (all_constant hn t w).symm

theorem embed_value (hn : ∀ h, arity h = 0) (e : Label H) :
    MultiConstructorFiniteTrees.embed (finiteValue hn e) = allValue e := by
  apply MultiConstructorTrees.Tree.ext
  intro w
  change (MultiConstructorFiniteTrees.embed (finiteValue hn e)).label w = e
  rw [all_constant hn]
  cases e <;> rfl

theorem finite_value_root (hn : ∀ h, arity h = 0) (e : Label H) : finiteRoot (finiteValue hn e) = e := by
  cases e <;> rfl

theorem finite_value_surjective (hn : ∀ h, arity h = 0) (t : MultiConstructorFiniteTrees.Tree arity) :
    finiteValue hn (finiteRoot t) = t := by
  apply MultiConstructorFiniteTrees.embed_injective
  rw [embed_value,← embed_root]
  exact all_value_surjective hn (MultiConstructorFiniteTrees.embed t)

theorem all_value_le (a b : Label H) : allValue (arity := arity) a ≤ allValue b ↔ a ≤ b :=
  ⟨fun h => h [],fun h _ => h⟩

theorem finite_value_le (hn : ∀ h, arity h = 0) (a b : Label H) : finiteValue hn a ≤ finiteValue hn b ↔ a ≤ b := by
  rw [← MultiConstructorFiniteTrees.embed_le_embed,embed_value,embed_value]
  exact all_value_le a b

theorem all_value_eq (a b : Label H) : allValue (arity := arity) a = allValue b ↔ a = b :=
  ⟨fun h => congrArg (fun t : Tree arity => t.label []) h,fun h => congrArg allValue h⟩

theorem finite_value_eq (hn : ∀ h, arity h = 0) (a b : Label H) : finiteValue hn a = finiteValue hn b ↔ a = b :=
  ⟨fun h => by simpa only [finite_value_root] using congrArg finiteRoot h,fun h => congrArg (finiteValue hn) h⟩

theorem all_regular (hn : ∀ h, arity h = 0) (t : Tree arity) : MultiConstructorRegularTrees.Regular t := by
  rw [← all_value_surjective hn t,← embed_value hn]
  exact MultiConstructorRegularTrees.finite_regular _

theorem finite_height (hn : ∀ h, arity h = 0) (e : Label H) :
    MultiConstructorFiniteTrees.height (finiteValue hn e) ≤ 1 := by
  cases e with
  | bot => exact Nat.zero_le _
  | top => exact Nat.zero_le _
  | node h =>
    change Finset.univ.sup (fun i : Fin (arity h) =>
      MultiConstructorFiniteTrees.height (arity := arity) (Fin.elim0 (Fin.cast (hn h) i))) + 1 ≤ 1
    have hz : Finset.univ.sup (fun i : Fin (arity h) =>
      MultiConstructorFiniteTrees.height (arity := arity) (Fin.elim0 (Fin.cast (hn h) i))) ≤ 0 :=
      Finset.sup_le (fun i _ => Fin.elim0 (Fin.cast (hn h) i))
    omega

end NSSE.MultiConstructorNullaryValues
