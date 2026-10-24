import NSSE.StoredFiniteSatisfiability
import Mathlib.Data.List.Forall2

namespace NSSE.StoredFiniteTree

inductive Tree where
  | bot
  | top
  | node (children : List Tree)

variable {d : Nat}

def denote (d : Nat) : Tree → FiniteSubtypeTrees.Tree d
  | .bot => .bot
  | .top => .top
  | .node cs =>
    let ds := cs.map (denote d)
    .node (fun i => ds[i.val]?.getD .bot)

mutual
def compare : Tree → Tree → Bool × Nat
  | .bot, _ => (true,1)
  | .top, .top => (true,1)
  | .top, .bot => (false,1)
  | .top, .node _ => (false,1)
  | .node _, .bot => (false,1)
  | .node _, .top => (true,1)
  | .node as, .node bs =>
    let r := compareLists as bs
    (r.1,1+r.2)
termination_by a _ => sizeOf a

def compareLists : List Tree → List Tree → Bool × Nat
  | [], [] => (true,1)
  | [], _::_ => (false,1)
  | _::_, [] => (false,1)
  | a::as, b::bs =>
    let h := compare a b
    let t := compareLists as bs
    (h.1 && t.1,1+h.2+t.2)
termination_by as _ => sizeOf as
end

def WellFormed (d : Nat) : Tree → Prop
  | .bot => True
  | .top => True
  | .node cs => cs.length=d ∧ ∀ t ∈ cs, WellFormed d t

theorem node_order (as bs : List Tree) (ha : as.length=d) (hb : bs.length=d) :
    denote d (.node as) ≤ denote d (.node bs) ↔
      List.Forall₂ (fun a b => denote d a ≤ denote d b) as bs := by
  rw [denote,denote,FiniteSubtypeTrees.node_le_node,List.forall₂_iff_get]
  constructor
  · intro h
    refine ⟨ha.trans hb.symm,?_⟩
    intro i hi hj
    have hh := h ⟨i,by omega⟩
    simpa [List.getElem?_eq_getElem,hi,hj] using hh
  · rintro ⟨_,h⟩ i
    have hi : i.val < as.length := by rw [ha]; exact i.isLt
    have hj : i.val < bs.length := by rw [hb]; exact i.isLt
    have hh := h i.val hi hj
    simpa [List.getElem?_eq_getElem,hi,hj] using hh

theorem correct (a b : Tree) (ha : WellFormed d a) (hb : WellFormed d b) :
    (compare a b).1 = true ↔ denote d a ≤ denote d b := by
  apply compare.induct
    (motive1 := fun a b => WellFormed d a → WellFormed d b →
      ((compare a b).1 = true ↔ denote d a ≤ denote d b))
    (motive2 := fun as bs => (∀ a ∈ as, WellFormed d a) → (∀ b ∈ bs, WellFormed d b) →
      ((compareLists as bs).1 = true ↔ List.Forall₂ (fun a b => denote d a ≤ denote d b) as bs))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a b ha hb
  · intro x _ _; simp [compare,denote]; exact FiniteSubtypeTrees.Below.bot _
  · intro _ _; simp [compare,denote]
  · intro _ _; simp [compare,denote]; intro h; cases h
  · intro cs _ _; simp [compare,denote]; intro h; cases h
  · intro cs _ _; simp [compare,denote]; intro h; cases h
  · intro cs _ _; simp [compare,denote]; exact FiniteSubtypeTrees.Below.top _
  · intro as bs ih ha hb
    simp only [WellFormed] at ha hb
    rw [compare]
    exact (ih ha.2 hb.2).trans (node_order as bs ha.1 hb.1).symm
  · intro _ _; simp [compareLists]
  · intro x xs _ _; simp [compareLists]
  · intro x xs _ _; simp [compareLists]
  · intro a as b bs ih it ha hb
    have hx := ih (ha a (by simp)) (hb b (by simp))
    have ht := it (fun x h => ha x (by simp [h])) (fun x h => hb x (by simp [h]))
    simp only [compareLists,Bool.and_eq_true,List.forall₂_cons,hx,ht]

def weight : Tree → Nat
  | .bot => 1
  | .top => 1
  | .node cs => 1+(cs.map (fun t => 1+weight t)).sum

theorem bound (a b : Tree) : (compare a b).2 ≤ 2*weight a := by
  apply compare.induct
    (motive1 := fun a b => (compare a b).2 ≤ 2*weight a)
    (motive2 := fun as bs => (compareLists as bs).2 ≤ 1+2*(as.map (fun t => 1+weight t)).sum)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a b
  · intro x; simp [compare,weight]
  · simp [compare,weight]
  · simp [compare,weight]
  · intro cs; simp [compare,weight]
  · intro cs; simp [compare,weight] ; omega
  · intro cs; simp [compare,weight] ; omega
  · intro as bs ih
    simp only [compare,weight]
    omega
  · simp [compareLists]
  · intro x xs; simp [compareLists]
  · intro x xs; simp [compareLists]
  · intro a as b bs ih it
    simp only [compareLists,List.map_cons,List.sum_cons]
    omega

end NSSE.StoredFiniteTree
