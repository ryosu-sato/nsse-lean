import NSSE.MultiConstructorGraph

/-! Head-dependent variance on the actual varying-arity tree carrier.
The encoding is an involution. It changes extreme labels according to
the polarities of the heads actually visited, stopping at leaves. -/
namespace NSSE.MultiVarianceEncoding
open MultiConstructorTrees
variable {H : Type*} {arity : H → Nat}

abbrev Polarity (arity : H → Nat) := (h : H) → Fin (arity h) → Bool

def swap : Label H → Label H
  | .bot => .top
  | .top => .bot
  | .node h => .node h

@[simp] theorem swap_swap (e : Label H) : swap (swap e) = e := by cases e <;> rfl

theorem swap_le_swap (a b : Label H) : swap a ≤ swap b ↔ b ≤ a := by
  cases a <;> cases b <;> simp [swap,Label.Below,LE.le,eq_comm]

theorem swap_stops (e : Label H) (i : Nat) :
    Label.Stops arity (swap e) i ↔ Label.Stops arity e i := by cases e <;> rfl

def dual (t : Tree arity) : Tree arity where
  label w := swap (t.label w)
  absorbs p i w hs := congrArg swap (t.absorbs p i w ((swap_stops _ _).mp hs))

@[simp] theorem dual_label (t : Tree arity) (w : List Nat) : (dual t).label w = swap (t.label w) := rfl

@[simp] theorem dual_dual (t : Tree arity) : dual (dual t) = t := by ext w; exact swap_swap _

theorem dual_le_dual (a b : Tree arity) : dual a ≤ dual b ↔ b ≤ a := by
  change (∀ w, swap (a.label w) ≤ swap (b.label w)) ↔ ∀ w, b.label w ≤ a.label w
  simp only [swap_le_swap]

def sign (s : Bool) (e : Label H) : Label H := if s then swap e else e

@[simp] theorem sign_sign (s : Bool) (e : Label H) : sign s (sign s e) = e := by
  cases s <;> simp [sign]

@[simp] theorem sign_node (s : Bool) (h : H) : sign s (.node h) = .node h := by cases s <;> rfl

def graph (pol : Polarity arity) : MultiConstructorGraph.Graph arity (Bool × Tree arity) where
  head s := sign s.1 (s.2.label [])
  next s i := match s.2.label [] with
    | .node h => if hi : i < arity h then (xor s.1 (pol h ⟨i,hi⟩),MultiConstructorTrees.Tree.project s.2 [i]) else s
    | _ => s

def encodeAt (pol : Polarity arity) (s : Bool) (t : Tree arity) : Tree arity :=
  MultiConstructorGraph.unfold (graph pol) (s,t)

@[simp] theorem encode_root (pol : Polarity arity) (s : Bool) (t : Tree arity) :
    (encodeAt pol s t).label [] = sign s (t.label []) := rfl

theorem encode_bot (pol : Polarity arity) (s : Bool) :
    encodeAt pol s (⊥ : Tree arity) = if s then ⊤ else ⊥ := by
  cases s
  · exact MultiConstructorTrees.Tree.eq_bot_of_root _ rfl
  · exact MultiConstructorTrees.Tree.eq_top_of_root _ rfl

theorem encode_top (pol : Polarity arity) (s : Bool) :
    encodeAt pol s (⊤ : Tree arity) = if s then ⊥ else ⊤ := by
  cases s
  · exact MultiConstructorTrees.Tree.eq_top_of_root _ rfl
  · exact MultiConstructorTrees.Tree.eq_bot_of_root _ rfl

theorem encode_node (pol : Polarity arity) (s : Bool) (h : H) (c : Fin (arity h) → Tree arity) :
    encodeAt pol s (MultiConstructorTrees.Tree.node h c) = MultiConstructorTrees.Tree.node h (fun i => encodeAt pol (xor s (pol h i)) (c i)) := by
  rw [encodeAt,MultiConstructorGraph.node (graph pol) (s,MultiConstructorTrees.Tree.node h c) h (by simp [graph])]
  congr 1
  funext i
  simp only [graph,MultiConstructorTrees.Tree.node_label_nil,i.isLt,dif_pos,MultiConstructorTrees.Tree.project_node]
  rfl

theorem encode_involutive (pol : Polarity arity) (s : Bool) (t : Tree arity) :
    encodeAt pol s (encodeAt pol s t) = t := by
  apply MultiConstructorTrees.Tree.ext
  intro w
  induction w generalizing s t with
  | nil => simp only [encode_root,sign_sign]
  | cons i w ih =>
    rcases MultiConstructorTrees.Tree.root_cases t with rfl | rfl | ⟨h,c,rfl⟩
    · cases s <;> simp [encode_bot,encode_top]
    · cases s <;> simp [encode_bot,encode_top]
    · rw [encode_node,encode_node]
      by_cases hi : i < arity h
      · simpa only [MultiConstructorTrees.Tree.node,hi,dif_pos] using ih (xor s (pol h ⟨i,hi⟩)) (c ⟨i,hi⟩)
      · simp [MultiConstructorTrees.Tree.node,hi]

theorem encode_flip_label (pol : Polarity arity) (s : Bool) (t : Tree arity) (w : List Nat) :
    (encodeAt pol (!s) t).label w = swap ((encodeAt pol s t).label w) := by
  induction w generalizing s t with
  | nil => cases s <;> simp [sign]
  | cons i w ih =>
    rcases MultiConstructorTrees.Tree.root_cases t with rfl | rfl | ⟨h,c,rfl⟩
    · cases s <;> simp [encode_bot,swap]
    · cases s <;> simp [encode_top,swap]
    · rw [encode_node,encode_node]
      by_cases hi : i < arity h
      · have hx : xor (!s) (pol h ⟨i,hi⟩) = !(xor s (pol h ⟨i,hi⟩)) := by
          cases s <;> cases pol h ⟨i,hi⟩ <;> rfl
        simpa only [MultiConstructorTrees.Tree.node,hi,dif_pos,hx] using ih (xor s (pol h ⟨i,hi⟩)) (c ⟨i,hi⟩)
      · simp [MultiConstructorTrees.Tree.node,hi,swap]

theorem encode_flip (pol : Polarity arity) (s : Bool) (t : Tree arity) :
    encodeAt pol (!s) t = dual (encodeAt pol s t) := by
  ext w
  exact encode_flip_label pol s t w

theorem encode_injective (pol : Polarity arity) (s : Bool) : Function.Injective (encodeAt pol s) :=
  Function.LeftInverse.injective (encode_involutive pol s)

theorem negative_le (pol : Polarity arity) (a b : Tree arity) :
    encodeAt pol true a ≤ encodeAt pol true b ↔ encodeAt pol false b ≤ encodeAt pol false a := by
  rw [show true = !false from rfl,encode_flip,encode_flip,dual_le_dual]

end NSSE.MultiVarianceEncoding
