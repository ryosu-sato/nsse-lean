import NSSE.MultiConstructorGraph
import NSSE.MultiConstructorFiniteTrees

/-! Regular trees have actual finite graph presentations. Constructor
closure combines the finitely many child presentations with one new root. -/
namespace NSSE.MultiConstructorRegularTrees
open MultiConstructorTrees MultiConstructorGraph
variable {H : Type*} {arity : H → Nat}

def Regular (t : Tree arity) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (G : Graph arity Q) (q : Q), unfold G q = t

theorem graph_regular {Q : Type} [Fintype Q] (G : Graph arity Q) (q : Q) : Regular (unfold G q) :=
  ⟨Q,inferInstance,G,q,rfl⟩

def leafGraph (e : Label H) : Graph arity Unit := ⟨fun _ => e,fun _ _ => ()⟩

theorem bot_regular : Regular (⊥ : Tree arity) :=
  ⟨Unit,inferInstance,leafGraph .bot,(),MultiConstructorGraph.bot _ _ rfl⟩

theorem top_regular : Regular (⊤ : Tree arity) :=
  ⟨Unit,inferInstance,leafGraph .top,(),MultiConstructorGraph.top _ _ rfl⟩

def joinGraph (h : H) (Q : Fin (arity h) → Type) (G : ∀ i, Graph arity (Q i)) (q : ∀ i, Q i) :
    Graph arity (Option (Sigma Q)) where
  head
    | none => .node h
    | some ⟨i,r⟩ => (G i).head r
  next
    | none,j => if hj : j < arity h then some ⟨⟨j,hj⟩,q ⟨j,hj⟩⟩ else none
    | some ⟨i,r⟩,j => some ⟨i,(G i).next r j⟩

theorem join_child_read (h : H) (Q : Fin (arity h) → Type) (G : ∀ i, Graph arity (Q i)) (q : ∀ i, Q i)
    (i : Fin (arity h)) (r : Q i) (w : List Nat) :
    read (joinGraph h Q G q) (some ⟨i,r⟩) w = read (G i) r w := by
  induction w generalizing r with
  | nil => rfl
  | cons j w ih =>
    rw [MultiConstructorGraph.read,MultiConstructorGraph.read]
    dsimp only [joinGraph]
    split_ifs
    · rfl
    · exact ih ((G i).next r j)

theorem join_child (h : H) (Q : Fin (arity h) → Type) (G : ∀ i, Graph arity (Q i)) (q : ∀ i, Q i)
    (i : Fin (arity h)) (r : Q i) : unfold (joinGraph h Q G q) (some ⟨i,r⟩) = unfold (G i) r := by
  apply MultiConstructorTrees.Tree.ext
  exact join_child_read h Q G q i r

theorem join_root (h : H) (Q : Fin (arity h) → Type) (G : ∀ i, Graph arity (Q i)) (q : ∀ i, Q i) :
    unfold (joinGraph h Q G q) none = MultiConstructorTrees.Tree.node h (fun i => unfold (G i) (q i)) := by
  rw [MultiConstructorGraph.node (joinGraph h Q G q) none h rfl]
  congr 1
  funext i
  change unfold (joinGraph h Q G q) (if hi : i.val < arity h then some ⟨⟨i.val,hi⟩,q ⟨i.val,hi⟩⟩ else none) = _
  rw [dif_pos i.isLt]
  exact join_child h Q G q i (q i)

theorem node_regular (h : H) (c : Fin (arity h) → Tree arity) (hc : ∀ i, Regular (c i)) :
    Regular (MultiConstructorTrees.Tree.node h c) := by
  classical
  choose Q f G q he using hc
  letI (i : Fin (arity h)) : Fintype (Q i) := f i
  refine ⟨Option (Sigma Q),inferInstance,joinGraph h Q G q,none,?_⟩
  rw [join_root]
  congr 1
  funext i
  exact he i

theorem finite_regular (t : MultiConstructorFiniteTrees.Tree arity) :
    Regular (MultiConstructorFiniteTrees.embed t) := by
  induction t with
  | bot => exact bot_regular
  | top => exact top_regular
  | node h c ih => exact node_regular h _ ih

end NSSE.MultiConstructorRegularTrees
