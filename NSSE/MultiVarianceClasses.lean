import NSSE.MultiVarianceTrees
import NSSE.MultiConstructorRegularTrees

/-! The head-dependent encoding preserves and reflects actual finite and
finite-graph tree classes. A graph encoding uses two signed copies of its
states. This is a semantic encoding, not a reduction of constraints. -/
namespace NSSE.MultiVarianceClasses
open MultiVarianceEncoding
open MultiConstructorGraph (Graph unfold)
variable {H : Type*} {arity : H → Nat} (pol : Polarity arity)

def finiteEncode (s : Bool) : MultiConstructorFiniteTrees.Tree arity → MultiConstructorFiniteTrees.Tree arity
  | .bot => if s then .top else .bot
  | .top => if s then .bot else .top
  | .node h c => .node h (fun i => finiteEncode (xor s (pol h i)) (c i))

theorem finite_embed (s : Bool) (t : MultiConstructorFiniteTrees.Tree arity) :
    MultiConstructorFiniteTrees.embed (finiteEncode pol s t) =
      encodeAt pol s (MultiConstructorFiniteTrees.embed t) := by
  induction t generalizing s with
  | bot => cases s <;> simp [finiteEncode,MultiConstructorFiniteTrees.embed,encode_bot]
  | top => cases s <;> simp [finiteEncode,MultiConstructorFiniteTrees.embed,encode_top]
  | node h c ih =>
    rw [finiteEncode,MultiConstructorFiniteTrees.embed,MultiConstructorFiniteTrees.embed,encode_node]
    exact congrArg (MultiConstructorTrees.Tree.node h) (funext (fun i => ih i _))

def Finite (t : MultiConstructorTrees.Tree arity) : Prop :=
  ∃ f : MultiConstructorFiniteTrees.Tree arity, MultiConstructorFiniteTrees.embed f = t

theorem finite_encode (s : Bool) (t : MultiConstructorTrees.Tree arity) (ht : Finite t) :
    Finite (encodeAt pol s t) := by
  obtain ⟨f,rfl⟩ := ht
  exact ⟨finiteEncode pol s f,finite_embed pol s f⟩

theorem finite_iff (s : Bool) (t : MultiConstructorTrees.Tree arity) :
    Finite (encodeAt pol s t) ↔ Finite t := by
  constructor
  · intro ht
    simpa only [encode_involutive] using finite_encode pol s _ ht
  · exact finite_encode pol s t

def signedGraph {Q : Type*} (G : Graph arity Q) : Graph arity (Bool × Q) where
  head sq := sign sq.1 (G.head sq.2)
  next sq i := match G.head sq.2 with
    | .node h => if hi : i < arity h then (xor sq.1 (pol h ⟨i,hi⟩),G.next sq.2 i) else sq
    | _ => sq

theorem graph_encode {Q : Type*} (G : Graph arity Q) (q : Q) (s : Bool) :
    unfold (signedGraph pol G) (s,q) = encodeAt pol s (unfold G q) := by
  apply MultiConstructorTrees.Tree.ext
  intro w
  induction w generalizing s q with
  | nil => rfl
  | cons i w ih =>
    cases hq : G.head q with
    | bot =>
      rw [MultiConstructorGraph.bot G q hq,encode_bot]
      cases s
      · rw [MultiConstructorGraph.bot (signedGraph pol G) (false,q) (by simp [signedGraph,hq,sign,swap])]
        rfl
      · rw [MultiConstructorGraph.top (signedGraph pol G) (true,q) (by simp [signedGraph,hq,sign,swap])]
        rfl
    | top =>
      rw [MultiConstructorGraph.top G q hq,encode_top]
      cases s
      · rw [MultiConstructorGraph.top (signedGraph pol G) (false,q) (by simp [signedGraph,hq,sign,swap])]
        rfl
      · rw [MultiConstructorGraph.bot (signedGraph pol G) (true,q) (by simp [signedGraph,hq,sign,swap])]
        rfl
    | node h =>
      rw [MultiConstructorGraph.node G q h hq,encode_node,
        MultiConstructorGraph.node (signedGraph pol G) (s,q) h (by simp [signedGraph,hq])]
      by_cases hi : i < arity h
      · simpa only [MultiConstructorTrees.Tree.node,hi,dif_pos,signedGraph,hq] using
          ih (G.next q i) (xor s (pol h ⟨i,hi⟩))
      · simp [MultiConstructorTrees.Tree.node,hi]

theorem graph_state_count {Q : Type*} [Fintype Q] : Fintype.card (Bool × Q) = 2*Fintype.card Q := by simp

theorem regular_encode (s : Bool) (t : MultiConstructorTrees.Tree arity)
    (ht : MultiConstructorRegularTrees.Regular t) : MultiConstructorRegularTrees.Regular (encodeAt pol s t) := by
  obtain ⟨Q,f,G,q,rfl⟩ := ht
  letI := f
  exact ⟨Bool × Q,inferInstance,signedGraph pol G,(s,q),graph_encode pol G q s⟩

theorem regular_iff (s : Bool) (t : MultiConstructorTrees.Tree arity) :
    MultiConstructorRegularTrees.Regular (encodeAt pol s t) ↔ MultiConstructorRegularTrees.Regular t := by
  constructor
  · intro ht
    simpa only [encode_involutive] using regular_encode pol s _ ht
  · exact regular_encode pol s t

def orderIso : MultiVarianceTrees.Tree pol ≃o MultiConstructorTrees.Tree arity where
  toFun := MultiVarianceTrees.encoded
  invFun t := ⟨encodeAt pol false t⟩
  left_inv t := MultiVarianceTrees.Tree.ext (encode_involutive pol false t.raw)
  right_inv t := encode_involutive pol false t
  map_rel_iff' := Iff.rfl

end NSSE.MultiVarianceClasses
