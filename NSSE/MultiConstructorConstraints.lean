import NSSE.MultiConstructorFiniteTrees

/-! Original four-form constraints for a varying-arity covariant signature.
Support decomposes only equal constructor heads. Both actual tree models
instantiate the algebra used in the soundness proof. -/
namespace NSSE.MultiConstructorConstraints

variable {H : Type*} (arity : H → Nat)

structure Bound (n : Nat) where
  parent : Fin n
  head : H
  children : Fin (arity head) → Fin n

structure Constraints (n : Nat) where
  upper : List (Bound arity n)
  lower : List (Bound arity n)
  bot : List (Fin n)
  top : List (Fin n)

structure Query (n : Nat) where
  constraints : Constraints arity n
  left : Fin n
  right : Fin n

variable {arity} {n : Nat}

inductive Support (phi : Constraints arity n) : Fin n → Fin n → Prop
  | refl (x) : Support phi x x
  | trans {x y z} : Support phi x y → Support phi y z → Support phi x z
  | decomp {h : H} {x y : Fin n} {a b : Fin (arity h) → Fin n}
      (lower : ⟨x,h,a⟩ ∈ phi.lower) (upper : ⟨y,h,b⟩ ∈ phi.upper)
      (parents : Support phi x y) (i : Fin (arity h)) : Support phi (a i) (b i)

structure Algebra (T : Type*) [PartialOrder T] [OrderBot T] [OrderTop T] where
  node : (h : H) → (Fin (arity h) → T) → T
  node_le_node : ∀ h a b, node h a ≤ node h b ↔ ∀ i, a i ≤ b i
  head_eq : ∀ h k a b, node h a ≤ node k b → h = k
  node_not_le_bot : ∀ h a, ¬ node h a ≤ ⊥
  top_not_le_node : ∀ h a, ¬ ⊤ ≤ node h a
  top_not_le_bot : ¬ (⊤ : T) ≤ ⊥

def allAlgebra : Algebra (arity := arity) (MultiConstructorTrees.Tree arity) where
  node := MultiConstructorTrees.Tree.node
  node_le_node := MultiConstructorTrees.Tree.node_le_node
  head_eq _ _ _ _ := MultiConstructorTrees.Tree.node_head_eq
  node_not_le_bot := MultiConstructorTrees.Tree.node_not_le_bot
  top_not_le_node := MultiConstructorTrees.Tree.top_not_le_node
  top_not_le_bot h := by
    have bad : MultiConstructorTrees.Label.Below (.top : MultiConstructorTrees.Label H) .bot := h []
    simp [MultiConstructorTrees.Label.Below] at bad

def finiteAlgebra : Algebra (arity := arity) (MultiConstructorFiniteTrees.Tree arity) where
  node := MultiConstructorFiniteTrees.Tree.node
  node_le_node := MultiConstructorFiniteTrees.node_le_node
  head_eq _ _ _ _ := MultiConstructorFiniteTrees.node_head_eq
  node_not_le_bot := MultiConstructorFiniteTrees.node_not_le_bot
  top_not_le_node := MultiConstructorFiniteTrees.top_not_le_node
  top_not_le_bot h := by cases h

variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

def Satisfies (F : Algebra (arity := arity) T) (phi : Constraints arity n)
    (rho : Fin n → T) : Prop :=
  (∀ a ∈ phi.upper, rho a.parent ≤ F.node a.head (fun i => rho (a.children i))) ∧
  (∀ a ∈ phi.lower, F.node a.head (fun i => rho (a.children i)) ≤ rho a.parent) ∧
  (∀ x ∈ phi.bot, rho x = ⊥) ∧ (∀ x ∈ phi.top, rho x = ⊤)

def Satisfiable (F : Algebra (arity := arity) T) (phi : Constraints arity n) : Prop :=
  ∃ rho, Satisfies F phi rho

def Entails (F : Algebra (arity := arity) T) (Q : Query arity n) : Prop :=
  ∀ rho, Satisfies F Q.constraints rho → rho Q.left ≤ rho Q.right

theorem support_sound (F : Algebra (arity := arity) T) (phi : Constraints arity n)
    (rho : Fin n → T) (hs : Satisfies F phi rho) {x y} (h : Support phi x y) :
    rho x ≤ rho y := by
  induction h with
  | refl _ => exact le_rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | @decomp h x y a b hl hu _ i ih =>
    exact (F.node_le_node h _ _).mp ((hs.2.1 _ hl).trans (ih.trans (hs.1 _ hu))) i

def LabelClash (phi : Constraints arity n) : Prop :=
  (∃ x ∈ phi.top, ∃ y ∈ phi.bot, Support phi x y) ∨
  (∃ x ∈ phi.top, ∃ b ∈ phi.upper, Support phi x b.parent) ∨
  (∃ a ∈ phi.lower, ∃ y ∈ phi.bot, Support phi a.parent y) ∨
  (∃ a ∈ phi.lower, ∃ b ∈ phi.upper, Support phi a.parent b.parent ∧ a.head ≠ b.head)

theorem no_label_clash (F : Algebra (arity := arity) T) (phi : Constraints arity n)
    (rho : Fin n → T) (hs : Satisfies F phi rho) : ¬ LabelClash phi := by
  rintro (⟨x,hx,y,hy,hxy⟩ | ⟨x,hx,b,hb,hxb⟩ | ⟨a,ha,y,hy,hay⟩ | ⟨a,ha,b,hb,hab,hne⟩)
  · have h := support_sound F phi rho hs hxy
    rw [hs.2.2.2 x hx,hs.2.2.1 y hy] at h
    exact F.top_not_le_bot h
  · have h := (support_sound F phi rho hs hxb).trans (hs.1 b hb)
    rw [hs.2.2.2 x hx] at h
    exact F.top_not_le_node b.head _ h
  · have h := (hs.2.1 a ha).trans (support_sound F phi rho hs hay)
    rw [hs.2.2.1 y hy] at h
    exact F.node_not_le_bot a.head _ h
  · exact hne (F.head_eq _ _ _ _
      ((hs.2.1 a ha).trans ((support_sound F phi rho hs hab).trans (hs.1 b hb))))

theorem clash_unsatisfiable (F : Algebra (arity := arity) T) (phi : Constraints arity n)
    (hc : LabelClash phi) : ¬ Satisfiable F phi :=
  fun ⟨rho,hs⟩ => no_label_clash F phi rho hs hc

theorem entails_of_unsatisfiable (F : Algebra (arity := arity) T) (Q : Query arity n)
    (hu : ¬ Satisfiable F Q.constraints) : Entails F Q :=
  fun rho hs => False.elim (hu ⟨rho,hs⟩)

theorem finite_satisfies_iff (phi : Constraints arity n)
    (rho : Fin n → MultiConstructorFiniteTrees.Tree arity) :
    Satisfies allAlgebra phi (fun x => MultiConstructorFiniteTrees.embed (rho x)) ↔
      Satisfies finiteAlgebra phi rho := by
  unfold Satisfies
  have hbot (x : Fin n) : MultiConstructorFiniteTrees.embed (rho x) = ⊥ ↔ rho x = ⊥ := by
    constructor
    · intro h
      exact MultiConstructorFiniteTrees.embed_injective h
    · intro h; rw [h]; rfl
  have htop (x : Fin n) : MultiConstructorFiniteTrees.embed (rho x) = ⊤ ↔ rho x = ⊤ := by
    constructor
    · intro h
      exact MultiConstructorFiniteTrees.embed_injective h
    · intro h; rw [h]; rfl
  have hu (a : Bound arity n) :
      MultiConstructorFiniteTrees.embed (rho a.parent) ≤
        allAlgebra.node a.head (fun i => MultiConstructorFiniteTrees.embed (rho (a.children i))) ↔
      rho a.parent ≤ finiteAlgebra.node a.head (fun i => rho (a.children i)) :=
    MultiConstructorFiniteTrees.embed_le_embed (rho a.parent)
      (.node a.head (fun i => rho (a.children i)))
  have hl (a : Bound arity n) :
      allAlgebra.node a.head (fun i => MultiConstructorFiniteTrees.embed (rho (a.children i))) ≤
        MultiConstructorFiniteTrees.embed (rho a.parent) ↔
      finiteAlgebra.node a.head (fun i => rho (a.children i)) ≤ rho a.parent :=
    MultiConstructorFiniteTrees.embed_le_embed (.node a.head (fun i => rho (a.children i)))
      (rho a.parent)
  simp only [hu,hl,hbot,htop]

end NSSE.MultiConstructorConstraints
