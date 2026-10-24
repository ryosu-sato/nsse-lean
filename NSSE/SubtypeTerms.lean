import NSSE.SubtypeConstraintOperations

/-! # Original finite terms and positive inequality/equality premises

These are actual inductive finite terms, not flattened variable names.
The single constructor is covariant and has the original fixed arity.
-/

namespace NSSE.SubtypeTerms

inductive Term (n d : Nat)
  | var (x : Fin n) : Term n d
  | bot : Term n d
  | top : Term n d
  | node (children : Fin d → Term n d) : Term n d

variable {n d : Nat}

def termDecEq : (a b : Term n d) → Decidable (a = b)
  | .var x, .var y => decidable_of_iff (x = y) (by simp)
  | .var _, .bot => isFalse (by intro h; cases h)
  | .var _, .top => isFalse (by intro h; cases h)
  | .var _, .node _ => isFalse (by intro h; cases h)
  | .bot, .var _ => isFalse (by intro h; cases h)
  | .bot, .bot => isTrue rfl
  | .bot, .top => isFalse (by intro h; cases h)
  | .bot, .node _ => isFalse (by intro h; cases h)
  | .top, .var _ => isFalse (by intro h; cases h)
  | .top, .bot => isFalse (by intro h; cases h)
  | .top, .top => isTrue rfl
  | .top, .node _ => isFalse (by intro h; cases h)
  | .node _, .var _ => isFalse (by intro h; cases h)
  | .node _, .bot => isFalse (by intro h; cases h)
  | .node _, .top => isFalse (by intro h; cases h)
  | .node c, .node e =>
      letI : DecidablePred (fun i => c i = e i) := fun i => termDecEq (c i) (e i)
      if h : ∀ i, c i = e i then isTrue (congrArg Term.node (funext h))
        else isFalse (fun he => h (fun i => congrFun (Term.node.inj he) i))

instance : DecidableEq (Term n d) := termDecEq

def subterms : Term n d → List (Term n d)
  | .var x => [.var x]
  | .bot => [.bot]
  | .top => [.top]
  | .node children => .node children :: (List.finRange d).flatMap (fun i => subterms (children i))

theorem mem_subterms (t : Term n d) : t ∈ subterms t := by cases t <;> simp [subterms]

theorem child_mem_subterms (children : Fin d → Term n d) (i : Fin d) :
    children i ∈ subterms (.node children) := by
  simp only [subterms, List.mem_cons, List.mem_flatMap]
  exact Or.inr ⟨i, List.mem_finRange i, mem_subterms (children i)⟩

theorem subterms_closed (t : Term n d) (children : Fin d → Term n d)
    (h : Term.node children ∈ subterms t) (i : Fin d) : children i ∈ subterms t := by
  induction t with
  | var x => simp [subterms] at h
  | bot => simp [subterms] at h
  | top => simp [subterms] at h
  | node c ih =>
      rcases (List.mem_cons.mp h) with he | hm
      · cases he
        exact child_mem_subterms _ i
      · obtain ⟨j,hj,hh⟩ := List.mem_flatMap.mp hm
        exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨j,hj,ih j hh⟩)

inductive Literal (n d : Nat)
  | le (left right : Term n d)
  | eq (left right : Term n d)

structure Query (n d : Nat) where
  premises : List (Literal n d)
  left : Term n d
  right : Term n d

def inequalities : Literal n d → List (Term n d × Term n d)
  | .le a b => [(a,b)]
  | .eq a b => [(a,b),(b,a)]

def expanded (Q : Query n d) : List (Term n d × Term n d) := Q.premises.flatMap inequalities

def terms (Q : Query n d) : List (Term n d) :=
  subterms Q.left ++ subterms Q.right ++ (expanded Q).flatMap (fun p => subterms p.1 ++ subterms p.2)

theorem left_mem_terms (Q : Query n d) : Q.left ∈ terms Q := by
  exact List.mem_append_left _ (List.mem_append_left _ (mem_subterms Q.left))

theorem right_mem_terms (Q : Query n d) : Q.right ∈ terms Q := by
  exact List.mem_append_left _ (List.mem_append_right _ (mem_subterms Q.right))

theorem pair_mem_terms (Q : Query n d) (p : Term n d × Term n d) (h : p ∈ expanded Q) :
    p.1 ∈ terms Q ∧ p.2 ∈ terms Q := by
  constructor
  · exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨p,h,List.mem_append_left _ (mem_subterms p.1)⟩)
  · exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨p,h,List.mem_append_right _ (mem_subterms p.2)⟩)

theorem terms_closed (Q : Query n d) (children : Fin d → Term n d)
    (h : Term.node children ∈ terms Q) (i : Fin d) : children i ∈ terms Q := by
  simp only [terms, List.mem_append, List.mem_flatMap] at h ⊢
  rcases h with (h | h) | ⟨p,hp,h | h⟩
  · exact Or.inl (Or.inl (subterms_closed _ _ h i))
  · exact Or.inl (Or.inr (subterms_closed _ _ h i))
  · exact Or.inr ⟨p,hp,Or.inl (subterms_closed _ _ h i)⟩
  · exact Or.inr ⟨p,hp,Or.inr (subterms_closed _ _ h i)⟩

section Semantics

open SubtypeConstraints (Constructor)

variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

def eval (F : Constructor T d) (ρ : Fin n → T) : Term n d → T
  | .var x => ρ x
  | .bot => ⊥
  | .top => ⊤
  | .node children => F.node (fun i => eval F ρ (children i))

def Holds (F : Constructor T d) (ρ : Fin n → T) : Literal n d → Prop
  | .le a b => eval F ρ a ≤ eval F ρ b
  | .eq a b => eval F ρ a = eval F ρ b

def Satisfies (F : Constructor T d) (Q : Query n d) (ρ : Fin n → T) : Prop :=
  ∀ l ∈ Q.premises, Holds F ρ l

def Satisfiable (F : Constructor T d) (Q : Query n d) : Prop := ∃ ρ, Satisfies F Q ρ

def Entails (F : Constructor T d) (Q : Query n d) : Prop :=
  ∀ ρ, Satisfies F Q ρ → eval F ρ Q.left ≤ eval F ρ Q.right

theorem holds_iff_inequalities (F : Constructor T d) (ρ : Fin n → T) (l : Literal n d) :
    Holds F ρ l ↔ ∀ p ∈ inequalities l, eval F ρ p.1 ≤ eval F ρ p.2 := by
  have heq (a b : T) : a = b ↔ a ≤ b ∧ b ≤ a :=
    ⟨fun h => ⟨le_of_eq h,le_of_eq h.symm⟩,fun h => le_antisymm h.1 h.2⟩
  cases l <;> simp [Holds, inequalities, heq]

theorem satisfies_iff_expanded (F : Constructor T d) (Q : Query n d) (ρ : Fin n → T) :
    Satisfies F Q ρ ↔ ∀ p ∈ expanded Q, eval F ρ p.1 ≤ eval F ρ p.2 := by
  simp only [Satisfies, expanded, List.forall_mem_flatMap, holds_iff_inequalities]

theorem eval_closed (F : Constructor T d) (P : T → Prop)
    (hb : P ⊥) (ht : P ⊤) (hn : ∀ c, (∀ i, P (c i)) → P (F.node c))
    (ρ : Fin n → T) (hρ : ∀ x, P (ρ x)) (t : Term n d) : P (eval F ρ t) := by
  induction t with
  | var x => exact hρ x
  | bot => exact hb
  | top => exact ht
  | node children ih => exact hn _ ih

end Semantics

end NSSE.SubtypeTerms
