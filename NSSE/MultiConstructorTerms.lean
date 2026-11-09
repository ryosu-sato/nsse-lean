import NSSE.MultiConstructorInputMap

/-! Original finite nested terms over varying-arity covariant heads,
with inequality/equality premises and an inequality query. -/
namespace NSSE.MultiConstructorTerms

inductive Term {H : Type*} (arity : H → Nat) (n : Nat)
  | var (x : Fin n)
  | bot
  | top
  | node (head : H) (children : Fin (arity head) → Term arity n)

variable {H : Type*} {arity : H → Nat} {n : Nat}

def termDecEq [DecidableEq H] : (a b : Term arity n) → Decidable (a = b)
  | .var x, .var y => decidable_of_iff (x = y) (by simp)
  | .var _, .bot => isFalse (by intro h; cases h)
  | .var _, .top => isFalse (by intro h; cases h)
  | .var _, .node _ _ => isFalse (by intro h; cases h)
  | .bot, .var _ => isFalse (by intro h; cases h)
  | .bot, .bot => isTrue rfl
  | .bot, .top => isFalse (by intro h; cases h)
  | .bot, .node _ _ => isFalse (by intro h; cases h)
  | .top, .var _ => isFalse (by intro h; cases h)
  | .top, .bot => isFalse (by intro h; cases h)
  | .top, .top => isTrue rfl
  | .top, .node _ _ => isFalse (by intro h; cases h)
  | .node _ _, .var _ => isFalse (by intro h; cases h)
  | .node _ _, .bot => isFalse (by intro h; cases h)
  | .node _ _, .top => isFalse (by intro h; cases h)
  | .node h c, .node g e =>
    if hh : h = g then by
      subst g
      letI : DecidablePred (fun i => c i = e i) := fun i => termDecEq (c i) (e i)
      exact if hc : ∀ i, c i = e i then isTrue (congrArg (Term.node h) (funext hc))
        else isFalse (by intro he; cases he; exact hc (fun _ => rfl))
    else isFalse (by intro he; cases he; exact hh rfl)

instance [DecidableEq H] : DecidableEq (Term arity n) := termDecEq

def subterms : Term arity n → List (Term arity n)
  | .var x => [.var x]
  | .bot => [.bot]
  | .top => [.top]
  | .node h c => .node h c :: (List.finRange (arity h)).flatMap (fun i => subterms (c i))

theorem mem_subterms (t : Term arity n) : t ∈ subterms t := by cases t <;> simp [subterms]

theorem child_mem_subterms (h : H) (c : Fin (arity h) → Term arity n) (i : Fin (arity h)) :
    c i ∈ subterms (.node h c) := by
  simp only [subterms,List.mem_cons,List.mem_flatMap]
  exact Or.inr ⟨i,List.mem_finRange i,mem_subterms (c i)⟩

theorem subterms_closed (t : Term arity n) (h : H) (c : Fin (arity h) → Term arity n)
    (hc : Term.node h c ∈ subterms t) (i : Fin (arity h)) : c i ∈ subterms t := by
  induction t with
  | var x => simp [subterms] at hc
  | bot => simp [subterms] at hc
  | top => simp [subterms] at hc
  | node g e ih =>
    rcases List.mem_cons.mp hc with he | hm
    · cases he
      exact child_mem_subterms _ _ i
    · obtain ⟨j,hj,hh⟩ := List.mem_flatMap.mp hm
      exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨j,hj,ih j hh⟩)

inductive Literal (arity : H → Nat) (n : Nat)
  | le (left right : Term arity n)
  | eq (left right : Term arity n)

structure Query (arity : H → Nat) (n : Nat) where
  premises : List (Literal arity n)
  left : Term arity n
  right : Term arity n

def inequalities : Literal arity n → List (Term arity n × Term arity n)
  | .le a b => [(a,b)]
  | .eq a b => [(a,b),(b,a)]

def expanded (Q : Query arity n) : List (Term arity n × Term arity n) := Q.premises.flatMap inequalities

def terms (Q : Query arity n) : List (Term arity n) :=
  subterms Q.left ++ subterms Q.right ++ (expanded Q).flatMap (fun p => subterms p.1 ++ subterms p.2)

theorem left_mem_terms (Q : Query arity n) : Q.left ∈ terms Q :=
  List.mem_append_left _ (List.mem_append_left _ (mem_subterms Q.left))

theorem right_mem_terms (Q : Query arity n) : Q.right ∈ terms Q :=
  List.mem_append_left _ (List.mem_append_right _ (mem_subterms Q.right))

theorem pair_mem_terms (Q : Query arity n) (p : Term arity n × Term arity n) (hp : p ∈ expanded Q) :
    p.1 ∈ terms Q ∧ p.2 ∈ terms Q :=
  ⟨List.mem_append_right _ (List.mem_flatMap.mpr ⟨p,hp,List.mem_append_left _ (mem_subterms p.1)⟩),
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨p,hp,List.mem_append_right _ (mem_subterms p.2)⟩)⟩

theorem terms_closed (Q : Query arity n) (h : H) (c : Fin (arity h) → Term arity n)
    (hc : Term.node h c ∈ terms Q) (i : Fin (arity h)) : c i ∈ terms Q := by
  simp only [terms,List.mem_append,List.mem_flatMap] at hc ⊢
  rcases hc with (hc | hc) | ⟨p,hp,hc | hc⟩
  · exact Or.inl (Or.inl (subterms_closed _ _ _ hc i))
  · exact Or.inl (Or.inr (subterms_closed _ _ _ hc i))
  · exact Or.inr ⟨p,hp,Or.inl (subterms_closed _ _ _ hc i)⟩
  · exact Or.inr ⟨p,hp,Or.inr (subterms_closed _ _ _ hc i)⟩

section Semantics
open MultiConstructorConstraints (Algebra)
variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

def eval (F : Algebra (arity := arity) T) (rho : Fin n → T) : Term arity n → T
  | .var x => rho x
  | .bot => ⊥
  | .top => ⊤
  | .node h c => F.node h (fun i => eval F rho (c i))

def Holds (F : Algebra (arity := arity) T) (rho : Fin n → T) : Literal arity n → Prop
  | .le a b => eval F rho a ≤ eval F rho b
  | .eq a b => eval F rho a = eval F rho b

def Satisfies (F : Algebra (arity := arity) T) (Q : Query arity n) (rho : Fin n → T) : Prop :=
  ∀ l ∈ Q.premises, Holds F rho l

def Satisfiable (F : Algebra (arity := arity) T) (Q : Query arity n) : Prop := ∃ rho, Satisfies F Q rho

def Entails (F : Algebra (arity := arity) T) (Q : Query arity n) : Prop :=
  ∀ rho, Satisfies F Q rho → eval F rho Q.left ≤ eval F rho Q.right

theorem holds_iff_inequalities (F : Algebra (arity := arity) T) (rho : Fin n → T) (l : Literal arity n) :
    Holds F rho l ↔ ∀ p ∈ inequalities l, eval F rho p.1 ≤ eval F rho p.2 := by
  have heq (a b : T) : a = b ↔ a ≤ b ∧ b ≤ a :=
    ⟨fun h => ⟨le_of_eq h,le_of_eq h.symm⟩,fun h => le_antisymm h.1 h.2⟩
  cases l <;> simp [Holds,inequalities,heq]

theorem satisfies_iff_expanded (F : Algebra (arity := arity) T) (Q : Query arity n) (rho : Fin n → T) :
    Satisfies F Q rho ↔ ∀ p ∈ expanded Q, eval F rho p.1 ≤ eval F rho p.2 := by
  simp only [Satisfies,expanded,List.forall_mem_flatMap,holds_iff_inequalities]

theorem eval_closed (F : Algebra (arity := arity) T) (P : T → Prop) (hb : P ⊥) (ht : P ⊤)
    (hn : ∀ h c, (∀ i, P (c i)) → P (F.node h c)) (rho : Fin n → T) (hr : ∀ x, P (rho x))
    (t : Term arity n) : P (eval F rho t) := by
  induction t with
  | var x => exact hr x
  | bot => exact hb
  | top => exact ht
  | node h c ih => exact hn h _ ih

end Semantics
end NSSE.MultiConstructorTerms
