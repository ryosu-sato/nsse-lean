import NSSE.SubtypeTerms

/-! # Variable renaming invariance of original nested-term entailment

An input query declares a variable universe `Fin n`, but only the variables
that actually occur in it can influence any semantics. This file proves the
exact invariance, for EVERY constructor and every ordered semantics at once:
renaming the variables of a query along an injective map changes neither
satisfiability nor entailment.

Only `OrderBot` is used, to send the unused part of the larger universe to a
definite value; no finiteness, regularity or model hypothesis appears.

This is the semantic half of the encoded-length question: the counted bound of
`StoredTermFiniteEntailment`/`StoredTermRegularEntailment` is stated in terms
of `StoredQuerySize.size`, which charges the DECLARED universe `n` and each
variable index in unary. Compaction along an injection is what replaces the
declared universe by the number of variables actually used; this file supplies
the fact that the answer is unchanged. Encoded input length and machine time
remain separate open questions.
-/

namespace NSSE.SubtypeTermRenaming

open SubtypeConstraints (Constructor)
open SubtypeTerms

variable {n m d : Nat}

/-! ## Renaming -/

def renameTerm (f : Fin n → Fin m) : Term n d → Term m d
  | .var x => .var (f x)
  | .bot => .bot
  | .top => .top
  | .node children => .node (fun i => renameTerm f (children i))

def renameLiteral (f : Fin n → Fin m) : Literal n d → Literal m d
  | .le a b => .le (renameTerm f a) (renameTerm f b)
  | .eq a b => .eq (renameTerm f a) (renameTerm f b)

def renameQuery (f : Fin n → Fin m) (Q : Query n d) : Query m d :=
  ⟨Q.premises.map (renameLiteral f), renameTerm f Q.left, renameTerm f Q.right⟩

@[simp] theorem renameTerm_var (f : Fin n → Fin m) (x : Fin n) :
    renameTerm (d := d) f (.var x) = .var (f x) := rfl

theorem renameTerm_comp (f : Fin n → Fin m) {k : Nat} (g : Fin m → Fin k) (t : Term n d) :
    renameTerm g (renameTerm f t) = renameTerm (g ∘ f) t := by
  induction t with
  | var x => rfl
  | bot => rfl
  | top => rfl
  | node children ih => simp only [renameTerm]; exact congrArg _ (funext ih)

theorem renameTerm_id (t : Term n d) : renameTerm id t = t := by
  induction t with
  | var x => rfl
  | bot => rfl
  | top => rfl
  | node children ih => simp only [renameTerm, id]; exact congrArg _ (funext ih)

section Semantics

variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

/-! ## Evaluation transports along the renaming -/

theorem eval_rename (F : Constructor T d) (ρ : Fin m → T) (f : Fin n → Fin m) (t : Term n d) :
    eval F ρ (renameTerm f t) = eval F (ρ ∘ f) t := by
  induction t with
  | var x => rfl
  | bot => rfl
  | top => rfl
  | node children ih => simp only [renameTerm, eval]; exact congrArg _ (funext ih)

theorem holds_rename (F : Constructor T d) (ρ : Fin m → T) (f : Fin n → Fin m) (l : Literal n d) :
    Holds F ρ (renameLiteral f l) ↔ Holds F (ρ ∘ f) l := by
  cases l <;> simp only [renameLiteral, Holds, eval_rename]

theorem satisfies_rename (F : Constructor T d) (ρ : Fin m → T) (f : Fin n → Fin m) (Q : Query n d) :
    Satisfies F (renameQuery f Q) ρ ↔ Satisfies F Q (ρ ∘ f) := by
  simp only [Satisfies, renameQuery, List.forall_mem_map, holds_rename]

/-! ## Extending a valuation along an injection

The unused part of the larger universe is sent to `⊥`; the value is irrelevant,
only the existence of a section of `f` matters. -/

noncomputable def extend (f : Fin n → Fin m) (ρ : Fin n → T) : Fin m → T :=
  fun y => if h : ∃ x, f x = y then ρ h.choose else ⊥

omit [OrderTop T] in
theorem extend_apply (f : Fin n → Fin m) (hf : Function.Injective f) (ρ : Fin n → T) (x : Fin n) :
    extend f ρ (f x) = ρ x := by
  have hx : ∃ z, f z = f x := ⟨x, rfl⟩
  simp only [extend, dif_pos hx]
  exact congrArg ρ (hf hx.choose_spec)

omit [OrderTop T] in
theorem extend_comp (f : Fin n → Fin m) (hf : Function.Injective f) (ρ : Fin n → T) :
    extend f ρ ∘ f = ρ := funext (extend_apply f hf ρ)

/-! ## Invariance -/

theorem satisfiable_rename (F : Constructor T d) (f : Fin n → Fin m)
    (hf : Function.Injective f) (Q : Query n d) :
    Satisfiable F (renameQuery f Q) ↔ Satisfiable F Q := by
  constructor
  · rintro ⟨ρ, hρ⟩
    exact ⟨ρ ∘ f, (satisfies_rename F ρ f Q).mp hρ⟩
  · rintro ⟨ρ, hρ⟩
    refine ⟨extend f ρ, (satisfies_rename F (extend f ρ) f Q).mpr ?_⟩
    rw [extend_comp f hf ρ]
    exact hρ

/-- The exact statement: entailment of the renamed query, over the larger
declared universe, is equivalent to entailment of the original one, for every
injective renaming, every constructor and every ordered semantics. -/
theorem entails_rename (F : Constructor T d) (f : Fin n → Fin m)
    (hf : Function.Injective f) (Q : Query n d) :
    Entails F (renameQuery f Q) ↔ Entails F Q := by
  constructor
  · intro h ρ hρ
    have hs : Satisfies F (renameQuery f Q) (extend f ρ) := by
      rw [satisfies_rename, extend_comp f hf ρ]; exact hρ
    have := h (extend f ρ) hs
    simpa only [renameQuery, eval_rename, extend_comp f hf ρ] using this
  · intro h ρ hρ
    have := h (ρ ∘ f) ((satisfies_rename F ρ f Q).mp hρ)
    simpa only [renameQuery, eval_rename] using this

/-- Injectivity is needed only for one direction: a renamed query that is
entailed over the larger universe is entailed over the smaller one. -/
theorem entails_of_entails_rename (F : Constructor T d) (f : Fin n → Fin m) (Q : Query n d)
    (h : Entails F Q) : Entails F (renameQuery f Q) := by
  intro ρ hρ
  have := h (ρ ∘ f) ((satisfies_rename F ρ f Q).mp hρ)
  simpa only [renameQuery, eval_rename] using this

/-! ## Entailment restricted to a class of values

The regular-tree semantics quantifies over valuations inside a class closed
under the constructor and containing `⊥`. Renaming invariance holds verbatim:
the extension of a valuation uses only old values and `⊥`. -/

def EntailsOn (F : Constructor T d) (P : T → Prop) (Q : Query n d) : Prop :=
  ∀ ρ : Fin n → T, (∀ x, P (ρ x)) → Satisfies F Q ρ →
    eval F ρ Q.left ≤ eval F ρ Q.right

omit [OrderTop T] in
theorem extend_class (f : Fin n → Fin m) (ρ : Fin n → T) (P : T → Prop) (hb : P ⊥)
    (hρ : ∀ x, P (ρ x)) : ∀ y, P (extend f ρ y) := by
  intro y
  by_cases h : ∃ x, f x = y
  · simpa only [extend, dif_pos h] using hρ h.choose
  · simpa only [extend, dif_neg h] using hb

theorem entailsOn_rename (F : Constructor T d) (P : T → Prop) (hb : P ⊥) (f : Fin n → Fin m)
    (hf : Function.Injective f) (Q : Query n d) :
    EntailsOn F P (renameQuery f Q) ↔ EntailsOn F P Q := by
  constructor
  · intro h ρ hP hρ
    have hs : Satisfies F (renameQuery f Q) (extend f ρ) := by
      rw [satisfies_rename, extend_comp f hf ρ]; exact hρ
    have := h (extend f ρ) (extend_class f ρ P hb hP) hs
    simpa only [renameQuery, eval_rename, extend_comp f hf ρ] using this
  · intro h ρ hP hρ
    have := h (ρ ∘ f) (fun x => hP (f x)) ((satisfies_rename F ρ f Q).mp hρ)
    simpa only [renameQuery, eval_rename] using this

end Semantics

end NSSE.SubtypeTermRenaming
