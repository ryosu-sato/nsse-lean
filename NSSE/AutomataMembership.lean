import NSSE.Automata

/-!
# Certified finite membership search

This module supplies the effective content of Corollary 1.4.  A DFA is
equipped with a Boolean productivity table whose certificate says exactly
which states admit an accepting continuation.  Prefix closure is therefore
decided by one table lookup, while split points and periodic witnesses are
searched over finite position types.
-/

namespace NSSE

universe u v v₁ v₂

/-- Constructive bounded existential search for core Lean's `Fin` type. -/
def decidableExistsFin (n : Nat) (P : Fin n → Prop)
    (hP : ∀ i, Decidable (P i)) :
    Decidable (∃ i, P i) := by
  induction n with
  | zero =>
      exact isFalse (by rintro ⟨i, -⟩; exact Fin.elim0 i)
  | succ n ih =>
      letI : Decidable (∃ i : Fin n, P i.succ) :=
        ih (fun i => P i.succ) (fun i => hP i.succ)
      exact decidable_of_iff
        (P ⟨0, Nat.zero_lt_succ n⟩ ∨ ∃ i : Fin n, P i.succ) <| by
          constructor
          · rintro (hzero | ⟨i, hi⟩)
            · exact ⟨⟨0, Nat.zero_lt_succ n⟩, hzero⟩
            · exact ⟨i.succ, hi⟩
          · rintro ⟨i, hi⟩
            revert hi
            refine Fin.cases ?_ (fun j hj => Or.inr ⟨j, hj⟩) i
            exact fun hzero => Or.inl hzero

instance instDecidableExistsFin
    (P : Fin n → Prop) [hP : ∀ i, Decidable (P i)] :
    Decidable (∃ i, P i) :=
  decidableExistsFin n P hP

/--
A DFA together with a checked table for states from which some accepting
continuation exists. Such a table is computable once for every finite DFA.
-/
structure ProductiveDFA (α : Type u) (Q : Type v) where
  automaton : DFA α Q
  productive : Q → Bool
  productive_iff (q : Q) :
    productive q = true ↔
      ∃ tail, automaton.accept (automaton.runFrom q tail)

namespace ProductiveDFA

def language (A : ProductiveDFA α Q) : Language α :=
  A.automaton.language

theorem prefixClosure_iff (A : ProductiveDFA α Q) (w : Word α) :
    Language.prefixClosure A.language w ↔
      A.productive (A.automaton.run w) = true := by
  rw [A.productive_iff]
  constructor
  · rintro ⟨tail, htail⟩
    refine ⟨tail, ?_⟩
    simpa [language, DFA.language, DFA.Accepts,
      A.automaton.run_append] using htail
  · rintro ⟨tail, htail⟩
    refine ⟨tail, ?_⟩
    simpa [language, DFA.language, DFA.Accepts,
      A.automaton.run_append] using htail

instance prefixClosure_decidable (A : ProductiveDFA α Q) (w : Word α) :
    Decidable (Language.prefixClosure A.language w) :=
  decidable_of_iff (A.productive (A.automaton.run w) = true)
    (A.prefixClosure_iff w).symm

end ProductiveDFA

def automataCapComponent
    (left : ProductiveDFA α Q₁) (right : ProductiveDFA α Q₂) :
    CapComponent α :=
  ⟨left.language, right.language⟩

/-- Finite-position presentation of the periodic branch of Lemma 1.3. -/
def FinitePeriodicWitness
    (c : CapComponent α) (w : Word α) : Prop :=
  ∃ j : Fin (w.length + 1), ∃ p : Fin (w.length + 1),
    ∃ e : Fin (w.length + 1),
      0 < p.1 ∧ 0 < e.1 ∧ j.1 + p.1 + e.1 = w.length ∧
      c.left (w.take j.1) ∧ c.right (Word.factor w j.1 p.1) ∧
      Word.WitnessCopy w j.1 p.1 e.1

theorem finitePeriodicWitness_iff
    (c : CapComponent α) (w : Word α) :
    FinitePeriodicWitness c w ↔ PeriodicWitness c w := by
  constructor
  · rintro ⟨j, p, e, hp, he, hlen, hleft, hright, hcopy⟩
    exact ⟨j.1, p.1, e.1, hp, he, hlen, hleft, hright, hcopy⟩
  · rintro ⟨j, p, e, hp, he, hlen, hleft, hright, hcopy⟩
    have hj : j < w.length + 1 := by omega
    have hpb : p < w.length + 1 := by omega
    have heb : e < w.length + 1 := by omega
    exact ⟨⟨j, hj⟩, ⟨p, hpb⟩, ⟨e, heb⟩,
      hp, he, hlen, hleft, hright, hcopy⟩

/-- Finite-position presentation of the split branch of Lemma 1.3. -/
def FiniteSplitRoute
    (c : CapComponent α) (w : Word α) : Prop :=
  ∃ j : Fin (w.length + 1),
    c.left (w.take j.1) ∧
      Language.prefixClosure c.right (w.drop j.1)

theorem finiteSplitRoute_iff
    (c : CapComponent α) (w : Word α) :
    FiniteSplitRoute c w ↔ SplitRoute c w := by
  constructor
  · rintro ⟨j, hleft, hright⟩
    exact ⟨j.1, by omega, hleft, hright⟩
  · rintro ⟨j, hj, hleft, hright⟩
    exact ⟨⟨j, by omega⟩, hleft, hright⟩

instance finitePeriodicWitness_decidable
    [DecidableEq α]
    (left : ProductiveDFA α Q₁) (right : ProductiveDFA α Q₂)
    [∀ q, Decidable (left.automaton.accept q)]
    [∀ q, Decidable (right.automaton.accept q)]
    (w : Word α) :
    Decidable
      (FinitePeriodicWitness (automataCapComponent left right) w) := by
  letI : DecidablePred left.language := fun v => by
    unfold ProductiveDFA.language DFA.language DFA.Accepts
    infer_instance
  letI : DecidablePred right.language := fun v => by
    unfold ProductiveDFA.language DFA.language DFA.Accepts
    infer_instance
  unfold FinitePeriodicWitness automataCapComponent
  apply decidableExistsFin
  intro j
  apply decidableExistsFin
  intro p
  apply decidableExistsFin
  intro e
  dsimp
  letI : Decidable (left.language (w.take j.1)) := by
    unfold ProductiveDFA.language DFA.language DFA.Accepts
    infer_instance
  letI : Decidable (right.language (Word.factor w j.1 p.1)) := by
    unfold ProductiveDFA.language DFA.language DFA.Accepts
    infer_instance
  letI : Decidable (Word.WitnessCopy w j.1 p.1 e.1) := by
    unfold Word.WitnessCopy Word.factor Word.suffix
    infer_instance
  infer_instance

instance finiteSplitRoute_decidable
    (left : ProductiveDFA α Q₁) (right : ProductiveDFA α Q₂)
    [∀ q, Decidable (left.automaton.accept q)]
    (w : Word α) :
    Decidable
      (FiniteSplitRoute (automataCapComponent left right) w) := by
  letI : DecidablePred left.language := fun v => by
    unfold ProductiveDFA.language DFA.language DFA.Accepts
    infer_instance
  letI : ∀ v, Decidable (Language.prefixClosure right.language v) :=
    fun v => right.prefixClosure_decidable v
  unfold FiniteSplitRoute automataCapComponent
  infer_instance

/--
The finite search proposition used to decide the three normal-form
branches for a pair of certified DFAs.
-/
def FiniteComponentNormalForm
    (left : ProductiveDFA α Q₁) (right : ProductiveDFA α Q₂)
    (w : Word α) : Prop :=
  left.productive (left.automaton.run w) = true ∨
    FiniteSplitRoute (automataCapComponent left right) w ∨
    FinitePeriodicWitness (automataCapComponent left right) w

theorem finiteComponentNormalForm_iff
    (left : ProductiveDFA α Q₁) (right : ProductiveDFA α Q₂)
    (w : Word α) :
    FiniteComponentNormalForm left right w ↔
      ComponentNormalForm (automataCapComponent left right) w := by
  unfold FiniteComponentNormalForm ComponentNormalForm PrefixRoute
  rw [← left.prefixClosure_iff w,
    finiteSplitRoute_iff, finitePeriodicWitness_iff]
  rfl

instance finiteComponentNormalForm_decidable
    [DecidableEq α]
    (left : ProductiveDFA α Q₁) (right : ProductiveDFA α Q₂)
    [∀ q, Decidable (left.automaton.accept q)]
    [∀ q, Decidable (right.automaton.accept q)]
    (w : Word α) :
    Decidable (FiniteComponentNormalForm left right w) := by
  unfold FiniteComponentNormalForm
  infer_instance

/--
Corollary 1.4 for one retained cap component: membership is decidable by
the finite normal-form search once the right language is known nonempty.
-/
def decideAutomataCapComponentCovers
    [DecidableEq α]
    (left : ProductiveDFA α Q₁) (right : ProductiveDFA α Q₂)
    [∀ q, Decidable (left.automaton.accept q)]
    [∀ q, Decidable (right.automaton.accept q)]
    (hright : ∃ mu, right.language mu)
    (w : Word α) :
    Decidable ((automataCapComponent left right |> capComponentCovers) w) :=
  decidable_of_iff (FiniteComponentNormalForm left right w) <|
    (finiteComponentNormalForm_iff left right w).trans <|
      (capComponentCovers_iff_componentNormalForm
        (automataCapComponent left right) hright w).symm

/-- One retained automata component, including its preprocessing witness. -/
structure ProductiveCapPair (α : Type u) (Q₁ : Type v₁) (Q₂ : Type v₂) where
  left : ProductiveDFA α Q₁
  right : ProductiveDFA α Q₂
  right_nonempty : ∃ mu, right.language mu

/-- Coverage by a finite homogeneous list of retained cap components. -/
def ProductiveCapFamilyCovers
    (components : List (ProductiveCapPair α Q₁ Q₂))
    (w : Word α) : Prop :=
  match components with
  | [] => False
  | c :: cs =>
      capComponentCovers (automataCapComponent c.left c.right) w ∨
        ProductiveCapFamilyCovers cs w

/--
Corollary 1.4 for the finite cap union `P`: membership is constructively
decidable by recursively invoking the finite normal-form search.
-/
def decideProductiveCapFamilyCovers
    [DecidableEq α]
    [∀ c : ProductiveCapPair α Q₁ Q₂,
      ∀ q, Decidable (c.left.automaton.accept q)]
    [∀ c : ProductiveCapPair α Q₁ Q₂,
      ∀ q, Decidable (c.right.automaton.accept q)]
    (w : Word α) :
    (components : List (ProductiveCapPair α Q₁ Q₂)) →
      Decidable (ProductiveCapFamilyCovers components w)
  | [] => isFalse id
  | c :: cs => by
      unfold ProductiveCapFamilyCovers
      letI : ∀ q, Decidable (c.left.automaton.accept q) :=
        fun q => inferInstance
      letI : ∀ q, Decidable (c.right.automaton.accept q) :=
        fun q => inferInstance
      letI : Decidable
          (capComponentCovers
            (automataCapComponent c.left c.right) w) :=
        decideAutomataCapComponentCovers
          c.left c.right c.right_nonempty w
      letI : Decidable (ProductiveCapFamilyCovers cs w) :=
        decideProductiveCapFamilyCovers w cs
      infer_instance

end NSSE
