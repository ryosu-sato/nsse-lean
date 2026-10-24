import NSSE.AutomataMembership
import Mathlib.Logic.Equiv.Fintype

/-!
# Reindexing finite automata

Automata used by different cap components may have unrelated finite state
types.  This file transports a DFA and its certified productivity table
along a state equivalence, without changing the accepted language.
-/

namespace NSSE

universe u v w v₁ v₂ w₁ w₂

variable {α : Type u} {Q : Type v} {R : Type w}

namespace DFA

def reindex (A : DFA α Q) (equiv : Equiv Q R) : DFA α R where
  start := equiv A.start
  step := fun state letter =>
    equiv (A.step (equiv.symm state) letter)
  accept := fun state => A.accept (equiv.symm state)

@[simp] theorem reindex_start
    (A : DFA α Q) (equiv : Equiv Q R) :
    (A.reindex equiv).start = equiv A.start :=
  rfl

@[simp] theorem reindex_step
    (A : DFA α Q) (equiv : Equiv Q R)
    (state : Q) (letter : α) :
    (A.reindex equiv).step (equiv state) letter =
      equiv (A.step state letter) := by
  simp [reindex]

@[simp] theorem reindex_accept
    (A : DFA α Q) (equiv : Equiv Q R) (state : Q) :
    (A.reindex equiv).accept (equiv state) ↔
      A.accept state := by
  simp [reindex]

theorem reindex_runFrom
    (A : DFA α Q) (equiv : Equiv Q R)
    (state : Q) (word : Word α) :
    (A.reindex equiv).runFrom (equiv state) word =
      equiv (A.runFrom state word) := by
  induction word generalizing state with
  | nil => rfl
  | cons letter word ih =>
      rw [runFrom_cons, reindex_step]
      change
        (A.reindex equiv).runFrom
            (equiv (A.step state letter)) word =
          equiv (A.runFrom (A.step state letter) word)
      exact ih (A.step state letter)

theorem reindex_run
    (A : DFA α Q) (equiv : Equiv Q R) (word : Word α) :
    (A.reindex equiv).run word = equiv (A.run word) := by
  exact A.reindex_runFrom equiv A.start word

@[simp] theorem reindex_accepts
    (A : DFA α Q) (equiv : Equiv Q R) (word : Word α) :
    (A.reindex equiv).Accepts word ↔ A.Accepts word := by
  unfold Accepts
  rw [A.reindex_run equiv word]
  simp [reindex]

theorem reindex_language
    (A : DFA α Q) (equiv : Equiv Q R) :
    (A.reindex equiv).language = A.language := by
  funext word
  exact propext (A.reindex_accepts equiv word)

noncomputable def finReindex
    [Fintype Q] (A : DFA α Q) :
    DFA α (Fin (Fintype.card Q)) :=
  A.reindex (Fintype.equivFin Q)

@[simp] theorem finReindex_accepts
    [Fintype Q] (A : DFA α Q) (word : Word α) :
    A.finReindex.Accepts word ↔ A.Accepts word :=
  A.reindex_accepts (Fintype.equivFin Q) word

theorem finReindex_language
    [Fintype Q] (A : DFA α Q) :
    A.finReindex.language = A.language :=
  A.reindex_language (Fintype.equivFin Q)

end DFA

namespace ProductiveDFA

def reindex (A : ProductiveDFA α Q) (equiv : Equiv Q R) :
    ProductiveDFA α R where
  automaton := A.automaton.reindex equiv
  productive := fun state => A.productive (equiv.symm state)
  productive_iff := by
    intro state
    rw [A.productive_iff]
    constructor
    · rintro ⟨tail, htail⟩
      refine ⟨tail, ?_⟩
      have hrun :=
        A.automaton.reindex_runFrom equiv
          (equiv.symm state) tail
      simp only [Equiv.apply_symm_apply] at hrun
      rw [hrun]
      simpa [DFA.reindex] using htail
    · rintro ⟨tail, htail⟩
      refine ⟨tail, ?_⟩
      have hrun :=
        A.automaton.reindex_runFrom equiv
          (equiv.symm state) tail
      simp only [Equiv.apply_symm_apply] at hrun
      rw [hrun] at htail
      simpa [DFA.reindex] using htail

@[simp] theorem reindex_productive
    (A : ProductiveDFA α Q) (equiv : Equiv Q R)
    (state : Q) :
    (A.reindex equiv).productive (equiv state) =
      A.productive state := by
  simp [reindex]

theorem reindex_language
    (A : ProductiveDFA α Q) (equiv : Equiv Q R) :
    (A.reindex equiv).language = A.language := by
  exact A.automaton.reindex_language equiv

noncomputable def finReindex
    [Fintype Q] (A : ProductiveDFA α Q) :
    ProductiveDFA α (Fin (Fintype.card Q)) :=
  A.reindex (Fintype.equivFin Q)

theorem finReindex_language
    [Fintype Q] (A : ProductiveDFA α Q) :
    A.finReindex.language = A.language :=
  A.reindex_language (Fintype.equivFin Q)

end ProductiveDFA

variable {Q₁ : Type v₁} {Q₂ : Type v₂}
variable {R₁ : Type w₁} {R₂ : Type w₂}

theorem automataCapComponent_reindex
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (leftEquiv : Equiv Q₁ R₁) (rightEquiv : Equiv Q₂ R₂) :
    automataCapComponent
        (left.reindex leftEquiv) (right.reindex rightEquiv) =
      automataCapComponent left right := by
  unfold automataCapComponent
  congr
  · exact left.reindex_language leftEquiv
  · exact right.reindex_language rightEquiv

theorem automataCapComponent_finReindex
    [Fintype Q₁] [Fintype Q₂]
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂) :
    automataCapComponent left.finReindex right.finReindex =
      automataCapComponent left right :=
  automataCapComponent_reindex left right
    (Fintype.equivFin Q₁) (Fintype.equivFin Q₂)

namespace ProductiveCapPair

def reindex
    (component : ProductiveCapPair α Q₁ Q₂)
    (leftEquiv : Equiv Q₁ R₁) (rightEquiv : Equiv Q₂ R₂) :
    ProductiveCapPair α R₁ R₂ where
  left := component.left.reindex leftEquiv
  right := component.right.reindex rightEquiv
  right_nonempty := by
    rw [component.right.reindex_language rightEquiv]
    exact component.right_nonempty

@[simp] theorem reindex_capComponent
    (component : ProductiveCapPair α Q₁ Q₂)
    (leftEquiv : Equiv Q₁ R₁) (rightEquiv : Equiv Q₂ R₂) :
    automataCapComponent
        (component.reindex leftEquiv rightEquiv).left
        (component.reindex leftEquiv rightEquiv).right =
      automataCapComponent component.left component.right :=
  automataCapComponent_reindex component.left component.right
    leftEquiv rightEquiv

noncomputable def finReindex
    [Fintype Q₁] [Fintype Q₂]
    (component : ProductiveCapPair α Q₁ Q₂) :
    ProductiveCapPair α
      (Fin (Fintype.card Q₁)) (Fin (Fintype.card Q₂)) :=
  component.reindex
    (Fintype.equivFin Q₁) (Fintype.equivFin Q₂)

@[simp] theorem finReindex_capComponent
    [Fintype Q₁] [Fintype Q₂]
    (component : ProductiveCapPair α Q₁ Q₂) :
    automataCapComponent
        component.finReindex.left component.finReindex.right =
      automataCapComponent component.left component.right :=
  component.reindex_capComponent
    (Fintype.equivFin Q₁) (Fintype.equivFin Q₂)

end ProductiveCapPair

theorem productiveCapFamilyCovers_reindex
    (components : List (ProductiveCapPair α Q₁ Q₂))
    (leftEquiv : Equiv Q₁ R₁) (rightEquiv : Equiv Q₂ R₂)
    (word : Word α) :
    ProductiveCapFamilyCovers
        (components.map fun component =>
          component.reindex leftEquiv rightEquiv) word ↔
      ProductiveCapFamilyCovers components word := by
  induction components with
  | nil => rfl
  | cons component components ih =>
      simp only [List.map_cons, ProductiveCapFamilyCovers,
        ProductiveCapPair.reindex_capComponent]
      rw [ih]

theorem productiveCapFamilyCovers_finReindex
    [Fintype Q₁] [Fintype Q₂]
    (components : List (ProductiveCapPair α Q₁ Q₂))
    (word : Word α) :
    ProductiveCapFamilyCovers
        (components.map ProductiveCapPair.finReindex) word ↔
      ProductiveCapFamilyCovers components word :=
  productiveCapFamilyCovers_reindex components
    (Fintype.equivFin Q₁) (Fintype.equivFin Q₂) word

end NSSE
