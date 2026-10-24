import NSSE.DFAReindexing

/-!
# Padding `Fin`-state automata

An automaton on `Fin n` can be embedded into any `Fin N` with `n ≤ N`.
The added states are rejecting self-loops.  They are unreachable from the
embedded start state, so runs, languages, and productivity certificates are
preserved.
-/

namespace NSSE

universe u

variable {α : Type u} {n N : Nat}

namespace DFA

def finPad (A : DFA α (Fin n)) (hsize : n ≤ N) :
    DFA α (Fin N) where
  start := Fin.castLE hsize A.start
  step := fun state letter =>
    if hstate : state.val < n then
      Fin.castLE hsize
        (A.step ⟨state.val, hstate⟩ letter)
    else
      state
  accept := fun state =>
    if hstate : state.val < n then
      A.accept ⟨state.val, hstate⟩
    else
      False

@[simp] theorem finPad_start
    (A : DFA α (Fin n)) (hsize : n ≤ N) :
    (A.finPad hsize).start = Fin.castLE hsize A.start :=
  rfl

@[simp] theorem finPad_step_castLE
    (A : DFA α (Fin n)) (hsize : n ≤ N)
    (state : Fin n) (letter : α) :
    (A.finPad hsize).step (Fin.castLE hsize state) letter =
      Fin.castLE hsize (A.step state letter) := by
  simp only [finPad, Fin.coe_castLE]
  rw [dif_pos state.isLt]

@[simp] theorem finPad_accept_castLE
    (A : DFA α (Fin n)) (hsize : n ≤ N)
    (state : Fin n) :
    (A.finPad hsize).accept (Fin.castLE hsize state) ↔
      A.accept state := by
  simp only [finPad, Fin.coe_castLE]
  rw [dif_pos state.isLt]

theorem finPad_runFrom
    (A : DFA α (Fin n)) (hsize : n ≤ N)
    (state : Fin n) (word : Word α) :
    (A.finPad hsize).runFrom (Fin.castLE hsize state) word =
      Fin.castLE hsize (A.runFrom state word) := by
  induction word generalizing state with
  | nil => rfl
  | cons letter word ih =>
      rw [runFrom_cons, finPad_step_castLE]
      exact ih (A.step state letter)

theorem finPad_runFrom_outside
    (A : DFA α (Fin n)) (hsize : n ≤ N)
    (state : Fin N) (hstate : ¬ state.val < n)
    (word : Word α) :
    (A.finPad hsize).runFrom state word = state := by
  induction word with
  | nil => rfl
  | cons letter word ih =>
      rw [runFrom_cons]
      change
        (A.finPad hsize).runFrom
          (if h : state.val < n then
            Fin.castLE hsize (A.step ⟨state.val, h⟩ letter)
          else state) word = state
      rw [dif_neg hstate]
      exact ih

theorem finPad_run
    (A : DFA α (Fin n)) (hsize : n ≤ N)
    (word : Word α) :
    (A.finPad hsize).run word =
      Fin.castLE hsize (A.run word) := by
  exact A.finPad_runFrom hsize A.start word

@[simp] theorem finPad_accepts
    (A : DFA α (Fin n)) (hsize : n ≤ N)
    (word : Word α) :
    (A.finPad hsize).Accepts word ↔ A.Accepts word := by
  unfold Accepts
  rw [A.finPad_run hsize word,
    A.finPad_accept_castLE hsize]

theorem finPad_language
    (A : DFA α (Fin n)) (hsize : n ≤ N) :
    (A.finPad hsize).language = A.language := by
  funext word
  exact propext (A.finPad_accepts hsize word)

end DFA

namespace ProductiveDFA

def finPad (A : ProductiveDFA α (Fin n)) (hsize : n ≤ N) :
    ProductiveDFA α (Fin N) where
  automaton := A.automaton.finPad hsize
  productive := fun state =>
    if hstate : state.val < n then
      A.productive ⟨state.val, hstate⟩
    else
      false
  productive_iff := by
    intro state
    by_cases hstate : state.val < n
    · let original : Fin n := ⟨state.val, hstate⟩
      have hstateEq :
          state = Fin.castLE hsize original := by
        exact Fin.ext rfl
      rw [hstateEq]
      simp only [Fin.coe_castLE, dif_pos original.isLt]
      rw [A.productive_iff]
      constructor
      · rintro ⟨tail, htail⟩
        refine ⟨tail, ?_⟩
        rw [A.automaton.finPad_runFrom hsize original tail,
          A.automaton.finPad_accept_castLE hsize]
        exact htail
      · rintro ⟨tail, htail⟩
        refine ⟨tail, ?_⟩
        rw [A.automaton.finPad_runFrom hsize original tail,
          A.automaton.finPad_accept_castLE hsize] at htail
        exact htail
    · simp only [dif_neg hstate, Bool.false_eq_true, false_iff]
      rintro ⟨tail, htail⟩
      rw [A.automaton.finPad_runFrom_outside
          hsize state hstate tail] at htail
      simp [DFA.finPad, hstate] at htail

@[simp] theorem finPad_productive_castLE
    (A : ProductiveDFA α (Fin n)) (hsize : n ≤ N)
    (state : Fin n) :
    (A.finPad hsize).productive (Fin.castLE hsize state) =
      A.productive state := by
  simp only [finPad, Fin.coe_castLE, dif_pos state.isLt]

theorem finPad_language
    (A : ProductiveDFA α (Fin n)) (hsize : n ≤ N) :
    (A.finPad hsize).language = A.language :=
  A.automaton.finPad_language hsize

end ProductiveDFA

theorem automataCapComponent_finPad
    (left : ProductiveDFA α (Fin n₁))
    (right : ProductiveDFA α (Fin n₂))
    (hleft : n₁ ≤ N₁) (hright : n₂ ≤ N₂) :
    automataCapComponent
        (left.finPad hleft) (right.finPad hright) =
      automataCapComponent left right := by
  unfold automataCapComponent
  congr
  · exact left.finPad_language hleft
  · exact right.finPad_language hright

namespace ProductiveCapPair

def finPad
    (component : ProductiveCapPair α (Fin n₁) (Fin n₂))
    (hleft : n₁ ≤ N₁) (hright : n₂ ≤ N₂) :
    ProductiveCapPair α (Fin N₁) (Fin N₂) where
  left := component.left.finPad hleft
  right := component.right.finPad hright
  right_nonempty := by
    rw [component.right.finPad_language hright]
    exact component.right_nonempty

@[simp] theorem finPad_capComponent
    (component : ProductiveCapPair α (Fin n₁) (Fin n₂))
    (hleft : n₁ ≤ N₁) (hright : n₂ ≤ N₂) :
    automataCapComponent
        (component.finPad hleft hright).left
        (component.finPad hleft hright).right =
      automataCapComponent component.left component.right :=
  automataCapComponent_finPad component.left component.right
    hleft hright

end ProductiveCapPair

theorem productiveCapFamilyCovers_finPad
    (components :
      List (ProductiveCapPair α (Fin n₁) (Fin n₂)))
    (hleft : n₁ ≤ N₁) (hright : n₂ ≤ N₂)
    (word : Word α) :
    ProductiveCapFamilyCovers
        (components.map fun component =>
          component.finPad hleft hright) word ↔
      ProductiveCapFamilyCovers components word := by
  induction components with
  | nil => rfl
  | cons component components ih =>
      simp only [List.map_cons, ProductiveCapFamilyCovers,
        ProductiveCapPair.finPad_capComponent]
      rw [ih]

end NSSE
