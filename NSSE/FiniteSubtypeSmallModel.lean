import NSSE.SubtypeShapeGrammar

/-! # An input-only small-model bound for original finite-tree constraints

If any finite solution exists, the actual two-set grammar stabilizes after
its number of states and computes a solution. The decreasing measure used
in the proof is not an input to the model construction or decision program.
-/

namespace NSSE.FiniteSubtypeSmallModel

open FiniteSubtypeTrees FiniteTreeGrammar SubtypeConstraints SubtypeShapeGrammar

variable {n d : Nat}

def Bounds (ρ : Fin n → Tree d) (s : State n) (t : Tree d) : Prop :=
  (∀ x ∈ s.1, ρ x ≤ t) ∧ (∀ x ∈ s.2, t ≤ ρ x)

theorem initial_bounds (φ : Constraints n d) (ρ : Fin n → Tree d)
    (hρ : Satisfies (constructor d) φ ρ) (x : Fin n) : Bounds ρ (initial φ x) (ρ x) := by
  constructor
  · intro z hz
    exact support_sound (constructor d) φ ρ hρ ((mem_down φ x z).mp hz)
  · intro z hz
    exact support_sound (constructor d) φ ρ hρ ((mem_up φ x z).mp hz)

theorem label_node_iff (φ : Constraints n d) (s : State n) :
    (grammar φ).label s = .node ↔ LowF φ s.1 ∧ HighF φ s.2 := by
  by_cases hl : LowF φ s.1 <;> by_cases hu : HighF φ s.2 <;>
    by_cases hb : HighBot φ s.2 <;> simp [grammar, hl, hu, hb]

/-- A required grammar node forces a genuine constructor in ANY finite
tree lying between the lower and upper variable sets. -/
theorem node_bounds (φ : Constraints n d) (ρ : Fin n → Tree d)
    (hρ : Satisfies (constructor d) φ ρ) (s : State n) (t : Tree d)
    (hs : Bounds ρ s t) (hn : (grammar φ).label s = .node) :
    ∃ children : Fin d → Tree d, t = .node children ∧
      ∀ i, Bounds ρ ((grammar φ).next s i) (children i) := by
  obtain ⟨⟨a,ha,haL⟩,⟨b,hb,hbU⟩⟩ := (label_node_iff φ s).mp hn
  have hlo := (hρ.2.1 a ha).trans (hs.1 a.1 haL)
  have hhi := (hs.2 b.1 hbU).trans (hρ.1 b hb)
  cases t with
  | bot => cases hlo
  | top => cases hhi
  | node children =>
      refine ⟨children,rfl,?_⟩
      intro i
      constructor
      · intro z hz
        obtain ⟨c,hc,hcL,hzc⟩ := (mem_lowStep φ _ i z).mp hz
        have hc' := (hρ.2.1 c hc).trans (hs.1 c.1 hcL)
        have hd := (node_le_node _ _).mp hc' i
        exact (support_sound (constructor d) φ ρ hρ hzc).trans hd
      · intro z hz
        obtain ⟨c,hc,hcU,hcz⟩ := (mem_highStep φ _ i z).mp hz
        have hc' := (hs.2 c.1 hcU).trans (hρ.1 c hc)
        have hd := (node_le_node _ _).mp hc' i
        exact hd.trans (support_sound (constructor d) φ ρ hρ hcz)

def stateBound (n : Nat) : Nat := Fintype.card (State n)

theorem stateBound_eq (n : Nat) : stateBound n = 2 ^ n * 2 ^ n := by
  simp [stateBound, State, Fintype.card_prod, Fintype.card_finset]

/-- The finite-tree height witness forbids cycles among compatible node
states. Counting smaller minimum heights replaces that measure by a rank
strictly below the literal finite number of grammar states. -/
theorem stable_equation (φ : Constraints n d) (ρ : Fin n → Tree d)
    (hρ : Satisfies (constructor d) φ ρ) (s : State n) (hs : ∃ t, Bounds ρ s t) :
    unfold (grammar φ) (stateBound n) s = match (grammar φ).label s with
      | .bot => .bot
      | .top => .top
      | .node => .node (fun i => unfold (grammar φ) (stateBound n) ((grammar φ).next s i)) := by
  classical
  let Good : State n → Prop := fun s => ∃ t, Bounds ρ s t
  have hex (s : State n) (hs : Good s) : ∃ k, ∃ t, Bounds ρ s t ∧ height t = k := by
    obtain ⟨t,ht⟩ := hs
    exact ⟨height t,t,ht,rfl⟩
  let μ : State n → Nat := fun s => if h : Good s then Nat.find (hex s h) else 0
  have hmin (s : State n) (t : Tree d) (ht : Bounds ρ s t) : μ s ≤ height t := by
    have hg : Good s := ⟨t,ht⟩
    simp only [μ, dif_pos hg]
    exact Nat.find_min' (hex s hg) ⟨t,ht,rfl⟩
  have hwit (s : State n) (hs : Good s) : ∃ t, Bounds ρ s t ∧ height t = μ s := by
    simpa only [μ, dif_pos hs] using Nat.find_spec (hex s hs)
  have hnext : ∀ s, Good s → (grammar φ).label s = .node → ∀ i, Good ((grammar φ).next s i) := by
    intro s hs hn i
    obtain ⟨t,ht⟩ := hs
    obtain ⟨children,_,hc⟩ := node_bounds φ ρ hρ s t ht hn
    exact ⟨children i,hc i⟩
  have hdec : ∀ s, Good s → (grammar φ).label s = .node → ∀ i,
      μ ((grammar φ).next s i) < μ s := by
    intro s hs hn i
    obtain ⟨t,ht,hm⟩ := hwit s hs
    obtain ⟨children,rfl,hc⟩ := node_bounds φ ρ hρ s t ht hn
    rw [← hm]
    exact (hmin _ _ (hc i)).trans_lt (child_height_lt children i)
  exact unfold_equation (grammar φ) Good μ hnext hdec s hs

/-- The program uses only the original finite constraints and n. -/
def model (φ : Constraints n d) (x : Fin n) : Tree d :=
  unfold (grammar φ) (stateBound n) (initial φ x)

theorem model_satisfies (φ : Constraints n d) (h : Satisfiable (constructor d) φ) :
    Satisfies (constructor d) φ (model φ) := by
  obtain ⟨ρ,hρ⟩ := h
  have he (x : Fin n) := stable_equation φ ρ hρ (initial φ x) ⟨ρ x,initial_bounds φ ρ hρ x⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro a ha
    change unfold (grammar φ) (stateBound n) (initial φ a.1) ≤
      Tree.node (fun i => unfold (grammar φ) (stateBound n) (initial φ (a.2 i)))
    rw [he a.1]
    have hu : HighF φ (up φ a.1) := ⟨a,ha,(mem_up φ _ _).mpr (.refl _)⟩
    by_cases hl : LowF φ (down φ a.1)
    · simp only [grammar, initial, hl, hu, ↓reduceIte]
      exact Below.node (fun i => unfold_mono φ _ (upper_next_refines φ a ha i))
    · simp only [grammar, initial, hl, hu, true_or, ↓reduceIte]
      exact bot_le
  · intro a ha
    change Tree.node (fun i => unfold (grammar φ) (stateBound n) (initial φ (a.2 i))) ≤
      unfold (grammar φ) (stateBound n) (initial φ a.1)
    rw [he a.1]
    have hl : LowF φ (down φ a.1) := ⟨a,ha,(mem_down φ _ _).mpr (.refl _)⟩
    by_cases hu : HighF φ (up φ a.1)
    · simp only [grammar, initial, hl, hu, ↓reduceIte]
      exact Below.node (fun i => unfold_mono φ _ (lower_next_refines φ a ha i))
    · simp only [grammar, initial, hl, hu, ↓reduceIte]
      exact le_top
  · intro x hx
    change unfold (grammar φ) (stateBound n) (initial φ x) = .bot
    rw [he x]
    have hl : ¬ LowF φ (down φ x) := by
      rintro ⟨a,ha,hax⟩
      have hh := (hρ.2.1 a ha).trans (support_sound (constructor d) φ ρ hρ ((mem_down φ _ _).mp hax))
      rw [hρ.2.2.1 x hx] at hh
      cases hh
    have hb : HighBot φ (up φ x) := ⟨x,hx,(mem_up φ _ _).mpr (.refl _)⟩
    simp [grammar, initial, hl, hb]
  · intro x hx
    change unfold (grammar φ) (stateBound n) (initial φ x) = .top
    rw [he x]
    have hu : ¬ HighF φ (up φ x) := by
      rintro ⟨a,ha,hxa⟩
      have hh := (support_sound (constructor d) φ ρ hρ ((mem_up φ _ _).mp hxa)).trans (hρ.1 a ha)
      rw [hρ.2.2.2 x hx] at hh
      cases hh
    have hb : ¬ HighBot φ (up φ x) := by
      rintro ⟨y,hy,hxy⟩
      have hh := support_sound (constructor d) φ ρ hρ ((mem_up φ _ _).mp hxy)
      rw [hρ.2.2.2 x hx,hρ.2.2.1 y hy] at hh
      cases hh
    by_cases hl : LowF φ (down φ x) <;> simp [grammar, initial, hl, hu, hb]

theorem satisfiable_iff_model (φ : Constraints n d) :
    Satisfiable (constructor d) φ ↔ Satisfies (constructor d) φ (model φ) :=
  ⟨model_satisfies φ, fun h => ⟨model φ,h⟩⟩

theorem unfold_height_le {S : Type*} (G : Grammar S d) (k : Nat) (s : S) :
    height (unfold G k s) ≤ k := by
  induction k generalizing s with
  | zero => exact le_rfl
  | succ k ih =>
      cases he : G.label s with
      | bot => simp [unfold, he, height]
      | top => simp [unfold, he, height]
      | node =>
          simp only [unfold, he, height]
          exact Nat.add_le_add_right (Finset.sup_le (fun i _ => ih (G.next s i))) 1

theorem small_model (φ : Constraints n d) (h : Satisfiable (constructor d) φ) :
    ∃ ρ, Satisfies (constructor d) φ ρ ∧ ∀ x, height (ρ x) ≤ 2 ^ n * 2 ^ n := by
  refine ⟨model φ,model_satisfies φ h,?_⟩
  intro x
  rw [← stateBound_eq]
  exact unfold_height_le _ _ _

end NSSE.FiniteSubtypeSmallModel
