import NSSE.FiniteTreeGrammar
import NSSE.FiniteSubtypeSupport

/-! # The actual finite lower/upper-set grammar of the original constraints

Both sides force a node; otherwise an extremum gives the smallest required
shape. All sets and transitions are computed from the exact support table.
-/

namespace NSSE.SubtypeShapeGrammar

open SubtypeConstraints FiniteSubtypeSupport FiniteTreeGrammar FiniteSubtypeTrees

abbrev State (n : Nat) := Finset (Fin n) × Finset (Fin n)

variable {n d : Nat}

instance (φ : Constraints n d) : DecidableRel (Support φ) := supportDecision φ

def down (φ : Constraints n d) (x : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun z => Support φ z x)

def up (φ : Constraints n d) (x : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun z => Support φ x z)

@[simp] theorem mem_down (φ : Constraints n d) (x z : Fin n) : z ∈ down φ x ↔ Support φ z x := by
  simp [down]
@[simp] theorem mem_up (φ : Constraints n d) (x z : Fin n) : z ∈ up φ x ↔ Support φ x z := by
  simp [up]

def lowStep (φ : Constraints n d) (L : Finset (Fin n)) (i : Fin d) : Finset (Fin n) :=
  Finset.univ.filter (fun z => ∃ a ∈ φ.lower, a.1 ∈ L ∧ Support φ z (a.2 i))

def highStep (φ : Constraints n d) (U : Finset (Fin n)) (i : Fin d) : Finset (Fin n) :=
  Finset.univ.filter (fun z => ∃ a ∈ φ.upper, a.1 ∈ U ∧ Support φ (a.2 i) z)

@[simp] theorem mem_lowStep (φ : Constraints n d) (L : Finset (Fin n)) (i : Fin d) (z : Fin n) :
    z ∈ lowStep φ L i ↔ ∃ a ∈ φ.lower, a.1 ∈ L ∧ Support φ z (a.2 i) := by simp [lowStep]
@[simp] theorem mem_highStep (φ : Constraints n d) (U : Finset (Fin n)) (i : Fin d) (z : Fin n) :
    z ∈ highStep φ U i ↔ ∃ a ∈ φ.upper, a.1 ∈ U ∧ Support φ (a.2 i) z := by simp [highStep]

def LowF (φ : Constraints n d) (L : Finset (Fin n)) : Prop := ∃ a ∈ φ.lower, a.1 ∈ L
def HighF (φ : Constraints n d) (U : Finset (Fin n)) : Prop := ∃ a ∈ φ.upper, a.1 ∈ U
def HighBot (φ : Constraints n d) (U : Finset (Fin n)) : Prop := ∃ x ∈ φ.bot, x ∈ U

instance (φ : Constraints n d) (L : Finset (Fin n)) : Decidable (LowF φ L) := by
  unfold LowF; infer_instance
instance (φ : Constraints n d) (U : Finset (Fin n)) : Decidable (HighF φ U) := by
  unfold HighF; infer_instance
instance (φ : Constraints n d) (U : Finset (Fin n)) : Decidable (HighBot φ U) := by
  unfold HighBot; infer_instance

def grammar (φ : Constraints n d) : Grammar (State n) d where
  label s := if LowF φ s.1 then (if HighF φ s.2 then .node else .top)
    else (if HighF φ s.2 ∨ HighBot φ s.2 then .bot else .top)
  next s i := (lowStep φ s.1 i, highStep φ s.2 i)

def initial (φ : Constraints n d) (x : Fin n) : State n := (down φ x, up φ x)

def Refines (s t : State n) : Prop := s.1 ⊆ t.1 ∧ t.2 ⊆ s.2

theorem lowStep_mono (φ : Constraints n d) {L M : Finset (Fin n)} (h : L ⊆ M) (i : Fin d) :
    lowStep φ L i ⊆ lowStep φ M i := by
  intro z hz
  obtain ⟨a,ha,hm,hs⟩ := (mem_lowStep φ L i z).mp hz
  exact (mem_lowStep φ M i z).mpr ⟨a,ha,h hm,hs⟩

theorem highStep_mono (φ : Constraints n d) {L M : Finset (Fin n)} (h : L ⊆ M) (i : Fin d) :
    highStep φ L i ⊆ highStep φ M i := by
  intro z hz
  obtain ⟨a,ha,hm,hs⟩ := (mem_highStep φ L i z).mp hz
  exact (mem_highStep φ M i z).mpr ⟨a,ha,h hm,hs⟩

theorem next_refines (φ : Constraints n d) {s t : State n} (h : Refines s t) (i : Fin d) :
    Refines ((grammar φ).next s i) ((grammar φ).next t i) :=
  ⟨lowStep_mono φ h.1 i, highStep_mono φ h.2 i⟩

theorem lowF_mono (φ : Constraints n d) {L M : Finset (Fin n)} (h : L ⊆ M) : LowF φ L → LowF φ M := by
  rintro ⟨a,ha,hm⟩; exact ⟨a,ha,h hm⟩
theorem highF_mono (φ : Constraints n d) {L M : Finset (Fin n)} (h : L ⊆ M) : HighF φ L → HighF φ M := by
  rintro ⟨a,ha,hm⟩; exact ⟨a,ha,h hm⟩
theorem highBot_mono (φ : Constraints n d) {L M : Finset (Fin n)} (h : L ⊆ M) : HighBot φ L → HighBot φ M := by
  rintro ⟨a,ha,hm⟩; exact ⟨a,ha,h hm⟩

theorem unfold_mono (φ : Constraints n d) (k : Nat) {s t : State n} (h : Refines s t) :
    unfold (grammar φ) k s ≤ unfold (grammar φ) k t := by
  induction k generalizing s t with
  | zero => exact le_rfl
  | succ k ih =>
      have hl := lowF_mono φ h.1
      have hu := highF_mono φ h.2
      have hb := highBot_mono φ h.2
      have hn : Tree.node (fun i => unfold (grammar φ) k ((grammar φ).next s i)) ≤
          Tree.node (fun i => unfold (grammar φ) k ((grammar φ).next t i)) :=
        Below.node (fun i => ih (next_refines φ h i))
      unfold unfold
      dsimp only [grammar]
      by_cases hsL : LowF φ s.1 <;> by_cases htL : LowF φ t.1 <;>
        by_cases hsU : HighF φ s.2 <;> by_cases htU : HighF φ t.2 <;>
        by_cases hsB : HighBot φ s.2 <;> by_cases htB : HighBot φ t.2 <;>
        simp_all only [true_or, false_or, ↓reduceIte]
      all_goals first | exact bot_le | exact le_top | exact hn

theorem lower_next_refines (φ : Constraints n d) (a : BoundLiteral n d) (ha : a ∈ φ.lower) (i : Fin d) :
    Refines (initial φ (a.2 i)) ((grammar φ).next (initial φ a.1) i) := by
  constructor
  · intro z hz
    exact (mem_lowStep φ _ i z).mpr ⟨a,ha,(mem_down φ _ _).mpr (.refl _), (mem_down φ _ _).mp hz⟩
  · intro z hz
    obtain ⟨b,hb,hab,hbz⟩ := (mem_highStep φ _ i z).mp hz
    exact (mem_up φ _ _).mpr ((Support.decomp ha hb ((mem_up φ _ _).mp hab) i).trans hbz)

theorem upper_next_refines (φ : Constraints n d) (a : BoundLiteral n d) (ha : a ∈ φ.upper) (i : Fin d) :
    Refines ((grammar φ).next (initial φ a.1) i) (initial φ (a.2 i)) := by
  constructor
  · intro z hz
    obtain ⟨b,hb,hba,hzb⟩ := (mem_lowStep φ _ i z).mp hz
    exact (mem_down φ _ _).mpr (hzb.trans (Support.decomp hb ha ((mem_down φ _ _).mp hba) i))
  · intro z hz
    exact (mem_highStep φ _ i z).mpr ⟨a,ha,(mem_up φ _ _).mpr (.refl _), (mem_up φ _ _).mp hz⟩

end NSSE.SubtypeShapeGrammar
