import NSSE.MultiConstructorTokens
import NSSE.GeneralCopyGrid

/-! Raw original-input token evolution and erasure after pin loss.
These statements hold for the total child recurrence, hence in particular
for its valid paths; no head selector or successful endpoint is assumed. -/
namespace NSSE.MultiConstructorRawTrace
open MultiConstructorConstraints MultiConstructorTokens
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

abbrev Row (n : Nat) := Tokens n × Tokens n

def initial (phi : Constraints arity n) (x y : Fin n) : Row n := (up phi {x},down phi {y})

def step (phi : Constraints arity n) (s : Row n) (letter : Nat) : Row n :=
  (upperNext phi s.1 letter,lowerNext phi s.2 letter)

def trace (phi : Constraints arity n) (s : Row n) (z : Nat → Nat) : Nat → Row n
  | 0 => s
  | k+1 => step phi (trace phi s z k) (z k)

theorem trace_closed (phi : Constraints arity n) (x y : Fin n) (z : Nat → Nat) (k : Nat) :
    UpperClosed phi (trace phi (initial phi x y) z k).1 ∧
    LowerClosed phi (trace phi (initial phi x y) z k).2 := by
  cases k with
  | zero => exact ⟨up_closed _ _,down_closed _ _⟩
  | succ k => exact ⟨upperNext_closed _ _ _,lowerNext_closed _ _ _⟩

theorem upper_empty_add (phi : Constraints arity n) (s : Row n) (z : Nat → Nat)
    (k d : Nat) (he : (trace phi s z k).1 = ∅) : (trace phi s z (k+d)).1 = ∅ := by
  induction d with
  | zero => simpa using he
  | succ d ih =>
    change upperNext phi (trace phi s z (k+d)).1 (z (k+d)) = ∅
    rw [ih,upperNext_empty]

theorem lower_empty_add (phi : Constraints arity n) (s : Row n) (z : Nat → Nat)
    (k d : Nat) (he : (trace phi s z k).2 = ∅) : (trace phi s z (k+d)).2 = ∅ := by
  induction d with
  | zero => simpa using he
  | succ d ih =>
    change lowerNext phi (trace phi s z (k+d)).2 (z (k+d)) = ∅
    rw [ih,lowerNext_empty]

theorem upper_empty_after_loss (phi : Constraints arity n) (s : Row n) (z : Nat → Nat)
    (k : Nat) (hp : upperPins phi (trace phi s z k).1 = ∅) :
    ∀ j, k < j → (trace phi s z j).1 = ∅ := by
  intro j hj
  have he : (trace phi s z (k+1)).1 = ∅ := upperNext_of_unpinned phi _ _ hp
  have h := upper_empty_add phi s z (k+1) (j-(k+1)) he
  simpa only [Nat.add_sub_of_le (show k+1 ≤ j by omega)] using h

theorem lower_empty_after_loss (phi : Constraints arity n) (s : Row n) (z : Nat → Nat)
    (k : Nat) (hp : lowerPins phi (trace phi s z k).2 = ∅) :
    ∀ j, k < j → (trace phi s z j).2 = ∅ := by
  intro j hj
  have he : (trace phi s z (k+1)).2 = ∅ := lowerNext_of_unpinned phi _ _ hp
  have h := lower_empty_add phi s z (k+1) (j-(k+1)) he
  simpa only [Nat.add_sub_of_le (show k+1 ≤ j by omega)] using h

theorem upper_unpinned_persists (phi : Constraints arity n) (s : Row n) (z : Nat → Nat)
    (k : Nat) (hp : upperPins phi (trace phi s z k).1 = ∅) :
    ∀ j, k ≤ j → upperPins phi (trace phi s z j).1 = ∅ := by
  intro j hj
  rcases hj.eq_or_lt with he | hl
  · simpa only [← he] using hp
  · rw [upper_empty_after_loss phi s z k hp j hl,upperPins_empty]

theorem lower_unpinned_persists (phi : Constraints arity n) (s : Row n) (z : Nat → Nat)
    (k : Nat) (hp : lowerPins phi (trace phi s z k).2 = ∅) :
    ∀ j, k ≤ j → lowerPins phi (trace phi s z j).2 = ∅ := by
  intro j hj
  rcases hj.eq_or_lt with he | hl
  · simpa only [← he] using hp
  · rw [lower_empty_after_loss phi s z k hp j hl,lowerPins_empty]

def annotation (phi : Constraints arity n) (x y : Fin n) (z : Nat → Nat)
    (heads : Nat → H) (k : Nat) : PeriodicCopyHeadNormalization.Annotation (Fin n) H Nat :=
  let s := trace phi (initial phi x y) z k
  ⟨s.1,s.2,heads k,z k⟩

theorem born_exact (phi : Constraints arity n) (x y : Fin n) (z : Nat → Nat)
    (heads : Nat → H) (a b : Nat) :
    GeneralCopyGrid.Born (annotation phi x y z heads) a b ↔
      ∃ u ∈ (trace phi (initial phi x y) z a).1,
      ∃ v ∈ (trace phi (initial phi x y) z b).2, Support phi u v := by
  rw [birth_iff_inter phi _ _ (trace_closed phi x y z a).1]
  simp only [GeneralCopyGrid.Born,annotation,Finset.Nonempty,Finset.mem_inter,Finset.mem_coe]

end NSSE.MultiConstructorRawTrace
