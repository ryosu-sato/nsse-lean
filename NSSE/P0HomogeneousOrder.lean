import Mathlib.Data.Finset.Max
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic

/-! The order geometry of four increasing position lists with identical
two-list shuffles. Tied coordinate intervals have one common orientation;
untied coordinates are separated across all four lists. -/
namespace NSSE.P0HomogeneousOrder

structure Grid (m : Nat) where
  pos : Fin 4 → Nat → Nat
  row : ∀ r i j, i < j → j < m → pos r i < pos r j
  apart : ∀ r s, r ≠ s → ∀ i j, i < m → j < m → pos r i ≠ pos s j
  homogeneous : ∀ r s, r < s → ∀ i j, i < m → j < m →
    (pos r i < pos s j ↔ pos 0 i < pos 1 j)

variable {m : Nat}

def Plus (G : Grid m) (i j : Nat) : Prop := G.pos 0 j < G.pos 1 i
def Minus (G : Grid m) (i j : Nat) : Prop := G.pos 1 j < G.pos 0 i
def Tied (G : Grid m) (i j : Nat) : Prop := Plus G i j ∨ Minus G i j
def Separated (G : Grid m) (i j : Nat) : Prop := ∀ r s, G.pos r i < G.pos s j

theorem row_le (G : Grid m) (r : Fin 4) (i j : Nat) (hij : i ≤ j) (hj : j < m) :
    G.pos r i ≤ G.pos r j := by
  rcases lt_or_eq_of_le hij with h | rfl
  · exact Nat.le_of_lt (G.row r i j h hj)
  · exact le_rfl

theorem reverse_cross (G : Grid m) (r s : Fin 4) (hrs : r < s) (i j : Nat)
    (hi : i < m) (hj : j < m) :
    G.pos s i < G.pos r j ↔ G.pos 1 i < G.pos 0 j := by
  have hh := G.homogeneous r s hrs j i hj hi
  have hn := G.apart r s (ne_of_lt hrs) j i hj hi
  have hn' := G.apart 0 1 (by decide) j i hj hi
  omega

theorem plus_trans (G : Grid m) (i j k : Nat) (hi : i < m) (hj : j < m) (hk : k < m)
    (hij : Plus G i j) (hjk : Plus G j k) : Plus G i k := by
  have h12 : G.pos 1 j < G.pos 2 i := (G.homogeneous 1 2 (by decide) j i hj hi).mpr hij
  exact (G.homogeneous 0 2 (by decide) k i hk hi).mp (lt_trans hjk h12)

theorem minus_trans (G : Grid m) (i j k : Nat) (hi : i < m) (hj : j < m) (hk : k < m)
    (hij : Minus G i j) (hjk : Minus G j k) : Minus G i k := by
  have h12 : G.pos 2 k < G.pos 1 j := (reverse_cross G 1 2 (by decide) k j hk hj).mpr hjk
  exact (reverse_cross G 0 2 (by decide) k i hk hi).mp (lt_trans h12 hij)

theorem plus_shrink (G : Grid m) (i j a b : Nat) (hia : i ≤ a) (hab : a ≤ b)
    (hbj : b ≤ j) (hj : j < m) (h : Plus G i j) : Plus G a b := by
  have hl := row_le G 0 b j hbj hj
  have hr := row_le G 1 i a hia (by omega)
  unfold Plus at *
  omega

theorem minus_shrink (G : Grid m) (i j a b : Nat) (hia : i ≤ a) (hab : a ≤ b)
    (hbj : b ≤ j) (hj : j < m) (h : Minus G i j) : Minus G a b := by
  have hl := row_le G 1 b j hbj hj
  have hr := row_le G 0 i a hia (by omega)
  unfold Minus at *
  omega

theorem tied_refl (G : Grid m) (i : Nat) (hi : i < m) : Tied G i i :=
  lt_or_gt_of_ne (G.apart 0 1 (by decide) i i hi hi)

theorem tied_shrink (G : Grid m) (i j a b : Nat) (hia : i ≤ a) (hab : a ≤ b)
    (hbj : b ≤ j) (hj : j < m) (h : Tied G i j) : Tied G a b := by
  rcases h with h | h
  · exact Or.inl (plus_shrink G i j a b hia hab hbj hj h)
  · exact Or.inr (minus_shrink G i j a b hia hab hbj hj h)

theorem tied_trans (G : Grid m) (i j k : Nat) (hij : i ≤ j) (hjk : j ≤ k) (hk : k < m)
    (h : Tied G i j) (h' : Tied G j k) : Tied G i k := by
  rcases h with h | h <;> rcases h' with h' | h'
  · exact Or.inl (plus_trans G i j k (by omega) (by omega) hk h h')
  · have hp := plus_shrink G i j j j hij (by omega) (by omega) (by omega) h
    have hn := minus_shrink G j k j j (by omega) (by omega) hjk hk h'
    exact False.elim (lt_asymm hp hn)
  · have hn := minus_shrink G i j j j hij (by omega) (by omega) (by omega) h
    have hp := plus_shrink G j k j j (by omega) (by omega) hjk hk h'
    exact False.elim (lt_asymm hp hn)
  · exact Or.inr (minus_trans G i j k (by omega) (by omega) hk h h')

theorem separated_of_not_tied (G : Grid m) (i j : Nat) (hij : i < j) (hj : j < m)
    (hn : ¬ Tied G i j) : Separated G i j := by
  have hp : ¬ Plus G i j := fun h => hn (Or.inl h)
  have hm : ¬ Minus G i j := fun h => hn (Or.inr h)
  have hn1 := G.apart 0 1 (by decide) i j (by omega) hj
  have hn2 := G.apart 0 1 (by decide) j i hj (by omega)
  have h01 : G.pos 0 i < G.pos 1 j := by unfold Minus at hm; omega
  have h10 : G.pos 1 i < G.pos 0 j := by unfold Plus at hp; omega
  intro r s
  rcases lt_trichotomy r s with hrs | rfl | hsr
  · exact (G.homogeneous r s hrs i j (by omega) hj).mpr h01
  · exact G.row r i j hij hj
  · exact (reverse_cross G s r hsr i j (by omega) hj).mpr h10

/-- Every position in one row-block precedes every position in the next
row-block, in the sign's group order. -/
def Block (G : Grid m) (lo hi : Nat) (positive : Bool) : Prop :=
  ∀ r s : Fin 4, r < s → ∀ i j, lo ≤ i → i < hi → lo ≤ j → j < hi →
    if positive then G.pos r i < G.pos s j else G.pos s i < G.pos r j

theorem plus_block (G : Grid m) (lo last : Nat) (hlast : last < m)
    (h : Plus G lo last) : Block G lo (last+1) true := by
  intro r s hrs i j hloi hi hloj hj
  have hl := row_le G r i last (by omega) hlast
  have hr := row_le G s lo j hloj (by omega)
  have hmid := (G.homogeneous r s hrs last lo hlast (by omega)).mpr h
  change G.pos r i < G.pos s j
  omega

theorem minus_block (G : Grid m) (lo last : Nat) (hlast : last < m)
    (h : Minus G lo last) : Block G lo (last+1) false := by
  intro r s hrs i j hloi hi hloj hj
  have hl := row_le G s i last (by omega) hlast
  have hr := row_le G r lo j hloj (by omega)
  have hmid := (reverse_cross G r s hrs last lo hlast (by omega)).mpr h
  change G.pos s i < G.pos r j
  omega

end NSSE.P0HomogeneousOrder
