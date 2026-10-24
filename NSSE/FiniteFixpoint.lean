import NSSE.TaggedCompiler
import NSSE.HypercubePaths
import Lean.Elab.Tactic.Omega

/-!
# Termination of finite Boolean-mask refinement

The guarded-atom and forbidden-query components of compiler states grow
monotonically.  This module proves directly, without a finite-set
library, that an inflationary update on a fixed-length Boolean mask
reaches a fixed point after at most one more step than the mask length.
-/

namespace NSSE

inductive MaskLe : List Bool → List Bool → Prop
  | nil : MaskLe [] []
  | cons {x y xs ys}
      (head : x = true → y = true)
      (tail : MaskLe xs ys) :
      MaskLe (x :: xs) (y :: ys)

namespace MaskLe

theorem refl (mask : List Bool) : MaskLe mask mask := by
  induction mask with
  | nil => exact .nil
  | cons bit rest ih => exact .cons (fun h => h) ih

theorem trans {x y z : List Bool}
    (hxy : MaskLe x y) (hyz : MaskLe y z) : MaskLe x z := by
  induction hxy generalizing z with
  | nil =>
      cases hyz
      exact .nil
  | @cons xh yh xs ys hhead htail ih =>
      cases hyz with
      | cons hhead₂ htail₂ =>
          exact .cons (fun hx => hhead₂ (hhead hx))
            (ih htail₂)

theorem length_eq {x y : List Bool} (h : MaskLe x y) :
    x.length = y.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem antisymm {x y : List Bool}
    (hxy : MaskLe x y) (hyx : MaskLe y x) : x = y := by
  induction hxy with
  | nil => rfl
  | @cons xh yh xs ys hhead htail ih =>
      cases hyx with
      | cons hhead₂ htail₂ =>
          have hbits : xh = yh := by
            cases xh <;> cases yh <;> simp_all
          have hrests : xs = ys := ih htail₂
          simp [hbits, hrests]

theorem rank_le {x y : List Bool} (h : MaskLe x y) :
    boolRank x ≤ boolRank y := by
  induction h with
  | nil => simp [boolRank]
  | @cons xh yh xs ys hhead htail ih =>
      cases xh <;> cases yh <;>
        simp [boolRank, List.countP_cons] at * <;> omega

theorem eq_of_rank_eq {x y : List Bool}
    (h : MaskLe x y) (hrank : boolRank x = boolRank y) :
    x = y := by
  induction h with
  | nil => rfl
  | @cons xh yh xs ys hhead htail ih =>
      cases xh <;> cases yh
      · congr 1
        apply ih
        simpa [boolRank, List.countP_cons] using hrank
      · have hle := htail.rank_le
        change List.countP id xs ≤ List.countP id ys at hle
        have hrank' :
            List.countP id xs = List.countP id ys + 1 := by
          simpa [boolRank, List.countP_cons,
            List.countP_cons_of_neg, List.countP_cons_of_pos] using hrank
        omega
      · simp at hhead
      · congr 1
        apply ih
        simpa [boolRank, List.countP_cons] using hrank

theorem rank_lt_of_ne {x y : List Bool}
    (h : MaskLe x y) (hne : x ≠ y) :
    boolRank x < boolRank y := by
  have hle := h.rank_le
  apply Nat.lt_of_le_of_ne hle
  intro heq
  exact hne (h.eq_of_rank_eq heq)

end MaskLe

def iterateMask (update : List Bool → List Bool) :
    Nat → List Bool → List Bool
  | 0, initial => initial
  | n + 1, initial => update (iterateMask update n initial)

@[simp] theorem iterateMask_zero
    (update : List Bool → List Bool) (initial : List Bool) :
    iterateMask update 0 initial = initial := rfl

@[simp] theorem iterateMask_succ
    (update : List Bool → List Bool) (n : Nat) (initial : List Bool) :
    iterateMask update (n + 1) initial =
      update (iterateMask update n initial) := rfl

theorem iterateMask_chain
    (update : List Bool → List Bool)
    (hinflationary : ∀ mask, MaskLe mask (update mask))
    (initial : List Bool) (n : Nat) :
    MaskLe (iterateMask update n initial)
      (iterateMask update (n + 1) initial) := by
  exact hinflationary _

theorem rank_growth
    (update : List Bool → List Bool)
    (hinflationary : ∀ mask, MaskLe mask (update mask))
    (initial : List Bool) :
    ∀ n,
      (∀ k, k < n →
        iterateMask update k initial ≠
          iterateMask update (k + 1) initial) →
      boolRank initial + n ≤
        boolRank (iterateMask update n initial)
  | 0, _ => by simp
  | n + 1, hall => by
      have hprevious :=
        rank_growth update hinflationary initial n
          (fun k hk => hall k (by omega))
      have hstrict :=
        (iterateMask_chain update hinflationary initial n).rank_lt_of_ne
          (hall n (by omega))
      omega

theorem boolRank_le_length (mask : List Bool) :
    boolRank mask ≤ mask.length := by
  exact List.countP_le_length

theorem iterateMask_length
    (update : List Bool → List Bool)
    (hinflationary : ∀ mask, MaskLe mask (update mask))
    (initial : List Bool) (n : Nat) :
    (iterateMask update n initial).length = initial.length := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (update (iterateMask update n initial)).length =
        initial.length
      exact (hinflationary _).length_eq.symm.trans ih

/--
An inflationary refinement of an `n`-bit mask has an adjacent fixed
point among iterations `0,...,n`.  Determinism then makes it a genuine
fixed point of `update`.
-/
theorem exists_fixedPoint_within_length
    (update : List Bool → List Bool)
    (hinflationary : ∀ mask, MaskLe mask (update mask))
    (initial : List Bool) :
    ∃ k, k ≤ initial.length ∧
      update (iterateMask update k initial) =
        iterateMask update k initial := by
  apply Classical.byContradiction
  intro hnot
  have hall :
      ∀ k, k < initial.length + 1 →
        iterateMask update k initial ≠
          iterateMask update (k + 1) initial := by
    intro k hk heq
    apply hnot
    refine ⟨k, by omega, ?_⟩
    simpa using heq.symm
  have hgrowth :=
    rank_growth update hinflationary initial
      (initial.length + 1) hall
  have hbound :=
    boolRank_le_length
      (iterateMask update (initial.length + 1) initial)
  have hlength :=
    iterateMask_length update hinflationary initial
      (initial.length + 1)
  omega

theorem iterateMask_add
    (update : List Bool → List Bool)
    (initial : List Bool) (m n : Nat) :
    iterateMask update (m + n) initial =
      iterateMask update n (iterateMask update m initial) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, iterateMask_succ, iterateMask_succ, ih]

theorem iterateMask_fixed
    (update : List Bool → List Bool)
    (mask : List Bool) (hfixed : update mask = mask) :
    ∀ n, iterateMask update n mask = mask
  | 0 => rfl
  | n + 1 => by
      rw [iterateMask_succ, iterateMask_fixed update mask hfixed n,
        hfixed]

/--
The fixed point is available at one known executable bound: iterate
exactly the mask length.  Thus no unbounded search is needed by the
compiler refinement.
-/
theorem iterateMask_length_is_fixed
    (update : List Bool → List Bool)
    (hinflationary : ∀ mask, MaskLe mask (update mask))
    (initial : List Bool) :
    update (iterateMask update initial.length initial) =
      iterateMask update initial.length initial := by
  obtain ⟨k, hk, hfixed⟩ :=
    exists_fixedPoint_within_length update hinflationary initial
  have hsum : k + (initial.length - k) = initial.length := by omega
  have hiterate :
      iterateMask update initial.length initial =
        iterateMask update k initial := by
    rw [← hsum, iterateMask_add,
      iterateMask_fixed update (iterateMask update k initial) hfixed]
  rw [hiterate, hfixed]

def MaskMonotone (update : List Bool → List Bool) : Prop :=
  ∀ {x y}, MaskLe x y → MaskLe (update x) (update y)

theorem iterateMask_le_fixed
    (update : List Bool → List Bool)
    (hmonotone : MaskMonotone update)
    {initial fixed : List Bool}
    (hbelow : MaskLe initial fixed)
    (hfixed : update fixed = fixed) :
    ∀ n, MaskLe (iterateMask update n initial) fixed
  | 0 => hbelow
  | n + 1 => by
      rw [iterateMask_succ, ← hfixed]
      exact hmonotone (iterateMask_le_fixed update hmonotone
        hbelow hfixed n)

/--
For a monotone inflationary update, the executable length-bounded
iteration is the least fixed point above the initial mask.
-/
theorem iterateMask_length_least
    (update : List Bool → List Bool)
    (hmonotone : MaskMonotone update)
    (initial fixed : List Bool)
    (hbelow : MaskLe initial fixed)
    (hfixed : update fixed = fixed) :
    MaskLe (iterateMask update initial.length initial) fixed :=
  iterateMask_le_fixed update hmonotone hbelow hfixed initial.length

theorem initial_le_iterateMask
    (update : List Bool → List Bool)
    (hinflationary : ∀ mask, MaskLe mask (update mask))
    (initial : List Bool) :
    ∀ n, MaskLe initial (iterateMask update n initial)
  | 0 => MaskLe.refl initial
  | n + 1 =>
      (initial_le_iterateMask update hinflationary initial n).trans
        (iterateMask_chain update hinflationary initial n)

/--
A semantic mask specification for a least fixed point above `initial`.
Extraction proves closure/fixedness; realization proves leastness.
-/
structure LeastFixedPointSpec
    (update : List Bool → List Bool)
    (initial semantic : List Bool) : Prop where
  initial_le : MaskLe initial semantic
  fixed : update semantic = semantic
  least :
    ∀ other, MaskLe initial other →
      update other = other → MaskLe semantic other

theorem iterateMask_eq_semantic
    (update : List Bool → List Bool)
    (hinflationary : ∀ mask, MaskLe mask (update mask))
    (hmonotone : MaskMonotone update)
    (initial semantic : List Bool)
    (hspec : LeastFixedPointSpec update initial semantic) :
    iterateMask update initial.length initial = semantic := by
  apply MaskLe.antisymm
  · exact iterateMask_length_least update hmonotone
      initial semantic hspec.initial_le hspec.fixed
  · apply hspec.least
    · exact initial_le_iterateMask update hinflationary initial
        initial.length
    · exact iterateMask_length_is_fixed update hinflationary initial

def maskBit (mask : List Bool) (index : Nat) : Bool :=
  (mask[index]?).getD false

def decideLeastFixedPoint
    (update : List Bool → List Bool)
    (initial : List Bool) (index : Nat) : Bool :=
  maskBit (iterateMask update initial.length initial) index

theorem decideLeastFixedPoint_correct
    (update : List Bool → List Bool)
    (hinflationary : ∀ mask, MaskLe mask (update mask))
    (hmonotone : MaskMonotone update)
    (initial semantic : List Bool)
    (hspec : LeastFixedPointSpec update initial semantic)
    (index : Nat) :
    decideLeastFixedPoint update initial index =
      maskBit semantic index := by
  rw [decideLeastFixedPoint,
    iterateMask_eq_semantic update hinflationary hmonotone
      initial semantic hspec]

end NSSE
