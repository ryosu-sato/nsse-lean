import NSSE.EdgeCut
import Lean.Elab.Tactic.Omega

/-!
# Ranked monotone cube paths

The combinatorial core of the cyclic-path argument from v398.  A lower
cube vertex has a rank (the number of restored coordinates).  At step
`k`, every path is at rank `k`, and the coordinate crossed at that step
determines the path start.  These two facts force distinct paths to be
edge-disjoint.
-/

namespace NSSE

universe u v w

def cyclicCoordinate {dimension : Nat}
    (start : Fin dimension) (step : Nat) : Fin dimension :=
  ⟨(start.val + step) % dimension,
    Nat.mod_lt _ (Nat.zero_lt_of_lt start.isLt)⟩

/--
Cancellation for the concrete cyclic coordinate `(start + step) mod d`.
This is the arithmetic field needed by the v398 path family.
-/
theorem cyclicCoordinate_injective (dimension step : Nat) :
    ∀ ⦃start₁ start₂ : Fin dimension⦄,
      cyclicCoordinate start₁ step = cyclicCoordinate start₂ step →
      start₁ = start₂ := by
  intro start₁ start₂ h
  have hdimension : 0 < dimension :=
    Nat.zero_lt_of_lt start₁.isLt
  let residue := step % dimension
  have hresidue : residue < dimension :=
    Nat.mod_lt step hdimension
  have hmod :
      (start₁.val + residue) % dimension =
        (start₂.val + residue) % dimension := by
    have hval := congrArg Fin.val h
    simpa [cyclicCoordinate, residue, Nat.add_mod_mod] using hval
  apply Fin.ext
  by_cases h₁ : start₁.val + residue < dimension
  · rw [Nat.mod_eq_of_lt h₁] at hmod
    by_cases h₂ : start₂.val + residue < dimension
    · rw [Nat.mod_eq_of_lt h₂] at hmod
      omega
    · have h₂le : dimension ≤ start₂.val + residue := by omega
      rw [Nat.mod_eq_sub_mod h₂le,
        Nat.mod_eq_of_lt (by omega)] at hmod
      omega
  · have h₁le : dimension ≤ start₁.val + residue := by omega
    rw [Nat.mod_eq_sub_mod h₁le,
      Nat.mod_eq_of_lt (by omega)] at hmod
    by_cases h₂ : start₂.val + residue < dimension
    · rw [Nat.mod_eq_of_lt h₂] at hmod
      omega
    · have h₂le : dimension ≤ start₂.val + residue := by omega
      rw [Nat.mod_eq_sub_mod h₂le,
        Nat.mod_eq_of_lt (by omega)] at hmod
      omega

def rotateOnce : List α → List α
  | [] => []
  | x :: xs => xs ++ [x]

def rotateLeft (xs : List α) : Nat → List α
  | 0 => xs
  | offset + 1 => rotateOnce (rotateLeft xs offset)

@[simp] theorem rotateOnce_length (xs : List α) :
    (rotateOnce xs).length = xs.length := by
  cases xs <;> simp [rotateOnce]

@[simp] theorem rotateLeft_length (xs : List α) (offset : Nat) :
    (rotateLeft xs offset).length = xs.length := by
  induction offset with
  | zero => rfl
  | succ offset ih => simp [rotateLeft, ih]

def boolRank (vertex : List Bool) : Nat :=
  vertex.countP id

theorem boolRank_rotateLeft (vertex : List Bool) (offset : Nat) :
    boolRank (rotateLeft vertex offset) = boolRank vertex := by
  induction offset with
  | zero => rfl
  | succ offset ih =>
      simp only [rotateLeft]
      have hone :
          boolRank (rotateOnce (rotateLeft vertex offset)) =
            boolRank (rotateLeft vertex offset) := by
        unfold boolRank
        cases rotateLeft vertex offset with
        | nil => rfl
        | cons bit rest =>
            cases bit <;>
              simp [rotateOnce, List.countP_append,
                List.countP_cons]
      exact hone.trans ih

/--
The concrete lower endpoint for the path beginning at `start`: a Boolean
vector consisting of `step` restored coordinates, cyclically rotated to
the selected starting phase.  For the path-relevant range
`step ≤ dimension`, its length is exactly `dimension`.
-/
def cyclicLower {dimension : Nat}
    (start : Fin dimension) (step : Nat) : List Bool :=
  rotateLeft
    (List.replicate step true ++
      List.replicate (dimension - step) false)
    (dimension - start.val)

theorem cyclicLower_rank {dimension : Nat}
    (start : Fin dimension) (step : Nat) :
    boolRank (cyclicLower start step) = step := by
  rw [cyclicLower, boolRank_rotateLeft]
  unfold boolRank
  rw [List.countP_append, List.countP_replicate,
    List.countP_replicate]
  simp

theorem cyclicLower_length {dimension : Nat}
    (start : Fin dimension) {step : Nat} (hstep : step ≤ dimension) :
    (cyclicLower start step).length = dimension := by
  simp [cyclicLower]
  omega

/-- Exact Boolean-cube adjacency: one `false` coordinate becomes `true`. -/
inductive OneBitRestore : List Bool → List Bool → Prop
  | here (rest : List Bool) :
      OneBitRestore (false :: rest) (true :: rest)
  | same (bit : Bool) {left right}
      (tail : OneBitRestore left right) :
      OneBitRestore (bit :: left) (bit :: right)

namespace OneBitRestore

theorem append_left (pre : List Bool)
    {left right : List Bool} (h : OneBitRestore left right) :
    OneBitRestore (pre ++ left) (pre ++ right) := by
  induction pre with
  | nil => exact h
  | cons bit pre ih => exact .same bit ih

theorem append_right {left right : List Bool}
    (h : OneBitRestore left right) (post : List Bool) :
    OneBitRestore (left ++ post) (right ++ post) := by
  induction h with
  | here rest =>
      exact OneBitRestore.here (rest ++ post)
  | same bit tail ih =>
      exact .same bit ih

theorem rotateOnce
    {left right : List Bool} (h : OneBitRestore left right) :
    OneBitRestore (NSSE.rotateOnce left) (NSSE.rotateOnce right) := by
  cases h with
  | here rest =>
      simp only [NSSE.rotateOnce]
      exact (OneBitRestore.here []).append_left rest
  | same bit tail =>
      simp only [NSSE.rotateOnce]
      exact tail.append_right [bit]

theorem rotateLeft
    {left right : List Bool} (h : OneBitRestore left right)
    (offset : Nat) :
    OneBitRestore (NSSE.rotateLeft left offset)
      (NSSE.rotateLeft right offset) := by
  induction offset with
  | zero => exact h
  | succ offset ih =>
      simp only [NSSE.rotateLeft]
      exact ih.rotateOnce

theorem rank_succ {left right : List Bool}
    (h : OneBitRestore left right) :
    boolRank right = boolRank left + 1 := by
  induction h with
  | here rest =>
      simp [boolRank, List.countP_cons]
  | same bit tail ih =>
      cases bit <;> simp_all [boolRank, List.countP_cons]

end OneBitRestore

theorem prefixMask_oneBitRestore
    {dimension step : Nat} (hstep : step < dimension) :
    OneBitRestore
      (List.replicate step true ++
        List.replicate (dimension - step) false)
      (List.replicate (step + 1) true ++
        List.replicate (dimension - (step + 1)) false) := by
  have hsub : dimension - step =
      (dimension - (step + 1)) + 1 := by omega
  rw [hsub, List.replicate_succ]
  rw [List.replicate_succ']
  simpa [List.append_assoc] using
    (OneBitRestore.here
      (List.replicate (dimension - (step + 1)) false)).append_left
        (List.replicate step true)

/-- Every consecutive pair on a concrete cyclic path is a cube edge. -/
theorem cyclicLower_oneBitRestore
    {dimension : Nat} (start : Fin dimension)
    {step : Nat} (hstep : step < dimension) :
    OneBitRestore (cyclicLower start step)
      (cyclicLower start (step + 1)) := by
  unfold cyclicLower
  exact (prefixMask_oneBitRestore hstep).rotateLeft
    (dimension - start.val)

structure CubeEdge (ν : Type u) (γ : Type v) where
  lower : ν
  coordinate : γ

/--
Data needed from a concrete family of cyclic monotone cube paths.
`rank_lower` says that step `k` starts at a vertex with exactly `k`
restored coordinates.  `coordinate_injective` is cyclic cancellation:
at a fixed step, the crossed coordinate determines the starting phase.
-/
structure RankedCubeFamily (ι : Type u) (ν : Type v) (γ : Type w) where
  lower : ι → Nat → ν
  coordinate : ι → Nat → γ
  rank : ν → Nat
  rank_lower : ∀ start step, rank (lower start step) = step
  coordinate_injective :
    ∀ step, ∀ ⦃start₁ start₂⦄,
      coordinate start₁ step = coordinate start₂ step →
      start₁ = start₂

/-- The concrete Boolean-vector cyclic family used in v398. -/
def booleanCyclicFamily (dimension : Nat) :
    RankedCubeFamily (Fin dimension) (List Bool) (Fin dimension) where
  lower := cyclicLower
  coordinate := cyclicCoordinate
  rank := boolRank
  rank_lower := cyclicLower_rank
  coordinate_injective := cyclicCoordinate_injective dimension

theorem nodup_map_of_injective
    (f : α → β)
    (hinjective : ∀ ⦃x y⦄, f x = f y → x = y)
    {xs : List α} (hxs : xs.Nodup) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
      have hparts := List.nodup_cons.mp hxs
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        simp only [List.mem_map] at hmem
        obtain ⟨y, hy, heq⟩ := hmem
        have hxy : x = y := hinjective heq.symm
        subst y
        exact hparts.1 hy
      · exact ih hparts.2

theorem finRange_nodup (dimension : Nat) :
    (List.finRange dimension).Nodup := by
  induction dimension with
  | zero => simp
  | succ dimension ih =>
      rw [List.finRange_succ]
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        simp only [List.mem_map] at hmem
        obtain ⟨i, hi, hzero⟩ := hmem
        exact Fin.succ_ne_zero i hzero
      · apply nodup_map_of_injective Fin.succ
          (fun {i j} h => by
            apply Fin.ext
            exact Nat.succ.inj (congrArg Fin.val h))
          ih

namespace RankedCubeFamily

def edge (F : RankedCubeFamily ι ν γ) (start : ι) (step : Nat) :
    CubeEdge ν γ :=
  ⟨F.lower start step, F.coordinate start step⟩

def path (F : RankedCubeFamily ι ν γ) (dimension : Nat) (start : ι) :
    List (CubeEdge ν γ) :=
  (List.range dimension).map (F.edge start)

theorem edge_eq_forces_step_eq
    (F : RankedCubeFamily ι ν γ)
    {start₁ start₂ : ι} {step₁ step₂ : Nat}
    (h : F.edge start₁ step₁ = F.edge start₂ step₂) :
    step₁ = step₂ := by
  have hlower :
      F.lower start₁ step₁ = F.lower start₂ step₂ :=
    congrArg CubeEdge.lower h
  calc
    step₁ = F.rank (F.lower start₁ step₁) :=
      (F.rank_lower start₁ step₁).symm
    _ = F.rank (F.lower start₂ step₂) := congrArg F.rank hlower
    _ = step₂ := F.rank_lower start₂ step₂

theorem edge_eq_forces_start_eq
    (F : RankedCubeFamily ι ν γ)
    {start₁ start₂ : ι} {step₁ step₂ : Nat}
    (h : F.edge start₁ step₁ = F.edge start₂ step₂) :
    start₁ = start₂ := by
  have hstep := F.edge_eq_forces_step_eq h
  subst step₂
  apply F.coordinate_injective step₁
  exact congrArg CubeEdge.coordinate h

theorem paths_pairwiseEdgeDisjoint
    (F : RankedCubeFamily ι ν γ)
    (dimension : Nat) (starts : List ι) :
    PairwiseEdgeDisjoint (starts.map (F.path dimension)) := by
  intro p hp q hq hpq edge hedgep hedgeq
  simp only [List.mem_map] at hp hq
  obtain ⟨start₁, hstart₁, rfl⟩ := hp
  obtain ⟨start₂, hstart₂, rfl⟩ := hq
  simp only [path, List.mem_map] at hedgep hedgeq
  obtain ⟨step₁, hstep₁, hedge₁⟩ := hedgep
  obtain ⟨step₂, hstep₂, hedge₂⟩ := hedgeq
  have hedge :
      F.edge start₁ step₁ = F.edge start₂ step₂ :=
    hedge₁.trans hedge₂.symm
  have hstart : start₁ = start₂ := F.edge_eq_forces_start_eq hedge
  subst start₂
  exact hpq rfl

theorem path_injective
    (F : RankedCubeFamily ι ν γ)
    {dimension : Nat} (hdimension : 0 < dimension) :
    ∀ ⦃start₁ start₂⦄,
      F.path dimension start₁ = F.path dimension start₂ →
      start₁ = start₂ := by
  intro start₁ start₂ hpaths
  have hzero : 0 ∈ List.range dimension := by
    simp
    exact hdimension
  have hedge :
      F.edge start₁ 0 = F.edge start₂ 0 := by
    have hmem₁ :
        F.edge start₁ 0 ∈ F.path dimension start₁ := by
      simp only [path, List.mem_map]
      exact ⟨0, hzero, rfl⟩
    rw [hpaths] at hmem₁
    simp only [path, List.mem_map] at hmem₁
    obtain ⟨step, hstep, hedgestep⟩ := hmem₁
    have hstepzero :
        step = 0 :=
      F.edge_eq_forces_step_eq hedgestep
    subst step
    exact hedgestep.symm
  exact F.edge_eq_forces_start_eq hedge

theorem paths_nodup
    (F : RankedCubeFamily ι ν γ)
    {dimension : Nat} (hdimension : 0 < dimension)
    {starts : List ι} (hstarts : starts.Nodup) :
    (starts.map (F.path dimension)).Nodup := by
  induction starts with
  | nil => exact List.nodup_nil
  | cons start starts ih =>
      have hparts := List.nodup_cons.mp hstarts
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        simp only [List.mem_map] at hmem
        obtain ⟨other, hother, heq⟩ := hmem
        have hstart : other = start :=
          F.path_injective hdimension heq
        subst other
        exact hparts.1 hother
      · exact ih hparts.2

/--
Every cut meeting all paths in a nonempty ranked cyclic family contains
at least one distinct edge per starting phase.
-/
theorem cut_bound
    (F : RankedCubeFamily ι ν γ)
    {dimension : Nat} (hdimension : 0 < dimension)
    (starts : List ι) (hstarts : starts.Nodup)
    (cut : CubeEdge ν γ → Prop)
    (hhit : HitsEveryPath cut (starts.map (F.path dimension))) :
    HasAtLeast cut starts.length := by
  have hbound :=
    edge_disjoint_paths_cut_bound cut (starts.map (F.path dimension))
      (F.paths_nodup hdimension hstarts)
      (F.paths_pairwiseEdgeDisjoint dimension starts) hhit
  simpa using hbound

end RankedCubeFamily

/--
Concrete v398 hypercube cut bound.  The `dimension` cyclic paths use
Boolean lower vertices and cross coordinates in the order
`start, start+1, ..., start+dimension-1` modulo `dimension`.
-/
theorem boolean_hypercube_cut_bound
    {dimension : Nat} (hdimension : 0 < dimension)
    (cut : CubeEdge (List Bool) (Fin dimension) → Prop)
    (hhit :
      HitsEveryPath cut
        ((List.finRange dimension).map
          ((booleanCyclicFamily dimension).path dimension))) :
    HasAtLeast cut dimension := by
  simpa using
    (booleanCyclicFamily dimension).cut_bound hdimension
      (List.finRange dimension) (finRange_nodup dimension) cut hhit

end NSSE
