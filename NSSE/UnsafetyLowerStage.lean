import NSSE.SubtypeLowerGraftCross
import NSSE.FiniteUnsafetyCompiler

/-! # The actual right-unsafety compiler starts with a conservative lower graft

The fresh-child hypothesis is proved for the literal shared-constant layout
of v1344, and the remaining upper stage composes to that exact compiler.
-/

namespace NSSE.UnsafetyLowerStage

open SubtypeConstraints SubtypeConstraintOperations SubtypeLowerGraft SubtypePathBounds
open FiniteUnsafetyCompiler

variable {n d : Nat}

def lowerStage (Q : Query n d) (path : List (Fin d)) : Constraints (n + extra path) d :=
  graft Q.constraints (gadget Q .right path).lower [botVar n path] []

def upperRest (Q : Query n d) (path : List (Fin d)) : Constraints (n + extra path) d where
  upper := (gadget Q .right path).upper
  lower := []
  bot := [rightParent Q path (Fin.last path.length)]
  top := [topVar n path]

theorem compiler_split (Q : Query n d) (path : List (Fin d)) :
    FiniteUnsafetyCompiler.compile Q .right path = combine (lowerStage Q path) (upperRest Q path) := by
  simp [FiniteUnsafetyCompiler.compile, lowerStage, upperRest, graft, combine, rename,
    gadget, old, renameBound, List.append_assoc]

theorem left_succ_fresh (Q : Query n d) (path : List (Fin d)) (k : Fin path.length) :
    ∃ z : Fin (extra path), leftParent Q path k.succ = Fin.natAdd n z := by
  refine ⟨Fin.castAdd 2 (Fin.castAdd (path.length + 1) k.succ), ?_⟩
  simp [leftParent, freshLeft]

theorem lower_fresh_children (Q : Query n d) (path : List (Fin d)) :
    FreshChildren (gadget Q .right path).lower := by
  intro a ha i
  change a ∈ (List.finRange path.length).map (lowerStep Q path) ++
    [(leftParent Q path (Fin.last path.length), fun _ => botVar n path)] at ha
  rcases List.mem_append.mp ha with hs | he
  · obtain ⟨k,_,rfl⟩ := List.mem_map.mp hs
    by_cases hi : i = path[k.val]
    · simpa only [lowerStep, hi, ↓reduceIte] using left_succ_fresh Q path k
    · refine ⟨Fin.natAdd ((path.length + 1) + (path.length + 1)) (0 : Fin 2), ?_⟩
      simp only [lowerStep, hi, ↓reduceIte, botVar]
  · have he' : a = (leftParent Q path (Fin.last path.length), fun _ => botVar n path) := by simpa using he
    subst a
    exact ⟨Fin.natAdd ((path.length + 1) + (path.length + 1)) (0 : Fin 2), rfl⟩

theorem old_support_iff (Q : Query n d) (path : List (Fin d)) (x y : Fin n) :
    Support (lowerStage Q path) (old path x) (old path y) ↔ Support Q.constraints x y :=
  support_old_iff Q.constraints _ _ _ (lower_fresh_children Q path) x y

theorem old_upper_path_iff (Q : Query n d) (path word : List (Fin d)) (x y : Fin n) :
    UpperPath (lowerStage Q path) (old path x) word (old path y) ↔ UpperPath Q.constraints x word y :=
  SubtypeLowerGraftPaths.upper_path_old_iff Q.constraints _ _ _ (lower_fresh_children Q path) x y word

theorem old_lower_path_iff (Q : Query n d) (path word : List (Fin d)) (x y : Fin n) :
    LowerPath (lowerStage Q path) (old path x) word (old path y) ↔ LowerPath Q.constraints x word y :=
  SubtypeLowerGraftPaths.lower_path_old_iff Q.constraints _ _ _ (lower_fresh_children Q path) x y word

theorem no_old_to_fresh (Q : Query n d) (path : List (Fin d)) (x : Fin n) (y : Fin (extra path)) :
    ¬ Support (lowerStage Q path) (old path x) (Fin.natAdd n y) :=
  no_old_fresh Q.constraints _ _ _ (lower_fresh_children Q path) x y

theorem fresh_support_iff (Q : Query n d) (path : List (Fin d)) (x y : Fin (extra path)) :
    Support (lowerStage Q path) (Fin.natAdd n x) (Fin.natAdd n y) ↔ x = y :=
  support_fresh_iff Q.constraints _ _ _ (lower_fresh_children Q path) x y

theorem leftParent_old_eq (Q : Query n d) (path : List (Fin d))
    (k : Fin (path.length + 1)) (x : Fin n) (h : leftParent Q path k = old path x) : x = Q.left := by
  by_cases hk : k.val = 0
  · simp only [leftParent, hk, ↓reduceIte] at h
    exact Fin.ext (congrArg (fun z : Fin (n + extra path) => z.val) h.symm)
  · simp only [leftParent, hk, ↓reduceIte] at h
    have he := congrArg (fun z : Fin (n + extra path) => z.val) h
    change n + k.val = x.val at he
    have hx := x.isLt
    omega

theorem origin_root (Q : Query n d) (path : List (Fin d)) {x word u}
    (h : SubtypeLowerGraftCross.Origin (gadget Q .right path).lower x word u) : x = Q.left := by
  induction h with
  | @first a x u i ha hp hc =>
      change a ∈ (List.finRange path.length).map (lowerStep Q path) ++
        [(leftParent Q path (Fin.last path.length), fun _ => botVar n path)] at ha
      rcases List.mem_append.mp ha with hs | he
      · obtain ⟨k,_,rfl⟩ := List.mem_map.mp hs
        exact leftParent_old_eq Q path k.castSucc x hp
      · have he' : a = (leftParent Q path (Fin.last path.length), fun _ => botVar n path) := by simpa using he
        subst a
        exact leftParent_old_eq Q path (Fin.last path.length) x hp
  | snoc _ _ _ _ ih => exact ih

/-- All fresh-to-old support in the ACTUAL lower stage has an original
upper trace from the query's left variable, matching an actual added trace. -/
theorem fresh_old_support_iff (Q : Query n d) (path : List (Fin d))
    (u : Fin (extra path)) (y : Fin n) :
    Support (lowerStage Q path) (Fin.natAdd n u) (old path y) ↔
      ∃ word, SubtypeLowerGraftCross.Origin (gadget Q .right path).lower Q.left word u ∧
        UpperPath Q.constraints Q.left word y := by
  refine (SubtypeLowerGraftCross.fresh_old_support_iff Q.constraints _ [botVar n path] []
    (lower_fresh_children Q path) u y).trans ?_
  constructor
  · rintro ⟨x,word,ho,hu⟩
    obtain rfl := origin_root Q path ho
    exact ⟨word,ho,hu⟩
  · rintro ⟨word,ho,hu⟩
    exact ⟨Q.left,word,ho,hu⟩

theorem fresh_upper_path_iff (Q : Query n d) (path tail : List (Fin d))
    (u : Fin (extra path)) (y : Fin n) :
    UpperPath (lowerStage Q path) (Fin.natAdd n u) tail (old path y) ↔
      ∃ word, SubtypeLowerGraftCross.Origin (gadget Q .right path).lower Q.left word u ∧
        UpperPath Q.constraints Q.left (word ++ tail) y := by
  refine (SubtypeLowerGraftCross.fresh_upper_iff Q.constraints _ [botVar n path] []
    (lower_fresh_children Q path) u y tail).trans ?_
  constructor
  · rintro ⟨x,word,ho,hu⟩
    obtain rfl := origin_root Q path ho
    exact ⟨word,ho,hu⟩
  · rintro ⟨word,ho,hu⟩
    exact ⟨Q.left,word,ho,hu⟩

end NSSE.UnsafetyLowerStage
