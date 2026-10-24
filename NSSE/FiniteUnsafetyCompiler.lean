import NSSE.FiniteSubtypeLadders
import NSSE.SubtypeConstraintOperations
import NSSE.FiniteSubtypeDecision

/-! # Compile path unsafety into the original four flat constraint forms

The two fresh chains have linear size in the path. Their endpoints use
only bottom/top or one constructor; all original variables are preserved.
-/

namespace NSSE.FiniteUnsafetyCompiler

open FiniteSubtypeTrees FiniteSubtypeSafety FiniteSubtypeProbes FiniteSubtypeLadders
open SubtypeConstraints SubtypeConstraintOperations ForwardTableAutomaton

variable {n d : Nat}

def extra (path : List (Fin d)) : Nat := ((path.length + 1) + (path.length + 1)) + 2

def old (path : List (Fin d)) (x : Fin n) : Fin (n + extra path) := Fin.castAdd _ x

def freshLeft (path : List (Fin d)) (k : Fin (path.length + 1)) : Fin (n + extra path) :=
  Fin.natAdd n (Fin.castAdd 2 (Fin.castAdd (path.length + 1) k))

def freshRight (path : List (Fin d)) (k : Fin (path.length + 1)) : Fin (n + extra path) :=
  Fin.natAdd n (Fin.castAdd 2 (Fin.natAdd (path.length + 1) k))

def botVar (n : Nat) (path : List (Fin d)) : Fin (n + extra path) :=
  Fin.natAdd n (Fin.natAdd ((path.length + 1) + (path.length + 1)) (0 : Fin 2))

def topVar (n : Nat) (path : List (Fin d)) : Fin (n + extra path) :=
  Fin.natAdd n (Fin.natAdd ((path.length + 1) + (path.length + 1)) (1 : Fin 2))

def leftParent (Q : Query n d) (path : List (Fin d)) (k : Fin (path.length + 1)) : Fin (n + extra path) :=
  if k.val = 0 then old path Q.left else freshLeft path k

def rightParent (Q : Query n d) (path : List (Fin d)) (k : Fin (path.length + 1)) : Fin (n + extra path) :=
  if k.val = 0 then old path Q.right else freshRight path k

def extend (path : List (Fin d)) (ρ : Fin n → Tree d)
    (L R : Fin (path.length + 1) → Tree d) : Fin (n + extra path) → Tree d :=
  Fin.addCases ρ (Fin.addCases (Fin.addCases L R) (fun k : Fin 2 => if k = 0 then .bot else .top))

@[simp] theorem extend_old (path : List (Fin d)) (ρ : Fin n → Tree d)
    (L R : Fin (path.length + 1) → Tree d) (x : Fin n) : extend path ρ L R (old path x) = ρ x := by
  simp [extend, old]

@[simp] theorem extend_bot (path : List (Fin d)) (ρ : Fin n → Tree d)
    (L R : Fin (path.length + 1) → Tree d) : extend path ρ L R (botVar n path) = .bot := by
  simp [extend, botVar, Fin.addCases_right]

@[simp] theorem extend_top (path : List (Fin d)) (ρ : Fin n → Tree d)
    (L R : Fin (path.length + 1) → Tree d) : extend path ρ L R (topVar n path) = .top := by
  simp [extend, topVar, Fin.addCases_right]

theorem extend_left (Q : Query n d) (path : List (Fin d)) (ρ : Fin n → Tree d)
    (L R : Fin (path.length + 1) → Tree d) (hL : L 0 = ρ Q.left) (k : Fin (path.length + 1)) :
    extend path ρ L R (leftParent Q path k) = L k := by
  by_cases hk : k.val = 0
  · have he : k = 0 := Fin.ext hk
    subst k
    simp [leftParent, hL]
  · simp [leftParent, hk, freshLeft, extend, Fin.addCases_right]

theorem extend_right (Q : Query n d) (path : List (Fin d)) (ρ : Fin n → Tree d)
    (L R : Fin (path.length + 1) → Tree d) (hR : R 0 = ρ Q.right) (k : Fin (path.length + 1)) :
    extend path ρ L R (rightParent Q path k) = R k := by
  by_cases hk : k.val = 0
  · have he : k = 0 := Fin.ext hk
    subst k
    simp [rightParent, hR]
  · simp only [rightParent, hk, ↓reduceIte, freshRight, extend, Fin.addCases_right, Fin.addCases_left]

def lowerStep (Q : Query n d) (path : List (Fin d)) (k : Fin path.length) : BoundLiteral (n + extra path) d :=
  (leftParent Q path k.castSucc, fun i => if i = path[k.val] then leftParent Q path k.succ else botVar n path)

def upperStep (Q : Query n d) (path : List (Fin d)) (k : Fin path.length) : BoundLiteral (n + extra path) d :=
  (rightParent Q path k.castSucc, fun i => if i = path[k.val] then rightParent Q path k.succ else topVar n path)

def gadget (Q : Query n d) (side : Side) (path : List (Fin d)) : Constraints (n + extra path) d where
  upper := (List.finRange path.length).map (upperStep Q path) ++ match side with
    | .left => [(rightParent Q path (Fin.last path.length), fun _ => topVar n path)]
    | .right => []
  lower := (List.finRange path.length).map (lowerStep Q path) ++ match side with
    | .left => []
    | .right => [(leftParent Q path (Fin.last path.length), fun _ => botVar n path)]
  bot := [botVar n path] ++ match side with | .left => [] | .right => [rightParent Q path (Fin.last path.length)]
  top := [topVar n path] ++ match side with | .left => [leftParent Q path (Fin.last path.length)] | .right => []

theorem gadget_chains (Q : Query n d) (side : Side) (path : List (Fin d))
    (σ : Fin (n + extra path) → Tree d) (hb : σ (botVar n path) = .bot) (ht : σ (topVar n path) = .top) :
    Satisfies (constructor d) (gadget Q side path) σ ↔
      LowerChain (lowerLeaf side d) path (fun k => σ (leftParent Q path k)) ∧
      UpperChain (upperLeaf side d) path (fun k => σ (rightParent Q path k)) := by
  have hbot (t : Tree d) : t ≤ Tree.bot ↔ t = (⊥ : Tree d) := eq_bot_iff.symm
  have htop (t : Tree d) : Tree.top ≤ t ↔ t = (⊤ : Tree d) := eq_top_iff.symm
  cases side <;>
    simp only [gadget, Satisfies, List.forall_mem_append, List.forall_mem_map,
      List.forall_mem_cons, List.forall_mem_nil] <;>
    simp [constructor, lowerStep, upperStep, apply_ite, hb, ht,
      LowerChain, UpperChain, lowerLeaf, upperLeaf, floorNode, ceilingNode, hbot, htop]
  all_goals tauto

def compile (Q : Query n d) (side : Side) (path : List (Fin d)) : Constraints (n + extra path) d :=
  combine (rename Q.constraints (old path)) (gadget Q side path)

theorem compiled_solution_unsafe (Q : Query n d) (side : Side) (path : List (Fin d))
    (σ : Fin (n + extra path) → Tree d) (h : Satisfies (constructor d) (compile Q side path) σ) :
    Satisfies (constructor d) Q.constraints (fun x => σ (old path x)) ∧
      ¬ Safe side (σ (old path Q.left)) (σ (old path Q.right)) path := by
  obtain ⟨ho,hg⟩ := (satisfies_combine _ _ _ σ).mp h
  refine ⟨(satisfies_rename _ _ _ σ).mp ho, ?_⟩
  have hb : σ (botVar n path) = .bot := hg.2.2.1 _ (by cases side <;> simp [gadget])
  have ht : σ (topVar n path) = .top := hg.2.2.2 _ (by cases side <;> simp [gadget])
  obtain ⟨hl,hu⟩ := (gadget_chains Q side path σ hb ht).mp hg
  apply (unsafe_iff_bounds side _ _ path).mpr
  have hl' := lowerChain_bound _ path _ hl
  have hu' := upperChain_bound _ path _ hu
  simpa only [leftParent, rightParent, Fin.val_zero, ↓reduceIte] using And.intro hl' hu'

theorem unsafe_extends (Q : Query n d) (side : Side) (path : List (Fin d))
    (ρ : Fin n → Tree d) (hρ : Satisfies (constructor d) Q.constraints ρ)
    (hu : ¬ Safe side (ρ Q.left) (ρ Q.right) path) :
    Satisfiable (constructor d) (compile Q side path) := by
  obtain ⟨hl,hr⟩ := (unsafe_iff_bounds side _ _ path).mp hu
  let L := chainValue (lowerSpine (lowerLeaf side d)) path (ρ Q.left)
  let R := chainValue (upperSpine (upperLeaf side d)) path (ρ Q.right)
  let σ := extend path ρ L R
  have hL : L 0 = ρ Q.left := chainValue_zero _ _ _
  have hR : R 0 = ρ Q.right := chainValue_zero _ _ _
  refine ⟨σ,(satisfies_combine _ _ _ σ).mpr ⟨?_,?_⟩⟩
  · apply (satisfies_rename _ _ _ σ).mpr
    simpa only [σ, extend_old] using hρ
  · apply (gadget_chains Q side path σ (extend_bot _ _ _ _) (extend_top _ _ _ _)).mpr
    simpa only [σ, extend_left Q path ρ L R hL, extend_right Q path ρ L R hR] using
      And.intro (lowerChain_exists _ path _ hl) (upperChain_exists _ path _ hr)

/-- Exact finite countermodel compilation, including the empty path and
queries whose two variables coincide. No original satisfiability premise. -/
theorem compile_satisfiable_iff (Q : Query n d) (side : Side) (path : List (Fin d)) :
    Satisfiable (constructor d) (compile Q side path) ↔ ¬ QuerySafe Q side path := by
  classical
  constructor
  · rintro ⟨σ,hσ⟩ hs
    obtain ⟨ho,hu⟩ := compiled_solution_unsafe Q side path σ hσ
    exact hu (hs _ ho)
  · intro h
    obtain ⟨ρ,hρ,hu⟩ : ∃ ρ, Satisfies (constructor d) Q.constraints ρ ∧
        ¬ Safe side (ρ Q.left) (ρ Q.right) path := by
      unfold QuerySafe at h
      push_neg at h
      exact h
    exact unsafe_extends Q side path ρ hρ hu

end NSSE.FiniteUnsafetyCompiler
