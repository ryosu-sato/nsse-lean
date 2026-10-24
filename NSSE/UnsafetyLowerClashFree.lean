import NSSE.UnsafetyLowerLabels
import NSSE.SubtypeLabelClashes

/-! # The actual lower stage is label-clash free under original consistency

Every new possible clash yields a bot-escape acceptance of the rejected
word. Shared-bottom and old/fresh disjointness cases are proved explicitly.
-/

namespace NSSE.UnsafetyLowerClashFree

open SubtypeConstraints SubtypeConstraintOperations SubtypeLabelClashes
open FiniteUnsafetyCompiler UnsafetyLowerStage UnsafetyLowerOrigins UnsafetyLowerLabels
open ConstraintForwardTables

variable {n d : Nat}

private theorem added_parent (Q : Query n d) (path : List (Fin d))
    (a : BoundLiteral (n + extra path) d) (ha : a ∈ (gadget Q .right path).lower) :
    ∃ k : Fin (path.length + 1), a.1 = leftParent Q path k := by
  change a ∈ (List.finRange path.length).map (lowerStep Q path) ++
    [(leftParent Q path (Fin.last path.length), fun _ => botVar n path)] at ha
  rcases List.mem_append.mp ha with hs | ht
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp hs
    exact ⟨j.castSucc,rfl⟩
  · have he : a = (leftParent Q path (Fin.last path.length), fun _ => botVar n path) := by simpa using ht
    subst a
    exact ⟨Fin.last path.length,rfl⟩

theorem old_not_bottom_slot (Q : Query n d) (path : List (Fin d)) (x : Fin n) :
    ¬ Support (lowerStage Q path) (old path x) (botVar n path) :=
  no_old_to_fresh Q path x (Fin.natAdd ((path.length + 1) + (path.length + 1)) (0 : Fin 2))

theorem parent_not_bottom_slot (Q : Query n d) (path : List (Fin d))
    (k : Fin (path.length + 1)) :
    ¬ Support (lowerStage Q path) (leftParent Q path k) (botVar n path) := by
  intro hs
  by_cases hk : k.val = 0
  · simp only [leftParent, hk, ↓reduceIte] at hs
    exact old_not_bottom_slot Q path Q.left hs
  · rw [parent_positive Q path k (Nat.pos_of_ne_zero hk)] at hs
    have he := (fresh_support_iff Q path (leftSlot path k)
      (Fin.natAdd ((path.length + 1) + (path.length + 1)) (0 : Fin 2))).mp hs
    exact bottom_ne_left path k (congrArg (Fin.natAdd n) he.symm)

theorem lowerStage_no_clash (Q : Query n d) (path : List (Fin d))
    (hc : ¬ LabelClash Q.constraints)
    (hr : ¬ ForwardCapAutomaton.Accepts (automaton Q .right) path) :
    ¬ LabelClash (lowerStage Q path) := by
  rintro (⟨x,hx,y,hy,hs⟩ | ⟨x,hx,a,ha,hs⟩ | ⟨a,ha,y,hy,hs⟩)
  · simp only [lowerStage, SubtypeLowerGraft.graft, List.mem_append, List.not_mem_nil, or_false] at hx
    obtain ⟨x₀,hx₀,rfl⟩ := List.mem_map.mp hx
    change y ∈ Q.constraints.bot.map (old path) ++ [botVar n path] at hy
    rcases List.mem_append.mp hy with ho | hn
    · obtain ⟨y₀,hy₀,rfl⟩ := List.mem_map.mp ho
      exact hc (Or.inl ⟨x₀,hx₀,y₀,hy₀,(old_support_iff Q path x₀ y₀).mp hs⟩)
    · have he : y = botVar n path := by simpa using hn
      subst y
      exact old_not_bottom_slot Q path x₀ hs
  · simp only [lowerStage, SubtypeLowerGraft.graft, List.mem_append, List.not_mem_nil, or_false] at hx
    obtain ⟨x₀,hx₀,rfl⟩ := List.mem_map.mp hx
    change a ∈ Q.constraints.upper.map (renameBound (old path)) at ha
    obtain ⟨a₀,ha₀,rfl⟩ := List.mem_map.mp ha
    exact hc (Or.inr (Or.inl ⟨x₀,hx₀,a₀,ha₀,(old_support_iff Q path x₀ a₀.1).mp hs⟩))
  · change a ∈ Q.constraints.lower.map (renameBound (old path)) ++ (gadget Q .right path).lower at ha
    change y ∈ Q.constraints.bot.map (old path) ++ [botVar n path] at hy
    rcases List.mem_append.mp ha with ho | hn
    · obtain ⟨a₀,ha₀,rfl⟩ := List.mem_map.mp ho
      rcases List.mem_append.mp hy with hb | hb
      · obtain ⟨y₀,hy₀,rfl⟩ := List.mem_map.mp hb
        exact hc (Or.inr (Or.inr ⟨a₀,ha₀,y₀,hy₀,(old_support_iff Q path a₀.1 y₀).mp hs⟩))
      · have he : y = botVar n path := by simpa using hb
        subst y
        exact old_not_bottom_slot Q path a₀.1 hs
    · obtain ⟨k,hk⟩ := added_parent Q path a hn
      rw [hk] at hs
      rcases List.mem_append.mp hy with hb | hb
      · obtain ⟨y₀,hy₀,rfl⟩ := List.mem_map.mp hb
        exact hr (parent_bottom_accepts Q path k y₀ hy₀ hs)
      · have he : y = botVar n path := by simpa using hb
        subst y
        exact parent_not_bottom_slot Q path k hs

/-- The finite original-SAT premise is discharged by the actual tree
semantics. This asserts label consistency, not yet lower-stage SAT. -/
theorem finite_sat_rejection_no_clash (Q : Query n d) (path : List (Fin d))
    (hs : Satisfiable (FiniteSubtypeTrees.constructor d) Q.constraints)
    (hr : ¬ ForwardCapAutomaton.Accepts (automaton Q .right) path) :
    ¬ LabelClash (lowerStage Q path) :=
  lowerStage_no_clash Q path (satisfiable_no_clash Q.constraints hs) hr

end NSSE.UnsafetyLowerClashFree
