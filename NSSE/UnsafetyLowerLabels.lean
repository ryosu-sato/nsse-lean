import NSSE.UnsafetyLowerSuffix
import NSSE.ForwardPeriodicCertificate

/-! # Rejection excludes the actual lower-stage constructor/top obstacles

This is the load-bearing label analysis for the regular lower-set model.
It constructs actual automaton acceptance, not a semantic SAT assumption.
-/

namespace NSSE.UnsafetyLowerLabels

open SubtypeConstraints SubtypeConstraintOperations SubtypePathBounds
open FiniteUnsafetyCompiler UnsafetyLowerStage UnsafetyLowerSuffix
open ConstraintForwardTables ForwardPeriodicCertificate

variable {n d : Nat}

theorem parent_bottom_accepts (Q : Query n d) (path : List (Fin d))
    (k : Fin (path.length + 1)) (b : Fin n) (hb : b ∈ Q.constraints.bot)
    (hs : Support (lowerStage Q path) (leftParent Q path k) (old path b)) :
    ForwardCapAutomaton.Accepts (automaton Q .right) path := by
  by_cases hk : k.val = 0
  · simp only [leftParent, hk, ↓reduceIte] at hs
    exact upper_bottom_accepts Q .right
      (.nil ((old_support_iff Q path Q.left b).mp hs)) hb List.nil_prefix
  · exact upper_bottom_accepts Q .right
      ((active_support_iff Q path b k (Nat.pos_of_ne_zero hk)).mp hs) hb (List.take_prefix _ _)

theorem lower_node_accepts (Q : Query n d) (hd : 0 < d) (path : List (Fin d))
    (h : ∃ l ∈ (lowerStage Q path).lower,
      LowerPath (lowerStage Q path) (old path Q.right) path l.1) :
    ForwardCapAutomaton.Accepts (automaton Q .right) path := by
  obtain ⟨l,hl,hp⟩ := h
  change l ∈ Q.constraints.lower.map (renameBound (old path)) ++ (gadget Q .right path).lower at hl
  rcases List.mem_append.mp hl with ho | hn
  · obtain ⟨l₀,hl₀,rfl⟩ := List.mem_map.mp ho
    exact ForwardPeriodicCertificate.lower_node_accepts Q hd path
      ⟨l₀,hl₀,(old_lower_path_iff Q path path Q.right l₀.1).mp hp⟩
  · change l ∈ (List.finRange path.length).map (lowerStep Q path) ++
      [(leftParent Q path (Fin.last path.length), fun _ => botVar n path)] at hn
    rcases List.mem_append.mp hn with hstep | hend
    · obtain ⟨j,_,rfl⟩ := List.mem_map.mp hstep
      obtain ⟨a,s,z,ha,hu,hl,hper⟩ := parent_lower_periodic Q path Q.right j.castSucc hp
      exact periodic_accepts Q path a s z ha hu hl hper
    · have he : l = (leftParent Q path (Fin.last path.length), fun _ => botVar n path) := by
        simpa using hend
      subst l
      obtain ⟨a,s,z,ha,hu,hl,hper⟩ := parent_lower_periodic Q path Q.right (Fin.last path.length) hp
      exact periodic_accepts Q path a s z ha hu hl hper

theorem lower_top_prefix_accepts (Q : Query n d) (path pref : List (Fin d))
    (hp : pref <+: path)
    (h : ∃ b ∈ (lowerStage Q path).top,
      LowerPath (lowerStage Q path) (old path Q.right) pref b) :
    ForwardCapAutomaton.Accepts (automaton Q .right) path := by
  obtain ⟨b,hb,hl⟩ := h
  simp only [lowerStage, SubtypeLowerGraft.graft, List.mem_append, List.not_mem_nil, or_false] at hb
  obtain ⟨b₀,hb₀,rfl⟩ := List.mem_map.mp hb
  exact lower_top_accepts Q .right ((old_lower_path_iff Q path pref Q.right b₀).mp hl) hb₀ hp

/-- The actual right rejection excludes all three new obstructions used
by the paper model proof. Original SAT is not assumed in this theorem. -/
theorem rejection_excludes (Q : Query n d) (hd : 0 < d) (path : List (Fin d))
    (hr : ¬ ForwardCapAutomaton.Accepts (automaton Q .right) path) :
    (∀ k b, b ∈ Q.constraints.bot →
      ¬ Support (lowerStage Q path) (leftParent Q path k) (old path b)) ∧
    (¬ ∃ l ∈ (lowerStage Q path).lower,
      LowerPath (lowerStage Q path) (old path Q.right) path l.1) ∧
    (∀ pref, pref <+: path → ¬ ∃ b ∈ (lowerStage Q path).top,
      LowerPath (lowerStage Q path) (old path Q.right) pref b) := by
  refine ⟨?_,?_,?_⟩
  · intro k b hb hs
    exact hr (parent_bottom_accepts Q path k b hb hs)
  · intro h
    exact hr (lower_node_accepts Q hd path h)
  · intro pref hp h
    exact hr (lower_top_prefix_accepts Q path pref hp h)

end NSSE.UnsafetyLowerLabels
