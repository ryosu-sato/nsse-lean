import NSSE.UnsafetyUpperExtension
import NSSE.UnsafetyLowerClashFree

/-! # Exact label clashes of the actual FULL right-unsafety compiler

All new clashes are precisely prefix-top and full-word constructor lower
bounds in the actual lower stage. No tree-model premise enters the identity.
-/

namespace NSSE.UnsafetyFullClashes

open SubtypeConstraints SubtypePathBounds SubtypeLabelClashes
open FiniteUnsafetyCompiler UnsafetyLowerStage UnsafetyUpperExtension
open ConstraintForwardTables

variable {n d : Nat}

def TopPrefix (Q : Query n d) (path : List (Fin d)) : Prop :=
  ∃ k : Fin (path.length + 1), ∃ b ∈ (lowerStage Q path).top,
    LowerPath (lowerStage Q path) (old path Q.right) (path.take k.val) b

def NodeAt (Q : Query n d) (path : List (Fin d)) : Prop :=
  ∃ l ∈ (lowerStage Q path).lower,
    LowerPath (lowerStage Q path) (old path Q.right) path l.1

theorem full_lower (Q : Query n d) (path : List (Fin d)) :
    (compile Q .right path).lower = (lowerStage Q path).lower := by rw [full_eq]; rfl

theorem full_upper (Q : Query n d) (path : List (Fin d)) :
    (compile Q .right path).upper = (lowerStage Q path).upper ++ (gadget Q .right path).upper := by
  rw [full_eq]; rfl

theorem full_bot (Q : Query n d) (path : List (Fin d)) :
    (compile Q .right path).bot = (lowerStage Q path).bot ++ [rightParent Q path (Fin.last path.length)] := by
  rw [full_eq]; rfl

theorem full_top (Q : Query n d) (path : List (Fin d)) :
    (compile Q .right path).top = (lowerStage Q path).top ++ [topVar n path] := by rw [full_eq]; rfl

theorem stage_top_base (Q : Query n d) (path : List (Fin d))
    {b : Fin (n + extra path)} (hb : b ∈ (lowerStage Q path).top) : Base path b := by
  simp only [lowerStage, SubtypeLowerGraft.graft, List.append_nil] at hb
  obtain ⟨b₀,_,rfl⟩ := List.mem_map.mp hb
  exact base_old path b₀

theorem stage_bot_base (Q : Query n d) (path : List (Fin d))
    {b : Fin (n + extra path)} (hb : b ∈ (lowerStage Q path).bot) : Base path b := by
  change b ∈ Q.constraints.bot.map (old path) ++ [botVar n path] at hb
  rcases List.mem_append.mp hb with ho | hn
  · obtain ⟨b₀,_,rfl⟩ := List.mem_map.mp ho
    exact base_old path b₀
  · have he : b = botVar n path := by simpa using hn
    subst b
    exact base_bot path

theorem added_upper_parent (Q : Query n d) (path : List (Fin d))
    (a : BoundLiteral (n + extra path) d) (ha : a ∈ (gadget Q .right path).upper) :
    ∃ j : Fin path.length, a.1 = rightParent Q path j.castSucc := by
  have hm : a ∈ (List.finRange path.length).map (upperStep Q path) := by
    simpa only [gadget, List.append_nil] using ha
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hm
  exact ⟨j,rfl⟩

theorem top_no_parent (Q : Query n d) (path : List (Fin d))
    (k : Fin (path.length + 1)) :
    ¬ Support (compile Q .right path) (topVar n path) (rightParent Q path k) := by
  intro hs
  by_cases hb : Base path (rightParent Q path k)
  · exact no_fresh_base Q path (not_base_top path) hb hs
  · exact top_ne_parent Q path k ((support_fresh_iff Q path (not_base_top path) hb).mp hs)

theorem clash_forward (Q : Query n d) (path : List (Fin d))
    (h : LabelClash (compile Q .right path)) :
    LabelClash (lowerStage Q path) ∨ TopPrefix Q path ∨ NodeAt Q path := by
  rcases h with ⟨x,hx,y,hy,hs⟩ | ⟨x,hx,a,ha,hs⟩ | ⟨a,ha,y,hy,hs⟩
  · rw [full_top] at hx
    rw [full_bot] at hy
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hy with hy | hy
      · exact Or.inl (Or.inl ⟨x,hx,y,hy,
          (support_base_iff Q path (stage_top_base Q path hx) (stage_bot_base Q path hy)).mp hs⟩)
      · have he : y = rightParent Q path (Fin.last path.length) := by simpa using hy
        subst y
        exact Or.inr (Or.inl ⟨Fin.last path.length,x,hx,
          (parent_support_iff Q path x (stage_top_base Q path hx) _).mp hs⟩)
    · have he : x = topVar n path := by simpa using hx
      subst x
      rcases List.mem_append.mp hy with hy | hy
      · exact False.elim (no_fresh_base Q path (not_base_top path) (stage_bot_base Q path hy) hs)
      · have he : y = rightParent Q path (Fin.last path.length) := by simpa using hy
        subst y
        exact False.elim (top_no_parent Q path _ hs)
  · rw [full_top] at hx
    rw [full_upper] at ha
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp ha with ha | ha
      · exact Or.inl (Or.inr (Or.inl ⟨x,hx,a,ha,
          (support_base_iff Q path (stage_top_base Q path hx)
            ((lower_stage_contained Q path).2 a ha).1).mp hs⟩))
      · obtain ⟨j,hj⟩ := added_upper_parent Q path a ha
        rw [hj] at hs
        exact Or.inr (Or.inl ⟨j.castSucc,x,hx,
          (parent_support_iff Q path x (stage_top_base Q path hx) _).mp hs⟩)
    · have he : x = topVar n path := by simpa using hx
      subst x
      rcases List.mem_append.mp ha with ha | ha
      · exact False.elim (no_fresh_base Q path (not_base_top path)
          ((lower_stage_contained Q path).2 a ha).1 hs)
      · obtain ⟨j,hj⟩ := added_upper_parent Q path a ha
        rw [hj] at hs
        exact False.elim (top_no_parent Q path j.castSucc hs)
  · rw [full_lower] at ha
    rw [full_bot] at hy
    rcases List.mem_append.mp hy with hy | hy
    · exact Or.inl (Or.inr (Or.inr ⟨a,ha,y,hy,
        (support_base_iff Q path ((lower_stage_contained Q path).1 a ha).1
          (stage_bot_base Q path hy)).mp hs⟩))
    · have he : y = rightParent Q path (Fin.last path.length) := by simpa using hy
      subst y
      refine Or.inr (Or.inr ⟨a,ha,?_⟩)
      have hp := (parent_support_iff Q path a.1 ((lower_stage_contained Q path).1 a ha).1 _).mp hs
      simpa using hp

theorem stage_clash_lift (Q : Query n d) (path : List (Fin d))
    (h : LabelClash (lowerStage Q path)) : LabelClash (compile Q .right path) := by
  have hS {a b} (hs : Support (lowerStage Q path) a b) : Support (compile Q .right path) a b := by
    rw [full_eq]
    exact SubtypeUpperExtension.support_lift _ _ _ _ hs
  have hT {b} (hb : b ∈ (lowerStage Q path).top) : b ∈ (compile Q .right path).top := by
    rw [full_top]; exact List.mem_append_left _ hb
  have hB {b} (hb : b ∈ (lowerStage Q path).bot) : b ∈ (compile Q .right path).bot := by
    rw [full_bot]; exact List.mem_append_left _ hb
  rcases h with ⟨x,hx,y,hy,hs⟩ | ⟨x,hx,a,ha,hs⟩ | ⟨a,ha,y,hy,hs⟩
  · exact Or.inl ⟨x,hT hx,y,hB hy,hS hs⟩
  · refine Or.inr (Or.inl ⟨x,hT hx,a,?_,hS hs⟩)
    rw [full_upper]; exact List.mem_append_left _ ha
  · refine Or.inr (Or.inr ⟨a,?_,y,hB hy,hS hs⟩)
    rw [full_lower]; exact ha

theorem top_prefix_clash (Q : Query n d) (path : List (Fin d))
    (h : TopPrefix Q path) : LabelClash (compile Q .right path) := by
  obtain ⟨k,b,hb,hp⟩ := h
  have hs := (parent_support_iff Q path b (stage_top_base Q path hb) k).mpr hp
  have ht : b ∈ (compile Q .right path).top := by rw [full_top]; exact List.mem_append_left _ hb
  by_cases hk : k = Fin.last path.length
  · subst k
    refine Or.inl ⟨b,ht,rightParent Q path (Fin.last path.length),?_,hs⟩
    rw [full_bot]; exact List.mem_append_right _ (List.mem_singleton_self _)
  · have hlt : k.val < path.length := by
      have hne : k.val ≠ path.length := fun he => hk (Fin.ext he)
      have := k.isLt
      omega
    let j : Fin path.length := ⟨k.val,hlt⟩
    have hj : j.castSucc = k := Fin.ext rfl
    refine Or.inr (Or.inl ⟨b,ht,upperStep Q path j,?_,?_⟩)
    · rw [full_upper]
      exact List.mem_append_right _ (upperStep_mem Q path j)
    · change Support (compile Q .right path) b (rightParent Q path j.castSucc)
      rw [hj]; exact hs

theorem node_at_clash (Q : Query n d) (path : List (Fin d))
    (h : NodeAt Q path) : LabelClash (compile Q .right path) := by
  obtain ⟨a,ha,hp⟩ := h
  refine Or.inr (Or.inr ⟨a,?_,rightParent Q path (Fin.last path.length),?_,?_⟩)
  · rw [full_lower]; exact ha
  · rw [full_bot]; exact List.mem_append_right _ (List.mem_singleton_self _)
  · apply (parent_support_iff Q path a.1 ((lower_stage_contained Q path).1 a ha).1 _).mpr
    simpa using hp

/-- The exact three-term identity uses no SAT, rejection, or arity premise. -/
theorem full_clash_iff (Q : Query n d) (path : List (Fin d)) :
    LabelClash (compile Q .right path) ↔
      LabelClash (lowerStage Q path) ∨ TopPrefix Q path ∨ NodeAt Q path := by
  constructor
  · exact clash_forward Q path
  · rintro (h | h | h)
    · exact stage_clash_lift Q path h
    · exact top_prefix_clash Q path h
    · exact node_at_clash Q path h

/-- Actual rejection excludes every FULL-compiler label clash. This is
syntactic consistency, proved without any finite or regular compiled model. -/
theorem rejection_no_clash (Q : Query n d) (hd : 0 < d) (path : List (Fin d))
    (hc : ¬ LabelClash Q.constraints)
    (hr : ¬ ForwardCapAutomaton.Accepts (automaton Q .right) path) :
    ¬ LabelClash (compile Q .right path) := by
  intro h
  have he := UnsafetyLowerLabels.rejection_excludes Q hd path hr
  rcases (full_clash_iff Q path).mp h with h | ⟨k,b,hb,hp⟩ | h
  · exact UnsafetyLowerClashFree.lowerStage_no_clash Q path hc hr h
  · exact he.2.2 (path.take k.val) (List.take_prefix _ _) ⟨b,hb,hp⟩
  · exact he.2.1 h

theorem finite_sat_rejection_no_clash (Q : Query n d) (hd : 0 < d) (path : List (Fin d))
    (hs : Satisfiable (FiniteSubtypeTrees.constructor d) Q.constraints)
    (hr : ¬ ForwardCapAutomaton.Accepts (automaton Q .right) path) :
    ¬ LabelClash (compile Q .right path) :=
  rejection_no_clash Q hd path (satisfiable_no_clash Q.constraints hs) hr

end NSSE.UnsafetyFullClashes
