import NSSE.MultiVarianceProperTrace

/-! Physical-side token facts use the current raw sign. A changed,
nontrivial separating terminal has no pin; token loss is independent
of later sign reversals. -/
namespace NSSE.MultiVarianceSideTokens
open MultiConstructorConstraints (Constraints)
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceTokenExact
open MultiVarianceSelectorHead MultiVarianceBranch MultiVarianceProperTrace
open MultiVarianceClashCharacterization MultiVarianceLabelBounds
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

def endLabel (C : Parameters arity n) (s : Bool) : Label H := if s then C.endY else C.endX

def Nontrivial (r : Bool) (a : Label H) : Prop := if r then a≠.top else a≠.bot

theorem compatible_pin_bound (phi : Constraints arity n) (r : Bool) (S : MultiVarianceModelTokens.Tokens n)
    (a : Label H) (k : H) (hc : Compatible phi r S a) (hp : k∈pins phi r S) :
    if r then (.node k : Label H)≤a else a≤.node k := by
  obtain ⟨b,hb,hm,rfl⟩ := (mem_pins phi r S k).mp hp
  have hbound : LabelBound phi (!r) b.parent (.node b.head) := by
    apply Or.inl
    exact ⟨b,by cases r <;> exact hb,rfl,rfl⟩
  exact hc b.parent hm (.node b.head) hbound

theorem changed_unpinned (phi : Constraints arity n) (r : Bool) (S : MultiVarianceModelTokens.Tokens n)
    (h : H) (a : Label H) (hc : Compatible phi r S (.node h)) (ha : Compatible phi r S a)
    (ht : Nontrivial r a) (hne : a≠.node h) : pins phi r S=∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro k hk
  have hh := compatible_pin phi r S h k hc hk
  have hb := compatible_pin_bound phi r S a k ha hk
  subst k
  cases r <;> cases a <;> simp_all [Nontrivial]

omit [DecidableEq H] in
theorem end_nontrivial (C : Parameters arity n) (F : Frame n) (he : EndValid C F) (s : Bool) :
    Nontrivial (roleOf F.sign s) (endLabel C s) := by
  have hn := he.2.2
  cases hs : F.sign <;> cases s <;>
    simp only [Nontrivial,endLabel,roleOf,hs,Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true] at hn ⊢
  · intro hh; rw [hh] at hn; exact hn bot_le
  · intro hh; rw [hh] at hn; exact hn le_top
  · intro hh; rw [hh] at hn; exact hn le_top
  · intro hh; rw [hh] at hn; exact hn bot_le

omit [DecidableEq H] in
theorem end_compatible (C : Parameters arity n) (F : Frame n) (he : EndValid C F) (s : Bool) :
    Compatible C.query.constraints (roleOf F.sign s) (tokensOf F s) (endLabel C s) := by
  cases s
  · exact he.1
  · exact he.2.1

omit [DecidableEq H] in
theorem ready_compatible (phi : Constraints arity n) (F : Frame n) (h : H)
    (hr : MultiVarianceSelectorHead.Ready phi F h) (s : Bool) :
    Compatible phi (roleOf F.sign s) (tokensOf F s) (.node h) := by
  cases s
  · exact hr.1
  · exact hr.2

theorem empty_no_symBirth (F : Frame n) (s : Bool) (G : Frame n) (t : Bool)
    (he : tokensOf G t=∅) : ¬SymBirth F s G t := by
  simp only [SymBirth,RawBirth,inspectBirth,he,Finset.inter_empty,Finset.empty_inter,
    Finset.not_nonempty_empty,decide_false,Bool.and_false,Bool.false_eq_true,or_self,not_false_eq_true]

variable (pol : Polarity arity)

theorem move_tokens (phi : Constraints arity n) (F : Frame n) (h : H) (i : Fin (arity h)) (s : Bool) :
    tokensOf (physicalMove pol phi F h i) s = advance pol phi (roleOf F.sign s) (tokensOf F s) h i := by
  cases s <;> rfl

theorem move_empty (phi : Constraints arity n) (F : Frame n) (h : H) (i : Fin (arity h)) (s : Bool)
    (he : tokensOf F s=∅) : tokensOf (physicalMove pol phi F h i) s=∅ := by
  rw [move_tokens,he,advance_empty]

theorem move_loss (phi : Constraints arity n) (F : Frame n) (h : H) (i : Fin (arity h)) (s : Bool)
    (hp : pins phi (roleOf F.sign s) (tokensOf F s)=∅) :
    tokensOf (physicalMove pol phi F h i) s=∅ := by
  rw [move_tokens]
  exact advance_of_no_pin pol phi _ _ h i (by rw [hp]; exact Finset.not_mem_empty _)

end NSSE.MultiVarianceSideTokens
