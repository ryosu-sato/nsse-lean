import NSSE.MultiVarianceLabelBounds

/-! Exhaustive origins of actual Bottom/Top assertions: the shared fill
or a terminal rail whose specified label is that extremum. -/
namespace NSSE.MultiVarianceSpineAssertions
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceGlobal MultiVarianceSpineSeparation
open MultiVarianceSpineRows MultiVarianceTokenExact MultiVarianceSpineSuffixes
open MultiVarianceLiteralGeometry MultiVarianceLabelBounds
variable {H : Type*} {arity : H → Nat}

def fillGlobal (s : Spine arity) (upper : Bool) : Fin (width s.depth) :=
  if upper then bottomAt s.depth else topAt s.depth

theorem shift_fill (h : H) (i : Fin (arity h)) (s : Spine arity) (r : Bool) :
    shift s.depth (fillGlobal s r) = fillGlobal (.step h i s) r := by
  cases r <;> simp only [fillGlobal,Bool.false_eq_true,if_false,if_true,Spine.depth,shift_bottom,shift_top]

theorem shift_rail (h : H) (i : Fin (arity h)) (s : Spine arity)
    (d : Nat) (hd : d ≤ s.depth) (hn : d+1 ≤ (Spine.step h i s).depth) (r : Bool) :
    shift s.depth (railSlot s d hd r) = railSlot (.step h i s) (d+1) hn r := by
  apply Fin.ext
  simp only [shift,railSlot,Fin.val_mk]
  omega

variable (pol : Polarity arity)

theorem assertions_stop (a b : Label H) (r : Bool) (k : Fin 4) :
    k ∈ assertions (compile pol (.stop a b : Spine arity)) r ↔
      k=fillGlobal (.stop a b : Spine arity) r ∨
        (k=railSlot (.stop a b : Spine arity) 0 (Nat.zero_le _) r ∧
          label (.stop a b : Spine arity) r = extreme r) := by
  cases r <;> cases a <;> cases b <;>
    simp [assertions,compile,MultiVarianceFlatStop.stopConstraints,
      MultiVarianceFlatStop.topAssertions,MultiVarianceFlatStop.bottomAssertions,
      fillGlobal,railSlot,topAt,bottomAt,parity,label,extreme,Spine.depth,or_comm]

theorem assertions_step (h : H) (i : Fin (arity h)) (s : Spine arity) (r : Bool) :
    assertions (compile pol (.step h i s)) r =
      fillGlobal (.step h i s) r :: (assertions (compile pol s) r).map (shift s.depth) := by
  cases r <;> simp only [assertions,compile,combine,remap,MultiVarianceFlatStep.stepConstraints,
    Bool.false_eq_true,if_false,if_true,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    stepEmbed_bot,stepEmbed_top,fillGlobal,Spine.depth]

theorem assertion_origin (s : Spine arity) (r : Bool) (k : Fin (width s.depth)) :
    k ∈ assertions (compile pol s) r ↔ k=fillGlobal s r ∨
      ∃ d, ∃ hd : d ≤ s.depth, k=railSlot s d hd r ∧ label (suffix s d) r=extreme r := by
  induction s with
  | stop a b =>
    rw [assertions_stop]
    constructor
    · rintro (hf | ⟨hk,hl⟩)
      · exact Or.inl hf
      · exact Or.inr ⟨0,Nat.zero_le _,hk,hl⟩
    · rintro (hf | ⟨d,hd,hk,hl⟩)
      · exact Or.inl hf
      · have hz : d=0 := by change d ≤ 0 at hd; omega
        subst d
        exact Or.inr ⟨hk,hl⟩
  | step h i s ih =>
    rw [assertions_step,List.mem_cons]
    constructor
    · rintro (hf | ht)
      · exact Or.inl hf
      · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ht
        rcases (ih v).mp hv with hf | ⟨d,hd,hk,hl⟩
        · exact Or.inl (by rw [hf,shift_fill])
        · have hn : d+1 ≤ (Spine.step h i s).depth := by change d+1 ≤ s.depth+1; omega
          exact Or.inr ⟨d+1,hn,by rw [hk,shift_rail h i s d hd hn r],hl⟩
    · rintro (hf | ⟨d,hd,hk,hl⟩)
      · exact Or.inl hf
      · apply Or.inr
        cases d with
        | zero => cases r <;> simp [suffix,label,extreme] at hl
        | succ d =>
          have ht : d ≤ s.depth := by change d+1 ≤ s.depth+1 at hd; omega
          apply List.mem_map.mpr
          refine ⟨railSlot s d ht r,(ih _).mpr (Or.inr ⟨d,ht,rfl,hl⟩),?_⟩
          exact (shift_rail h i s d ht hd r).trans hk.symm

end NSSE.MultiVarianceSpineAssertions
