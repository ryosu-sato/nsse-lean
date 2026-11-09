import NSSE.P0LayoutSeams
import NSSE.P0ModuleCut

/-! All-position Entry for four equal-profile union children. Every
retained partner is handled, including unselected children and positions
outside the parent module. No new-word safety premise is assumed. -/
namespace NSSE.P0FourGroupEntry
open P0HomogeneousOrder P0SignedLayout P0LayoutCuts P0LayoutWordCut P0LayoutSeams
open P0DDeadReader P0DDeadColor P0ModuleCut P0CutComparison
variable {Q A H : Type*} {m : Nat}

def InRow (G : Grid m) (r : Fin 4) (p : Nat) : Prop := ∃ i, i < m ∧ p = G.pos r i

def EqualMatrices (J : Reader Q A H) (w : List A) (G : Grid m) : Prop :=
  ∀ r s i j, i < m → j < m → i ≠ j →
    (Compatible w (leftAt J w) (rightAt J w) (G.pos r i) (G.pos r j) ↔
      Compatible w (leftAt J w) (rightAt J w) (G.pos s i) (G.pos s j))

def UnionSeparated (J : Reader Q A H) (w : List A) (U : Finset Nat) (G : Grid m) : Prop :=
  ∀ r i, i < m → ∀ p ∈ U, ¬ InRow G r p →
    Compatible w (leftAt J w) (rightAt J w) (G.pos r i) p ∧
      Compatible w (leftAt J w) (rightAt J w) p (G.pos r i)

theorem one_seam (J : Reader Q A H) (w : List A) (U : Finset Nat) (G : Grid m)
    {L : List (Nat × Bool)} (h : Layout G 0 m L)
    (hb : ∀ r i, i < m → G.pos r i ≤ w.length)
    (hin : ∀ r i, i < m → G.pos r i ∈ U)
    (hu : P0LayoutReader.UniformStates J w G) (hm : ColoredModule J w U)
    (he : EqualMatrices J w G) (hc : UnionSeparated J w U G)
    (a b : Nat) (ha : a ≤ P0IntervalMap.length (family G h le_rfl w.length hb))
    (hb' : b ≤ P0IntervalMap.length (family G h le_rfl w.length hb)) (hne : a ≠ b)
    (hs : Seam (layoutCut w G h hb) a) :
    (Compatible w (leftAt J w) (rightAt J w)
        ((layoutCut w G h hb).source a) ((layoutCut w G h hb).source b) →
      Compatible w (leftAt J w) (rightAt J w)
        ((layoutCut w G h hb).lift a) ((layoutCut w G h hb).lift b)) ∧
    (Compatible w (leftAt J w) (rightAt J w)
        ((layoutCut w G h hb).source b) ((layoutCut w G h hb).source a) →
      Compatible w (leftAt J w) (rightAt J w)
        ((layoutCut w G h hb).lift b) ((layoutCut w G h hb).lift a)) := by
  classical
  let C := layoutCut w G h hb
  obtain ⟨s,i,hi,hsa,hta⟩ := seam_shape w G h hb a ha hs
  change C.source a = G.pos (sourceGroup s) i at hsa
  change C.lift a = G.pos (targetGroup s) i at hta
  by_cases hbu : C.lift b ∈ U
  · by_cases hbr : InRow G (targetGroup s) (C.lift b)
    · obtain ⟨j,hj,htb⟩ := hbr
      have hsb := retained_middle_source w G h hb b hb' (targetGroup s) (target_middle s) j hj htb
      rw [outer_target] at hsb
      have hij : i ≠ j := by
        intro hij
        subst j
        exact hne (C.lift_injective a b ha hb' (hta.trans htb.symm))
      have hf := he (sourceGroup s) (targetGroup s) i j hi hj hij
      have hr := he (sourceGroup s) (targetGroup s) j i hj hi (Ne.symm hij)
      change C.source b = G.pos (sourceGroup s) j at hsb
      change (_ → _) ∧ (_ → _)
      simp only [show layoutCut w G h hb = C from rfl,hsa,hsb,hta,htb]
      exact ⟨hf.mp,hr.mp⟩
    · have hh := hc (targetGroup s) i hi (C.lift b) hbu hbr
      constructor
      · intro _
        change Compatible w (leftAt J w) (rightAt J w) (C.lift a) (C.lift b)
        rw [hta]
        exact hh.1
      · intro _
        change Compatible w (leftAt J w) (rightAt J w) (C.lift b) (C.lift a)
        rw [hta]
        exact hh.2
  · have hsb : C.source b = C.lift b := by
      by_contra hn
      obtain ⟨t,j,hj,_,ht⟩ := seam_shape w G h hb b hb' hn
      exact hbu (ht ▸ hin (targetGroup t) j hj)
    have hh := hm (G.pos (sourceGroup s) i) (hin _ _ hi)
      (G.pos (targetGroup s) i) (hin _ _ hi) (hu _ _ i hi)
      (C.lift b) (C.lift_le b hb') hbu
    change (_ → _) ∧ (_ → _)
    simp only [show layoutCut w G h hb = C from rfl,hsa,hsb,hta]
    exact ⟨hh.1.mp,hh.2.mp⟩

theorem entry (J : Reader Q A H) (w : List A) (U : Finset Nat) (G : Grid m)
    {L : List (Nat × Bool)} (h : Layout G 0 m L)
    (hb : ∀ r i, i < m → G.pos r i ≤ w.length)
    (hin : ∀ r i, i < m → G.pos r i ∈ U)
    (hu : P0LayoutReader.UniformStates J w G) (hm : ColoredModule J w U)
    (he : EqualMatrices J w G) (hc : UnionSeparated J w U G) :
    Entry (layoutCut w G h hb) (leftAt J w) (rightAt J w) := by
  intro a ha b hb' hne hs hcomp
  rcases hs with hs | hs
  · exact (one_seam J w U G h hb hin hu hm he hc a b ha hb' hne hs).1 hcomp
  · exact (one_seam J w U G h hb hin hu hm he hc b a hb' ha (Ne.symm hne) hs).2 hcomp

theorem shorten (J : Reader Q A H) (w : List A) (U : Finset Nat) (G : Grid m)
    (hmpos : 0 < m) (hb : ∀ r i, i < m → G.pos r i ≤ w.length)
    (hin : ∀ r i, i < m → G.pos r i ∈ U)
    (hu : P0LayoutReader.UniformStates J w G) (hm : ColoredModule J w U)
    (he : EqualMatrices J w G) (hc : UnionSeparated J w U G)
    (hends : J.endX ≠ J.endY) (hw : Accepted J w) :
    ∃ v, Accepted J v ∧ v.length < w.length := by
  obtain ⟨L,hL,_,_⟩ := whole_layout G
  let F := family G hL le_rfl w.length hb
  refine ⟨(layoutCut w G hL hb).word,?_⟩
  exact P0FamilyWordCut.accepted_word J w F (family_nonempty G hL le_rfl _ hb hmpos)
    hends hw (family_loops J w hw.1 G hL le_rfl hb hu)
    (entry J w U G hL hb hin hu hm he hc)

end NSSE.P0FourGroupEntry
