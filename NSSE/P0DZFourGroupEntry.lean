import NSSE.P0DZLayout
import NSSE.P0FourGroupEntry

/-! Full four-rail Entry for an actual signed-layout deletion from four
equal-profile union children. Every retained partner is handled. -/
namespace NSSE.P0DZFourGroupEntry
open P0HomogeneousOrder P0SignedLayout P0LayoutCuts P0LayoutWordCut P0LayoutSeams
open P0DZBranch P0DZRankColor P0DZCotree P0DZLayout P0DZCutSafety P0SuffixRank
open P0CutComparison (Seam)
open P0FourGroupEntry (InRow)
variable {Q Z A H : Type*} [DecidableEq Q] [DecidableEq A] {m : Nat}

def EqualMatrices (J : Branch Q Z A H) (w : List A) (G : Grid m) : Prop :=
  ∀ r s i j, i < m → j < m → i ≠ j → ∀ x y,
    (Compatible J w (G.pos r i) x (G.pos r j) y ↔
      Compatible J w (G.pos s i) x (G.pos s j) y)

def UnionSeparated (J : Branch Q Z A H) (w : List A) (U : Finset Nat) (G : Grid m) : Prop :=
  ∀ r i, i < m → ∀ p ∈ U, ¬ InRow G r p → ∀ x y,
    Compatible J w (G.pos r i) x p y ∧ Compatible J w p x (G.pos r i) y

theorem one_seam (J : Branch Q Z A H) (w : List A) (U : Finset Nat) (G : Grid m)
    {L : List (Nat × Bool)} (h : Layout G 0 m L)
    (hb : ∀ r i, i < m → G.pos r i ≤ w.length)
    (hin : ∀ r i, i < m → G.pos r i ∈ U)
    (hu : UniformColors J w G) (hm : ColoredModule J w U)
    (he : EqualMatrices J w G) (hc : UnionSeparated J w U G)
    (a b : Nat) (ha : a ≤ P0IntervalMap.length (family G h le_rfl w.length hb))
    (hb' : b ≤ P0IntervalMap.length (family G h le_rfl w.length hb)) (hne : a ≠ b)
    (hs : Seam (layoutCut w G h hb) a) (x y : Bool) :
    (Compatible J w ((layoutCut w G h hb).source a) x ((layoutCut w G h hb).source b) y →
      Compatible J w ((layoutCut w G h hb).lift a) x ((layoutCut w G h hb).lift b) y) ∧
    (Compatible J w ((layoutCut w G h hb).source b) x ((layoutCut w G h hb).source a) y →
      Compatible J w ((layoutCut w G h hb).lift b) x ((layoutCut w G h hb).lift a) y) := by
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
      have hf := he (sourceGroup s) (targetGroup s) i j hi hj hij x y
      have hr := he (sourceGroup s) (targetGroup s) j i hj hi (Ne.symm hij) x y
      change C.source b = G.pos (sourceGroup s) j at hsb
      change (_ → _) ∧ (_ → _)
      simp only [show layoutCut w G h hb = C from rfl,hsa,hsb,hta,htb]
      exact ⟨hf.mp,hr.mp⟩
    · have hh := hc (targetGroup s) i hi (C.lift b) hbu hbr x y
      constructor
      · intro _
        change Compatible J w (C.lift a) x (C.lift b) y
        rw [hta]
        exact hh.1
      · intro _
        change Compatible J w (C.lift b) x (C.lift a) y
        rw [hta]
        exact hh.2
  · have hsb : C.source b = C.lift b := by
      by_contra hn
      obtain ⟨t,j,hj,_,ht⟩ := seam_shape w G h hb b hb' hn
      exact hbu (ht ▸ hin (targetGroup t) j hj)
    have hh := hm (G.pos (sourceGroup s) i) (hin _ _ hi)
      (G.pos (targetGroup s) i) (hin _ _ hi) (hu _ _ i hi)
      (C.lift b) (C.lift_le b hb') hbu x y
    change (_ → _) ∧ (_ → _)
    simp only [show layoutCut w G h hb = C from rfl,hsa,hsb,hta]
    exact ⟨hh.1.mp,hh.2.mp⟩

theorem entry (J : Branch Q Z A H) (w : List A) (U : Finset Nat) (G : Grid m)
    {L : List (Nat × Bool)} (h : Layout G 0 m L)
    (hb : ∀ r i, i < m → G.pos r i ≤ w.length)
    (hin : ∀ r i, i < m → G.pos r i ∈ U)
    (hu : UniformColors J w G) (hm : ColoredModule J w U)
    (he : EqualMatrices J w G) (hc : UnionSeparated J w U G) :
    FullEntry (layoutCut w G h hb) J := by
  intro x y a ha b hb' hne hs hcomp
  rcases hs with hs | hs
  · exact (one_seam J w U G h hb hin hu hm he hc a b ha hb' hne hs x y).1 hcomp
  · exact (one_seam J w U G h hb hin hu hm he hc b a hb' ha (Ne.symm hne) hs x y).2 hcomp

theorem shorten (J : Branch Q Z A H) (w : List A) (U : Finset Nat) (G : Grid m)
    (hmpos : 0 < m) (hb : ∀ r i, i < m → G.pos r i ≤ w.length)
    (hin : ∀ r i, i < m → G.pos r i ∈ U)
    (hu : UniformColors J w G) (hm : ColoredModule J w U)
    (he : EqualMatrices J w G) (hc : UnionSeparated J w U G)
    (hends : J.endX ≠ J.endY) (hw : Accepted J w) :
    ∃ v, Accepted J v ∧ v.length < w.length ∧ maxRank J v ≤ maxRank J w := by
  obtain ⟨L,hL,_,_⟩ := whole_layout G
  let F := family G hL le_rfl w.length hb
  have hl := family_states J w hw.1 G hL le_rfl hb hu
  have he' := entry J w U G hL hb hin hu hm he hc
  have hh := accepted_family J w F (family_nonempty G hL le_rfl _ hb hmpos) hends hw hl he'
  exact ⟨(layoutCut w G hL hb).word,hh.1,hh.2,P0DZCutRank.family_rank J w F hw.1 hends hl he'⟩

end NSSE.P0DZFourGroupEntry
