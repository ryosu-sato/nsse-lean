import NSSE.GeneralCopyGrid

/-! Combinatorial parts of the free-frontier argument. The semantic step
from a shortest counterseed to its forward witness is not assumed proved here.
-/
namespace NSSE.FreeFrontierCopyTail
open PeriodicCopyHeadNormalization GeneralCopyGrid
variable {V H I : Type*}

def EmptyAfter (q : Nat → Annotation V H I) (F : Nat) : Prop :=
  ∀ j, F < j → (q j).upper = ∅

theorem birth_before_frontier (q : Nat → Annotation V H I) (F a b : Nat)
    (he : EmptyAfter q F) (hb : Born q a b) : a ≤ F := by
  by_contra h
  obtain ⟨v,hv,_⟩ := hb
  rw [he a (by omega)] at hv
  exact hv

theorem source_bound (q : Nat → Annotation V H I) (F N k j : Nat)
    (he : EmptyAfter q F) (ha : Active q N k j) : j ≤ k+F := by
  obtain ⟨_,a,b,r,ha,hb,hr⟩ := (active_iff_ray q N k j).mp ha
  have hbound := birth_before_frontier q F a b he hr.1
  omega

theorem ray_prefix (q : Nat → Annotation V H I) (a b r s : Nat)
    (hr : Ray q a b r) (hs : s ≤ r) : Ray q a b s :=
  ⟨hr.1,fun t ht => hr.2 t (by omega)⟩

/-- Proper copy sources have the head of the row they contribute to. -/
def ProperCoherent (q : Nat → Annotation V H I) (N : Nat) : Prop :=
  ∀ k j, k < N → j < N → Active q N k j → (q j).head = (q k).head

/-- A forward copy reaching the last proper source forces a periodic tail:
indices agree through N-2, heads through N-1. The final exit index is free. -/
theorem last_forward_period (q : Nat → Annotation V H I) (F N : Nat)
    (he : EmptyAfter q F) (hc : ProperCoherent q N)
    (hw : ∃ k, k < N-1 ∧ Active q N k (N-1)) :
    ∃ a b r, b < a ∧ a ≤ F ∧ a+r = N-1 ∧ Ray q a b r ∧
      (∀ s, s ≤ r → (q (a+s)).head = (q (b+s)).head) := by
  obtain ⟨k,hk,ha⟩ := hw
  obtain ⟨_,a,b,r,has,hbt,hr⟩ := (active_iff_ray q N k (N-1)).mp ha
  have hf := birth_before_frontier q F a b he hr.1
  refine ⟨a,b,r,by omega,hf,has,hr,?_⟩
  intro s hs
  apply hc (b+s) (a+s) (by omega) (by omega)
  exact (active_iff_ray q N (b+s) (a+s)).mpr
    ⟨by omega,a,b,s,rfl,rfl,ray_prefix q a b r s hr hs⟩

/-- The label needed when a normalized copy is advanced by one last step. -/
def lookAhead (q : Nat → Annotation V H I) (j : Nat) : Annotation V (I × H) I :=
  ⟨(q j).upper,(q j).lower,((q j).index,(q (j+1)).head),(q j).index⟩

theorem lookAhead_phase (q : Nat → Annotation V H I) (T P : Nat)
    (hq : PhasePeriodic q T P) : PhasePeriodic (lookAhead q) T P := by
  intro a b ha hb hm
  unfold lookAhead
  rw [hq a b ha hb hm, hq (a+1) (b+1) (by omega) (by omega) (hm.add_right 1)]

/-- Before the final exit, normalize while preserving BOTH the source index
and its following head. Absence of a diagonal copy forces the replacement
source to remain strictly before the final proper position L. -/
theorem normalize_before_exit (q : Nat → Annotation V H I) (T P L a b r : Nat)
    (hp : 0 < P) (hq : PhasePeriodic q T P)
    (hs : a+r < L) (ht : b+r = L) (hr : Ray q a b r)
    (hn : ¬ Active q L L L) :
    ∃ a' b' r', a'+r' < L ∧ b'+r' = L ∧ Ray q a' b' r' ∧
      (q (a'+r')).index = (q (a+r)).index ∧
      (q (a'+r'+1)).head = (q (a+r+1)).head ∧
      (Near (T+P) a' b' ∨ r' ≤ T+P) := by
  have hrl : Ray (lookAhead q) a b r := hr
  obtain ⟨a',b',r',hs',ht',hr',hh',hb'⟩ :=
    normalize (lookAhead q) T P L a b r hp (lookAhead_phase q T P hq)
      (by omega) (by omega) hrl
  have hsource : a'+r' < L := by
    by_contra h
    have eq : a'+r' = L := by omega
    apply hn
    exact (active_iff_ray q L L L).mpr ⟨by omega,a',b',r',eq,by omega,hr'⟩
  exact ⟨a',b',r',hsource,by omega,hr',congrArg Prod.fst hh',congrArg Prod.snd hh',hb'⟩

/-- One further matching-index step costs at most one unit of propagation
budget and no additional distance. This is the endpoint-exit correction. -/
theorem advance_retained (q : Nat → Annotation V H I) (N B a b r : Nat)
    (hs : a+r+1 ≤ N) (hr : Ray q a b r)
    (hi : (q (a+r)).index = (q (b+r)).index)
    (hb : Near B a b ∨ r ≤ B) :
    Retained q N B (B+1) (b+r+1) (a+r+1) := by
  refine ⟨hs,a,b,r+1,by omega,by omega,(ray_succ q a b r).mpr ⟨hr,hi⟩,?_⟩
  rcases hb with hn | hl
  · exact Or.inl hn
  · exact Or.inr (by omega)

end NSSE.FreeFrontierCopyTail
