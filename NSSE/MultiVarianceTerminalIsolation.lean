import NSSE.MultiVarianceSideTokens

/-! The common virtual D terminal and the accepted Z terminal share
exactly the same raw frame. Every changed side is unpinned and isolated,
including same-rail comparisons and both temporal/support directions. -/
namespace NSSE.MultiVarianceTerminalIsolation
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceTokenExact
open MultiVarianceBranch MultiVarianceBranchLocal MultiVarianceBranchAssignment
open MultiVarianceProperTrace MultiVarianceSideTokens
open P0DZBranch P0DZTrace P0ProperWords
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}
variable (pol : Polarity arity)

def Incident (C : Parameters arity n) (w : List (Fin D)) (side : Bool) (m : Nat) : Prop :=
  ∃ a b l other, a+l≤m ∧ b+l=m ∧
    SymBirth (rawAt pol C w a) other (rawAt pol C w b) side ∧ WordMatch w a b l

theorem accepted_end (C : Parameters arity n) (w : List (Fin D)) (ha : Accepted (branch pol C D) w) :
    EndValid C (rawAt pol C w w.length) := by
  simpa only [rawAt,List.take_length] using
    local_end pol C w _ ((MultiVarianceBranchAssignment.accepted_iff pol C w).mp ha).1

theorem rays_eq (C : Parameters arity n) (w : List (Fin D)) (ha : Accepted (branch pol C D) w)
    (a b l : Nat) (s t : Bool) (hal : a+l≤w.length) (hbl : b+l≤w.length)
    (hb : SymBirth (rawAt pol C w a) s (rawAt pol C w b) t) (hm : WordMatch w a b l) :
    value pol C w s (a+l)=value pol C w t (b+l) := by
  have hr := ((MultiVarianceBranchAssignment.accepted_iff pol C w).mp ha).2
  rcases hb with hb | hb
  · exact agree_eq (hr a (by omega) b (by omega) s t hb l (by omega) hal hbl hm)
  · exact (agree_eq (hr b (by omega) a (by omega) t s hb l (by omega) hbl hal
      (fun i hi => (hm i hi).symm))).symm

theorem no_diagonal (C : Parameters arity n) (w : List (Fin D)) (ha : Accepted (branch pol C D) w)
    (a : Nat) (haN : a≤w.length) (s t : Bool) :
    ¬SymBirth (rawAt pol C w a) s (rawAt pol C w a) t := by
  intro hb
  have hst : s≠t := by
    intro he
    subst t
    exact no_same_vertex_symBirth _ s hb
  have he := rays_eq pol C w ha a a (w.length-a) s t (by omega) (by omega) hb (fun _ _ => rfl)
  rw [show a+(w.length-a)=w.length by omega] at he
  simp only [value,lt_self_iff_false,if_false] at he
  have hn := ends_distinct C _ (accepted_end pol C w ha)
  cases s <;> cases t <;> simp_all

theorem changed_isolated (C : Parameters arity n) (w : List (Fin D))
    (ha : Accepted (branch pol C D) w) (hg : GoodWord (P0DZProperMachine.machine (branch pol C D)) w)
    (side : Bool) (hne : endLabel C side≠.node (headAt pol C w w.length)) :
    ¬Incident pol C w side w.length := by
  rintro ⟨a,b,l,other,hal,hbl,hborn,hm⟩
  have halt : a+l<w.length := by
    by_contra hn
    have he : a=b := by omega
    subst b
    exact no_diagonal pol C w ha a (by omega) other side hborn
  have he := rays_eq pol C w ha a b l other side hal (by omega) hborn hm
  have hh := head_match pol C w hg a b l other side hal (by omega) hborn hm
  rw [hbl] at he hh
  simp only [value,if_pos halt,lt_self_iff_false,if_false] at he
  exact hne (he.symm.trans (congrArg Label.node hh))

theorem changed_unpinned (C : Parameters arity n) (w : List (Fin D))
    (ha : Accepted (branch pol C D) w) (hg : GoodWord (P0DZProperMachine.machine (branch pol C D)) w)
    (side : Bool) (hne : endLabel C side≠.node (headAt pol C w w.length)) :
    pins C.query.constraints (roleOf (rawAt pol C w w.length).sign side) (tokensOf (rawAt pol C w w.length) side)=∅ := by
  have hc := ((P0DZProperMachine.good_iff (branch pol C D) w).mp hg).1
  have hready := (terminal_ready pol C w (complete_nonempty _ _ ha.1) hc).1
  have hr : MultiVarianceSelectorHead.Ready C.query.constraints (rawAt pol C w w.length)
      (headAt pol C w w.length) := by
    simpa only [rawAt,headAt,List.take_length] using hready
  have he := accepted_end pol C w ha
  exact MultiVarianceSideTokens.changed_unpinned C.query.constraints _ _ _ _
    (ready_compatible _ _ _ hr side) (end_compatible C _ he side) (end_nontrivial C _ he side) hne

theorem changed_side (C : Parameters arity n) (w : List (Fin D))
    (ha : Accepted (branch pol C D) w) (hg : GoodWord (P0DZProperMachine.machine (branch pol C D)) w) :
    ∃ side, pins C.query.constraints (roleOf (rawAt pol C w w.length).sign side)
      (tokensOf (rawAt pol C w w.length) side)=∅ ∧ ¬Incident pol C w side w.length := by
  have hd := ends_distinct C _ (accepted_end pol C w ha)
  have hx : ∃ side, endLabel C side≠.node (headAt pol C w w.length) := by
    by_cases he : C.endX=.node (headAt pol C w w.length)
    · refine ⟨true,?_⟩
      intro hy
      exact hd (he.trans hy.symm)
    · exact ⟨false,he⟩
  obtain ⟨side,hs⟩ := hx
  exact ⟨side,changed_unpinned pol C w ha hg side hs,changed_isolated pol C w ha hg side hs⟩

end NSSE.MultiVarianceTerminalIsolation
