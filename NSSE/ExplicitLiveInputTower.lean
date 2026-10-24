import NSSE.ExplicitPeriodMonitorSize

/-! Actual live period bound and automaton sizes from original cap input. -/

namespace NSSE.ExplicitLiveInputTower

open FiniteSOARankDecision FiniteCapFrontEnd ExplicitCapFrontEndSize
open ExplicitCapTerminalTower (size eval_exp_linear)
open DirectRankStateTower DirectRankFormulaTower PolynomialTowerEnvelope

variable {d : Nat}

theorem member_sum {α : Type*} (xs : List α) (f : α → Nat) (x : α) (hx : x ∈ xs) :
    f x ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    simp only [List.mem_cons] at hx
    simp only [List.map_cons, List.sum_cons]
    rcases hx with rfl | hx
    · omega
    · have := ih hx; omega

theorem row_counts (E : Input (Fin d)) (c : Component (Fin d)) (hc : c ∈ E.rows) :
    c.left.count ≤ size E ∧ c.right.count ≤ size E := by
  have h := member_sum E.rows (fun c => 2*c.left.count+c.right.count) c hc
  dsimp only at h
  unfold size
  omega

theorem root_bound (E : Input (Fin d)) :
    LiveShortRoot.rootBound (FiniteCapLive.rootPresentation (prepared E)) ≤ size E := by
  apply Finset.sup_le
  intro i _
  change (((prepared E).rows.get (FiniteCapLive.rowIndex (prepared E) i)).right.count) ≤ _
  have hm := List.get_mem (prepared E).rows (FiniteCapLive.rowIndex (prepared E) i)
  exact (row_counts E _ (List.mem_filter.mp hm).1).2

theorem period_bound (E : Input (Fin d)) : FiniteCapLive.bound E ≤ 2^(2*size E) := by
  have hg := (G_count E).trans (exp_mono (show (E.routes.map (fun A => A.count+1)).sum ≤ size E by unfold size; omega))
  have hr := (root_bound E).trans (self_le_exp (size E))
  simpa only [FiniteCapLive.bound, two_mul] using mul_exp hg hr

def monitorExpression : Expr := .var 0*(.var 1+(.var 2+3)*.var 0+3)

def monitorExponent (E : Input (Fin d)) := 15*(2*size E+d+1)

theorem monitor_exponent_bound (E : Input (Fin d)) (n : Nat) (hn : n ≤ size E) :
    FiniteCapLive.bound E*(n+(d+3)*FiniteCapLive.bound E+3) ≤ 2^(monitorExponent E) := by
  have hb := (period_bound E).trans (exp_mono (show 2*size E ≤ 2*size E+d+1 by omega))
  have hn' := hn.trans ((self_le_exp (size E)).trans (exp_mono (show size E ≤ 2*size E+d+1 by omega)))
  have hd := (self_le_exp d).trans (exp_mono (show d ≤ 2*size E+d+1 by omega))
  have hv : ∀ i : Fin 4, (![FiniteCapLive.bound E,n,d,0] : Fin 4 → Nat) i ≤ 2^(2*size E+d+1) := by
    intro i
    fin_cases i
    · exact hb
    · exact hn'
    · exact hd
    · exact Nat.zero_le _
  exact eval_exp_linear monitorExpression ![FiniteCapLive.bound E,n,d,0] _ (by omega) hv

theorem monitor_count (E : Input (Fin d)) (c : Component (Fin d)) (hc : c ∈ E.rows) :
    (FiniteBoundedPeriods.bounded (finEnumeration d) c.right (FiniteCapLive.bound E)).count ≤
      tower 2 (monitorExponent E) := by
  have h := ExplicitPeriodMonitorSize.bounded_exp (finEnumeration d) c.right (FiniteCapLive.bound E)
  simp only [finEnumeration, ExplicitPeriodMonitorSize.finValues_length] at h
  exact h.trans (exp_mono (monitor_exponent_bound E c.right.count (row_counts E c hc).2))

theorem periodic_count (E : Input (Fin d)) (c : Component (Fin d)) (hc : c ∈ E.rows) :
    (FiniteCapLive.periodicComponent (finEnumeration d) c (FiniteCapLive.bound E)).count ≤
      tower 3 (monitorExponent E+size E) := by
  rw [FiniteCapLive.periodicComponent, concat_count]
  apply exp_mono
  have h := Nat.add_le_add (row_counts E c hc).1 (monitor_count E c hc)
  exact h.trans (by simpa only [Nat.add_comm] using
    CountedRankEvaluationTower.add_to_tower_two (monitorExponent E) (size E))

theorem mul_tower_two (x m : Nat) : m*tower 2 x ≤ tower 2 (x+m) := by
  have h := mul_exp (self_le_exp m) (Nat.le_refl (2^(2^x)))
  exact h.trans (exp_mono (by simpa only [Nat.add_comm] using exp_add_le x m))

theorem K_count (E : Input (Fin d)) :
    (FiniteCapLive.K (finEnumeration d) E (FiniteCapLive.bound E)).count ≤
      tower 3 (monitorExponent E+3*size E) := by
  let y := monitorExponent E+size E
  have hu := mapped_unions_exp (prepared E).rows
    (fun c => FiniteCapLive.periodicComponent (finEnumeration d) c (FiniteCapLive.bound E))
    (fun _ => tower 2 y) (fun c hc => periodic_count E c (List.mem_filter.mp hc).1)
  have hr := (R_count E).trans (exp_mono (show (E.rows.map (fun c => 2*c.left.count+c.right.count)).sum ≤ size E by unfold size; omega))
  have hl : (prepared E).rows.length ≤ size E :=
    (List.length_filter_le _ _).trans (by unfold size; omega)
  have he := (Nat.mul_le_mul_right (tower 2 y) hl).trans (mul_tower_two y (size E))
  have ha : size E+(prepared E).rows.length*tower 2 y ≤ tower 2 (y+size E+size E) :=
    (Nat.add_le_add_left he (size E)).trans
    (by simpa only [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using CountedRankEvaluationTower.add_to_tower_two (y+size E) (size E))
  have hh := mul_exp hr hu
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hh
  rw [show y+size E+size E = monitorExponent E+3*size E by dsimp [y]; omega] at ha
  exact hh.trans (exp_mono ha)

/-- The actual DFA tested for nonemptiness by the live inclusion decision. -/
def inclusionDFA (E : Input (Fin d)) : InputDFA (Fin d) :=
  FiniteDFAOperations.inter (FiniteCapLive.L E)
    (FiniteDFAOperations.complement (FiniteCapLive.K (finEnumeration d) E (FiniteCapLive.bound E)))

theorem inclusion_count (E : Input (Fin d)) :
    (inclusionDFA E).count ≤ tower 3 (monitorExponent E+4*size E) := by
  have hl := (G_count E).trans (exp_mono (show (E.routes.map (fun A => A.count+1)).sum ≤ size E by unfold size; omega))
  have hh := mul_exp hl (K_count E)
  have hs : size E+tower 2 (monitorExponent E+3*size E) ≤
      tower 2 (monitorExponent E+4*size E) := by
    have ha := CountedRankEvaluationTower.add_to_tower_two (monitorExponent E+3*size E) (size E)
    rw [show monitorExponent E+3*size E+size E = monitorExponent E+4*size E by omega] at ha
    simpa only [Nat.add_comm] using ha
  exact hh.trans (exp_mono hs)

theorem inclusion_count_explicit (E : Input (Fin d)) :
    (inclusionDFA E).count ≤ tower 3 (34*size E+15*d+15) := by
  have h := inclusion_count E
  rw [show monitorExponent E+4*size E = 34*size E+15*d+15 by unfold monitorExponent; ring] at h
  exact h

theorem inclusion_accepts (E : Input (Fin d)) (xs : List (Fin d)) :
    (inclusionDFA E).automaton.Accepts xs ↔
      NonliveBorderRank.Live (G E).automaton xs ∧
        ¬ LiveShortRoot.BoundedCovered (prepared E).denote (FiniteCapLive.bound E) xs := by
  rw [inclusionDFA, FiniteDFAOperations.inter_accepts, FiniteDFAOperations.complement_accepts,
    FiniteCapLive.L_accepts, FiniteCapLive.K_accepts]

end NSSE.ExplicitLiveInputTower
