import NSSE.StoredCapFrontEnd

namespace NSSE.StoredDFAExtensions
open StoredForwardTableBuild
variable {d : Nat}

def possible (A : FiniteSOARankDecision.InputDFA (Fin d)) (k : Nat) (q : Fin A.count) : Prop :=
  ∃ f : Fin k → Fin d, A.automaton.accept (A.automaton.runFrom q (List.ofFn f))
instance (A : FiniteSOARankDecision.InputDFA (Fin d)) (k : Nat) (q : Fin A.count) :
    Decidable (possible A k q) := inferInstanceAs (Decidable (∃ f : Fin k → Fin d, A.automaton.accept (A.automaton.runFrom q (List.ofFn f))))

theorem possible_zero (A : FiniteSOARankDecision.InputDFA (Fin d)) (q : Fin A.count) :
    possible A 0 q ↔ A.automaton.accept q := by
  simp [possible]

theorem possible_succ (A : FiniteSOARankDecision.InputDFA (Fin d)) (k : Nat) (q : Fin A.count) :
    possible A (k+1) q ↔ ∃ i : Fin d, possible A k (A.automaton.step q i) := by
  simp [possible,Fin.exists_fin_succ_pi,List.ofFn_succ]

def cell (A : StoredOrdinaryDFABuild.Data) (s : List Bool) (q : Fin A.count) : Bool × Nat :=
  StoredForwardFinal.existsFin d (fun i =>
    let t := StoredDFAAccess.step A q i
    let r := StoredForwardLookup.get false s t.1
    (r.1,1+t.2+r.2))

def build (A : StoredOrdinaryDFABuild.Data) : Nat → List Bool × Nat
  | 0 => CountedFinEnumeration.tabulate A.count (StoredDFAAccess.final A)
  | k+1 =>
    let s := build A k
    let t := CountedFinEnumeration.tabulate A.count (cell (d := d) A s.1)
    (t.1,1+s.2+t.2)

def budget (n d k : Nat) := tabBudget n n+k*(1+tabBudget n (tabBudget d (2*n+d+2)))

theorem cell_bound (A : StoredOrdinaryDFABuild.Data) (h : StoredDFAProductCells.Valid (d := d) A)
    (s : List Bool) (q : Fin A.count) : (cell (d := d) A s q).2 ≤ tabBudget d (2*A.count+d+2) := by
  apply StoredForwardFinal.existsFin_bound
  intro i
  have ht := StoredDFAAccess.step_bound A q i
  have hr := (StoredForwardLookup.get_bound false s (StoredDFAAccess.step A q i).1).trans (h.step q i)
  dsimp only
  omega

theorem bound (A : StoredOrdinaryDFABuild.Data) (h : StoredDFAProductCells.Valid (d := d) A) (k : Nat) :
    (build (d := d) A k).2 ≤ budget A.count d k := by
  induction k with
  | zero => simpa only [build,budget,Nat.zero_mul,Nat.add_zero] using CountedFinEnumeration.tabulate_bound A.count _ A.count (StoredDFAAccess.final_bound A)
  | succ k ih =>
    have ht := CountedFinEnumeration.tabulate_bound A.count (cell (d := d) A (build (d := d) A k).1)
      (tabBudget d (2*A.count+d+2)) (cell_bound A h _)
    simp only [build,budget] at *
    dsimp only [tabBudget] at *
    nlinarith

theorem value (A : FiniteSOARankDecision.InputDFA (Fin d)) (k : Nat) :
    (build (d := d) (StoredOrdinaryDFABuild.snapshot A) k).1 =
      List.ofFn (fun q => decide (possible A k q)) := by
  induction k with
  | zero =>
    simp only [build,CountedFinEnumeration.tabulate_value,StoredDFAAccess.final,
      StoredOrdinaryDFABuild.snapshot,StoredForwardLookup.get_ofFn,possible_zero]
  | succ k ih =>
    simp only [build,CountedFinEnumeration.tabulate_value,ih]
    apply congrArg List.ofFn
    funext q
    apply Bool.eq_iff_iff.mpr
    simp only [cell,StoredForwardFinal.existsFin_value,StoredDFAAccess.step_snapshot,
      StoredForwardLookup.get_ofFn,decide_eq_true_eq,possible_succ]
end NSSE.StoredDFAExtensions
