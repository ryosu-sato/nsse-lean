import NSSE.StoredPrefixCoreBuild

namespace NSSE.StoredNormalizationBuild
open StoredForwardTableBuild
variable {d : Nat}

structure Data where
  rows : List StoredNormalizationRows.Row
  routes : List StoredOrdinaryDFABuild.Data
  deriving BEq

def snapshot (E : FiniteCapFrontEnd.Input (Fin d)) : Data :=
  ⟨E.rows.map StoredNormalizationRows.snapshot,E.routes.map StoredOrdinaryDFABuild.snapshot⟩

def epsilon (d : Nat) : StoredOrdinaryDFABuild.Data × Nat :=
  let t := StoredOrdinaryDFABuild.rows 2 d (fun _ _ => (1,1))
  (⟨2,0,t.1,[true,false]⟩,4+t.2)

theorem epsilon_value (d : Nat) : (epsilon d).1 =
    StoredOrdinaryDFABuild.snapshot (ForwardCapNormalization.epsilon (α := Fin d)) := by
  simp only [epsilon,StoredOrdinaryDFABuild.rows_value,StoredOrdinaryDFABuild.snapshot,ForwardCapNormalization.epsilon]
  rfl

theorem epsilon_bound (d : Nat) : (epsilon d).2 ≤ 4+tabBudget 2 (tabBudget d 1) :=
  Nat.add_le_add_left (StoredOrdinaryDFABuild.rows_bound 2 d 1 (fun _ _ => (1,1)) (fun _ _ => le_rfl)) 4

theorem ordinary_start (A : StoredForwardAutomatonBuild.Data) (h : A.start<A.count) :
    (StoredOrdinaryDFABuild.build (d := d) A h).1.start < (StoredOrdinaryDFABuild.build (d := d) A h).1.count := by
  rw [StoredOrdinaryDFABuild.value]
  exact (ForwardCapNormalization.ordinaryDFA (StoredForwardAutomatonAccess.input (d := d) A h)).automaton.start.isLt

def build (A : StoredForwardAutomatonBuild.Data) (h : A.start<A.count) : Data × Nat :=
  let o := StoredOrdinaryDFABuild.build (d := d) A h
  let p := StoredPrefixCoreBuild.build (d := d) o.1 (ordinary_start A h)
  let u := StoredUniversalCoreBuild.build (d := d) o.1
  let r := StoredNormalizationRows.build (d := d) A h
  let e := epsilon d
  (⟨⟨p.1,e.1⟩::r.1,[u.1]⟩,4+o.2+p.2+u.2+r.2+e.2)

def budget (n d : Nat) := 4+StoredOrdinaryDFABuild.budget n d+
  StoredPrefixCoreBuild.budget (2^n) d+StoredUniversalCoreBuild.budget (2^n) d+
  StoredNormalizationRows.budget n d+(4+tabBudget 2 (tabBudget d 1))

theorem bound (A : StoredForwardAutomatonBuild.Data) (h : A.start<A.count) :
    (build (d := d) A h).2 ≤ budget A.count d := by
  have ho := StoredOrdinaryDFABuild.bound (d := d) A h
  have hp := StoredPrefixCoreBuild.bound (d := d) (StoredOrdinaryDFABuild.build (d := d) A h).1 (ordinary_start A h)
  have hu := StoredUniversalCoreBuild.bound (d := d) (StoredOrdinaryDFABuild.build (d := d) A h).1
  have hr := StoredNormalizationRows.bound (d := d) A h
  have he := epsilon_bound d
  have hc : (StoredOrdinaryDFABuild.build (d := d) A h).1.count = 2^A.count := by
    exact CountedModelDepth.powTwo_value A.count
  rw [hc] at hp hu
  simp only [build,budget]; omega

theorem value (A : StoredForwardAutomatonBuild.Data) (h : A.start<A.count) :
    (build (d := d) A h).1 = snapshot
      (ForwardCapNormalization.normalize (StoredForwardAutomatonAccess.input (d := d) A h)) := by
  simp only [build,StoredOrdinaryDFABuild.value,StoredPrefixCoreBuild.value,StoredUniversalCoreBuild.value,
    StoredNormalizationRows.value,epsilon_value,snapshot,ForwardCapNormalization.normalize,
    List.tail_cons,List.map_cons,List.map_nil,StoredNormalizationRows.snapshot,ForwardCapNormalization.coreRow]
end NSSE.StoredNormalizationBuild
