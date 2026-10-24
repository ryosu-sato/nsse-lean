import NSSE.Cap
import NSSE.SOA
import Lean.Elab.Tactic.Omega

/-!
# Concrete suffix-occurrence avoidance instances

This module connects the abstract shortest-avoider core in `NSSE.SOA` to
the concrete SOA semantics used by `soa_decidability_proof.md`.
-/

namespace NSSE

universe u

/-- A finite SOA instance: one regular-candidate predicate and finitely
many `(anchor, root)` rows.  Regular presentations are supplied later by
automata; the semantic layer only needs their languages. -/
structure SOAInstance (α : Type u) where
  candidate : Language α
  rows : List (CapComponent α)

namespace SOAInstance

/-- One row covers a word precisely when it has the marked suffix
occurrence from Theorem 9.1. -/
def RowCovers (row : CapComponent α) (w : Word α) : Prop :=
  MarkedOccurrence row w

/-- Original `w = a b c`, `b c = c d` presentation of one SOA row. -/
def EquationRowCovers (row : CapComponent α) (w : Word α) : Prop :=
  ∃ a b c d,
    w = a ++ b ++ c ∧
    b ≠ [] ∧ c ≠ [] ∧
    row.left a ∧ row.right b ∧
    b ++ c = c ++ d

theorem equation_witness_equal_outer_lengths
    {b c d : Word α} (h : b ++ c = c ++ d) :
    b.length = d.length := by
  have hlen := congrArg List.length h
  simp only [List.length_append] at hlen
  omega

def RootCov (I : SOAInstance α) (w : Word α) : Prop :=
  ∃ row ∈ I.rows, RowCovers row w

def Avoider (I : SOAInstance α) (w : Word α) : Prop :=
  I.candidate w ∧ ¬ I.RootCov w

/-- Canonical positive root queries retain the concrete row. -/
def RootQuery (I : SOAInstance α) (row : CapComponent α)
    (w : Word α) : Prop :=
  row ∈ I.rows ∧ RowCovers row w

theorem rootCov_iff_exists_rootQuery (I : SOAInstance α) (w : Word α) :
    I.RootCov w ↔ ∃ row, I.RootQuery row w := by
  rfl

/-- The cut-coordinate form of one concrete SOA row witness. -/
theorem rowCovers_iff_cuts (row : CapComponent α) (w : Word α) :
    RowCovers row w ↔
      ∃ j t,
        j < t ∧ t < w.length ∧
        row.left (w.take j) ∧
        row.right (Word.factor w j (t - j)) ∧
        OccursSuffixAt w j t := by
  rfl

/-- Equivalent periodic-witness coordinates `(j,p,e)`. -/
theorem rowCovers_iff_periodicWitness
    (row : CapComponent α) (w : Word α) :
    RowCovers row w ↔ PeriodicWitness row w :=
  (periodicWitness_iff_markedOccurrence row w).symm

theorem periodicWitness_iff_equationRowCovers
    (row : CapComponent α) (w : Word α) :
    PeriodicWitness row w ↔ EquationRowCovers row w := by
  constructor
  · rintro ⟨j, p, e, hp, he, hlen, hleft, hright, hcopy⟩
    let s := w.drop j
    let a := w.take j
    let b := s.take p
    let c := s.drop p
    let d := s.drop e
    have hslen : s.length = p + e := by
      simp only [s, List.length_drop]
      omega
    have hclen : c.length = e := by
      simp only [c, List.length_drop, hslen]
      omega
    have hc : c ≠ [] := List.length_pos_iff.mp (by omega)
    have hb : b ≠ [] := by
      have hblen : b.length = p := by
        simp only [b, List.length_take, hslen]
        omega
      exact List.length_pos_iff.mp (by omega)
    have hoff : w.length - e = j + p := by omega
    have hcopyS : s.take e = c := by
      unfold Word.WitnessCopy Word.factor Word.suffix at hcopy
      simp only [hoff] at hcopy
      simpa [s, c, List.drop_drop, Nat.add_comm] using hcopy
    refine ⟨a, b, c, d, ?_, hb, hc, ?_, ?_, ?_⟩
    · calc
        w = a ++ s := (List.take_append_drop j w).symm
        _ = a ++ (b ++ c) := by
          rw [List.take_append_drop p s]
        _ = a ++ b ++ c := by simp [List.append_assoc]
    · exact hleft
    · simpa [b, s, Word.factor] using hright
    · calc
        b ++ c = s := List.take_append_drop p s
        _ = s.take e ++ s.drop e := (List.take_append_drop e s).symm
        _ = c ++ d := by rw [hcopyS]
  · rintro ⟨a, b, c, d, rfl, hb, hc, hleft, hright, heq⟩
    let j := a.length
    let p := b.length
    let e := c.length
    have hp : 0 < p := List.length_pos_iff.mpr hb
    have he : 0 < e := List.length_pos_iff.mpr hc
    have hlen : j + p + e = (a ++ b ++ c).length := by
      simp [j, p, e, Nat.add_assoc]
    have htake : (b ++ c).take c.length = c := by
      have h := congrArg (List.take c.length) heq
      simpa using h
    refine ⟨j, p, e, hp, he, hlen, ?_, ?_, ?_⟩
    · simpa [j] using hleft
    · simpa [j, p, Word.factor, List.drop_append,
        List.take_append] using hright
    · unfold Word.WitnessCopy Word.factor Word.suffix
      simp only [j, p, e, List.length_append]
      have hoff :
          (a.length + b.length + c.length) - c.length =
            a.length + b.length := by omega
      rw [hoff]
      simpa [List.drop_append, List.take_append] using htake

theorem rowCovers_iff_equationRowCovers
    (row : CapComponent α) (w : Word α) :
    RowCovers row w ↔ EquationRowCovers row w := by
  rw [rowCovers_iff_periodicWitness]
  exact periodicWitness_iff_equationRowCovers row w

/-! ## Concrete contiguous deletions -/

def eraseFactor (w : Word α) (start len : Nat) : Word α :=
  w.take start ++ w.drop (start + len)

theorem eraseFactor_append (left deleted right : Word α) :
    eraseFactor (left ++ deleted ++ right)
      left.length deleted.length = left ++ right := by
  simp [eraseFactor, List.take_append, List.drop_append,
    List.append_assoc]

theorem eraseFactor_length
    (w : Word α) (start len : Nat)
    (hbound : start + len ≤ w.length) :
    (eraseFactor w start len).length = w.length - len := by
  simp only [eraseFactor, List.length_append, List.length_take,
    List.length_drop]
  rw [Nat.min_eq_left (Nat.le_trans (Nat.le_add_right start len) hbound)]
  omega

/--
An admissible concrete deletion removes a nonempty contiguous factor and
keeps the resulting word in the candidate language.  Factorization-forest
child deletions instantiate this relation after their product-value
preservation proof.
-/
def DeletesTo (I : SOAInstance α) (u w : Word α) : Prop :=
  ∃ start len,
    0 < len ∧
    start + len ≤ w.length ∧
    u = eraseFactor w start len ∧
    I.candidate u

theorem deletesTo_candidate {I : SOAInstance α} {u w : Word α}
    (h : I.DeletesTo u w) : I.candidate u := by
  rcases h with ⟨start, len, hlen, hbound, rfl, hcand⟩
  exact hcand

theorem deletesTo_shorter {I : SOAInstance α} {u w : Word α}
    (h : I.DeletesTo u w) : u.length < w.length := by
  rcases h with ⟨start, len, hlen, hbound, rfl, _⟩
  rw [eraseFactor_length w start len hbound]
  omega

theorem deletesTo_append
    (I : SOAInstance α)
    (left deleted right : Word α)
    (hdeleted : deleted ≠ [])
    (hcandidate : I.candidate (left ++ right)) :
    I.DeletesTo (left ++ right) (left ++ deleted ++ right) := by
  refine ⟨left.length, deleted.length,
    List.length_pos_iff.mpr hdeleted, ?_, ?_, hcandidate⟩
  · simp
  · exact (eraseFactor_append left deleted right).symm

def asProblem (I : SOAInstance α) : SOAProblem α where
  Candidate := I.candidate
  RootCov := I.RootCov
  Reduction := I.DeletesTo
  reduction_candidate := deletesTo_candidate
  reduction_shorter := deletesTo_shorter

theorem asProblem_avoider_iff (I : SOAInstance α) (w : Word α) :
    I.asProblem.Avoider w ↔ I.Avoider w := by
  rfl

def AllDel (I : SOAInstance α) (w : Word α) : Prop :=
  ∀ u, I.DeletesTo u w → I.RootCov u

def Critical (I : SOAInstance α) (w : Word α) : Prop :=
  I.candidate w ∧ I.AllDel w ∧ ¬ I.RootCov w

def LengthMinimalAvoider (I : SOAInstance α) (w : Word α) : Prop :=
  I.Avoider w ∧ ∀ u, I.Avoider u → w.length ≤ u.length

theorem exists_lengthMinimalAvoider_iff_exists_avoider
    (I : SOAInstance α) :
    (∃ w, I.LengthMinimalAvoider w) ↔ ∃ w, I.Avoider w := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, hw.1⟩
  · rintro ⟨w₀, hw₀⟩
    classical
    have main :
        ∀ n, ∀ w : Word α, w.length = n → I.Avoider w →
          ∃ v, I.LengthMinimalAvoider v := by
      intro n
      induction n using Nat.strongRecOn with
      | ind n ih =>
          intro w hwlen hw
          by_cases hsmall :
              ∃ u, I.Avoider u ∧ u.length < n
          · obtain ⟨u, hu, hulen⟩ := hsmall
            exact ih u.length hulen u rfl hu
          · refine ⟨w, hw, ?_⟩
            intro u hu
            by_cases hun : n ≤ u.length
            · simpa [hwlen] using hun
            · have hlt : u.length < n := by omega
              exact False.elim (hsmall ⟨u, hu, hlt⟩)
    exact main w₀.length w₀ rfl hw₀

theorem covered_of_candidate_shorter
    {I : SOAInstance α} {w u : Word α}
    (hw : I.LengthMinimalAvoider w)
    (huCandidate : I.candidate u)
    (hshort : u.length < w.length) :
    I.RootCov u := by
  apply Classical.byContradiction
  intro hnot
  have huAvoider : I.Avoider u := ⟨huCandidate, hnot⟩
  have hmin := hw.2 u huAvoider
  omega

theorem lengthMinimalAvoider_allDel
    {I : SOAInstance α} {w : Word α}
    (hw : I.LengthMinimalAvoider w) :
    I.AllDel w := by
  intro u hdelete
  exact covered_of_candidate_shorter hw
    (deletesTo_candidate hdelete)
    (deletesTo_shorter hdelete)

theorem lengthMinimalAvoider_critical
    {I : SOAInstance α} {w : Word α}
    (hw : I.LengthMinimalAvoider w) :
    I.Critical w := by
  exact ⟨hw.1.1, lengthMinimalAvoider_allDel hw, hw.1.2⟩

theorem critical_avoider
    {I : SOAInstance α} {w : Word α}
    (hw : I.Critical w) :
    I.Avoider w :=
  ⟨hw.1, hw.2.2⟩

theorem exists_critical_iff_exists_lengthMinimalAvoider
    (I : SOAInstance α) :
    (∃ w, I.Critical w) ↔
      ∃ w, I.LengthMinimalAvoider w := by
  constructor
  · rintro ⟨w, hw⟩
    apply I.exists_lengthMinimalAvoider_iff_exists_avoider.2
    exact ⟨w, critical_avoider hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, lengthMinimalAvoider_critical hw⟩

/--
The three proper vertices of a two-hole deletion square are covered by
shortest-avoider minimality.  No witness is shared or merged here.
-/
theorem covered_deletion_square
    {I : SOAInstance α} {w side₁ side₂ bottom : Word α}
    (hw : I.LengthMinimalAvoider w)
    (hside₁Candidate : I.candidate side₁)
    (hside₂Candidate : I.candidate side₂)
    (hbottomCandidate : I.candidate bottom)
    (hside₁Short : side₁.length < w.length)
    (hside₂Short : side₂.length < w.length)
    (hbottomShort : bottom.length < w.length) :
    I.RootCov side₁ ∧ I.RootCov side₂ ∧ I.RootCov bottom := by
  exact ⟨covered_of_candidate_shorter hw hside₁Candidate hside₁Short,
    covered_of_candidate_shorter hw hside₂Candidate hside₂Short,
    covered_of_candidate_shorter hw hbottomCandidate hbottomShort⟩

theorem asProblem_critical_iff (I : SOAInstance α) (w : Word α) :
    I.asProblem.Critical w ↔ I.Critical w := by
  rfl

/-- Concrete shortest-avoider equivalence for SOA. -/
theorem exists_critical_iff_exists_avoider (I : SOAInstance α) :
    (∃ w, I.Critical w) ↔ ∃ w, I.Avoider w := by
  change (∃ w, I.asProblem.Critical w) ↔ ∃ w, I.asProblem.Avoider w
  exact SOAProblem.exists_critical_iff_exists_avoider I.asProblem

/-- Full-row query prohibition is exactly root noncoverage. -/
theorem forbids_all_rows_iff_not_rootCov
    (I : SOAInstance α) (w : Word α) :
    SOAProblem.Forbids I.RootQuery (fun _ => True) w ↔
      ¬ I.RootCov w :=
  SOAProblem.forbids_all_iff_not_rootCov I.asProblem I.RootQuery
    I.rootCov_iff_exists_rootQuery w

end SOAInstance

end NSSE
