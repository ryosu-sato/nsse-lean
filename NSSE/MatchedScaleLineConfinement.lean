import NSSE.LineCollapse
import Lean.Elab.Tactic.Omega

/-!
# Matched-scale line confinement

This is Theorem 8.1 of `proofs_en.md`.  If every periodic witness has a
border longer than `|w| - K`, then every witness starts before `K` and has
period below `K`.  Its suffix is therefore on the corresponding short
periodic line.
-/

namespace NSSE

def EveryPeriodicWitnessBorderAbove
    (c : CapComponent α) (w : Word α) (K : Nat) : Prop :=
  ∀ j p e,
    0 < p →
    0 < e →
    j + p + e = w.length →
    c.left (w.take j) →
    c.right (Word.factor w j p) →
    Word.WitnessCopy w j p e →
    w.length - K < e

theorem matchedScale_witness_lineConfinement
    (w : Word α) (K j p e : Nat)
    (hp : 0 < p) (he : 0 < e)
    (hlen : j + p + e = w.length)
    (hborder : w.length - K < e)
    (hcopy : Word.WitnessCopy w j p e) :
    j < K ∧ p < K ∧ Word.AnchoredPeriod w j p := by
  have hjp : j + p < K := by
    omega
  refine ⟨by omega, by omega, ?_⟩
  exact
    (Word.witnessCopy_iff_anchoredPeriod
      w j p e hlen he).1 hcopy

theorem periodicWitness_matchedScale_lineConfinement
    (c : CapComponent α) (w : Word α) (K : Nat)
    (hall : EveryPeriodicWitnessBorderAbove c w K)
    (hwitness : PeriodicWitness c w) :
    ∃ j p,
      j < K ∧
      p < K ∧
      c.left (w.take j) ∧
      c.right (Word.factor w j p) ∧
      Word.AnchoredPeriod w j p := by
  obtain ⟨j, p, e, hp, he, hlen, hleft, hright, hcopy⟩ :=
    hwitness
  have hborder : w.length - K < e :=
    hall j p e hp he hlen hleft hright hcopy
  obtain ⟨hj, hpK, hperiod⟩ :=
    matchedScale_witness_lineConfinement
      w K j p e hp he hlen hborder hcopy
  exact ⟨j, p, hj, hpK, hleft, hright, hperiod⟩

/-- Full line formulation of Theorem 8.1: the anchored suffix is a finite
prefix of powers of a root of length `p < K`. -/
theorem matchedScale_witness_shortPowerLine
    (w : Word α) (K j p e : Nat)
    (hp : 0 < p) (he : 0 < e)
    (hlen : j + p + e = w.length)
    (hborder : w.length - K < e)
    (hcopy : Word.WitnessCopy w j p e) :
    ∃ root,
      root.length = p ∧
      j < K ∧
      p < K ∧
      PrefixOfPowerLine (w.drop j) root := by
  have hperiod : Word.HasPeriod (w.drop j) p :=
    (Word.witnessCopy_iff_anchoredPeriod
      w j p e hlen he).1 hcopy
  let root := (w.drop j).take p
  have hrootLength : root.length = p := by
    dsimp [root]
    rw [List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hperiod.1)]
  obtain ⟨repetitions, tail, hpower⟩ :=
    Language.hasPeriod_prefix_wordPower
      (w.drop j) p hp hperiod
  have hwordPower :
      Word.power root repetitions =
        w.drop j ++ tail := by
    rw [← language_wordPower_eq_word_power]
    simpa [root] using hpower
  have hconfined :=
    matchedScale_witness_lineConfinement
      w K j p e hp he hlen hborder hcopy
  exact ⟨root, hrootLength, hconfined.1,
    hconfined.2.1, repetitions, tail, hwordPower⟩

end NSSE
