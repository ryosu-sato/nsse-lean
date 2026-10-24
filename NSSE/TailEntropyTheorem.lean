import NSSE.TailEntropyCounting
import NSSE.TailEntropyGeometry
import NSSE.RegularSkeleton

/-!
# Tail Entropy Theorem

This assembles the one-step theorem retained in Section 6 of
`proofs_en.md`. It does not state or use the retracted iterated-cone
corollary.
-/

namespace NSSE

universe u

structure TailWitness
    (E : CapExpression α) (w : Word α) where
  component : CapComponent α
  component_mem : component ∈ E.caps
  anchor : Nat
  period : Nat
  border : Nat
  period_pos : 0 < period
  border_pos : 0 < border
  length_eq : anchor + period + border = w.length
  left_accept : component.left (w.take anchor)
  right_accept :
    component.right (Word.factor w anchor period)
  copy : Word.WitnessCopy w anchor period border

theorem tailWitness_of_residue_of_covered
    (E : CapExpression α)
    (hright :
      ∀ component ∈ E.caps,
        ∃ word, component.right word)
    (B c : Nat) (w : Word α)
    (hresidue : SkeletonResidue E B c w)
    (hcovered : E.Covers w) :
    ∃ witness : TailWitness E w,
      B < witness.period ∧ c < witness.border := by
  have hcap : capCovered E w := by
    rcases hcovered with hcap | hroute
    · exact hcap
    · exact False.elim (hresidue.1 hroute)
  obtain ⟨component, hcomponent, hcomponentCover⟩ := hcap
  have hnormal :=
    (capComponentCovers_iff_componentNormalForm
      component (hright component hcomponent) w).1
      hcomponentCover
  have hbounds :=
    skeletonResidue_witness_bounds E B c w
      hresidue component hcomponent
  rcases hnormal with hprefix | hsplit | hperiodic
  · exact False.elim (hbounds.1 hprefix)
  · exact False.elim (hbounds.2.1 hsplit)
  · obtain ⟨j, p, e, hp, he, hlen,
        hleft, hrightAccept, hcopy⟩ := hperiodic
    have hpe :=
      hbounds.2.2 j p e hp he hlen hleft
        hrightAccept hcopy
    exact ⟨{
      component := component
      component_mem := hcomponent
      anchor := j
      period := p
      border := e
      period_pos := hp
      border_pos := he
      length_eq := hlen
      left_accept := hleft
      right_accept := hrightAccept
      copy := hcopy
    }, hpe⟩

def LongTailCode
    (E : CapExpression α) (base : Word α) (c n : Nat)
    (endpoint : Fin n) (completion : Word α) : Prop :=
  completion.length = c + 1 ∧
  ∃ witness : TailWitness E (base ++ completion),
    c < witness.border ∧
    c + 1 ≤ witness.period ∧
    endpoint.1 = witness.anchor + witness.border

def ShortTailCode
    (E : CapExpression α) (base : Word α) (c n : Nat)
    (anchorPeriod : Fin n × Fin n)
    (completion : Word α) : Prop :=
  completion.length = c + 1 ∧
  ∃ witness : TailWitness E (base ++ completion),
    c < witness.border ∧
    witness.period ≤ c ∧
    anchorPeriod.1.1 = witness.anchor ∧
    anchorPeriod.2.1 = witness.period

theorem longTailCode_unique
    (E : CapExpression α) (base : Word α) (c n : Nat)
    (endpoint : Fin n) (first second : Word α)
    (hfirst : LongTailCode E base c n endpoint first)
    (hsecond : LongTailCode E base c n endpoint second) :
    first = second := by
  rcases hfirst with ⟨hfirstLength, wf, hbf, hpf, hef⟩
  rcases hsecond with ⟨hsecondLength, ws, hbs, hps, hes⟩
  have hefBorder : first.length ≤ wf.border := by omega
  have hesBorder : second.length ≤ ws.border := by omega
  have hefEnd : wf.anchor + wf.border ≤ base.length := by
    apply longPeriod_source_ends_in_prefix
      base.length first.length wf.anchor wf.period wf.border
      hfirstLength (by simpa using wf.length_eq)
    exact hpf
  have hesEnd : ws.anchor + ws.border ≤ base.length := by
    apply longPeriod_source_ends_in_prefix
      base.length second.length ws.anchor ws.period ws.border
      hsecondLength (by simpa using ws.length_eq)
    exact hps
  apply longPeriod_completion_unique base first second
    wf.anchor wf.period wf.border
    ws.anchor ws.period ws.border
    (by omega) hefBorder hesBorder hefEnd hesEnd
    (by omega) wf.copy ws.copy

theorem shortTailCode_unique
    (E : CapExpression α) (base : Word α) (c n : Nat)
    (anchorPeriod : Fin n × Fin n)
    (first second : Word α)
    (hfirst : ShortTailCode E base c n anchorPeriod first)
    (hsecond : ShortTailCode E base c n anchorPeriod second) :
    first = second := by
  rcases hfirst with
    ⟨hfirstLength, wf, hbf, hpf, hjf, hperF⟩
  rcases hsecond with
    ⟨hsecondLength, ws, hbs, hps, hjs, hperS⟩
  have hsameAnchor : wf.anchor = ws.anchor := by omega
  have hsamePeriod : wf.period = ws.period := by omega
  have hrootInside :
      wf.anchor + wf.period ≤ base.length := by
    apply shortPeriod_root_inside_prefix
      base.length first.length wf.anchor wf.period wf.border
      hfirstLength (by simpa using wf.length_eq)
    exact hbf
  have hfirstPeriod :
      Word.HasPeriod ((base ++ first).drop wf.anchor)
        wf.period :=
    (Word.witnessCopy_iff_anchoredPeriod
      (base ++ first) wf.anchor wf.period wf.border
      wf.length_eq wf.border_pos).1 wf.copy
  have hsecondPeriod :
      Word.HasPeriod ((base ++ second).drop wf.anchor)
        wf.period := by
    have hs :=
      (Word.witnessCopy_iff_anchoredPeriod
        (base ++ second) ws.anchor ws.period ws.border
        ws.length_eq ws.border_pos).1 ws.copy
    simpa [hsameAnchor, hsamePeriod] using hs
  exact shortPeriod_completion_unique base first second
    wf.anchor wf.period wf.period_pos
    (by omega) hrootInside (by omega)
    hfirstPeriod hsecondPeriod

/-- Theorem 6.1 (one-step Tail Entropy Theorem). Legal completions are
represented here by a finite set whose members all have length `c+1` and
whose completed words lie in the semantic skeleton residue. -/
theorem tailEntropyTheorem
    [DecidableEq α]
    (E : CapExpression α)
    (hright :
      ∀ component ∈ E.caps,
        ∃ word, component.right word)
    (B c : Nat) (base : Word α)
    (completions : Finset (Word α))
    (hlength :
      ∀ v ∈ completions, v.length = c + 1)
    (hlegal :
      ∀ v ∈ completions,
        SkeletonResidue E B c (base ++ v))
    (hmany :
      let n := base.length + c + 1
      n * n + n < completions.card) :
    ∃ v ∈ completions, ¬E.Covers (base ++ v) := by
  classical
  let n := base.length + c + 1
  apply tailEntropy_counting_relations
    (fun v => E.Covers (base ++ v))
    completions n
    (LongTailCode E base c n)
    (ShortTailCode E base c n)
  · exact longTailCode_unique E base c n
  · exact shortTailCode_unique E base c n
  · intro v hv hcovered
    have hvLength := hlength v hv
    obtain ⟨witness, _hperiodBound, hborderBound⟩ :=
      tailWitness_of_residue_of_covered E hright B c
        (base ++ v) (hlegal v hv) hcovered
    by_cases hlong : c + 1 ≤ witness.period
    · left
      have hend :
          witness.anchor + witness.border ≤ base.length := by
        apply longPeriod_source_ends_in_prefix
          base.length v.length witness.anchor
          witness.period witness.border
          hvLength (by simpa using witness.length_eq)
          hlong
      have hendN :
          witness.anchor + witness.border < n := by
        dsimp [n]
        omega
      let endpoint : Fin n :=
        ⟨witness.anchor + witness.border, hendN⟩
      exact ⟨endpoint, hvLength, witness,
        hborderBound, hlong, rfl⟩
    · right
      have hshort : witness.period ≤ c := by omega
      have hanchorN : witness.anchor < n := by
        dsimp [n]
        have hwlen :
            witness.anchor + witness.period + witness.border =
              base.length + v.length := by
          simpa using witness.length_eq
        omega
      have hperiodN : witness.period < n := by
        dsimp [n]
        have hwlen :
            witness.anchor + witness.period + witness.border =
              base.length + v.length := by
          simpa using witness.length_eq
        omega
      let anchorPeriod : Fin n × Fin n :=
        (⟨witness.anchor, hanchorN⟩,
          ⟨witness.period, hperiodN⟩)
      exact ⟨anchorPeriod, hvLength, witness,
        hborderBound, hshort, rfl, rfl⟩
  · exact hmany

end NSSE
