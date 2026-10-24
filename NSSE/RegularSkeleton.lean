import NSSE.Cap

/-!
# The bounded-period / short-border regular skeleton

This module formalizes the semantic content of Lemma 2.2 in `proofs_en.md`.
The predicates match the two extra skeleton languages; their automata
constructions (Lemma 2.1) are kept separate from this soundness proof.
-/

namespace NSSE

universe u

/-- `Per_{≤B}(S)`: an accepted period root of length at most `B`. -/
def BoundedPeriodLanguage
    (S : Language α) (B : Nat) : Language α := fun sigma =>
  ∃ p, 0 < p ∧ p ≤ B ∧
    Word.HasPeriod sigma p ∧ S (sigma.take p)

/--
`Bord_{≤c}(S)`: a short positive proper border whose complementary prefix
is accepted by `S`.
-/
def ShortBorderLanguage
    (S : Language α) (c : Nat) : Language α := fun sigma =>
  ∃ e, 0 < e ∧ e ≤ c ∧ e < sigma.length ∧
    Word.BorderCopy sigma e ∧ S (sigma.take (sigma.length - e))

def BoundedPeriodRoute
    (component : CapComponent α) (B : Nat) (w : Word α) : Prop :=
  ∃ j, j ≤ w.length ∧ component.left (w.take j) ∧
    BoundedPeriodLanguage component.right B (w.drop j)

def ShortBorderRoute
    (component : CapComponent α) (c : Nat) (w : Word α) : Prop :=
  ∃ j, j ≤ w.length ∧ component.left (w.take j) ∧
    ShortBorderLanguage component.right c (w.drop j)

/-- One component of `Reg_{B,c}`. -/
def SkeletonComponent
    (component : CapComponent α) (B c : Nat) (w : Word α) : Prop :=
  PrefixRoute component w ∨
    SplitRoute component w ∨
    BoundedPeriodRoute component B w ∨
    ShortBorderRoute component c w

theorem boundedPeriodRoute_capComponentCovers
    (component : CapComponent α) (B : Nat) (w : Word α)
    (hroute : BoundedPeriodRoute component B w) :
    capComponentCovers component w := by
  rcases hroute with
    ⟨j, hj, hleft, p, hp, hpB, hperiod, hroot⟩
  have hcap : Language.cap component.right (w.drop j) :=
    Language.mem_cap_of_period component.right (w.drop j)
      p hp hperiod hroot
  exact ⟨[], w.take j, w.drop j, by simp, hleft, hcap⟩

theorem shortBorderRoute_boundedPeriodRoute
    (component : CapComponent α) (c : Nat) (w : Word α)
    (hroute : ShortBorderRoute component c w) :
    BoundedPeriodRoute component w.length w := by
  rcases hroute with
    ⟨j, hj, hleft, e, he, hec, helen, hborder, hroot⟩
  let sigma := w.drop j
  let p := sigma.length - e
  have hp : 0 < p := by
    dsimp [p, sigma]
    omega
  have hplen : p < sigma.length := by
    dsimp [p, sigma]
    omega
  have hperiod : Word.HasPeriod sigma p := by
    apply (Word.hasPeriod_iff_borderCopy sigma p hplen).2
    have hsub : sigma.length - p = e := by
      dsimp [p]
      omega
    simpa [hsub] using hborder
  have hpw : p ≤ w.length := by
    dsimp [p, sigma]
    simp only [List.length_drop]
    omega
  refine ⟨j, hj, hleft, p, hp, hpw, hperiod, ?_⟩
  simpa [p, sigma] using hroot

theorem shortBorderRoute_capComponentCovers
    (component : CapComponent α) (c : Nat) (w : Word α)
    (hroute : ShortBorderRoute component c w) :
    capComponentCovers component w :=
  boundedPeriodRoute_capComponentCovers component w.length w
    (shortBorderRoute_boundedPeriodRoute component c w hroute)

/-- Lemma 2.2 for one retained component. -/
theorem skeletonComponent_capComponentCovers
    (component : CapComponent α)
    (hright : ∃ mu, component.right mu)
    (B c : Nat) (w : Word α)
    (hskeleton : SkeletonComponent component B c w) :
    capComponentCovers component w := by
  rcases hskeleton with
    hprefix | hsplit | hperiod | hborder
  · exact prefixRoute_capComponentCovers component w hright hprefix
  · exact splitRoute_capComponentCovers component w hsplit
  · exact boundedPeriodRoute_capComponentCovers component B w hperiod
  · exact shortBorderRoute_capComponentCovers component c w hborder

/-- The finite union `Reg_{B,c}` over the components of an expression. -/
def RegularSkeleton
    (E : CapExpression α) (B c : Nat) (w : Word α) : Prop :=
  ∃ component ∈ E.caps, SkeletonComponent component B c w

/-- Lemma 2.2: `Reg_{B,c} ⊆ P`. -/
theorem regularSkeleton_capCovered
    (E : CapExpression α)
    (hright : ∀ component ∈ E.caps, ∃ mu, component.right mu)
    (B c : Nat) (w : Word α)
    (hskeleton : RegularSkeleton E B c w) :
    capCovered E w := by
  rcases hskeleton with ⟨component, hcomponent, hw⟩
  exact ⟨component, hcomponent,
    skeletonComponent_capComponentCovers component
      (hright component hcomponent) B c w hw⟩

/--
The consequence in Lemma 2.2: covering every route-free word by the
skeleton suffices for universality of the original expression.
-/
theorem universal_of_routeFree_le_regularSkeleton
    (E : CapExpression α)
    (hright : ∀ component ∈ E.caps, ∃ mu, component.right mu)
    (B c : Nat)
    (hcover : ∀ w, routeFree E w → RegularSkeleton E B c w) :
    E.Universal := by
  apply (universal_iff_routeFree_capCovered E).2
  intro w hrouteFree
  exact regularSkeleton_capCovered E hright B c w
    (hcover w hrouteFree)

/-- The regular residue `C_{B,c}` at the semantic language level. -/
def SkeletonResidue
    (E : CapExpression α) (B c : Nat) (w : Word α) : Prop :=
  routeFree E w ∧ ¬ RegularSkeleton E B c w

/--
The defining witness property of `C_{B,c}`: regular routes are absent and
every remaining periodic witness has both parameters above the skeleton
bounds.
-/
theorem skeletonResidue_witness_bounds
    (E : CapExpression α) (B c : Nat) (w : Word α)
    (hresidue : SkeletonResidue E B c w)
    (component : CapComponent α) (hcomponent : component ∈ E.caps) :
    (¬ PrefixRoute component w) ∧
    (¬ SplitRoute component w) ∧
    ∀ j p e,
      0 < p → 0 < e → j + p + e = w.length →
      component.left (w.take j) →
      component.right (Word.factor w j p) →
      Word.WitnessCopy w j p e →
      B < p ∧ c < e := by
  rcases hresidue with ⟨hrouteFree, hskeleton⟩
  have hnotComponent :
      ¬ SkeletonComponent component B c w := by
    intro hcomponentSkeleton
    exact hskeleton ⟨component, hcomponent, hcomponentSkeleton⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hprefix
    exact hnotComponent (Or.inl hprefix)
  · intro hsplit
    exact hnotComponent (Or.inr (Or.inl hsplit))
  · intro j p e hp he hlen hleft hright hcopy
    have hperiod : Word.AnchoredPeriod w j p :=
      (Word.witnessCopy_iff_anchoredPeriod
        w j p e hlen he).1 hcopy
    have hj : j ≤ w.length := by omega
    constructor
    · by_cases hpB : p ≤ B
      · apply False.elim
        apply hnotComponent
        apply Or.inr
        apply Or.inr
        apply Or.inl
        refine ⟨j, hj, hleft, p, hp, hpB, hperiod, ?_⟩
        simpa [Word.factor] using hright
      · omega
    · by_cases hec : e ≤ c
      · apply False.elim
        apply hnotComponent
        apply Or.inr
        apply Or.inr
        apply Or.inr
        let sigma := w.drop j
        have hsigmaLen : sigma.length = p + e := by
          dsimp [sigma]
          simp only [List.length_drop]
          omega
        have heSigma : e < sigma.length := by rw [hsigmaLen]; omega
        have hborder : Word.BorderCopy sigma e := by
          have hpSigma : p < sigma.length := by rw [hsigmaLen]; omega
          have hperiodSigma : Word.HasPeriod sigma p := hperiod
          have hdual :=
            (Word.hasPeriod_iff_borderCopy sigma p hpSigma).1 hperiodSigma
          have hsub : sigma.length - p = e := by rw [hsigmaLen]; omega
          simpa [hsub] using hdual
        refine ⟨j, hj, hleft, e, he, hec, heSigma, hborder, ?_⟩
        have hsub : (w.drop j).length - e = p := by
          simpa [sigma] using (show sigma.length - e = p by
            rw [hsigmaLen]
            omega)
        rw [hsub]
        simpa [Word.factor] using hright
      · omega

end NSSE
