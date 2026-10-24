import NSSE.IntervalSideTaggedRules
import NSSE.NatIntervalNotFinite

/-!
# A fixed finite quotient for interval-side recursion

Absolute interval coordinates are not part of the compiler alphabet.
For a fixed recursion height, a side tag stores only a finite rank.
The executable side rule permits a nonstrong or side child exactly when
its rank is strictly smaller.  Concrete intervals are supplied later by
a semantic realization witness.
-/

namespace NSSE

abbrev SideRank (height : Nat) := Fin (height + 1)

abbrev RankedCompilerTag
    (height : Nat)
    (Ctl Cut Ori Macro Wire Atom QClass : Type) :=
  CompilerTag Ctl Cut Ori (SideRank height) Macro Wire Atom QClass

def CompilerTag.sideRank? :
    RankedCompilerTag height Ctl Cut Ori Macro Wire Atom QClass →
      Option (SideRank height)
  | .nonstrong _ _ rank _ _ => some rank
  | .side _ _ rank => some rank
  | _ => none

def rankedSideEnabled
    (_control : Ctl) (_cut : Cut) (parent : SideRank height)
    (child :
      RankedCompilerTag height Ctl Cut Ori Macro Wire Atom QClass) :
    Bool :=
  match child.sideRank? with
  | some childRank => decide (childRank.1 < parent.1)
  | none => false

theorem rankedSideEnabled_has_smaller_rank
    (control : Ctl) (cut : Cut) (parent : SideRank height)
    (child :
      RankedCompilerTag height Ctl Cut Ori Macro Wire Atom QClass)
    (henabled : rankedSideEnabled control cut parent child = true) :
    ∃ childRank,
      child.sideRank? = some childRank ∧ childRank.1 < parent.1 := by
  cases child with
  | nonstrong childControl childCut childRank macroData wire =>
      exact ⟨childRank, rfl, by
        simpa [rankedSideEnabled, CompilerTag.sideRank?] using henabled⟩
  | side childControl childCut childRank =>
      exact ⟨childRank, rfl, by
        simpa [rankedSideEnabled, CompilerTag.sideRank?] using henabled⟩
  | strong childControl childCut macroData wire quotient =>
      simp [rankedSideEnabled, CompilerTag.sideRank?] at henabled
  | hub childControl childCut macroData wire =>
      simp [rankedSideEnabled, CompilerTag.sideRank?] at henabled
  | copy childControl childCut orientation macroData wire =>
      simp [rankedSideEnabled, CompilerTag.sideRank?] at henabled
  | bounded childControl childCut atom =>
      simp [rankedSideEnabled, CompilerTag.sideRank?] at henabled

def sideRankEnumeration (height : Nat) : Enumeration (SideRank height) :=
  finEnumeration (height + 1)

def rankedCompilerTagEnumeration
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori)
    (macros : Enumeration Macro) (wire : Enumeration Wire)
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (height : Nat) :
    Enumeration
      (RankedCompilerTag height Ctl Cut Ori Macro Wire Atom QClass) :=
  CompilerTag.enumeration ctl cut ori (sideRankEnumeration height)
    macros wire atom quotient

def rankedSideRuleSystem
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori)
    (macros : Enumeration Macro) (wire : Enumeration Wire)
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (height : Nat) :=
  (sideOnlyRuleTests
    (rankedSideEnabled
      (Ctl := Ctl) (Cut := Cut) (Ori := Ori)
      (Macro := Macro) (Wire := Wire)
      (Atom := Atom) (QClass := QClass))).ruleSystem
    ctl cut ori (sideRankEnumeration height)
      macros wire atom quotient

theorem rankedSide_taggedDerives_iff
    (ctl : Enumeration Ctl) (cutEnum : Enumeration Cut)
    (ori : Enumeration Ori)
    (macros : Enumeration Macro) (wire : Enumeration Wire)
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (height : Nat)
    (control : Ctl) (cut : Cut) (rank : SideRank height) :
    (rankedSideRuleSystem ctl cutEnum ori macros wire atom quotient
      height).TaggedDerives (.side control cut rank) ↔
      ∃ child,
        rankedSideEnabled control cut rank child = true ∧
        (rankedSideRuleSystem ctl cutEnum ori macros wire atom quotient
          height).TaggedDerives child := by
  exact sideOnly_taggedDerives_iff
    (rankedSideEnabled
      (Ctl := Ctl) (Cut := Cut) (Ori := Ori)
      (Macro := Macro) (Wire := Wire)
      (Atom := Atom) (QClass := QClass))
    ctl cutEnum ori (sideRankEnumeration height)
      macros wire atom quotient control cut rank

structure SideRankIntervalRealization
    (height : Nat) (attachment : AttachmentDomains) where
  Realizes : SideRank height → NatInterval → Prop
  side_sound :
    ∀ {parentRank childRank : SideRank height}
      {parentInterval childInterval : NatInterval},
      Realizes parentRank parentInterval →
      Realizes childRank childInterval →
      childRank.1 < parentRank.1 →
      SideDelegation parentInterval childInterval attachment

theorem SideRankIntervalRealization.enabled_sideDelegation
    (realization : SideRankIntervalRealization height attachment)
    (control : Ctl) (cut : Cut) (parent : SideRank height)
    (parentInterval : NatInterval)
    (child :
      RankedCompilerTag height Ctl Cut Ori Macro Wire Atom QClass)
    (childInterval : NatInterval)
    (hparent : realization.Realizes parent parentInterval)
    (henabled : rankedSideEnabled control cut parent child = true) :
    ∃ childRank,
      child.sideRank? = some childRank ∧
      (realization.Realizes childRank childInterval →
        SideDelegation parentInterval childInterval attachment) := by
  obtain ⟨childRank, hchild, hlt⟩ :=
    rankedSideEnabled_has_smaller_rank
      control cut parent child henabled
  exact ⟨childRank, ⟨hchild, fun hchildInterval =>
    realization.side_sound hparent hchildInterval hlt⟩⟩

end NSSE
