import NSSE.MultiConstructorRawTrace

/-! Computable local domains of the original two-token path. Different
terminal pins are allowed; a common proper head imposes the stronger
combined-pin condition and its own child-arity check. -/
namespace NSSE.MultiConstructorRawValidity
open MultiConstructorConstraints MultiConstructorSupportDecision
open MultiConstructorTokens MultiConstructorRawTrace MultiConstructorTrees
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

def pins (phi : Constraints arity n) (s : Row n) : Finset H :=
  upperPins phi s.1 ∪ lowerPins phi s.2

def Valid (phi : Constraints arity n) (s : Row n) : Prop :=
  (upperPins phi s.1).card ≤ 1 ∧ (lowerPins phi s.2).card ≤ 1 ∧
  (∀ u ∈ s.1, ∀ b ∈ phi.bot, ¬Support phi u b) ∧
  (∀ v ∈ s.2, ∀ t ∈ phi.top, ¬Support phi t v)

def validDecision (phi : Constraints arity n) (s : Row n) : Decidable (Valid phi s) := by
  letI := supportDecision phi
  unfold Valid
  infer_instance

def ForcedBot (phi : Constraints arity n) (u : Fin n) : Prop :=
  (∃ b ∈ phi.bot, Support phi u b) ∨ 1 < (upperPins phi {u}).card

def ForcedTop (phi : Constraints arity n) (v : Fin n) : Prop :=
  (∃ t ∈ phi.top, Support phi t v) ∨ 1 < (lowerPins phi {v}).card

theorem upper_singleton_subset (phi : Constraints arity n) (S : Tokens n) (u : Fin n)
    (hu : u ∈ S) : upperPins phi {u} ⊆ upperPins phi S := by
  intro h hh
  obtain ⟨a,ha,⟨t,ht,hrel⟩,he⟩ := (mem_upperPins phi {u} h).mp hh
  have ht' : t = u := Finset.mem_singleton.mp ht
  subst t
  exact (mem_upperPins phi S h).mpr ⟨a,ha,⟨u,hu,hrel⟩,he⟩

theorem lower_singleton_subset (phi : Constraints arity n) (S : Tokens n) (v : Fin n)
    (hv : v ∈ S) : lowerPins phi {v} ⊆ lowerPins phi S := by
  intro h hh
  obtain ⟨a,ha,⟨t,ht,hrel⟩,he⟩ := (mem_lowerPins phi {v} h).mp hh
  have ht' : t = v := Finset.mem_singleton.mp ht
  subst t
  exact (mem_lowerPins phi S h).mpr ⟨a,ha,⟨v,hv,hrel⟩,he⟩

theorem valid_iff_no_forced_extreme (phi : Constraints arity n) (s : Row n) :
    Valid phi s ↔ (upperPins phi s.1).card ≤ 1 ∧ (lowerPins phi s.2).card ≤ 1 ∧
      (∀ u ∈ s.1, ¬ForcedBot phi u) ∧ (∀ v ∈ s.2, ¬ForcedTop phi v) := by
  constructor
  · rintro ⟨hu,hl,hb,ht⟩
    refine ⟨hu,hl,?_,?_⟩
    · intro u hus h
      rcases h with ⟨b,hb',hrel⟩ | hc
      · exact hb u hus b hb' hrel
      · have hle := Finset.card_le_card (upper_singleton_subset phi s.1 u hus)
        omega
    · intro v hvs h
      rcases h with ⟨t,ht',hrel⟩ | hc
      · exact ht v hvs t ht' hrel
      · have hle := Finset.card_le_card (lower_singleton_subset phi s.2 v hvs)
        omega
  · rintro ⟨hu,hl,hb,ht⟩
    exact ⟨hu,hl,fun u hus b hb' hrel => hb u hus (Or.inl ⟨b,hb',hrel⟩),
      fun v hvs t ht' hrel => ht v hvs (Or.inl ⟨t,ht',hrel⟩)⟩

def Proper (phi : Constraints arity n) (s : Row n) : Prop :=
  Valid phi s ∧ (pins phi s).card ≤ 1

def properDecision (phi : Constraints arity n) (s : Row n) : Decidable (Proper phi s) := by
  letI := validDecision phi s
  unfold Proper
  infer_instance

def Compatible (phi : Constraints arity n) (s : Row n) (h : H) : Prop :=
  ∀ g ∈ pins phi s, g = h

def compatibleDecision (phi : Constraints arity n) (s : Row n) (h : H) :
    Decidable (Compatible phi s h) := by unfold Compatible; infer_instance

def ArityOK (phi : Constraints arity n) (s : Row n) (i : Nat) : Prop :=
  ∀ h ∈ pins phi s, i < arity h

def arityDecision (phi : Constraints arity n) (s : Row n) (i : Nat) :
    Decidable (ArityOK phi s i) := by unfold ArityOK; infer_instance

theorem compatible_card (phi : Constraints arity n) (s : Row n) (h : H)
    (hc : Compatible phi s h) : (pins phi s).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact (hc a ha).trans (hc b hb).symm

theorem compatible_arity (phi : Constraints arity n) (s : Row n) (h : H) (i : Nat)
    (hc : Compatible phi s h) (hi : i < arity h) : ArityOK phi s i := by
  intro g hg
  rwa [hc g hg]

def UpperDomain (phi : Constraints arity n) (s : Row n) : Label H → Prop
  | .bot => False
  | .top => upperPins phi s.1 = ∅
  | .node h => ∀ g ∈ upperPins phi s.1, g = h

def LowerDomain (phi : Constraints arity n) (s : Row n) : Label H → Prop
  | .bot => lowerPins phi s.2 = ∅
  | .top => False
  | .node h => ∀ g ∈ lowerPins phi s.2, g = h

def upperDomainDecision (phi : Constraints arity n) (s : Row n) :
    DecidablePred (UpperDomain phi s) := by
  intro e
  cases e <;> unfold UpperDomain <;> infer_instance

def lowerDomainDecision (phi : Constraints arity n) (s : Row n) :
    DecidablePred (LowerDomain phi s) := by
  intro e
  cases e <;> unfold LowerDomain <;> infer_instance

theorem common_domains (phi : Constraints arity n) (s : Row n) (h : H) :
    UpperDomain phi s (.node h) ∧ LowerDomain phi s (.node h) ↔ Compatible phi s h := by
  simp only [UpperDomain,LowerDomain,Compatible,pins,Finset.mem_union]
  exact ⟨fun ⟨hu,hl⟩ g hg => hg.elim (hu g) (hl g),
    fun hc => ⟨fun g hg => hc g (Or.inl hg),fun g hg => hc g (Or.inr hg)⟩⟩

theorem empty_valid (phi : Constraints arity n) : Valid phi (∅,∅) := by
  simp [Valid,upperPins_empty,lowerPins_empty]

theorem empty_proper (phi : Constraints arity n) : Proper phi (∅,∅) := by
  exact ⟨empty_valid phi,by simp [pins,upperPins_empty,lowerPins_empty]⟩

theorem empty_step (phi : Constraints arity n) (i : Nat) : step phi (∅,∅) i = (∅,∅) := by
  simp [step,upperNext_empty,lowerNext_empty]

end NSSE.MultiConstructorRawValidity
