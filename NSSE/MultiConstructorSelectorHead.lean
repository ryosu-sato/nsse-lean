import NSSE.MultiConstructorRawValidity

/-! Computable head selection and reset transitions on actual raw rows.
Candidates are taken from input lists, so selection needs no arbitrary
ordering or choice operation on the constructor type. -/
namespace NSSE.MultiConstructorSelectorHead
open MultiConstructorConstraints MultiConstructorSupportDecision
open MultiConstructorTokens MultiConstructorRawTrace MultiConstructorRawValidity
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

def candidates (phi : Constraints arity n) (s : Row n) : List H :=
  letI := supportDecision phi
  ((phi.upper.filter (fun a => ∃ t ∈ s.1, Support phi t a.parent)).map Bound.head) ++
  ((phi.lower.filter (fun a => ∃ t ∈ s.2, Support phi a.parent t)).map Bound.head)

theorem mem_candidates (phi : Constraints arity n) (s : Row n) (h : H) :
    h ∈ candidates phi s ↔ h ∈ pins phi s := by
  simp only [candidates,pins,upperPins,lowerPins,List.mem_append,
    Finset.mem_union,List.mem_toFinset]

def choose (phi : Constraints arity n) (s : Row n) (fallback : H) : H :=
  match candidates phi s with
  | [] => fallback
  | h :: _ => h

theorem choose_compatible (phi : Constraints arity n) (s : Row n) (fallback : H)
    (hc : (pins phi s).card ≤ 1) : Compatible phi s (choose phi s fallback) := by
  cases he : candidates phi s with
  | nil =>
    intro g hg
    have hm := (mem_candidates phi s g).mpr hg
    rw [he] at hm
    contradiction
  | cons h hs =>
    rw [choose,he]
    intro g hg
    have hh : h ∈ pins phi s := (mem_candidates phi s h).mp (by rw [he]; exact List.mem_cons_self)
    exact Finset.card_le_one.mp hc g hg h hh

theorem choose_forced (phi : Constraints arity n) (s : Row n) (fallback h : H)
    (hc : (pins phi s).card ≤ 1) (hh : h ∈ pins phi s) : choose phi s fallback = h :=
  (choose_compatible phi s fallback hc h hh).symm

theorem choose_unpinned (phi : Constraints arity n) (s : Row n) (fallback : H)
    (hp : pins phi s = ∅) : choose phi s fallback = fallback := by
  have he : candidates phi s = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro g hg
    have hm := (mem_candidates phi s g).mp hg
    rw [hp] at hm
    exact Finset.not_mem_empty _ hm
  rw [choose,he]

theorem proper_domains (phi : Constraints arity n) (s : Row n) (fallback : H)
    (hp : Proper phi s) :
    UpperDomain phi s (.node (choose phi s fallback)) ∧
      LowerDomain phi s (.node (choose phi s fallback)) :=
  (common_domains phi s _).mpr (choose_compatible phi s fallback hp.2)

def next (phi : Constraints arity n) (reset s : Row n) (letter : Nat) : Row n :=
  let t := step phi s letter
  if t = (∅,∅) then reset else t

theorem next_reset (phi : Constraints arity n) (reset s : Row n) (letter : Nat)
    (he : step phi s letter = (∅,∅)) : next phi reset s letter = reset := by
  simp [next,he]

theorem next_raw (phi : Constraints arity n) (reset s : Row n) (letter : Nat)
    (he : step phi s letter ≠ (∅,∅)) : next phi reset s letter = step phi s letter := by
  simp [next,he]

theorem empty_reset (phi : Constraints arity n) (reset : Row n) (letter : Nat) :
    next phi reset (∅,∅) letter = reset := next_reset phi reset _ letter (empty_step phi letter)

theorem empty_default (phi : Constraints arity n) (fallback : H) :
    choose phi (∅,∅) fallback = fallback :=
  choose_unpinned phi _ fallback (by simp [pins,upperPins_empty,lowerPins_empty])

end NSSE.MultiConstructorSelectorHead
