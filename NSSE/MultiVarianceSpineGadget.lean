import NSSE.MultiVarianceSpineSeparation

/-!
Executable syntax-free semantics of the signed two-rail spine gadget.

Each step is made of TWO ORIGINAL signed constructor inequalities and
fresh rail values u,v. At a negative child the rails are exchanged.
This module proves that existential assignments of the fresh rails are
equivalent to the bounded separating spine of
MultiVarianceSpineSeparation. No finite word bound or SAT completeness
assumption is used.
-/
namespace NSSE.MultiVarianceSpineGadget
open MultiVarianceEncoding MultiVarianceTrees MultiVarianceSpineSeparation
open MultiConstructorTrees (Label)
variable {H : Type*} {arity : H → Nat}
variable (pol : Polarity arity)

def lowerShell (h : H) (i : Fin (arity h)) (a b : Tree pol) : Tree pol :=
  node h (fun j => if j = i then (if pol h i then b else a)
                   else lowFill pol h j)

def upperShell (h : H) (i : Fin (arity h)) (a b : Tree pol) : Tree pol :=
  node h (fun j => if j = i then (if pol h i then a else b)
                   else highFill pol h j)

@[simp] theorem lower_step (h : H) (i : Fin (arity h)) (s : Spine arity) :
    lower pol (.step h i s) =
      lowerShell pol h i (lower pol s) (upper pol s) := rfl

@[simp] theorem upper_step (h : H) (i : Fin (arity h)) (s : Spine arity) :
    upper pol (.step h i s) =
      upperShell pol h i (lower pol s) (upper pol s) := rfl

theorem lowerShell_mono (h : H) (i : Fin (arity h))
    {a b c d : Tree pol} (ha : a ≤ c) (hb : d ≤ b) :
    lowerShell pol h i a b ≤ lowerShell pol h i c d := by
  unfold lowerShell
  apply (node_le_node h _ _).mpr
  intro j
  by_cases hj : j = i
  · subst j
    cases hp : pol h i
    · simpa [hp] using ha
    · simpa [hp] using hb
  · cases hp : pol h j <;> simp [hj, hp]

theorem upperShell_mono (h : H) (i : Fin (arity h))
    {a b c d : Tree pol} (ha : a ≤ c) (hb : d ≤ b) :
    upperShell pol h i c d ≤ upperShell pol h i a b := by
  unfold upperShell
  apply (node_le_node h _ _).mpr
  intro j
  by_cases hj : j = i
  · subst j
    cases hp : pol h i
    · simpa [hp] using hb
    · simpa [hp] using ha
  · cases hp : pol h j <;> simp [hj, hp]

/-- The two inequalities at one step are actual constructor inequalities
over the SAME trees, not independently split positive/negative valuations. -/
def GadgetHolds : Spine arity → Tree pol → Tree pol → Prop
  | .stop a b, x, y =>
      lowHead pol a ≤ x ∧ y ≤ highHead pol b
  | .step h i s, x, y =>
      ∃ u v : Tree pol,
        lowerShell pol h i u v ≤ x ∧
        y ≤ upperShell pol h i u v ∧
        GadgetHolds s u v

theorem gadget_self (s : Spine arity) :
    GadgetHolds pol s (lower pol s) (upper pol s) := by
  induction s with
  | stop a b =>
    change lowHead pol a ≤ lowHead pol a ∧
      highHead pol b ≤ highHead pol b
    exact ⟨le_rfl, le_rfl⟩
  | step h i s ih =>
    change ∃ u v : Tree pol,
      lowerShell pol h i u v ≤ lower pol (.step h i s) ∧
      upper pol (.step h i s) ≤ upperShell pol h i u v ∧
      GadgetHolds pol s u v
    refine ⟨lower pol s, upper pol s, ?_, ?_, ih⟩
    · rw [lower_step]
    · rw [upper_step]

theorem gadget_weaken (s : Spine arity) {x y x' y' : Tree pol}
    (hg : GadgetHolds pol s x y) (hx : x ≤ x') (hy : y' ≤ y) :
    GadgetHolds pol s x' y' := by
  cases s with
  | stop a b =>
    change lowHead pol a ≤ x ∧ y ≤ highHead pol b at hg
    change lowHead pol a ≤ x' ∧ y' ≤ highHead pol b
    exact ⟨hg.1.trans hx, hy.trans hg.2⟩
  | step h i s =>
    rcases hg with ⟨u,v,hl,hr,ht⟩
    exact ⟨u,v,hl.trans hx,hy.trans hr,ht⟩

theorem gadget_to_fits (s : Spine arity) (x y : Tree pol)
    (hg : GadgetHolds pol s x y) : Fits pol s x y := by
  induction s generalizing x y with
  | stop a b =>
    exact hg
  | step h i s ih =>
    obtain ⟨u,v,hl,hr,ht⟩ := hg
    have hh : Fits pol s u v := ih u v ht
    constructor
    · calc
        lower pol (.step h i s) =
          lowerShell pol h i (lower pol s) (upper pol s) := lower_step pol h i s
        _ ≤ lowerShell pol h i u v := lowerShell_mono pol h i hh.1 hh.2
        _ ≤ x := hl
    · calc
        y ≤ upperShell pol h i u v := hr
        _ ≤ upperShell pol h i (lower pol s) (upper pol s) :=
          upperShell_mono pol h i hh.1 hh.2
        _ = upper pol (.step h i s) := (upper_step pol h i s).symm

theorem gadget_iff_fits (s : Spine arity) (x y : Tree pol) :
    GadgetHolds pol s x y ↔ Fits pol s x y := by
  constructor
  · exact gadget_to_fits pol s x y
  · intro hf
    exact gadget_weaken pol s (gadget_self pol s) hf.1 hf.2

/-- Exact, UNBOUNDED counterexample/gadget characterization for the
original mixed-variance order. This does not supply a short-spine theorem. -/
theorem not_le_iff_gadget (x y : Tree pol) :
    ¬ x ≤ y ↔ ∃ s : Spine arity, s.Valid ∧ GadgetHolds pol s x y := by
  constructor
  · intro hn
    obtain ⟨s,hv,hf⟩ := (not_le_iff_spine pol x y).mp hn
    exact ⟨s,hv,(gadget_iff_fits pol s x y).mpr hf⟩
  · rintro ⟨s,hv,hg⟩
    exact (not_le_iff_spine pol x y).mpr
      ⟨s,hv,(gadget_iff_fits pol s x y).mp hg⟩

end NSSE.MultiVarianceSpineGadget
