import NSSE.MultiVarianceClasses

/-! Finite separating spines in the ORIGINAL head-dependent signed order.
A negative selected child swaps the two recursive bounds. No least model,
independent signed value variables, or a priori path bound is assumed. -/
namespace NSSE.MultiVarianceSpineSeparation
open MultiVarianceEncoding MultiVarianceTrees
open MultiConstructorTrees (Label)
variable {H : Type*} {arity : H → Nat}

inductive Spine (arity : H → Nat)
  | stop (left right : Label H)
  | step (head : H) (child : Fin (arity head)) (rest : Spine arity)

def Spine.depth : Spine arity → Nat
  | .stop _ _ => 0
  | .step _ _ s => s.depth + 1

def Spine.Valid : Spine arity → Prop
  | .stop a b => ¬ a ≤ b
  | .step _ _ s => s.Valid

variable (pol : Polarity arity)

def root (t : Tree pol) : Label H := t.raw.label []

@[simp] theorem root_bot : root pol (⊥ : Tree pol) = .bot := rfl
@[simp] theorem root_top : root pol (⊤ : Tree pol) = .top := rfl
@[simp] theorem root_node (h : H) (c : Fin (arity h) → Tree pol) :
    root pol (node h c) = .node h := rfl

theorem root_mono {a b : Tree pol} (hab : a ≤ b) : root pol a ≤ root pol b := by
  change encoded a ≤ encoded b at hab
  have hh := hab []
  simpa only [encoded, encode_root, sign, Bool.false_eq_true, if_false] using hh

def lowFill (h : H) (i : Fin (arity h)) : Tree pol :=
  if pol h i then ⊤ else ⊥

def highFill (h : H) (i : Fin (arity h)) : Tree pol :=
  if pol h i then ⊥ else ⊤

def lowHead : Label H → Tree pol
  | .bot => ⊥
  | .top => ⊤
  | .node h => node h (lowFill pol h)

def highHead : Label H → Tree pol
  | .bot => ⊥
  | .top => ⊤
  | .node h => node h (highFill pol h)

@[simp] theorem root_lowHead (e : Label H) : root pol (lowHead pol e) = e := by
  cases e <;> rfl

@[simp] theorem root_highHead (e : Label H) : root pol (highHead pol e) = e := by
  cases e <;> rfl

theorem lowHead_le (t : Tree pol) : lowHead pol (root pol t) ≤ t := by
  rcases root_cases t with rfl | rfl | ⟨h,c,rfl⟩
  · exact le_rfl
  · exact le_rfl
  · apply (node_le_node h _ c).mpr
    intro i
    cases hp : pol h i <;> simp [lowFill, hp]

theorem le_highHead (t : Tree pol) : t ≤ highHead pol (root pol t) := by
  rcases root_cases t with rfl | rfl | ⟨h,c,rfl⟩
  · exact le_rfl
  · exact le_rfl
  · apply (node_le_node h c _).mpr
    intro i
    cases hp : pol h i <;> simp [highFill, hp]

def bounds : Spine arity → Tree pol × Tree pol
  | .stop a b => (lowHead pol a, highHead pol b)
  | .step h i s =>
    let t := bounds s
    (node h (fun j => if j = i then (if pol h i then t.2 else t.1) else lowFill pol h j),
     node h (fun j => if j = i then (if pol h i then t.1 else t.2) else highFill pol h j))

def lower (s : Spine arity) : Tree pol := (bounds pol s).1
def upper (s : Spine arity) : Tree pol := (bounds pol s).2

def Fits (s : Spine arity) (a b : Tree pol) : Prop := lower pol s ≤ a ∧ b ≤ upper pol s

theorem fits_stop (a b : Tree pol) :
    Fits pol (.stop (root pol a) (root pol b)) a b :=
  ⟨lowHead_le pol a, le_highHead pol b⟩

theorem fits_step (h : H) (i : Fin (arity h)) (s : Spine arity)
    (a b : Fin (arity h) → Tree pol)
    (hs : if pol h i then Fits pol s (b i) (a i) else Fits pol s (a i) (b i)) :
    Fits pol (.step h i s) (node h a) (node h b) := by
  constructor
  · apply (node_le_node h _ a).mpr
    intro j
    by_cases hj : j = i
    · subst j
      cases hp : pol h i
      · simp only [hp, Bool.false_eq_true, if_false] at hs
        simpa [lower, bounds, hp] using hs.1
      · simp only [hp, if_true] at hs
        simpa [upper, bounds, hp] using hs.2
    · cases hp : pol h j <;> simp [lower, bounds, hj, lowFill, hp]
  · apply (node_le_node h b _).mpr
    intro j
    by_cases hj : j = i
    · subst j
      cases hp : pol h i
      · simp only [hp, Bool.false_eq_true, if_false] at hs
        simpa [upper, bounds, hp] using hs.2
      · simp only [hp, if_true] at hs
        simpa [lower, bounds, hp] using hs.1
    · cases hp : pol h j <;> simp [upper, bounds, hj, highFill, hp]

theorem bounds_not_ordered (s : Spine arity) (hv : s.Valid) :
    ¬ lower pol s ≤ upper pol s := by
  induction s with
  | stop a b =>
    intro ho
    have hh := root_mono pol ho
    exact hv (by simpa [lower, upper, bounds] using hh)
  | step h i s ih =>
    intro ho
    have hc := (node_le_node h _ _).mp ho i
    apply ih hv
    cases hp : pol h i <;> simpa [lower, upper, bounds, hp] using hc

theorem fits_not_ordered (s : Spine arity) (hv : s.Valid)
    {a b : Tree pol} (hs : Fits pol s a b) : ¬ a ≤ b := by
  intro hab
  exact bounds_not_ordered pol s hv (hs.1.trans (hab.trans hs.2))

/-- Absence of every finite separating spine is a structural simulation. -/
theorem le_of_no_spine (a b : Tree pol)
    (hn : ¬ ∃ s : Spine arity, s.Valid ∧ Fits pol s a b) : a ≤ b := by
  classical
  apply coinduction (fun a b => ¬ ∃ s : Spine arity, s.Valid ∧ Fits pol s a b) _ a b hn
  intro a b hab
  have hr : root pol a ≤ root pol b := by
    by_contra hh
    exact hab ⟨.stop (root pol a) (root pol b), hh, fits_stop pol a b⟩
  rcases root_cases a with rfl | rfl | ⟨h,ca,rfl⟩
  · exact Or.inl rfl
  · rcases root_cases b with rfl | rfl | ⟨k,cb,rfl⟩
    · change (Label.top : Label H) ≤ Label.bot at hr
      rcases hr with hh | hh | hh <;> cases hh
    · exact Or.inr (Or.inl rfl)
    · exact False.elim ((Label.top_not_le_node k) hr)
  · rcases root_cases b with rfl | rfl | ⟨k,cb,rfl⟩
    · exact False.elim ((Label.node_not_le_bot h) hr)
    · exact Or.inr (Or.inl rfl)
    · have hk : h = k := (Label.node_le_node h k).mp hr
      subst k
      refine Or.inr (Or.inr ⟨h,ca,cb,rfl,rfl,?_⟩)
      intro i
      cases hp : pol h i
      · simp only [hp, Bool.false_eq_true, if_false]
        rintro ⟨s,hv,hs⟩
        exact hab ⟨.step h i s,hv,fits_step pol h i s ca cb (by simpa [hp] using hs)⟩
      · simp only [hp, if_true]
        rintro ⟨s,hv,hs⟩
        exact hab ⟨.step h i s,hv,fits_step pol h i s ca cb (by simpa [hp] using hs)⟩

/-- Exact finite-spine characterization, with no depth premise. -/
theorem not_le_iff_spine (a b : Tree pol) :
    ¬ a ≤ b ↔ ∃ s : Spine arity, s.Valid ∧ Fits pol s a b := by
  classical
  constructor
  · intro hab
    by_contra hn
    exact hab (le_of_no_spine pol a b hn)
  · rintro ⟨s,hv,hs⟩
    exact fits_not_ordered pol s hv hs

end NSSE.MultiVarianceSpineSeparation
