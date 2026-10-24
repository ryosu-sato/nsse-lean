import NSSE.ContraConstraints
import NSSE.HornCompiler
import NSSE.SubtypeConstraintOperations

/-! # Polarity-aware support closure of a flat contravariant system (stage S2)

Notes v1361 §2, v1362 §2. The support relation `x ≤s y` of a four-form system
`φ` under the polarity vector `POL` is the least relation closed under

* reflexivity and transitivity,
* polarity-aware decomposition: for an ORIGINAL lower literal `f(c̄) ≤ v` and an
  ORIGINAL upper literal `v' ≤ f(c̄')` with `v ≤s v'`, infer `c_i ≤s c'_i` at a
  covariant position `i` and `c'_i ≤s c_i` at a contravariant position `i`.

The bottom/top rules are, as in the covariant journal Table 1, the derived
predicates `SupportedBot x :⟺ ∃ y ∈ bot, x ≤s y` and
`SupportedTop x :⟺ ∃ y ∈ top, y ≤s x`; the child bounds `SupportedUpper` and
`SupportedLower` are the polarity-aware ones of v1362 §2.

Everything is sound in EVERY model of the abstract contravariant constructor law
(`ContraConstructor`), in particular for arbitrary, regular and finite trees.

The relation is computed exactly by the finite Horn kernel (`HornCompiler`) on
the `n*n` variable pairs; `table_correct` certifies the Boolean matrix.
-/

namespace NSSE.ContraSupport

open SubtypeConstraints (Constraints Query BoundLiteral)
open ContraTrees ContraConstraints

variable {n d : Nat}

/-! ## The relation -/

/-- Polarity-aware syntactic support `≤s`. -/
inductive Support (POL : Polarity d) (φ : Constraints n d) : Fin n → Fin n → Prop
  | refl (x : Fin n) : Support POL φ x x
  | trans {x y z : Fin n} : Support POL φ x y → Support POL φ y z → Support POL φ x z
  /-- Decomposition at a covariant position. -/
  | decompCov {a b : BoundLiteral n d} (ha : a ∈ φ.lower) (hb : b ∈ φ.upper)
      (h : Support POL φ a.1 b.1) (i : Fin d) (hi : POL i = false) :
      Support POL φ (a.2 i) (b.2 i)
  /-- Decomposition at a contravariant position (the children swap). -/
  | decompCon {a b : BoundLiteral n d} (ha : a ∈ φ.lower) (hb : b ∈ φ.upper)
      (h : Support POL φ a.1 b.1) (i : Fin d) (hi : POL i = true) :
      Support POL φ (b.2 i) (a.2 i)

variable {POL : Polarity d}

/-- The directed child relation `c ≤_{POL i} c'`: `c ≤s c'` at a covariant and
`c' ≤s c` at a contravariant position. -/
def SupportAt (POL : Polarity d) (φ : Constraints n d) (i : Fin d) (u v : Fin n) : Prop :=
  if POL i = true then Support POL φ v u else Support POL φ u v

/-- Decomposition in one statement. -/
theorem Support.decomp {φ : Constraints n d} {a b : BoundLiteral n d} (ha : a ∈ φ.lower)
    (hb : b ∈ φ.upper) (h : Support POL φ a.1 b.1) (i : Fin d) :
    SupportAt POL φ i (a.2 i) (b.2 i) := by
  unfold SupportAt
  cases hp : POL i
  · simpa using Support.decompCov ha hb h i hp
  · simpa using Support.decompCon ha hb h i hp

/-! ## Derived predicates: child bounds and the bottom/top rules (v1362 §2) -/

/-- `upper(u,i,z)`: some original `v ≤ f(d̄)` with `u ≤s v` and `d_i ≤s z`
(covariant `i`) resp. `z ≤s d_i` (contravariant `i`). -/
def SupportedUpper (POL : Polarity d) (φ : Constraints n d) (u : Fin n) (i : Fin d) (z : Fin n) :
    Prop :=
  ∃ a ∈ φ.upper, Support POL φ u a.1 ∧ SupportAt POL φ i (a.2 i) z

/-- `lower(u,i,z)`: some original `f(c̄) ≤ v` with `v ≤s u` and `z ≤s c_i`
(covariant `i`) resp. `c_i ≤s z` (contravariant `i`). -/
def SupportedLower (POL : Polarity d) (φ : Constraints n d) (u : Fin n) (i : Fin d) (z : Fin n) :
    Prop :=
  ∃ a ∈ φ.lower, SupportAt POL φ i z (a.2 i) ∧ Support POL φ a.1 u

def SupportedBot (POL : Polarity d) (φ : Constraints n d) (x : Fin n) : Prop :=
  ∃ y ∈ φ.bot, Support POL φ x y

def SupportedTop (POL : Polarity d) (φ : Constraints n d) (x : Fin n) : Prop :=
  ∃ y ∈ φ.top, Support POL φ y x

/-! ## Soundness in every model of the contravariant constructor law -/

section Soundness

variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

/-- The constructor law read at one position, as a directed relation. -/
def LeAt (POL : Polarity d) (i : Fin d) (s t : T) : Prop := if POL i = true then t ≤ s else s ≤ t

omit [OrderBot T] [OrderTop T] in
theorem le_node_at (F : ContraConstructor T POL) {a b : Fin d → T} (h : F.node a ≤ F.node b)
    (i : Fin d) : LeAt POL i (a i) (b i) := by
  have hi := ((F.le_iff a b).mp h) i
  unfold LeAt
  cases hp : POL i
  · exact hi.2 hp
  · simpa using hi.1 hp

/-- **Soundness of `≤s`.** -/
theorem support_sound (F : ContraConstructor T POL) (φ : Constraints n d) (ρ : Fin n → T)
    (hρ : Satisfies F φ ρ) {x y : Fin n} (h : Support POL φ x y) : ρ x ≤ ρ y := by
  induction h with
  | refl x => exact le_rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | @decompCov a b ha hb _ i hi ih =>
      have := le_node_at F ((hρ.2.1 a ha).trans (ih.trans (hρ.1 b hb))) i
      simpa [LeAt, hi] using this
  | @decompCon a b ha hb _ i hi ih =>
      have := le_node_at F ((hρ.2.1 a ha).trans (ih.trans (hρ.1 b hb))) i
      simpa [LeAt, hi] using this

theorem supportAt_sound (F : ContraConstructor T POL) (φ : Constraints n d) (ρ : Fin n → T)
    (hρ : Satisfies F φ ρ) {i : Fin d} {u v : Fin n} (h : SupportAt POL φ i u v) :
    LeAt POL i (ρ u) (ρ v) := by
  unfold SupportAt at h; unfold LeAt
  split_ifs at h ⊢ <;> exact support_sound F φ ρ hρ h

omit [OrderBot T] [OrderTop T] in
/-- Replacing one child of a constructor along the directed relation moves the
node in the stated direction. -/
theorem node_update_le (F : ContraConstructor T POL) (c : Fin d → T) (i : Fin d) (t : T)
    (h : LeAt POL i (c i) t) :
    F.node c ≤ F.node (fun j => if j = i then t else c j) := by
  apply (F.le_iff _ _).mpr
  intro j
  by_cases hj : j = i
  · subst j
    unfold LeAt at h
    constructor
    · intro hp; simpa [hp] using h
    · intro hp; simpa [hp] using h
  · simp [hj]

omit [OrderBot T] [OrderTop T] in
theorem update_node_le (F : ContraConstructor T POL) (c : Fin d → T) (i : Fin d) (t : T)
    (h : LeAt POL i t (c i)) :
    F.node (fun j => if j = i then t else c j) ≤ F.node c := by
  apply (F.le_iff _ _).mpr
  intro j
  by_cases hj : j = i
  · subst j
    unfold LeAt at h
    constructor
    · intro hp; simpa [hp] using h
    · intro hp; simpa [hp] using h
  · simp [hj]

/-- **v1362 Lemma 2, upper half.** `upper(u,i,z)` gives an f-node above `ρ(u)`
whose `i`-th child is `ρ(z)`. Projected: `P_i ρ(u) ≤ ρ(z)` (covariant) resp.
`ρ(z) ≤ P_i ρ(u)` (contravariant) unless `ρ(u) = ⊤`. -/
theorem supportedUpper_sound (F : ContraConstructor T POL) (φ : Constraints n d) (ρ : Fin n → T)
    (hρ : Satisfies F φ ρ) {u z : Fin n} {i : Fin d} (h : SupportedUpper POL φ u i z) :
    ∃ children : Fin d → T, children i = ρ z ∧ ρ u ≤ F.node children := by
  obtain ⟨a, ha, hu, hz⟩ := h
  refine ⟨fun j => if j = i then ρ z else ρ (a.2 j), by simp, ?_⟩
  refine (support_sound F φ ρ hρ hu).trans ((hρ.1 a ha).trans ?_)
  exact node_update_le F (fun j => ρ (a.2 j)) i (ρ z) (supportAt_sound F φ ρ hρ hz)

/-- **v1362 Lemma 2, lower half.** -/
theorem supportedLower_sound (F : ContraConstructor T POL) (φ : Constraints n d) (ρ : Fin n → T)
    (hρ : Satisfies F φ ρ) {u z : Fin n} {i : Fin d} (h : SupportedLower POL φ u i z) :
    ∃ children : Fin d → T, children i = ρ z ∧ F.node children ≤ ρ u := by
  obtain ⟨a, ha, hz, hu⟩ := h
  refine ⟨fun j => if j = i then ρ z else ρ (a.2 j), by simp, ?_⟩
  refine le_trans ?_ ((hρ.2.1 a ha).trans (support_sound F φ ρ hρ hu))
  exact update_node_le F (fun j => ρ (a.2 j)) i (ρ z) (supportAt_sound F φ ρ hρ hz)

theorem supportedBot_sound (F : ContraConstructor T POL) (φ : Constraints n d) (ρ : Fin n → T)
    (hρ : Satisfies F φ ρ) {x : Fin n} (h : SupportedBot POL φ x) : ρ x = ⊥ := by
  obtain ⟨y, hy, hs⟩ := h
  apply le_antisymm ?_ bot_le
  simpa only [hρ.2.2.1 y hy] using support_sound F φ ρ hρ hs

theorem supportedTop_sound (F : ContraConstructor T POL) (φ : Constraints n d) (ρ : Fin n → T)
    (hρ : Satisfies F φ ρ) {x : Fin n} (h : SupportedTop POL φ x) : ρ x = ⊤ := by
  obtain ⟨y, hy, hs⟩ := h
  apply le_antisymm le_top
  simpa only [hρ.2.2.2 y hy] using support_sound F φ ρ hρ hs

end Soundness

/-! ## Transport through literal renamings (for term flattening, S7) -/

open SubtypeConstraintOperations in
theorem support_map {m : Nat} (φ : Constraints n d) (ψ : Constraints m d) (f : Fin n → Fin m)
    (hl : ∀ a ∈ φ.lower, renameBound f a ∈ ψ.lower)
    (hu : ∀ a ∈ φ.upper, renameBound f a ∈ ψ.upper)
    {x y : Fin n} (h : Support POL φ x y) : Support POL ψ (f x) (f y) := by
  induction h with
  | refl x => exact .refl _
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | @decompCov a b ha hb _ i hi ih => exact .decompCov (hl a ha) (hu b hb) ih i hi
  | @decompCon a b ha hb _ i hi ih => exact .decompCon (hl a ha) (hu b hb) ih i hi

/-! ## Exact executable closure via the finite Horn kernel -/

def pairId (x y : Fin n) : Nat := (finProdFinEquiv (x, y)).val

theorem pairId_lt (x y : Fin n) : pairId x y < n * n := (finProdFinEquiv (x, y)).isLt

theorem pairId_injective {x y u v : Fin n} (h : pairId x y = pairId u v) : x = u ∧ y = v := by
  have he : finProdFinEquiv (x, y) = finProdFinEquiv (u, v) := Fin.ext h
  exact Prod.mk.inj (finProdFinEquiv.injective he)

def terminal (n : Nat) (s : Nat) : Bool :=
  if hs : s < n * n then
    let p : Fin n × Fin n := finProdFinEquiv.symm ⟨s, hs⟩
    decide (p.1 = p.2)
  else false

theorem terminal_pair (x y : Fin n) : terminal n (pairId x y) = true ↔ x = y := by
  rw [terminal, dif_pos (pairId_lt x y)]
  change decide ((finProdFinEquiv.symm (finProdFinEquiv (x, y))).1 =
    (finProdFinEquiv.symm (finProdFinEquiv (x, y))).2) = true ↔ x = y
  simp only [Equiv.symm_apply_apply, decide_eq_true_eq]

def transRule (x y z : Fin n) : HornRule := ⟨pairId x z, [pairId x y, pairId y z]⟩

/-- The decomposition rule at position `i`, oriented by the polarity bit. -/
def decompRule (POL : Polarity d) (a b : BoundLiteral n d) (i : Fin d) : HornRule :=
  if POL i = true then ⟨pairId (b.2 i) (a.2 i), [pairId a.1 b.1]⟩
  else ⟨pairId (a.2 i) (b.2 i), [pairId a.1 b.1]⟩

def transRules (n : Nat) : List HornRule :=
  (List.finRange n).flatMap fun x => (List.finRange n).flatMap fun y =>
    (List.finRange n).map fun z => transRule x y z

def decompRules (POL : Polarity d) (φ : Constraints n d) : List HornRule :=
  φ.lower.flatMap fun a => φ.upper.flatMap fun b => (List.finRange d).map (decompRule POL a b)

theorem mem_transRules (r : HornRule) :
    r ∈ transRules n ↔ ∃ x y z : Fin n, transRule x y z = r := by
  simp [transRules]

theorem mem_decompRules (φ : Constraints n d) (r : HornRule) :
    r ∈ decompRules POL φ ↔ ∃ a ∈ φ.lower, ∃ b ∈ φ.upper, ∃ i, decompRule POL a b i = r := by
  simp [decompRules]

def compiler (POL : Polarity d) (φ : Constraints n d) : FiniteHornCompiler where
  stateCount := n * n
  terminal := terminal n
  rules := transRules n ++ decompRules POL φ

theorem support_derives (φ : Constraints n d) {x y : Fin n} (h : Support POL φ x y) :
    HornDerives (compiler POL φ) (pairId x y) := by
  induction h with
  | refl x => exact .terminal (pairId_lt x x) ((terminal_pair x x).mpr rfl)
  | @trans x y z _ _ ihxy ihyz =>
      apply HornDerives.rule (rule := transRule x y z)
      · exact List.mem_append.mpr (Or.inl ((mem_transRules _).mpr ⟨x, y, z, rfl⟩))
      · exact pairId_lt x z
      · intro s hs
        simp only [transRule, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact ihxy
        · exact ihyz
  | @decompCov a b ha hb _ i hi ih =>
      have hpar : (decompRule POL a b i).parent = pairId (a.2 i) (b.2 i) := by
        simp [decompRule, hi]
      rw [← hpar]
      apply HornDerives.rule (rule := decompRule POL a b i)
      · exact List.mem_append.mpr (Or.inr ((mem_decompRules φ _).mpr ⟨a, ha, b, hb, i, rfl⟩))
      · rw [hpar]; exact pairId_lt _ _
      · intro s hs
        simp only [decompRule, hi, Bool.false_eq_true, if_false, List.mem_singleton] at hs
        subst s; exact ih
  | @decompCon a b ha hb _ i hi ih =>
      have hpar : (decompRule POL a b i).parent = pairId (b.2 i) (a.2 i) := by
        simp [decompRule, hi]
      rw [← hpar]
      apply HornDerives.rule (rule := decompRule POL a b i)
      · exact List.mem_append.mpr (Or.inr ((mem_decompRules φ _).mpr ⟨a, ha, b, hb, i, rfl⟩))
      · rw [hpar]; exact pairId_lt _ _
      · intro s hs
        simp only [decompRule, hi, if_true, List.mem_singleton] at hs
        subst s; exact ih

def Meaning (POL : Polarity d) (φ : Constraints n d) (s : Nat) : Prop :=
  ∃ x y, pairId x y = s ∧ Support POL φ x y

theorem meaning_pair (φ : Constraints n d) (x y : Fin n) :
    Meaning POL φ (pairId x y) ↔ Support POL φ x y := by
  constructor
  · rintro ⟨u, v, he, h⟩
    obtain ⟨rfl, rfl⟩ := pairId_injective he
    exact h
  · intro h; exact ⟨x, y, rfl, h⟩

theorem derives_meaning (φ : Constraints n d) {s : Nat} (h : HornDerives (compiler POL φ) s) :
    Meaning POL φ s := by
  induction h with
  | @terminal s hs ht =>
      let p : Fin n × Fin n := finProdFinEquiv.symm ⟨s, hs⟩
      have he : pairId p.1 p.2 = s := congrArg Fin.val (finProdFinEquiv.apply_symm_apply ⟨s, hs⟩)
      have hp : p.1 = p.2 := (terminal_pair p.1 p.2).mp (by rwa [he])
      refine ⟨p.1, p.2, he, ?_⟩
      rw [← hp]
      exact .refl _
  | @rule r hr _ _ ih =>
      rcases List.mem_append.mp hr with ht | hd
      · obtain ⟨x, y, z, rfl⟩ := (mem_transRules _).mp ht
        exact ⟨x, z, rfl, .trans
          ((meaning_pair φ x y).mp (ih (pairId x y) (by simp [transRule])))
          ((meaning_pair φ y z).mp (ih (pairId y z) (by simp [transRule])))⟩
      · obtain ⟨a, ha, b, hb, i, rfl⟩ := (mem_decompRules φ _).mp hd
        cases hp : POL i
        · have hab : Support POL φ a.1 b.1 :=
            (meaning_pair φ a.1 b.1).mp (ih (pairId a.1 b.1) (by simp [decompRule, hp]))
          refine ⟨a.2 i, b.2 i, by simp [decompRule, hp], .decompCov ha hb hab i hp⟩
        · have hab : Support POL φ a.1 b.1 :=
            (meaning_pair φ a.1 b.1).mp (ih (pairId a.1 b.1) (by simp [decompRule, hp]))
          refine ⟨b.2 i, a.2 i, by simp [decompRule, hp], .decompCon ha hb hab i hp⟩

theorem derives_iff (φ : Constraints n d) (x y : Fin n) :
    HornDerives (compiler POL φ) (pairId x y) ↔ Support POL φ x y :=
  ⟨fun h => (meaning_pair φ x y).mp (derives_meaning φ h), support_derives φ⟩

/-- The exact support matrix, after the kernel's proved saturation. -/
def table (POL : Polarity d) (φ : Constraints n d) : Fin n → Fin n → Bool :=
  let mask := hornSemantic (compiler POL φ)
  fun x y => maskBit mask (pairId x y)

theorem table_correct (φ : Constraints n d) (x y : Fin n) :
    table POL φ x y = true ↔ Support POL φ x y :=
  (hornSemantic_bit_iff_derives (compiler POL φ) (pairId x y) (pairId_lt x y)).trans
    (derives_iff φ x y)

def supportDecision (φ : Constraints n d) (x y : Fin n) : Decidable (Support POL φ x y) :=
  decidable_of_iff (table POL φ x y = true) (table_correct φ x y)

instance (φ : Constraints n d) : DecidableRel (Support POL φ) := supportDecision φ

/-! ## The executable tables read by the later automaton stages (S3)

All five relations of v1362 §2 as Booleans computed from the original syntax. -/

/-- The directed child relation as a Boolean. -/
def atB (POL : Polarity d) (φ : Constraints n d) (i : Fin d) (u v : Fin n) : Bool :=
  if POL i = true then table POL φ v u else table POL φ u v

theorem atB_correct (φ : Constraints n d) (i : Fin d) (u v : Fin n) :
    atB POL φ i u v = true ↔ SupportAt POL φ i u v := by
  unfold atB SupportAt
  split_ifs <;> exact table_correct φ _ _

structure Tables (n d : Nat) where
  le : Fin n → Fin n → Bool
  upper : Fin n → Fin d → Fin n → Bool
  lower : Fin n → Fin d → Fin n → Bool
  bot : Fin n → Bool
  top : Fin n → Bool

def tables (POL : Polarity d) (φ : Constraints n d) : Tables n d :=
  let rel := table POL φ
  { le := rel
    upper := fun u i z => φ.upper.any (fun a => rel u a.1 && atB POL φ i (a.2 i) z)
    lower := fun u i z => φ.lower.any (fun a => atB POL φ i z (a.2 i) && rel a.1 u)
    bot := fun x => φ.bot.any (fun y => rel x y)
    top := fun x => φ.top.any (fun y => rel y x) }

theorem le_correct (φ : Constraints n d) (x y : Fin n) :
    (tables POL φ).le x y = true ↔ Support POL φ x y := table_correct φ x y

theorem upper_correct (φ : Constraints n d) (u : Fin n) (i : Fin d) (z : Fin n) :
    (tables POL φ).upper u i z = true ↔ SupportedUpper POL φ u i z := by
  simp [tables, List.any_eq_true, table_correct, atB_correct, SupportedUpper]

theorem lower_correct (φ : Constraints n d) (u : Fin n) (i : Fin d) (z : Fin n) :
    (tables POL φ).lower u i z = true ↔ SupportedLower POL φ u i z := by
  simp [tables, List.any_eq_true, table_correct, atB_correct, SupportedLower]

theorem bot_correct (φ : Constraints n d) (x : Fin n) :
    (tables POL φ).bot x = true ↔ SupportedBot POL φ x := by
  simp [tables, List.any_eq_true, table_correct, SupportedBot]

theorem top_correct (φ : Constraints n d) (x : Fin n) :
    (tables POL φ).top x = true ↔ SupportedTop POL φ x := by
  simp [tables, List.any_eq_true, table_correct, SupportedTop]

section TableSoundness

variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

theorem computed_le_sound (F : ContraConstructor T POL) (φ : Constraints n d) (ρ : Fin n → T)
    (hρ : Satisfies F φ ρ) {x y : Fin n} (h : (tables POL φ).le x y = true) : ρ x ≤ ρ y :=
  support_sound F φ ρ hρ ((le_correct φ x y).mp h)

theorem computed_upper_sound (F : ContraConstructor T POL) (φ : Constraints n d) (ρ : Fin n → T)
    (hρ : Satisfies F φ ρ) {u z : Fin n} {i : Fin d} (h : (tables POL φ).upper u i z = true) :
    ∃ children : Fin d → T, children i = ρ z ∧ ρ u ≤ F.node children :=
  supportedUpper_sound F φ ρ hρ ((upper_correct φ u i z).mp h)

theorem computed_lower_sound (F : ContraConstructor T POL) (φ : Constraints n d) (ρ : Fin n → T)
    (hρ : Satisfies F φ ρ) {u z : Fin n} {i : Fin d} (h : (tables POL φ).lower u i z = true) :
    ∃ children : Fin d → T, children i = ρ z ∧ F.node children ≤ ρ u :=
  supportedLower_sound F φ ρ hρ ((lower_correct φ u i z).mp h)

theorem computed_bot_sound (F : ContraConstructor T POL) (φ : Constraints n d) (ρ : Fin n → T)
    (hρ : Satisfies F φ ρ) {x : Fin n} (h : (tables POL φ).bot x = true) : ρ x = ⊥ :=
  supportedBot_sound F φ ρ hρ ((bot_correct φ x).mp h)

theorem computed_top_sound (F : ContraConstructor T POL) (φ : Constraints n d) (ρ : Fin n → T)
    (hρ : Satisfies F φ ρ) {x : Fin n} (h : (tables POL φ).top x = true) : ρ x = ⊤ :=
  supportedTop_sound F φ ρ hρ ((top_correct φ x).mp h)

end TableSoundness

/-! ## Sanity: the covariant special case -/

/-- With every position covariant, the polarity-aware closure is the journal's
covariant support relation. -/
theorem support_iff_covariant (hPOL : ∀ i, POL i = false) (φ : Constraints n d) (x y : Fin n) :
    Support POL φ x y ↔ SubtypeConstraints.Support φ x y := by
  constructor
  · intro h
    induction h with
    | refl x => exact .refl _
    | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
    | decompCov ha hb _ i _ ih => exact .decomp ha hb ih i
    | decompCon _ _ _ i hi _ => exact absurd hi (by simp [hPOL i])
  · intro h
    induction h with
    | refl x => exact .refl _
    | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
    | decomp ha hb _ i ih => exact .decompCov ha hb ih i (hPOL i)

end NSSE.ContraSupport
