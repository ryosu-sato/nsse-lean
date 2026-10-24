import NSSE.SubtypeTermFlattening
import NSSE.ContraTermSemantics

/-! # Flattening original nested terms to the four flat forms, contravariant law (S7)

Reused from the covariant program (signature-agnostic SYNTAX only):
`SubtypeTermLayout.Layout`, `layout`, `count`, `old`, `termSlot`, `edgeSlot`, `padding`,
`ref`, `padded`, `restrict`, and `SubtypeTermDefinitions.termClause` / `definitions`
(each subterm slot gets `x_t ≤ f(refs)` and `f(refs) ≤ x_t`, `x_t = ⊥`, `x_t = ⊤`;
these are exact equalities whatever the variance, by antisymmetry).

NOT reusable: the covariant edge clause. A premise inequality `a ≤ b` is encoded with a
fresh slot `e` and the chosen position `i`,
`f(…, x_low, …) ≤ e ≤ f(…, x_high, …)` (other children = the shared padding variable),
which yields `f(…x_low…) ≤ f(…x_high…)`. Covariantly (`POL i = false`) this is
`x_low ≤ x_high`, so `low = a`, `high = b` (the covariant clause). If position `i` is
CONTRAVARIANT (`POL i = true`) the constructor law flips it to `x_high ≤ x_low`, so the
clause must be emitted with `low = b`, `high = a`. Hence `edgeClause` depends on
`POL i`, and all semantic lemmas are reproved against `ContraConstructor.le_iff`.

The extension of a term valuation puts `e := f(padded i (value of low) ⊥)` in both cases.
-/

namespace NSSE.ContraTermFlattening

open SubtypeTerms (Term Query expanded terms left_mem_terms right_mem_terms pair_mem_terms)
open SubtypeTermLayout SubtypeTermDefinitions
open SubtypeConstraints (Constraints)
open SubtypeConstraintOperations (combine)
open ContraTrees ContraFiniteTrees ContraRegularTrees ContraConstraints ContraTermSemantics

variable {n d m : Nat} {POL : Polarity d}

/-! ## Variance-directed endpoints -/

/-- The endpoint placed on the LOWER side of the edge clause for `a ≤ b`. -/
def lowOf (POL : Polarity d) (i : Fin d) {α : Type*} (a b : α) : α :=
  if POL i = true then b else a

/-- The endpoint placed on the UPPER side of the edge clause for `a ≤ b`. -/
def highOf (POL : Polarity d) (i : Fin d) {α : Type*} (a b : α) : α :=
  if POL i = true then a else b

theorem lowOf_map (i : Fin d) {α β : Type*} (f : α → β) (a b : α) :
    f (lowOf POL i a b) = lowOf POL i (f a) (f b) := by
  unfold lowOf; split <;> rfl

theorem highOf_map (i : Fin d) {α β : Type*} (f : α → β) (a b : α) :
    f (highOf POL i a b) = highOf POL i (f a) (f b) := by
  unfold highOf; split <;> rfl

section Semantics

variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

/-- The directed comparison at position `i` (contravariant positions compare backwards). -/
def LeAt (POL : Polarity d) (i : Fin d) (a b : T) : Prop :=
  if POL i = true then b ≤ a else a ≤ b

omit [OrderBot T] [OrderTop T] in
theorem leAt_low_high (i : Fin d) (a b : T) :
    LeAt POL i (lowOf POL i a b) (highOf POL i a b) ↔ a ≤ b := by
  unfold LeAt lowOf highOf
  by_cases h : POL i = true <;> simp [h]

omit [OrderBot T] [OrderTop T] in
/-- Padded comparison under the contravariant law: only position `i` matters, in the
direction of `POL i`. -/
theorem padded_order (F : ContraConstructor T POL) (i : Fin d) (a b e : T) :
    F.node (padded i a e) ≤ F.node (padded i b e) ↔ LeAt POL i a b := by
  rw [F.le_iff]
  unfold LeAt
  constructor
  · intro h
    have hi := h i
    simp only [padded, if_pos rfl] at hi
    by_cases hp : POL i = true
    · rw [if_pos hp]; exact hi.1 hp
    · rw [if_neg hp]; exact hi.2 (by simpa using hp)
  · intro h j
    by_cases hj : j = i
    · subst hj
      simp only [padded, if_pos rfl]
      refine ⟨fun hp => ?_, fun hp => ?_⟩
      · rwa [if_pos hp] at h
      · rwa [if_neg (by simp [hp])] at h
    · simp only [padded, if_neg hj]
      exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩

/-! ## Flat satisfaction of combined and joined systems (contravariant semantics) -/

theorem satisfies_combine (F : ContraConstructor T POL) (φ ψ : Constraints m d) (ρ : Fin m → T) :
    ContraConstraints.Satisfies F (combine φ ψ) ρ ↔
      ContraConstraints.Satisfies F φ ρ ∧ ContraConstraints.Satisfies F ψ ρ := by
  simp only [combine, ContraConstraints.Satisfies, List.mem_append, or_imp, forall_and]
  tauto

theorem satisfies_join (F : ContraConstructor T POL) (xs : List (Constraints m d)) (σ : Fin m → T) :
    ContraConstraints.Satisfies F (join xs) σ ↔ ∀ φ ∈ xs, ContraConstraints.Satisfies F φ σ := by
  induction xs with
  | nil => simp [join, empty, ContraConstraints.Satisfies]
  | cons x xs ih =>
      change ContraConstraints.Satisfies F (combine x (join xs)) σ ↔ _
      rw [satisfies_combine, ih]
      simp

/-! ## Term definitions (reused syntax, contravariant semantics) -/

def Equation (F : ContraConstructor T POL) (L : Layout n d) (σ : Fin L.count → T) :
    Term n d → Prop
  | .var _ => True
  | .bot => σ (L.ref .bot) = ⊥
  | .top => σ (L.ref .top) = ⊤
  | .node c => σ (L.ref (.node c)) = F.node (fun i => σ (L.ref (c i)))

theorem termClause_correct (F : ContraConstructor T POL) (L : Layout n d) (σ : Fin L.count → T)
    (t : Term n d) : ContraConstraints.Satisfies F (termClause L t) σ ↔ Equation F L σ t := by
  have heq (a b : T) : a ≤ b ∧ b ≤ a ↔ a = b :=
    ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨le_of_eq h, le_of_eq h.symm⟩⟩
  cases t <;> simp [termClause, empty, Equation, ContraConstraints.Satisfies, heq]

theorem definitions_correct (F : ContraConstructor T POL) (L : Layout n d) (σ : Fin L.count → T) :
    ContraConstraints.Satisfies F (definitions L) σ ↔ ∀ t ∈ L.terms, Equation F L σ t := by
  simp only [definitions, satisfies_join, List.forall_mem_map, termClause_correct]

/-- Under the definitions, every listed term's slot carries the term's value. -/
theorem term_value (F : ContraConstructor T POL) (L : Layout n d) (hc : Closed L)
    (σ : Fin L.count → T) (hσ : ContraConstraints.Satisfies F (definitions L) σ)
    (t : Term n d) (hm : t ∈ L.terms) : σ (L.ref t) = eval F (L.restrict σ) t := by
  have he := (definitions_correct F L σ).mp hσ
  induction t with
  | var x => rfl
  | bot => exact he .bot hm
  | top => exact he .top hm
  | node c ih =>
      have hn := he (.node c) hm
      change σ (L.ref (.node c)) = F.node (fun i => σ (L.ref (c i))) at hn
      rw [hn]
      exact congrArg F.node (funext (fun i => ih i (hc c hm i)))

/-! ## The extension of a term valuation to the flat variables -/

/-- Old variables keep their values, term slots get the term values, edge slots get
`f(padded i (value of the low endpoint) ⊥)`, the padding variable gets `⊥`. -/
def cextend (POL : Polarity d) (L : Layout n d) (i : Fin d) (F : ContraConstructor T POL)
    (ρ : Fin n → T) : Fin L.count → T :=
  Fin.addCases ρ (Fin.addCases (fun j => eval F ρ L.terms[j.val])
    (Fin.addCases (fun j => F.node (padded i
        (lowOf POL i (eval F ρ L.pairs[j.val].1) (eval F ρ L.pairs[j.val].2)) ⊥))
      (fun _ => ⊥)))

@[simp] theorem cextend_old (L : Layout n d) (i : Fin d) (F : ContraConstructor T POL)
    (ρ : Fin n → T) (x : Fin n) : cextend POL L i F ρ (L.old x) = ρ x := by
  simp [cextend, Layout.old]

@[simp] theorem restrict_cextend (L : Layout n d) (i : Fin d) (F : ContraConstructor T POL)
    (ρ : Fin n → T) : L.restrict (cextend POL L i F ρ) = ρ := by
  funext x
  exact cextend_old L i F ρ x

@[simp] theorem cextend_termSlot (L : Layout n d) (i : Fin d) (F : ContraConstructor T POL)
    (ρ : Fin n → T) (j : Fin L.terms.length) :
    cextend POL L i F ρ (L.termSlot j) = eval F ρ L.terms[j.val] := by
  simp [cextend, Layout.termSlot, Fin.addCases_right]

@[simp] theorem cextend_edgeSlot (L : Layout n d) (i : Fin d) (F : ContraConstructor T POL)
    (ρ : Fin n → T) (j : Fin L.pairs.length) :
    cextend POL L i F ρ (L.edgeSlot j) = F.node (padded i
        (lowOf POL i (eval F ρ L.pairs[j.val].1) (eval F ρ L.pairs[j.val].2)) ⊥) := by
  simp [cextend, Layout.edgeSlot, Fin.addCases_right]

@[simp] theorem cextend_padding (L : Layout n d) (i : Fin d) (F : ContraConstructor T POL)
    (ρ : Fin n → T) : cextend POL L i F ρ L.padding = ⊥ := by
  simp [cextend, Layout.padding, Fin.addCases_right]

theorem cextend_ref (L : Layout n d) (i : Fin d) (F : ContraConstructor T POL)
    (ρ : Fin n → T) (t : Term n d) (h : t ∈ L.terms) :
    cextend POL L i F ρ (L.ref t) = eval F ρ t := by
  cases t with
  | var x => exact cextend_old L i F ρ x
  | bot => simp only [Layout.ref, dif_pos h, cextend_termSlot, List.getElem_idxOf]
  | top => simp only [Layout.ref, dif_pos h, cextend_termSlot, List.getElem_idxOf]
  | node c => simp only [Layout.ref, dif_pos h, cextend_termSlot, List.getElem_idxOf]

/-- The extension stays in any class closed under `⊥`, `⊤`, the constructor. -/
theorem cextend_closed (L : Layout n d) (i : Fin d) (F : ContraConstructor T POL) (P : T → Prop)
    (hb : P ⊥) (ht : P ⊤) (hn : ∀ c, (∀ j, P (c j)) → P (F.node c))
    (ρ : Fin n → T) (hρ : ∀ x, P (ρ x)) : ∀ x, P (cextend POL L i F ρ x) := by
  apply Fin.addCases
  · intro x
    simp only [cextend, Fin.addCases_left]
    exact hρ x
  · apply Fin.addCases
    · intro j
      simp only [cextend, Fin.addCases_right, Fin.addCases_left]
      exact eval_closed F P hb ht hn ρ hρ L.terms[j.val]
    · apply Fin.addCases
      · intro k
        simp only [cextend, Fin.addCases_right, Fin.addCases_left]
        apply hn
        intro j
        by_cases hj : j = i
        · simp only [padded, if_pos hj, lowOf]
          split
          · exact eval_closed F P hb ht hn ρ hρ _
          · exact eval_closed F P hb ht hn ρ hρ _
        · simpa only [padded, if_neg hj] using hb
      · intro k
        simp only [cextend, Fin.addCases_right]
        exact hb

theorem cextend_definitions (L : Layout n d) (hc : Closed L) (i : Fin d)
    (F : ContraConstructor T POL) (ρ : Fin n → T) :
    ContraConstraints.Satisfies F (definitions L) (cextend POL L i F ρ) := by
  apply (definitions_correct F L _).mpr
  intro t hm
  cases t with
  | var x => trivial
  | bot => exact cextend_ref L i F ρ .bot hm
  | top => exact cextend_ref L i F ρ .top hm
  | node c =>
      change cextend POL L i F ρ (L.ref (.node c)) =
        F.node (fun j => cextend POL L i F ρ (L.ref (c j)))
      rw [cextend_ref L i F ρ (.node c) hm]
      exact congrArg F.node (funext (fun j => (cextend_ref L i F ρ (c j) (hc c hm j)).symm))

end Semantics

/-! ## The variance-directed edge clauses and the flattening -/

/-- The edge clause of premise pair `j`: `f(padded i x_low pad) ≤ e ≤ f(padded i x_high pad)`,
emitted as one upper and one lower flat literal on the fresh slot `e`. -/
def edgeClause (POL : Polarity d) (L : Layout n d) (i : Fin d) (j : Fin L.pairs.length) :
    Constraints L.count d :=
  ⟨[(L.edgeSlot j, padded i (L.ref (highOf POL i L.pairs[j.val].1 L.pairs[j.val].2)) L.padding)],
   [(L.edgeSlot j, padded i (L.ref (lowOf POL i L.pairs[j.val].1 L.pairs[j.val].2)) L.padding)],
   [], []⟩

def edges (POL : Polarity d) (L : Layout n d) (i : Fin d) : Constraints L.count d :=
  join ((List.finRange L.pairs.length).map (edgeClause POL L i))

/-- **The flattening.** Definitions of all subterm slots, plus one variance-directed edge
clause per expanded premise inequality; the query compares the slots of the two query
terms. All emitted literals are EXACTLY the four flat forms. -/
def flatten (POL : Polarity d) (Q : Query n d) (i : Fin d) :
    SubtypeConstraints.Query (layout Q).count d :=
  ⟨combine (definitions (layout Q)) (edges POL (layout Q) i),
    (layout Q).ref Q.left, (layout Q).ref Q.right⟩

/-- With all positions covariant, the contravariant flattening is literally the certified
covariant flattening (sanity check). -/
theorem flatten_covariant (hPOL : ∀ i, POL i = false) (Q : Query n d) (i : Fin d) :
    flatten POL Q i = SubtypeTermFlattening.flatten Q i := by
  have hl : ∀ {α : Type} (a b : α), lowOf POL i a b = a := by
    intro α a b; simp [lowOf, hPOL i]
  have hh : ∀ {α : Type} (a b : α), highOf POL i a b = b := by
    intro α a b; simp [highOf, hPOL i]
  have he : edgeClause POL (layout Q) i = SubtypeTermFlattening.edgeClause (layout Q) i := by
    funext j
    simp only [edgeClause, SubtypeTermFlattening.edgeClause, hl, hh]
  simp only [flatten, SubtypeTermFlattening.flatten, edges, SubtypeTermFlattening.edges, he]

section Semantics

variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

theorem edgeClause_correct (F : ContraConstructor T POL) (L : Layout n d) (i : Fin d)
    (σ : Fin L.count → T) (j : Fin L.pairs.length) :
    ContraConstraints.Satisfies F (edgeClause POL L i j) σ ↔
      σ (L.edgeSlot j) ≤ F.node (padded i
          (σ (L.ref (highOf POL i L.pairs[j.val].1 L.pairs[j.val].2))) (σ L.padding)) ∧
      F.node (padded i (σ (L.ref (lowOf POL i L.pairs[j.val].1 L.pairs[j.val].2))) (σ L.padding)) ≤
        σ (L.edgeSlot j) := by
  have hp (a e : Fin L.count) : (fun k => σ (padded i a e k)) = padded i (σ a) (σ e) := by
    funext k; unfold padded; split <;> rfl
  simp only [edgeClause, ContraConstraints.Satisfies, List.mem_singleton, forall_eq,
    List.not_mem_nil, false_imp_iff, implies_true, and_true, hp]

theorem edges_correct (F : ContraConstructor T POL) (L : Layout n d) (i : Fin d)
    (σ : Fin L.count → T) :
    ContraConstraints.Satisfies F (edges POL L i) σ ↔
      ∀ j : Fin L.pairs.length,
        σ (L.edgeSlot j) ≤ F.node (padded i
            (σ (L.ref (highOf POL i L.pairs[j.val].1 L.pairs[j.val].2))) (σ L.padding)) ∧
        F.node (padded i (σ (L.ref (lowOf POL i L.pairs[j.val].1 L.pairs[j.val].2))) (σ L.padding)) ≤
          σ (L.edgeSlot j) := by
  simp only [edges, satisfies_join, List.forall_mem_map, List.mem_finRange, forall_const,
    edgeClause_correct]

/-- The edge clauses force every premise pair, in the ORIGINAL direction, whatever the
variance of the chosen position. -/
theorem edges_imply (F : ContraConstructor T POL) (L : Layout n d) (i : Fin d)
    (σ : Fin L.count → T) (h : ContraConstraints.Satisfies F (edges POL L i) σ)
    (p : Term n d × Term n d) (hp : p ∈ L.pairs) : σ (L.ref p.1) ≤ σ (L.ref p.2) := by
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hp
  have he := (edges_correct F L i σ).mp h j
  have hle := (padded_order F i _ _ _).mp (he.2.trans he.1)
  rw [lowOf_map i (fun t => σ (L.ref t)), highOf_map i (fun t => σ (L.ref t)),
    leAt_low_high] at hle
  exact hle

theorem cextend_edges (F : ContraConstructor T POL) (Q : Query n d) (i : Fin d) (ρ : Fin n → T)
    (hρ : ContraTermSemantics.Satisfies F Q ρ) :
    ContraConstraints.Satisfies F (edges POL (layout Q) i) (cextend POL (layout Q) i F ρ) := by
  apply (edges_correct F (layout Q) i _).mpr
  intro j
  have hp : (expanded Q)[j.val] ∈ expanded Q := List.getElem_mem j.isLt
  obtain ⟨ha, hb⟩ := pair_mem_terms Q _ hp
  have he := (satisfies_iff_expanded F Q ρ).mp hρ _ hp
  have hlow : cextend POL (layout Q) i F ρ ((layout Q).ref
      (lowOf POL i (layout Q).pairs[j.val].1 (layout Q).pairs[j.val].2)) =
      lowOf POL i (eval F ρ (layout Q).pairs[j.val].1) (eval F ρ (layout Q).pairs[j.val].2) := by
    unfold lowOf; split
    · exact cextend_ref _ i F ρ _ hb
    · exact cextend_ref _ i F ρ _ ha
  have hhigh : cextend POL (layout Q) i F ρ ((layout Q).ref
      (highOf POL i (layout Q).pairs[j.val].1 (layout Q).pairs[j.val].2)) =
      highOf POL i (eval F ρ (layout Q).pairs[j.val].1) (eval F ρ (layout Q).pairs[j.val].2) := by
    unfold highOf; split
    · exact cextend_ref _ i F ρ _ ha
    · exact cextend_ref _ i F ρ _ hb
  rw [cextend_edgeSlot, hlow, hhigh, cextend_padding]
  refine ⟨(padded_order F i _ _ _).mpr ((leAt_low_high i _ _).mpr he), le_rfl⟩

/-- **Extension.** A term model extends to a model of the flat system. -/
theorem extension_spec (F : ContraConstructor T POL) (Q : Query n d) (i : Fin d) (ρ : Fin n → T)
    (hρ : ContraTermSemantics.Satisfies F Q ρ) :
    ContraConstraints.Satisfies F (flatten POL Q i).constraints (cextend POL (layout Q) i F ρ) := by
  apply (satisfies_combine F _ _ _).mpr
  exact ⟨cextend_definitions (layout Q) (layout_closed Q) i F ρ, cextend_edges F Q i ρ hρ⟩

theorem extension_left (F : ContraConstructor T POL) (Q : Query n d) (i : Fin d)
    (ρ : Fin n → T) :
    cextend POL (layout Q) i F ρ (flatten POL Q i).left = eval F ρ Q.left :=
  cextend_ref _ i F ρ Q.left (left_mem_terms Q)

theorem extension_right (F : ContraConstructor T POL) (Q : Query n d) (i : Fin d)
    (ρ : Fin n → T) :
    cextend POL (layout Q) i F ρ (flatten POL Q i).right = eval F ρ Q.right :=
  cextend_ref _ i F ρ Q.right (right_mem_terms Q)

/-- **Restriction.** A flat model restricts to a term model, and the query slots carry the
values of the query terms. -/
theorem restriction_spec (F : ContraConstructor T POL) (Q : Query n d) (i : Fin d)
    (σ : Fin (layout Q).count → T)
    (hσ : ContraConstraints.Satisfies F (flatten POL Q i).constraints σ) :
    ContraTermSemantics.Satisfies F Q ((layout Q).restrict σ) ∧
      eval F ((layout Q).restrict σ) Q.left = σ (flatten POL Q i).left ∧
      eval F ((layout Q).restrict σ) Q.right = σ (flatten POL Q i).right := by
  obtain ⟨hdef, hedge⟩ := (satisfies_combine F _ _ σ).mp hσ
  have hval := term_value F (layout Q) (layout_closed Q) σ hdef
  refine ⟨?_, (hval Q.left (left_mem_terms Q)).symm, (hval Q.right (right_mem_terms Q)).symm⟩
  apply (satisfies_iff_expanded F Q _).mpr
  intro p hp
  obtain ⟨ha, hb⟩ := pair_mem_terms Q p hp
  rw [← hval p.1 ha, ← hval p.2 hb]
  exact edges_imply F (layout Q) i σ hedge p hp

/-- **Satisfiability is preserved and reflected** (any contravariant model: arbitrary,
finite). -/
theorem satisfiable_iff (F : ContraConstructor T POL) (Q : Query n d) (i : Fin d) :
    ContraConstraints.Satisfiable F (flatten POL Q i).constraints ↔
      ContraTermSemantics.Satisfiable F Q := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨(layout Q).restrict σ, (restriction_spec F Q i σ hσ).1⟩
  · rintro ⟨ρ, hρ⟩
    exact ⟨cextend POL (layout Q) i F ρ, extension_spec F Q i ρ hρ⟩

/-- **Entailment is preserved and reflected** (any contravariant model: arbitrary, finite). -/
theorem entails_iff (F : ContraConstructor T POL) (Q : Query n d) (i : Fin d) :
    ContraConstraints.Entails F (flatten POL Q i) ↔ ContraTermSemantics.Entails F Q := by
  constructor
  · intro h ρ hρ
    have he := h _ (extension_spec F Q i ρ hρ)
    rwa [extension_left, extension_right] at he
  · intro h σ hσ
    obtain ⟨ho, hl, hr⟩ := restriction_spec F Q i σ hσ
    rw [← hl, ← hr]
    exact h _ ho

end Semantics

/-! ## Regular trees -/

theorem cextend_regular (Q : Query n d) (i : Fin d) (ρ : Fin n → CTree POL)
    (hρ : ∀ x, CRegular (ρ x)) :
    ∀ x, CRegular (cextend POL (layout Q) i (treeConstructor POL) ρ x) :=
  cextend_closed (layout Q) i (treeConstructor POL) CRegular cregular_bot cregular_top
    (fun _ h => cregular_node h) ρ hρ

theorem regularSatisfiable_iff (Q : Query n d) (i : Fin d) :
    ContraConstraints.RegularSatisfiable POL (flatten POL Q i).constraints ↔
      ContraTermSemantics.RegularSatisfiable POL Q := by
  constructor
  · rintro ⟨σ, hr, hσ⟩
    exact ⟨(layout Q).restrict σ, fun x => hr ((layout Q).old x),
      (restriction_spec (treeConstructor POL) Q i σ hσ).1⟩
  · rintro ⟨ρ, hr, hρ⟩
    exact ⟨cextend POL (layout Q) i (treeConstructor POL) ρ, cextend_regular Q i ρ hr,
      extension_spec (treeConstructor POL) Q i ρ hρ⟩

theorem regularEntails_iff (Q : Query n d) (i : Fin d) :
    ContraConstraints.RegularEntails POL (flatten POL Q i) ↔
      ContraTermSemantics.RegularEntails POL Q := by
  constructor
  · intro h ρ hr hρ
    have he := h _ (cextend_regular Q i ρ hr) (extension_spec (treeConstructor POL) Q i ρ hρ)
    rwa [extension_left, extension_right] at he
  · intro h σ hr hσ
    obtain ⟨ho, hl, hv⟩ := restriction_spec (treeConstructor POL) Q i σ hσ
    rw [← hl, ← hv]
    exact h ((layout Q).restrict σ) (fun x => hr ((layout Q).old x)) ho

end NSSE.ContraTermFlattening
