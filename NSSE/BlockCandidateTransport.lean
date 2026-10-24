import NSSE.UnifiedBlockPresentation

/-! # Exact transport of the entire regular candidate into the common word structure -/

namespace NSSE.BlockCandidateTransport

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks GuardedBlockRelation
open TerminalBorderRank TerminalCutGeometry SymbolicOutsideController
open UnifiedBlockPresentation SymbolicReachability

universe u v w
variable {L : FirstOrder.Language.{u, v}} {P : Type w} {k c : Nat} {ns : Fin k → Nat}

def filterNonempty {X Q : Type*} (T : NSSE.NFA X Q) (Good : X → Prop) : NSSE.NFA X (Option Q) where
  start q := match q with | none => True | some _ => False
  accept q := match q with | none => False | some q => T.accept q
  step q x r := match q, r with
    | _, none => False
    | none, some r => Good x ∧ ∃ q, T.start q ∧ T.step q x r
    | some q, some r => Good x ∧ T.step q x r

theorem filter_step_none {X Q : Type*} (T : NSSE.NFA X Q) (Good : X → Prop)
    (q : Option Q) (x : X) : ¬ (filterNonempty T Good).step q x none := by cases q <;> exact id

theorem filter_step_some {X Q : Type*} (T : NSSE.NFA X Q) (Good : X → Prop)
    (q r : Q) (x : X) : (filterNonempty T Good).step (some q) x (some r) ↔ Good x ∧ T.step q x r := Iff.rfl

theorem filter_step_start {X Q : Type*} (T : NSSE.NFA X Q) (Good : X → Prop)
    (r : Q) (x : X) : (filterNonempty T Good).step none x (some r) ↔
      Good x ∧ ∃ q, T.start q ∧ T.step q x r := Iff.rfl

theorem exists_option {Q : Type*} (P : Option Q → Prop) :
    (∃ q, P q) ↔ P none ∨ ∃ q, P (some q) := by
  constructor
  · rintro ⟨q, hq⟩
    cases q with
    | none => exact Or.inl hq
    | some q => exact Or.inr ⟨q, hq⟩
  · rintro (h | ⟨q, h⟩)
    · exact ⟨none, h⟩
    · exact ⟨some q, h⟩

theorem acceptFrom_some {X Q : Type*} (T : NSSE.NFA X Q) (Good : X → Prop) (q : Q) (xs : List X) :
    AcceptFrom (filterNonempty T Good) (some q) xs ↔
      (∀ x ∈ xs, Good x) ∧ AcceptFrom T q xs := by
  induction xs generalizing q with
  | nil => simp [acceptFrom_nil, filterNonempty]
  | cons x xs ih =>
      rw [acceptFrom_cons]
      simp only [exists_option, filter_step_none, filter_step_some, false_and, false_or, ih,
        List.forall_mem_cons, acceptFrom_cons]
      constructor
      · rintro ⟨r, ⟨hx, hs⟩, hxs, hr⟩
        exact ⟨⟨hx, hxs⟩, r, hs, hr⟩
      · rintro ⟨⟨hx, hxs⟩, r, hs, hr⟩
        exact ⟨r, ⟨hx, hs⟩, hxs, hr⟩

theorem filterNonempty_accepts {X Q : Type*} (T : NSSE.NFA X Q) (Good : X → Prop) (xs : List X) :
    (filterNonempty T Good).Accepts xs ↔ xs ≠ [] ∧ (∀ x ∈ xs, Good x) ∧ T.Accepts xs := by
  have ha : (filterNonempty T Good).Accepts xs ↔ AcceptFrom (filterNonempty T Good) none xs := by
    constructor
    · rintro ⟨q, r, hq, hrun, hr⟩
      cases q with
      | none => exact ⟨r, hrun, hr⟩
      | some q => exact hq.elim
    · rintro ⟨r, hrun, hr⟩
      exact ⟨none, r, trivial, hrun, hr⟩
  rw [ha]
  cases xs with
  | nil => simp [acceptFrom_nil, filterNonempty]
  | cons x xs =>
      rw [acceptFrom_cons]
      simp only [exists_option, filter_step_none, filter_step_start, false_and, false_or, acceptFrom_some,
        List.cons_ne_nil, not_false_eq_true, true_and, List.forall_mem_cons]
      constructor
      · rintro ⟨r, ⟨hx, q, hq, hs⟩, hxs, z, hrun, hz⟩
        exact ⟨by simp, ⟨hx, hxs⟩, q, z, hq, .cons hs hrun, hz⟩
      · rintro ⟨_, ⟨hx, hxs⟩, q, z, hq, hrun, hz⟩
        cases hrun with
        | cons hs hr => exact ⟨_, ⟨hx, q, hq, hs⟩, hxs, z, hr, hz⟩

theorem block_accepts (C : Row L P c) (seed last : P) {D : Type*} [L.Structure D]
    (p : P → D) (bs : List (List D)) :
    (blockNFA C seed last p).Accepts bs ↔ (C.dataNFA p).Accepts (p seed :: decodeBlocks (p last) bs) := by
  constructor
  · rintro ⟨q, r, ⟨z, hz, hs⟩, hrun, hr⟩
    exact ⟨z, r, hz, .cons hs ((BlockEndpointGluing.block_runs C seed last p q r bs).mp hrun), hr⟩
  · rintro ⟨z, r, hz, hrun, hr⟩
    cases hrun with
    | cons hs hrest => exact ⟨_, r, ⟨z, hz, hs⟩,
        (BlockEndpointGluing.block_runs C seed last p _ r bs).mpr hrest, hr⟩

def semanticCandidate (C : Row L P c) (seed last : P) {D : Type*} [L.Structure D] (p : P → D) :=
  filterNonempty (blockNFA C seed last p) (fun U => p last ∉ U)

theorem semanticCandidate_correct (C : Row L P c) (seed last : P) {D : Type*} [L.Structure D]
    (p : P → D) (bs : List (List D)) :
    (semanticCandidate C seed last p).Accepts bs ↔
      bs ≠ [] ∧ NoA (p last) bs ∧ (C.dataNFA p).Accepts (p seed :: decodeBlocks (p last) bs) := by
  rw [semanticCandidate, filterNonempty_accepts, block_accepts]
  rfl

def states (c : Nat) : List (Option (Fin c)) := none :: (List.finRange c).map some

def stateAt (c : Nat) (i : Fin (states c).length) : Option (Fin c) := (states c).get i

theorem stateAt_surjective (c : Nat) : Function.Surjective (stateAt c) := by
  intro q
  have hmem : q ∈ states c := by cases q <;> simp [states]
  exact List.mem_iff_get.mp hmem

theorem length_states (c : Nat) : (states c).length = c + 1 := by simp [states]

def noAAtom (ns : Fin k → Nat) (c : Nat) : (language ns c).Formula (Empty ⊕ Fin 1) :=
  FirstOrder.Language.Relations.formula₁ (L := language ns c) Rel.noA (Term.var (Sum.inr 0))

def initialGuard (ns : Fin k → Nat) (c : Nat) : Option (Fin c) → (language ns c).Formula Empty
  | none => ⊤
  | some _ => ⊥

def finalGuard (ns : Fin k → Nat) (c : Nat) : Option (Fin c) → (language ns c).Formula Empty
  | none => ⊥
  | some q => (candidateHom ns c).onFormula (SymbolicOutsideController.finalAtom q)

def dataGuard (ns : Fin k → Nat) (c : Nat) :
    Option (Fin c) → Option (Fin c) → (language ns c).Formula (Empty ⊕ Fin 1)
  | _, none => ⊥
  | none, some r => noAAtom ns c ⊓ any c (fun q =>
      ((candidateHom ns c).onFormula (SymbolicOutsideController.initialAtom q)).relabel Sum.inl ⊓
      (candidateHom ns c).onFormula (SymbolicOutsideController.blockAtom q r))
  | some q, some r => noAAtom ns c ⊓
      (candidateHom ns c).onFormula (SymbolicOutsideController.blockAtom q r)

/-- Actual epsilon-free candidate syntax, with one fresh start state that
cannot be final or re-entered. Nonempty block words are enforced by construction. -/
def compile (ns : Fin k → Nat) (c : Nat) : Row (language ns c) Empty (states c).length where
  initial i := initialGuard ns c (stateAt c i)
  final i := finalGuard ns c (stateAt c i)
  data i j := dataGuard ns c (stateAt c i) (stateAt c j)
  left _ _ := ⊥
  right _ _ := ⊥
  guard := ⊥

theorem realize_noAAtom (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (seed last : P)
    {D : Type*} [L.Structure D] (p : P → D) (v : Empty → List D) (U : List D) :
    letI := UnifiedBlockPresentation.model rows C seed last p
    (noAAtom ns c).Realize (Sum.elim v (fun _ => U)) ↔ p last ∉ U := by
  letI := UnifiedBlockPresentation.model rows C seed last p
  rw [noAAtom, Formula.realize_rel₁]
  exact noA_interpret rows C seed last p U

theorem initialGuard_correct (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (seed last : P)
    {D : Type*} [L.Structure D] (p : P → D) (v : Empty → List D) (q : Option (Fin c)) :
    letI := UnifiedBlockPresentation.model rows C seed last p
    (initialGuard ns c q).Realize v ↔ (semanticCandidate C seed last p).start q := by
  letI := UnifiedBlockPresentation.model rows C seed last p
  cases q <;> simp [initialGuard, semanticCandidate, filterNonempty]

theorem finalGuard_correct (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (seed last : P)
    {D : Type*} [L.Structure D] (p : P → D) (v : Empty → List D) (q : Option (Fin c)) :
    letI := UnifiedBlockPresentation.model rows C seed last p
    (finalGuard ns c q).Realize v ↔ (semanticCandidate C seed last p).accept q := by
  letI := UnifiedBlockPresentation.model rows C seed last p
  letI := BlockRelationPresentation.model C seed last p
  letI := candidate_expansion rows C seed last p
  cases q with
  | none => rfl
  | some q =>
      rw [finalGuard, LHom.realize_onFormula]
      exact realize_finalAtom C seed last p q v

theorem dataGuard_correct (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (seed last : P)
    {D : Type*} [L.Structure D] (p : P → D) (v : Empty → List D)
    (q r : Option (Fin c)) (U : List D) :
    letI := UnifiedBlockPresentation.model rows C seed last p
    (dataGuard ns c q r).Realize (Sum.elim v (fun _ => U)) ↔
      (semanticCandidate C seed last p).step q U r := by
  letI := UnifiedBlockPresentation.model rows C seed last p
  letI := BlockRelationPresentation.model C seed last p
  letI := candidate_expansion rows C seed last p
  cases r with
  | none => cases q <;> rfl
  | some r =>
      cases q with
      | none =>
          simp only [dataGuard, Formula.realize_inf, realize_noAAtom rows C seed last p v U,
            realize_any, Formula.realize_relabel, LHom.realize_onFormula]
          change (p last ∉ U ∧ ∃ q,
            (SymbolicOutsideController.initialAtom q).Realize v ∧
            (SymbolicOutsideController.blockAtom q r).Realize (Sum.elim v (fun _ => U))) ↔ _
          simp only [realize_initialAtom C seed last p, realize_blockAtom C seed last p]
          rfl
      | some q =>
          simp only [dataGuard, Formula.realize_inf, realize_noAAtom rows C seed last p v U,
            LHom.realize_onFormula, realize_blockAtom C seed last p]
          rfl

theorem compile_interpret (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (seed last : P)
    {D : Type*} [L.Structure D] (p : P → D) (v : Empty → List D) :
    letI := UnifiedBlockPresentation.model rows C seed last p
    (compile ns c).dataNFA v = SymbolicComplement.pullback (semanticCandidate C seed last p) (stateAt c) := by
  letI := UnifiedBlockPresentation.model rows C seed last p
  unfold Row.dataNFA compile SymbolicComplement.pullback
  congr 1
  · funext q
    exact propext (initialGuard_correct rows C seed last p v _)
  · funext q U r
    exact propext (dataGuard_correct rows C seed last p v _ _ U)
  · funext q
    exact propext (finalGuard_correct rows C seed last p v _)

/-- Exact preservation of the ENTIRE old candidate, including all prior
subtractions encoded in C. The new syntax enforces both NoA and nonemptiness. -/
theorem compile_correct (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (seed last : P)
    {D : Type*} [L.Structure D] (p : P → D) (v : Empty → List D) (bs : List (List D)) :
    letI := UnifiedBlockPresentation.model rows C seed last p
    ((compile ns c).dataNFA v).Accepts bs ↔
      bs ≠ [] ∧ NoA (p last) bs ∧ (C.dataNFA p).Accepts (p seed :: decodeBlocks (p last) bs) := by
  letI := UnifiedBlockPresentation.model rows C seed last p
  rw [compile_interpret rows C seed last p v,
    SymbolicComplement.pullback_accepts _ _ (stateAt_surjective c), semanticCandidate_correct]

theorem decode_terminal {D : Type*} (a : D) (bs : List (List D)) (hne : bs ≠ []) :
    ∃ w, decodeBlocks a bs = w ++ [a] := by
  induction bs with
  | nil => exact (hne rfl).elim
  | cons U bs ih =>
      cases bs with
      | nil => exact ⟨U, rfl⟩
      | cons V bs =>
          obtain ⟨w, hw⟩ := ih (by simp)
          refine ⟨U ++ a :: w, ?_⟩
          simp only [decodeBlocks] at hw ⊢
          rw [hw]
          simp [List.append_assoc]

/-- NoA decoding is injective even with arbitrarily many empty blocks. -/
theorem decode_injective {D : Type*} (a : D) (xs ys : List (List D))
    (hx : NoA a xs) (hy : NoA a ys) (he : decodeBlocks a xs = decodeBlocks a ys) : xs = ys := by
  have hxy : xs <+: ys := (decode_prefix_iff a xs ys hx hy).mp (by rw [he])
  have hyx : ys <+: xs := (decode_prefix_iff a ys xs hy hx).mp (by rw [he])
  exact hxy.eq_of_length (Nat.le_antisymm hxy.length_le hyx.length_le)

/-- The new candidate really is the entire canonical encoding of the old
terminal slice, not a subset consisting of chosen witnesses. -/
theorem compile_split (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (seed last : P)
    {D : Type*} [L.Structure D] [DecidableEq D] (p : P → D) (v : Empty → List D) (w : List D) :
    letI := UnifiedBlockPresentation.model rows C seed last p
    ((compile ns c).dataNFA v).Accepts (TerminalBorderRank.split (p last) w) ↔
      (C.dataNFA p).Accepts (p seed :: (w ++ [p last])) := by
  rw [compile_correct rows C seed last p v, decodeBlocks_split]
  exact ⟨fun h => h.2.2, fun h =>
    ⟨split_ne_nil (p last) w, separator_not_mem_split (p last) w, h⟩⟩

/-- Candidate membership AND avoidance of the full Fin-indexed row family
are transported together, under ONE structure and ONE parameter valuation. -/
theorem exists_avoider_iff (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (seed last : P) {D : Type*} [L.Structure D] (p : P → D) :
    (∃ w : List D, (C.dataNFA p).Accepts (p seed :: (w ++ [p last])) ∧
      ∀ i, ¬ GuardedRowFiring.PositiveFires (rows i) p (p seed) (w ++ [p last])) ↔
      letI := UnifiedBlockPresentation.model rows C seed last p
      ∃ bs : List (List D), ((compile ns c).dataNFA (Empty.elim : Empty → List D)).Accepts bs ∧
        ∀ i : Fin (branches ns).length,
          ¬ GuardedRowFiring.Fires (familyRows ns c i) (Empty.elim : Empty → List D)
            (bs.head?.getD []) bs.tail := by
  classical
  letI := UnifiedBlockPresentation.model rows C seed last p
  constructor
  · rintro ⟨w, hC, hav⟩
    let bs := TerminalBorderRank.split (p last) w
    have hNoA : NoA (p last) bs := separator_not_mem_split (p last) w
    refine ⟨bs, (compile_split rows C seed last p Empty.elim w).mpr hC, ?_⟩
    apply (avoids_enumerated_family rows C seed last p bs hNoA).mp
    simpa only [bs, decodeBlocks_split] using hav
  · rintro ⟨bs, hC, hav⟩
    obtain ⟨hne, hNoA, hCold⟩ := (compile_correct rows C seed last p Empty.elim bs).mp hC
    obtain ⟨w, hw⟩ := decode_terminal (p last) bs hne
    have havOld := (avoids_enumerated_family rows C seed last p bs hNoA).mpr hav
    rw [hw] at hCold havOld
    exact ⟨w, hCold, havOld⟩

/-- EVERY newly accepted body has the strictly lowered literal rank,
not just the encoding of a selected old avoider. -/
theorem candidate_rank_bound (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (seed last : P) {D : Type*} [L.Structure D] [DecidableEq D] (p : P → D) (h : Nat) (hh : 0 < h)
    (hbound : ∀ w, (C.dataNFA p).Accepts (p seed :: w) → suffixBorderRank w ≤ h)
    (bs : List (List D)) :
    letI := UnifiedBlockPresentation.model rows C seed last p
    ((compile ns c).dataNFA (Empty.elim : Empty → List D)).Accepts bs →
      suffixBorderRank bs.tail ≤ h - 1 := by
  intro hC
  obtain ⟨hne, _, hCold⟩ := (compile_correct rows C seed last p Empty.elim bs).mp hC
  have hb := hbound _ hCold
  cases bs with
  | nil => exact (hne rfl).elim
  | cons first body =>
      rw [decodeBlocks_cons] at hb
      exact rankBound_descent (p last) first body hh hb

end NSSE.BlockCandidateTransport
