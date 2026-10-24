import NSSE.SymbolicOutsideController

/-! # Four-endpoint gluing for all local witnesses on a fixed block pair -/

namespace NSSE.BlockEndpointGluing

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks GuardedBlockRelation
open SymbolicOutsideController

universe u v w
variable {L : FirstOrder.Language.{u, v}} {P : Type w} {n : Nat}

def StartsThrough {A Q : Type*} (T : NSSE.NFA A Q) (w : List A) (q : Q) : Prop :=
  ∃ z, T.start z ∧ T.Runs z w q

/-- Every accepting run yields its own FOUR cut states; every compatible
five-piece path glues back. No representative accepting run is selected. -/
theorem accepts_five {A Q : Type*} (T : NSSE.NFA A Q)
    (pre left mid right post : List A) :
    T.Accepts (pre ++ (left ++ (mid ++ (right ++ post)))) ↔
      ∃ r0 r1 t0 t1, StartsThrough T pre r0 ∧ T.Runs r0 left r1 ∧
        T.Runs r1 mid t0 ∧ T.Runs t0 right t1 ∧ AcceptFrom T t1 post := by
  constructor
  · rintro ⟨q, r, hq, hrun, hr⟩
    obtain ⟨r0, hp, hrun⟩ := (runs_append_iff T q r pre _).mp hrun
    obtain ⟨r1, hl, hrun⟩ := (runs_append_iff T r0 r left _).mp hrun
    obtain ⟨t0, hm, hrun⟩ := (runs_append_iff T r1 r mid _).mp hrun
    obtain ⟨t1, ht, hpost⟩ := (runs_append_iff T t0 r right post).mp hrun
    exact ⟨r0, r1, t0, t1, ⟨q, hq, hp⟩, hl, hm, ht, ⟨r, hpost, hr⟩⟩
  · rintro ⟨r0, r1, t0, t1, ⟨q, hq, hp⟩, hl, hm, ht, ⟨r, hpost, hr⟩⟩
    exact ⟨q, r, hq, hp.append T (hl.append T (hm.append T (ht.append T hpost))), hr⟩

theorem block_runs (R : Row L P n) (seed last : P) {D : Type*} [L.Structure D]
    (p : P → D) (q r : Fin n) (bs : List (List D)) :
    (blockNFA R seed last p).Runs q bs r ↔
      (R.dataNFA p).Runs q (TerminalBorderRank.decodeBlocks (p last) bs) r := by
  induction bs generalizing q with
  | nil => exact (runs_nil_iff _ _ _).trans (runs_nil_iff _ _ _).symm
  | cons U bs ih =>
      have hd : TerminalBorderRank.decodeBlocks (p last) (U :: bs) =
          (U ++ [p last]) ++ TerminalBorderRank.decodeBlocks (p last) bs := by
        simp only [TerminalBorderRank.decodeBlocks, List.append_assoc, List.singleton_append]
      rw [OutsideBlockController.Data.runs_cons_iff, hd, runs_append_iff]
      apply exists_congr
      intro s
      exact and_congr Iff.rfl (ih s)

theorem block_runs_marked (R : Row L P n) (seed last : P) {D : Type*} [L.Structure D]
    (p : P → D) (q r : Fin n) (bs : List (List D)) :
    (blockNFA R seed last p).Runs q bs r ↔
      (R.markedNFA p).Runs q ((TerminalBorderRank.decodeBlocks (p last) bs).map Sum.inl) r :=
  (block_runs R seed last p q r bs).trans (R.data_runs_marked p q r _)

theorem block_before (R : Row L P n) (seed last : P) {D : Type*} [L.Structure D]
    (p : P → D) (q : Fin n) (pre : List (List D)) :
    StartsThrough (blockNFA R seed last p) pre q ↔
      StartsThrough (R.markedNFA p)
        ((p seed :: TerminalBorderRank.decodeBlocks (p last) pre).map Sum.inl) q := by
  constructor
  · rintro ⟨r, ⟨z, hz, hs⟩, hp⟩
    exact ⟨z, hz, (R.data_runs_marked p z q _).mp (.cons hs ((block_runs R seed last p r q pre).mp hp))⟩
  · rintro ⟨z, hz, hp⟩
    have hd := (R.data_runs_marked p z q _).mpr hp
    cases hd with
    | cons hs hrest => exact ⟨_, ⟨z, hz, hs⟩, (block_runs R seed last p _ q pre).mpr hrest⟩

theorem block_after (R : Row L P n) (seed last : P) {D : Type*} [L.Structure D]
    (p : P → D) (q : Fin n) (post : List (List D)) :
    AcceptFrom (blockNFA R seed last p) q post ↔
      AcceptFrom (R.markedNFA p) q ((TerminalBorderRank.decodeBlocks (p last) post).map Sum.inl) := by
  simp only [AcceptFrom, block_runs_marked]
  rfl

def Outside (R : Row L P n) (e : Ends n) (seed last : P)
    {D : Type*} [L.Structure D] (p : P → D) (pre mid post : List (List D)) : Prop :=
  StartsThrough (R.markedNFA p)
    ((p seed :: TerminalBorderRank.decodeBlocks (p last) pre).map Sum.inl) e.leftStart ∧
  (R.markedNFA p).Runs e.leftEnd
    ((TerminalBorderRank.decodeBlocks (p last) mid).map Sum.inl) e.rightStart ∧
  AcceptFrom (R.markedNFA p) e.rightEnd ((TerminalBorderRank.decodeBlocks (p last) post).map Sum.inl)

/-- The compiled block row recognizes precisely the THREE outside paths
of the original row, at the SAME four endpoints used by H. -/
theorem compile_input_correct (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (v : Empty → List D)
    (pre : List (List D)) (U : List D) (mid : List (List D)) (V : List D) (post : List (List D)) :
    letI := BlockRelationPresentation.model R seed last p
    ((SymbolicOutsideController.compile e first).markedNFA v).Accepts
      (OutsideBlockController.Data.input pre U mid V post) ↔
        pre.isEmpty = first ∧ Outside R e seed last p pre mid post := by
  letI := BlockRelationPresentation.model R seed last p
  have h := (compile_accepts R e seed last first p v
    (OutsideBlockController.Data.input pre U mid V post)).trans
    ((semantics R e seed last first p).accepts_input pre U mid V post)
  refine h.trans ?_
  change (_ ∧ StartsThrough (blockNFA R seed last p) pre e.leftStart ∧
    (blockNFA R seed last p).Runs e.leftEnd mid e.rightStart ∧
    AcceptFrom (blockNFA R seed last p) e.rightEnd post) ↔ _
  rw [block_before, block_runs_marked, block_after]
  rfl

def oldInput {D : Type*} (seed last : D) (pre mid post : List (List D))
    (px py shared : List D) : List (D ⊕ Bool) :=
  (seed :: TerminalBorderRank.decodeBlocks last pre).map Sum.inl ++
    ((px.map Sum.inl ++ .inr false :: (shared ++ [last]).map Sum.inl) ++
      ((TerminalBorderRank.decodeBlocks last mid).map Sum.inl ++
        ((py.map Sum.inl ++ .inr true :: (shared ++ [last]).map Sum.inl) ++
          (TerminalBorderRank.decodeBlocks last post).map Sum.inl)))

def OldWitness (R : Row L P n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D)
    (pre : List (List D)) (U : List D) (mid : List (List D)) (V : List D) (post : List (List D)) : Prop :=
  pre.isEmpty = first ∧ ∃ px py shared : List D, U = px ++ shared ∧ V = py ++ shared ∧
    R.guard.Realize (Sum.elim p ![px.reverse.head?.getD (p (fallback seed last first)),
      py.reverse.head?.getD (p last)]) ∧
    (R.markedNFA p).Accepts (oldInput (p seed) (p last) pre mid post px py shared)

/-- New control acceptance plus its predecessor guard, on the genuine
parameter-free compiled Row in the automatic block structure. -/
def NewWitness (R : Row L P n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D)
    (pre : List (List D)) (U : List D) (mid : List (List D)) (V : List D) (post : List (List D)) : Prop :=
  letI := BlockRelationPresentation.model R seed last p
  ∃ e : Ends n,
    ((SymbolicOutsideController.compile e first).markedNFA (Empty.elim : Empty → List D)).Accepts
      (OutsideBlockController.Data.input pre U mid V post) ∧
    (SymbolicOutsideController.compile e first).guard.Realize
      (Sum.elim (Empty.elim : Empty → List D) ![U, V])

/-- The exact existential equivalence on each block-pair fiber. Every old
accepting run supplies its own endpoints; every new endpoint choice glues
compatible paths, with one common suffix and one shared parameter valuation.
Copied-tail equality/cut geometry is a separate subsequent theorem. -/
theorem newWitness_iff_oldWitness (R : Row L P n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P → D)
    (pre : List (List D)) (U : List D) (mid : List (List D)) (V : List D) (post : List (List D)) :
    NewWitness R seed last first p pre U mid V post ↔ OldWitness R seed last first p pre U mid V post := by
  letI := BlockRelationPresentation.model R seed last p
  constructor
  · rintro ⟨e, hcontroller, hguard⟩
    obtain ⟨hfirst, hout⟩ := (compile_input_correct R e seed last first p Empty.elim pre U mid V post).mp hcontroller
    obtain ⟨px, py, shared, hU, hV, hg, hl, hr⟩ :=
      (compile_guard R e seed last first p Empty.elim U V).mp hguard
    refine ⟨hfirst, px, py, shared, hU, hV, hg, ?_⟩
    exact (accepts_five (R.markedNFA p) _ _ _ _ _).mpr
      ⟨e.leftStart, e.leftEnd, e.rightStart, e.rightEnd, hout.1, hl, hout.2.1, hr, hout.2.2⟩
  · rintro ⟨hfirst, px, py, shared, hU, hV, hg, haccept⟩
    obtain ⟨r0, r1, t0, t1, hp, hl, hm, hr, ht⟩ := (accepts_five (R.markedNFA p) _ _ _ _ _).mp haccept
    let e : Ends n := ⟨r0, r1, t0, t1⟩
    refine ⟨e, ?_, ?_⟩
    · exact (compile_input_correct R e seed last first p Empty.elim pre U mid V post).mpr
        ⟨hfirst, hp, hm, ht⟩
    · exact (compile_guard R e seed last first p Empty.elim U V).mpr
        ⟨px, py, shared, hU, hV, hg, hl, hr⟩

end NSSE.BlockEndpointGluing
