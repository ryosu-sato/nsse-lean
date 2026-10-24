import NSSE.BlockEndpointGluing
import NSSE.TerminalCutGeometry

/-! # Literal firing semantics and transport of every guarded suffix witness -/

namespace NSSE.GuardedRowFiring

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks TerminalBorderRank
open TerminalCutGeometry BlockEndpointGluing

universe u v w
variable {L : FirstOrder.Language.{u, v}} {P : Type w} {n : Nat}

def lastOr {D : Type*} (d : D) (xs : List D) : D := xs.reverse.head?.getD d

theorem lastOr_append {D : Type*} (d : D) (xs ys : List D) :
    lastOr d (xs ++ ys) = lastOr (lastOr d xs) ys := by
  simp only [lastOr, List.reverse_append, List.head?_append]
  cases ys.reverse.head? <;> rfl

@[simp] theorem lastOr_singleton {D : Type*} (d x : D) : lastOr d [x] = x := rfl

@[simp] theorem lastOr_append_singleton {D : Type*} (d x : D) (xs : List D) :
    lastOr d (xs ++ [x]) = x := by rw [lastOr_append, lastOr_singleton]

theorem lastOr_seed_cons {D : Type*} (s : D) (xs : List D) :
    lastOr s (s :: xs) = lastOr s xs := by
  change lastOr s ([s] ++ xs) = _
  rw [lastOr_append, lastOr_singleton]

theorem lastOr_decode {D : Type*} (s a : D) (A : List (List D)) :
    lastOr s (decodeBlocks a A) = if A.isEmpty then s else a := by
  induction A generalizing s with
  | nil => rfl
  | cons U A ih =>
      have hd : decodeBlocks a (U :: A) = (U ++ [a]) ++ decodeBlocks a A := by
        simp [decodeBlocks, List.append_assoc]
      rw [hd]
      rw [lastOr_append, lastOr_append_singleton, ih]
      simp

/-- Insert the two literal markers at full-word cuts k,l. -/
def markedOn {D : Type*} (xs : List D) (k l : Nat) : List (D ⊕ Bool) :=
  (xs.take k).map Sum.inl ++ .inr false ::
    ((xs.drop k).take (l - k)).map Sum.inl ++ .inr true :: (xs.drop l).map Sum.inl

theorem markedOn_split {D : Type*} (pref gap tail : List D) :
    markedOn (pref ++ (gap ++ tail)) pref.length (pref.length + gap.length) =
      pref.map Sum.inl ++ .inr false :: gap.map Sum.inl ++ .inr true :: tail.map Sum.inl := by
  simp [markedOn, List.drop_append]

theorem markedOn_body {D : Type*} (seed : D) (body : List D) (j t : Nat) :
    markedOn (seed :: body) (j + 1) (t + 1) =
      (seed :: body.take j).map Sum.inl ++ .inr false ::
        ((body.drop j).take (t - j)).map Sum.inl ++ .inr true :: (body.drop t).map Sum.inl := by
  simp [markedOn]

theorem predecessor_body {D : Type*} (seed : D) (body : List D) (j : Nat) :
    lastOr seed ((seed :: body).take (j + 1)) = lastOr seed (body.take j) := by
  simp only [List.take_succ_cons, lastOr_seed_cons]

/-- The exact paper semantics: body cuts 0<=j<t<=|body|, predecessor
guard, original marked-NFA acceptance, and the original copy equality. -/
def FiresAt (R : Row L P n) {D : Type*} [L.Structure D] (p : P → D)
    (seed : D) (body : List D) (j t : Nat) : Prop :=
  j < t ∧ t ≤ body.length ∧
    (R.markedNFA p).Accepts (markedOn (seed :: body) (j + 1) (t + 1)) ∧
    R.guard.Realize (Sum.elim p ![lastOr seed ((seed :: body).take (j + 1)),
      lastOr seed ((seed :: body).take (t + 1))]) ∧
    OccursSuffixAt body j t

def Fires (R : Row L P n) {D : Type*} [L.Structure D] (p : P → D)
    (seed : D) (body : List D) : Prop := ∃ j t, FiresAt R p seed body j t

def PositiveFires (R : Row L P n) {D : Type*} [L.Structure D] (p : P → D)
    (seed : D) (body : List D) : Prop :=
  ∃ j t, FiresAt R p seed body j t ∧ t < body.length

def EmptyTailFires (R : Row L P n) {D : Type*} [L.Structure D] (p : P → D)
    (seed : D) (body : List D) : Prop := ∃ j, FiresAt R p seed body j body.length

theorem fires_iff_positive_or_empty (R : Row L P n) {D : Type*} [L.Structure D]
    (p : P → D) (seed : D) (body : List D) :
    Fires R p seed body ↔ PositiveFires R p seed body ∨ EmptyTailFires R p seed body := by
  constructor
  · rintro ⟨j, t, hfire⟩
    rcases lt_or_eq_of_le hfire.2.1 with ht | ht
    · exact Or.inl ⟨j, t, hfire, ht⟩
    · subst t
      exact Or.inr ⟨j, hfire⟩
  · rintro (⟨j, t, hfire, _⟩ | ⟨j, hfire⟩)
    · exact ⟨j, t, hfire⟩
    · exact ⟨j, body.length, hfire⟩

theorem predecessor_at_cut {D : Type*} (s a : D) (A C : List (List D)) (P S : List D) :
    lastOr s ((s :: decodeBlocks a (A ++ (P ++ S) :: C)).take
      ((decodeBlocks a A).length + P.length + 1)) =
        lastOr (if A.isEmpty then s else a) P := by
  have he : s :: decodeBlocks a (A ++ (P ++ S) :: C) =
      (s :: (decodeBlocks a A ++ P)) ++ (S ++ a :: decodeBlocks a C) := by
    simp [decodeBlocks, List.append_assoc]
  have hlen : (decodeBlocks a A).length + P.length + 1 =
      (s :: (decodeBlocks a A ++ P)).length := by simp
  rw [he, hlen, List.take_left, lastOr_seed_cons, lastOr_append, lastOr_decode]

theorem old_pair_marked {D : Type*} (s a : D) (A M C : List (List D)) (P Q S : List D) :
    markedOn (s :: decodeBlocks a (A ++ (P ++ S) :: (M ++ (Q ++ S) :: C)))
      ((decodeBlocks a A).length + P.length + 1)
      ((decodeBlocks a (A ++ (P ++ S) :: M)).length + Q.length + 1) =
        oldInput s a A M C P Q S := by
  let pref := s :: (decodeBlocks a A ++ P)
  let gap := S ++ a :: (decodeBlocks a M ++ Q)
  let tail := S ++ a :: decodeBlocks a C
  have he : s :: decodeBlocks a (A ++ (P ++ S) :: (M ++ (Q ++ S) :: C)) =
      pref ++ (gap ++ tail) := by simp [pref, gap, tail, decodeBlocks, List.append_assoc]
  have hj : (decodeBlocks a A).length + P.length + 1 = pref.length := by
    simp [pref]
  have ht : (decodeBlocks a (A ++ (P ++ S) :: M)).length + Q.length + 1 =
      pref.length + gap.length := by
    simp [pref, gap, decodeBlocks]; omega
  rw [he, hj, ht, markedOn_split]
  simp [pref, gap, tail, oldInput, List.map_append, List.append_assoc]

/-- The new seed really is the first block, including when that block is empty. -/
theorem firstBlock_cons_tail {D : Type*} (bs : List (List D)) (h : bs ≠ []) :
    bs.head?.getD [] :: bs.tail = bs := by cases bs <;> simp_all

theorem new_pair_marked {D : Type*} (A M C : List (List D)) (U V : List D) :
    markedOn (A ++ U :: (M ++ V :: C)) (A.length + 1) (A.length + M.length + 1 + 1) =
      OutsideBlockController.Data.input A U M V C := by
  have he : A ++ U :: (M ++ V :: C) = (A ++ [U]) ++ ((M ++ [V]) ++ C) := by
    simp [List.append_assoc]
  have hj : A.length + 1 = (A ++ [U]).length := by simp
  have ht : A.length + M.length + 1 + 1 = (A ++ [U]).length + (M ++ [V]).length := by
    simp; omega
  rw [he, hj, ht, markedOn_split]
  simp [OutsideBlockController.Data.input, List.append_assoc]

theorem new_pair_predecessors {D : Type*} (d : List D) (A M C : List (List D)) (U V : List D) :
    lastOr d ((A ++ U :: (M ++ V :: C)).take (A.length + 1)) = U ∧
    lastOr d ((A ++ U :: (M ++ V :: C)).take (A.length + M.length + 1 + 1)) = V := by
  have hl : (A ++ U :: (M ++ V :: C)).take (A.length + 1) = A ++ [U] := by
    simp [List.take_append]
  have hr : (A ++ U :: (M ++ V :: C)).take (A.length + M.length + 1 + 1) =
      (A ++ U :: M) ++ [V] := by
    rw [show A.length + M.length + 1 + 1 = A.length + (M.length + 2) by omega]
    simp [List.take_append, List.append_assoc]
  rw [hl, hr, lastOr_append_singleton, lastOr_append_singleton]
  exact ⟨rfl, rfl⟩

/-- Literal firing on a block pair, for any Row over the whole block domain. -/
theorem firesAt_block_pair (R : Row L P n) {D : Type*} [L.Structure (List D)] (p : P → List D)
    (A M C : List (List D)) (U V : List D) :
    FiresAt R p ((A ++ U :: (M ++ V :: C)).head?.getD [])
      (A ++ U :: (M ++ V :: C)).tail A.length (A.length + M.length + 1) ↔
    (R.markedNFA p).Accepts (OutsideBlockController.Data.input A U M V C) ∧
      R.guard.Realize (Sum.elim p ![U, V]) ∧
      OccursSuffixAt (A ++ U :: (M ++ V :: C)).tail A.length (A.length + M.length + 1) := by
  have hbs : A ++ U :: (M ++ V :: C) ≠ [] := by simp
  have hpred := new_pair_predecessors ((A ++ U :: (M ++ V :: C)).head?.getD []) A M C U V
  have hlegal := block_pair_legal A M C U V
  unfold FiresAt
  rw [firstBlock_cons_tail _ hbs, new_pair_marked, hpred.1, hpred.2]
  exact ⟨fun h => h.2.2, fun h => ⟨hlegal.1, hlegal.2, h⟩⟩

/-- In a fixed common-suffix fiber, retain the ORIGINAL input, predecessor
guard and copy equality. The constructed controller is not used in this lemma. -/
theorem firesAt_old_pair (R : Row L P n) (seed last : P) {D : Type*} [L.Structure D]
    (p : P → D) (A M C : List (List D)) (px py S : List D)
    (hNoA : NoA (p last) (A ++ (px ++ S) :: (M ++ (py ++ S) :: C))) :
    FiresAt R p (p seed) (decodeBlocks (p last) (A ++ (px ++ S) :: (M ++ (py ++ S) :: C)))
      ((decodeBlocks (p last) A).length + px.length)
      ((decodeBlocks (p last) (A ++ (px ++ S) :: M)).length + py.length) ↔
    (R.markedNFA p).Accepts (oldInput (p seed) (p last) A M C px py S) ∧
      R.guard.Realize (Sum.elim p ![lastOr (p (fallback seed last A.isEmpty)) px,
        lastOr (p last) py]) ∧
      OccursSuffixAt (A ++ (px ++ S) :: (M ++ (py ++ S) :: C)).tail
        A.length (A.length + M.length + 1) := by
  have hl := predecessor_at_cut (p seed) (p last) A (M ++ (py ++ S) :: C) px S
  have hl' : lastOr (if A.isEmpty then p seed else p last) px =
      lastOr (p (fallback seed last A.isEmpty)) px := by
    cases A.isEmpty <;> rfl
  have hr := predecessor_at_cut (p seed) (p last) (A ++ (px ++ S) :: M) C py S
  simp only [List.append_assoc, List.cons_append] at hr
  have hr' : (A ++ (px ++ S) :: M).isEmpty = false := by simp
  rw [hr'] at hr
  have hlegal := old_pair_legal (p last) A M C px py S
  unfold FiresAt
  rw [old_pair_marked, hl, hl', hr, old_pair_occurs (p last) A M C px py S hNoA]
  exact ⟨fun h => h.2.2, fun h => ⟨hlegal.1, hlegal.2.le, h⟩⟩

/-- v1317 (11), before subtracting old empty-tail firings: all original
POSITIVE-tail firings correspond to ALL firings of some constructed row.
The new side includes empty tails. No representative old run or cut is
selected; old parameters keep one valuation in the automatic word model. -/
theorem positive_fires_iff_new (R : Row L P n) (seed last : P) {D : Type*} [L.Structure D]
    (p : P → D) (bs : List (List D)) (hNoA : NoA (p last) bs) :
    PositiveFires R p (p seed) (decodeBlocks (p last) bs) ↔
      letI := BlockRelationPresentation.model R seed last p
      ∃ e : Ends n, ∃ first : Bool,
        Fires (SymbolicOutsideController.compile e first) (Empty.elim : Empty → List D)
          (bs.head?.getD []) bs.tail := by
  letI := BlockRelationPresentation.model R seed last p
  constructor
  · rintro ⟨j, t, hfire, ht⟩
    obtain ⟨A, px, py, S, M, C, hbs, hj, ht', _⟩ :=
      (occurs_iff_fiber (p last) bs hNoA j t hfire.1 ht).mp hfire.2.2.2.2
    subst bs
    subst j
    subst t
    obtain ⟨haccept, hguard, hcopy⟩ := (firesAt_old_pair R seed last p A M C px py S hNoA).mp hfire
    have hold : OldWitness R seed last A.isEmpty p A (px ++ S) M (py ++ S) C :=
      ⟨rfl, px, py, S, rfl, rfl, hguard, haccept⟩
    obtain ⟨e, hcontrol, hH⟩ := (newWitness_iff_oldWitness R seed last A.isEmpty p
      A (px ++ S) M (py ++ S) C).mpr hold
    refine ⟨e, A.isEmpty, A.length, A.length + M.length + 1, ?_⟩
    exact (firesAt_block_pair (SymbolicOutsideController.compile e A.isEmpty) Empty.elim
      A M C (px ++ S) (py ++ S)).mpr ⟨hcontrol, hH, hcopy⟩
  · rintro ⟨e, first, j, t, hfire⟩
    obtain ⟨A, U, M, V, C, hbs, hj, ht⟩ := locate_block_pair bs j t hfire.1 hfire.2.1
    subst bs
    subst j
    subst t
    obtain ⟨hcontrol, hH, hcopy⟩ := (firesAt_block_pair
      (SymbolicOutsideController.compile e first) Empty.elim A M C U V).mp hfire
    have hnew : NewWitness R seed last first p A U M V C := ⟨e, hcontrol, hH⟩
    obtain ⟨hfirst, px, py, S, hU, hV, hguard, haccept⟩ :=
      (newWitness_iff_oldWitness R seed last first p A U M V C).mp hnew
    subst first
    subst U
    subst V
    refine ⟨(decodeBlocks (p last) A).length + px.length,
      (decodeBlocks (p last) (A ++ (px ++ S) :: M)).length + py.length, ?_,
      (old_pair_legal (p last) A M C px py S).2⟩
    exact (firesAt_old_pair R seed last p A M C px py S hNoA).mpr ⟨haccept, hguard, hcopy⟩

/-- Avoiding one old row's positive firings is avoiding ALL its compiled
rows. There is no bound on block lengths or determinism/run hypothesis. -/
theorem no_positive_fires_iff_new (R : Row L P n) (seed last : P) {D : Type*} [L.Structure D]
    (p : P → D) (bs : List (List D)) (hNoA : NoA (p last) bs) :
    ¬ PositiveFires R p (p seed) (decodeBlocks (p last) bs) ↔
      letI := BlockRelationPresentation.model R seed last p
      ∀ e : Ends n, ∀ first : Bool,
        ¬ Fires (SymbolicOutsideController.compile e first) (Empty.elim : Empty → List D)
          (bs.head?.getD []) bs.tail := by
  rw [positive_fires_iff_new R seed last p bs hNoA]
  simp only [not_exists]

/-- Once the old candidate has had its empty-tail firing language removed,
full avoidance is preserved. Constructing that regular subtraction uniformly
at EVERY recursive level remains a separate compiler task. -/
theorem no_fires_after_empty_removal (R : Row L P n) (seed last : P) {D : Type*} [L.Structure D]
    (p : P → D) (bs : List (List D)) (hNoA : NoA (p last) bs)
    (hEmpty : ¬ EmptyTailFires R p (p seed) (decodeBlocks (p last) bs)) :
    ¬ Fires R p (p seed) (decodeBlocks (p last) bs) ↔
      letI := BlockRelationPresentation.model R seed last p
      ∀ e : Ends n, ∀ first : Bool,
        ¬ Fires (SymbolicOutsideController.compile e first) (Empty.elim : Empty → List D)
          (bs.head?.getD []) bs.tail := by
  rw [fires_iff_positive_or_empty, not_or]
  exact (and_iff_left hEmpty).trans (no_positive_fires_iff_new R seed last p bs hNoA)

/-- Apply the actual terminal split, so separator-freeness is supplied by
the proved splitting algorithm rather than a caller's geometric hypothesis. -/
theorem positive_fires_split (R : Row L P n) (seed last : P) {D : Type*}
    [L.Structure D] [DecidableEq D] (p : P → D) (w : List D) :
    PositiveFires R p (p seed) (w ++ [p last]) ↔
      letI := BlockRelationPresentation.model R seed last p
      ∃ e : Ends n, ∃ first : Bool,
        Fires (SymbolicOutsideController.compile e first) (Empty.elim : Empty → List D)
          ((TerminalBorderRank.split (p last) w).head?.getD [])
          (TerminalBorderRank.split (p last) w).tail := by
  have h := positive_fires_iff_new R seed last p (TerminalBorderRank.split (p last) w)
    (separator_not_mem_split (p last) w)
  rwa [decodeBlocks_split] at h

/-- One genuine rank-decreasing terminal step: the actual block word both
has lower literal suffix-border rank and preserves all row-firing witnesses.
This is not yet the candidate/row-family recursion or a decision procedure. -/
theorem ranked_terminal_step (R : Row L P n) (seed last : P) {D : Type*}
    [L.Structure D] [DecidableEq D] (p : P → D) (w : List D) (h : Nat) (hh : 0 < h)
    (hbound : suffixBorderRank (w ++ [p last]) ≤ h) :
    suffixBorderRank (TerminalBorderRank.split (p last) w).tail ≤ h - 1 ∧
      (PositiveFires R p (p seed) (w ++ [p last]) ↔
        letI := BlockRelationPresentation.model R seed last p
        ∃ e : Ends n, ∃ first : Bool,
          Fires (SymbolicOutsideController.compile e first) (Empty.elim : Empty → List D)
            ((TerminalBorderRank.split (p last) w).head?.getD [])
            (TerminalBorderRank.split (p last) w).tail) :=
  ⟨rankBound_split (p last) w hh hbound, positive_fires_split R seed last p w⟩

theorem not_fires_nil (R : Row L P n) {D : Type*} [L.Structure D]
    (p : P → D) (seed : D) : ¬ Fires R p seed [] := by
  rintro ⟨j, t, hjt, ht, _⟩
  simp only [List.length_nil] at ht
  omega

end NSSE.GuardedRowFiring
