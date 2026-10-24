import Lean.Elab.Tactic.Omega

/-!
# NSSE: finite-word core for the SOA development

This file formalizes the dependency-light combinatorics appearing in
`proofs_en.md` Lemma 1.3 and `notes_v28.md` Lemma 19.

Status:
* Definitions and elementary decomposition lemmas are implemented.
* The global saturation / pigeonhole and block-recursion arguments are
  stated as interfaces only; they are not proved here.
-/

namespace NSSE

universe u

abbrev Word (α : Type u) := List α

namespace Word

def factor (w : Word α) (start len : Nat) : Word α :=
  (w.drop start).take len

def «prefix» (w : Word α) (len : Nat) : Word α :=
  w.take len

def suffix (w : Word α) (len : Nat) : Word α :=
  w.drop (w.length - len)

/--
A zero-based period formulation suited to finite words:
the prefix of length `|w|-p` equals the block starting at offset `p`
of the same length.
-/
def HasPeriod (w : Word α) (p : Nat) : Prop :=
  p < w.length ∧
    factor w 0 (w.length - p) = factor w p (w.length - p)

/-- A suffix beginning at `anchor` has period `p`. -/
def AnchoredPeriod (w : Word α) (anchor p : Nat) : Prop :=
  HasPeriod (w.drop anchor) p

/--
The equality used by the witness normal form:
the first `e` symbols after `anchor` equal the final `e` symbols.
-/
def WitnessCopy (w : Word α) (anchor _p e : Nat) : Prop :=
  factor w anchor e = suffix w e

/-- Equality of the prefix and suffix of length `b` (without size side conditions). -/
def BorderCopy (w : Word α) (b : Nat) : Prop :=
  «prefix» w b = suffix w b

/-- Borders are nested: a shorter border of `w` is a border of every
longer border word. -/
theorem borderCopy_nested
    (w : Word α) (b₁ b₂ : Nat)
    (hb₁₂ : b₁ ≤ b₂) (hb₂len : b₂ ≤ w.length)
    (h₁ : BorderCopy w b₁) (h₂ : BorderCopy w b₂) :
    BorderCopy (w.take b₂) b₁ := by
  unfold BorderCopy «prefix» suffix at h₁ h₂ ⊢
  simp only [List.length_take, Nat.min_eq_left hb₂len,
    List.take_take, Nat.min_eq_left hb₁₂]
  rw [h₂, List.drop_drop]
  have hoff : w.length - b₂ + (b₂ - b₁) = w.length - b₁ := by omega
  rw [hoff]
  exact h₁

theorem factor_zero (w : Word α) (n : Nat) :
    factor w 0 n = w.take n := by
  simp [factor]

theorem factor_length (w : Word α) (start len : Nat) :
    (factor w start len).length = min len (w.length - start) := by
  simp [factor]

/-- Taking a factor of a factor just adds the two starting offsets. -/
theorem factor_factor (w : Word α) (start len start' len' : Nat) :
    factor (factor w start len) start' len' =
      factor w (start + start') (min len' (len - start')) := by
  simp [factor, List.drop_take, List.take_take, Nat.add_comm]

/-- A shorter initial part may be extracted from an equality of factors. -/
theorem factor_eq_of_factor_eq_of_le
    (w : Word α) (i j large small : Nat)
    (hsmall : small ≤ large)
    (h : factor w i large = factor w j large) :
    factor w i small = factor w j small := by
  have ht := congrArg (List.take small) h
  simpa [factor, List.take_take, Nat.min_eq_left hsmall] using ht

/-- A period `p` is equivalently a border copy of length `|w|-p`. -/
theorem hasPeriod_iff_borderCopy
    (w : Word α) (p : Nat) (hp : p < w.length) :
    HasPeriod w p ↔ BorderCopy w (w.length - p) := by
  have hsub : w.length - (w.length - p) = p := by omega
  have htake : (w.drop p).take (w.length - p) = w.drop p := by
    apply List.take_of_length_le
    simp
  unfold HasPeriod BorderCopy «prefix» suffix factor
  rw [hsub, htake]
  simp only [List.drop_zero]
  exact ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩

/-- Two nested borders force their length difference to be a period of the
longer border word. -/
theorem border_difference_period
    (w : Word α) (b₁ b₂ : Nat)
    (hb₁pos : 0 < b₁) (hb₁₂ : b₁ < b₂) (hb₂len : b₂ ≤ w.length)
    (h₁ : BorderCopy w b₁) (h₂ : BorderCopy w b₂) :
    HasPeriod (w.take b₂) (b₂ - b₁) := by
  have hlen : (w.take b₂).length = b₂ := by
    simp [Nat.min_eq_left hb₂len]
  have hp : b₂ - b₁ < (w.take b₂).length := by rw [hlen]; omega
  rw [hasPeriod_iff_borderCopy (w.take b₂) (b₂ - b₁) hp]
  have hsub : (w.take b₂).length - (b₂ - b₁) = b₁ := by rw [hlen]; omega
  rw [hsub]
  exact borderCopy_nested w b₁ b₂ (Nat.le_of_lt hb₁₂) hb₂len h₁ h₂

/--
A direct, indexing-free version of Lemma 1.3's equivalence.
The length equation says that the anchored suffix has length `p+e`.
-/
theorem witnessCopy_iff_anchoredPeriod
    (w : Word α) (anchor p e : Nat)
    (hlen : anchor + p + e = w.length) (he : 0 < e) :
    WitnessCopy w anchor p e ↔ AnchoredPeriod w anchor p := by
  have hslen : (w.drop anchor).length = p + e := by
    simp only [List.length_drop]
    omega
  have htail : w.drop (w.length - e) = (w.drop anchor).drop p := by
    rw [List.drop_drop]
    congr 1
    omega
  have htake : ((w.drop anchor).drop p).take e = (w.drop anchor).drop p := by
    apply List.take_of_length_le
    simp only [List.length_drop, hslen]
    omega
  unfold WitnessCopy suffix AnchoredPeriod HasPeriod
  rw [hslen]
  simp only [factor, List.drop_zero, Nat.add_sub_cancel_left,
    htail, true_and]
  rw [htake]
  exact ⟨fun h => ⟨by omega, h⟩, fun h => h.2⟩

end Word

/--
The suffix beginning at cut `t` occurs at cut `j`, with the length forced
to be the whole suffix after `t`.  Cuts are zero-based positions between
letters, matching the coordinates in `soa_single_row_en.md` after shifting
its one-based letter intervals.
-/
def OccursSuffixAt (w : Word α) (j t : Nat) : Prop :=
  Word.factor w j (w.length - t) = Word.factor w t (w.length - t)

theorem Word.factor_prefix_shift
    (pre w : Word α) (start len : Nat) :
    Word.factor (pre ++ w) (pre.length + start) len =
      Word.factor w start len := by
  simp [Word.factor, List.drop_append]

/--
Adding a common prefix preserves a suffix-occurrence witness after
shifting both cuts by the prefix length.
-/
theorem occursSuffixAt_prefix_shift
    (pre w : Word α) (j t : Nat)
    (h : OccursSuffixAt w j t) :
    OccursSuffixAt (pre ++ w)
      (pre.length + j) (pre.length + t) := by
  unfold OccursSuffixAt at h ⊢
  simp only [List.length_append]
  have hremaining :
      pre.length + w.length - (pre.length + t) =
        w.length - t := by omega
  rw [hremaining, Word.factor_prefix_shift,
    Word.factor_prefix_shift]
  exact h

theorem occursSuffixAt_prefix_shift_iff
    (pre w : Word α) (j t : Nat) :
    OccursSuffixAt (pre ++ w)
      (pre.length + j) (pre.length + t) ↔
      OccursSuffixAt w j t := by
  constructor
  · intro h
    unfold OccursSuffixAt at h ⊢
    simp only [List.length_append] at h
    have hremaining :
        pre.length + w.length - (pre.length + t) =
          w.length - t := by omega
    rw [hremaining, Word.factor_prefix_shift,
      Word.factor_prefix_shift] at h
    exact h
  · exact occursSuffixAt_prefix_shift pre w j t

/--
The period half of the theta-coordinate interval form (Lemma 1.1): a suffix
occurrence at displacement `t-j` is exactly a period of the suffix anchored
at `j`.
-/
theorem occursSuffixAt_iff_anchoredPeriod
    (w : Word α) (j t : Nat) (hjt : j < t) (ht : t < w.length) :
    OccursSuffixAt w j t ↔ Word.AnchoredPeriod w j (t - j) := by
  have hjlen : j < w.length := Nat.lt_trans hjt ht
  have hslen : (w.drop j).length = w.length - j := by simp
  have hp : t - j < (w.drop j).length := by
    rw [hslen]
    omega
  have hremain : (w.drop j).length - (t - j) = w.length - t := by
    rw [hslen]
    omega
  have hdrop : (w.drop j).drop (t - j) = w.drop t := by
    rw [List.drop_drop]
    congr 1
    omega
  unfold OccursSuffixAt Word.AnchoredPeriod Word.HasPeriod Word.factor
  rw [hremain, hdrop]
  simp only [List.drop_zero]
  exact ⟨fun h => ⟨hp, h⟩, fun h => h.2⟩

/--
Suffix occurrences are upward closed along a fixed stride: shifting both
cuts to the right preserves the occurrence while the shifted suffix remains
nonempty.  This is the interval-monotonicity part of theta coordinates.
-/
theorem OccursSuffixAt.shift
    {w : Word α} {j t : Nat} (hocc : OccursSuffixAt w j t)
    (d : Nat) (htd : t + d < w.length) :
    OccursSuffixAt w (j + d) (t + d) := by
  have hd : d ≤ w.length - t := by omega
  have h := congrArg (fun x => Word.factor x d (w.length - (t + d))) hocc
  unfold OccursSuffixAt at hocc ⊢
  dsimp only at h
  rw [Word.factor_factor, Word.factor_factor] at h
  have hlen : w.length - (t + d) = w.length - t - d := by omega
  simpa [hlen, Nat.min_eq_left (Nat.le_refl _), Nat.add_assoc] using h

/-- A suffix-occurrence pair: a prefix reappears at displacement `δ`. -/
def SO (w : Word α) (lam δ : Nat) : Prop :=
  0 < lam ∧
  lam ≤ w.length ∧
  δ + lam ≤ w.length ∧
  Word.factor w 0 lam = Word.factor w δ lam

structure StraddleData where
  lam : Nat
  delta : Nat
  rho : Nat
  gap : Nat
  left : Nat
  hleft : left = rho - delta
  hleft_pos : 0 < left
  hleft_lt : left < lam

/--
The purely arithmetic part of the straddle decomposition:
`lam = left + (lam-left)`, with both pieces nonempty.
-/
theorem straddle_length_split (d : StraddleData) :
    d.lam = d.left + (d.lam - d.left) ∧
    0 < d.lam - d.left := by
  have hlt := d.hleft_lt
  constructor
  · omega
  · omega

/--
First collage piece of Lemma 19.

With zero-based indexing, `rho = delta + left`; therefore the part of the
copy before the deletion point is an actual shorter SO pair.
-/
theorem straddle_first_piece
    (w : Word α) (d : StraddleData)
    (hso : SO w d.lam d.delta) :
    Word.factor w 0 d.left = Word.factor w d.delta d.left := by
  exact Word.factor_eq_of_factor_eq_of_le w 0 d.delta d.lam d.left
    (Nat.le_of_lt d.hleft_lt) hso.2.2.2

/-- Every nonempty shorter prefix of an SO copy is itself an SO copy. -/
theorem SO.shrink
    {w : Word α} {lam delta small : Nat}
    (hso : SO w lam delta) (hsmall_pos : 0 < small)
    (hsmall : small ≤ lam) :
    SO w small delta := by
  rcases hso with ⟨hlam_pos, hlam_len, hcopy_len, hcopy⟩
  refine ⟨hsmall_pos, ?_, ?_,
    Word.factor_eq_of_factor_eq_of_le w 0 delta lam small hsmall hcopy⟩
  · omega
  · omega

/-- Lemma 19's first collage piece, packaged as a genuine SO pair. -/
theorem straddle_first_SO
    (w : Word α) (d : StraddleData) (hso : SO w d.lam d.delta) :
    SO w d.left d.delta :=
  hso.shrink d.hleft_pos (Nat.le_of_lt d.hleft_lt)

/-! ## Splicing: the finite-word core of notes v43--v45 -/

/-- Delete the half-open interval `[i,j)` from a word. -/
def splice (w : Word α) (i j : Nat) : Word α :=
  w.take i ++ w.drop j

theorem splice_length
    (w : Word α) (i j : Nat) (hij : i ≤ j) (hj : j ≤ w.length) :
    (splice w i j).length = i + (w.length - j) := by
  simp [splice, Nat.min_eq_left (Nat.le_trans hij hj)]

/-- A prefix wholly to the left of the deleted interval is unchanged. -/
theorem take_splice_of_le
    (w : Word α) (i j b : Nat) (hb : b ≤ i) (hi : i ≤ w.length) :
    (splice w i j).take b = w.take b := by
  rw [splice, List.take_append_of_le_length]
  · rw [List.take_take, Nat.min_eq_left hb]
  · simpa [Nat.min_eq_left hi] using hb

/-- A suffix wholly to the right of the deleted interval is unchanged. -/
theorem suffix_splice_of_le
    (w : Word α) (i j b : Nat) (hij : i ≤ j) (hj : j ≤ w.length)
    (hb : b ≤ w.length - j) :
    Word.suffix (splice w i j) b = Word.suffix w b := by
  unfold Word.suffix splice
  rw [List.length_append, List.length_take, List.length_drop,
    Nat.min_eq_left (Nat.le_trans hij hj)]
  have hoff : i + (w.length - j) - b = i + (w.length - j - b) := by omega
  rw [hoff]
  have htake_len : (w.take i).length = i := by
    simp [Nat.min_eq_left (Nat.le_trans hij hj)]
  have hdrop :
      (w.take i ++ w.drop j).drop (i + (w.length - j - b)) =
        (w.drop j).drop (w.length - j - b) := by
    simpa only [htake_len] using
      (List.drop_append (l₁ := w.take i) (l₂ := w.drop j) (w.length - j - b))
  rw [hdrop]
  rw [List.drop_drop]
  congr 1
  omega

/--
The word-combinatorial lifting step in notes v43, Theorem 45': a border
of a splice lifts to a border of the original word when both copies of
the border stay in the preserved regions.
-/
theorem splice_border_lifts
    (w : Word α) (i j b : Nat) (hij : i ≤ j) (hj : j ≤ w.length)
    (hb_left : b ≤ i) (hb_right : b ≤ w.length - j)
    (hborder : Word.«prefix» (splice w i j) b = Word.suffix (splice w i j) b) :
    Word.«prefix» w b = Word.suffix w b := by
  unfold Word.«prefix» at hborder ⊢
  rw [take_splice_of_le w i j b hb_left (Nat.le_trans hij hj)] at hborder
  rw [suffix_splice_of_le w i j b hij hj hb_right] at hborder
  exact hborder

theorem splice_borderCopy_lifts
    (w : Word α) (i j b : Nat) (hij : i ≤ j) (hj : j ≤ w.length)
    (hb_left : b ≤ i) (hb_right : b ≤ w.length - j)
    (hborder : Word.BorderCopy (splice w i j) b) :
    Word.BorderCopy w b :=
  splice_border_lifts w i j b hij hj hb_left hb_right hborder

/--
Second collage piece of Lemma 19, isolated as the exact local hypothesis
created by deleting a gap. The theorem records that the surviving tail is
the remaining suffix of the copied prefix.
-/
def SecondCollagePiece
    (w : Word α) (d : StraddleData) : Prop :=
  Word.factor w (d.rho + d.gap) (d.lam - d.left) =
    Word.factor w d.left (d.lam - d.left)

/--
A finite block alphabet used by the proposed block recursion.
`decode blocks = B₁ ++ ... ++ Bᵣ`.
-/
def decode (blocks : List (Word α)) : Word α :=
  blocks.flatten

/-- Offset of block `i` in the decoded word. -/
def blockOffset (blocks : List (Word α)) (i : Nat) : Nat :=
  ((blocks.take i).map List.length).sum

theorem decode_nil : decode ([] : List (Word α)) = [] := rfl

theorem decode_cons (b : Word α) (bs : List (Word α)) :
    decode (b :: bs) = b ++ decode bs := by
  rfl

theorem decode_length (blocks : List (Word α)) :
    (decode blocks).length = (blocks.map List.length).sum := by
  simp [decode]

theorem blockOffset_zero (blocks : List (Word α)) :
    blockOffset blocks 0 = 0 := by
  simp [blockOffset]

theorem blockOffset_succ (blocks : List (Word α)) (i : Nat)
    (hi : i < blocks.length) :
    blockOffset blocks (i + 1) = blockOffset blocks i + (blocks.get ⟨i, hi⟩).length := by
  induction blocks generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
      cases i with
      | zero => simp [blockOffset]
      | succ i =>
          have hi' : i < bs.length := by
            apply Nat.lt_of_succ_lt_succ
            simpa using hi
          simpa [blockOffset, Nat.add_assoc] using ih i hi'

theorem blockOffset_le_decode_length (blocks : List (Word α)) (i : Nat) :
    blockOffset blocks i ≤ (decode blocks).length := by
  induction blocks generalizing i with
  | nil => simp [blockOffset, decode]
  | cons b bs ih =>
      cases i with
      | zero => simp [blockOffset]
      | succ i =>
          simp only [blockOffset, List.take_succ_cons, List.map_cons, List.sum_cons,
            decode_cons, List.length_append]
          exact Nat.add_le_add_left (ih i) b.length

/--
Interface for the unproved saturation step in `notes_v28.md`.
It deliberately exposes the missing mathematical content rather than hiding
it behind an implementation.
-/
structure SaturatedEnvelope (α : Type u) where
  anchor : Word α
  gapBound : Nat
  blocks : List (Word α)
  blockBound : ∀ b ∈ blocks, b.length ≤ gapBound

/-!
The open targets (G-3″a) and (G-3″b) are intentionally not represented by
propositions yet.  Their notions of block alignment, local phase, bounded
exceptions, and contraction still require precise definitions; using `True`
here would provide no useful formal interface.
-/

section Examples

example : Word.factor ([0, 1, 2, 3] : Word Nat) 1 2 = [1, 2] := by decide

example : Word.HasPeriod ([0, 1, 0, 1] : Word Nat) 2 := by
  unfold Word.HasPeriod Word.factor
  decide

example : Word.BorderCopy ([0, 1, 0, 1] : Word Nat) 2 := by
  unfold Word.BorderCopy Word.«prefix» Word.suffix
  decide

example : SO ([0, 1, 0, 1] : Word Nat) 2 2 := by
  unfold SO Word.factor
  decide

example : OccursSuffixAt ([0, 1, 0, 1] : Word Nat) 0 2 := by
  unfold OccursSuffixAt Word.factor
  decide

example (d : StraddleData) :
    d.lam = d.left + (d.lam - d.left) :=
  (straddle_length_split d).1

end Examples

end NSSE
