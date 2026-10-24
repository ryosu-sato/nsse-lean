import NSSE
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Infix

/-!
# Literal suffix-border rank and terminal block descent

The rank is exactly the maximum number of nonempty proper borders of a
suffix, as in notes v1317 §3. Blocks are literal words; empty blocks are
retained. This file does not assert avoidance decidability or SAB.
-/

namespace NSSE.TerminalBorderRank

universe u
variable {α : Type u}

/-- Prefix every block by the separator. Every block, even an empty one,
contributes at least one original letter. -/
def lead (a : α) (bs : List (List α)) : List α :=
  bs.flatMap (fun b => a :: b)

/-- The word `a U₁ a ... Uₘ a`, including both boundary separators. -/
def frame (a : α) (bs : List (List α)) : List α :=
  lead a bs ++ [a]

@[simp] theorem lead_nil (a : α) : lead a [] = [] := rfl

@[simp] theorem lead_cons (a : α) (b : List α) (bs : List (List α)) :
    lead a (b :: bs) = (a :: b) ++ lead a bs := rfl

@[simp] theorem lead_append (a : α) (xs ys : List (List α)) :
    lead a (xs ++ ys) = lead a xs ++ lead a ys := by
  simp [lead]

@[simp] theorem frame_nil (a : α) : frame a [] = [a] := rfl

theorem frame_append (a : α) (xs ys : List (List α)) :
    frame a (xs ++ ys) = lead a xs ++ frame a ys := by
  simp [frame, List.append_assoc]

theorem length_le_lead (a : α) (bs : List (List α)) :
    bs.length ≤ (lead a bs).length := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      simp only [lead_cons, List.length_append, List.length_cons] at *
      omega

theorem frame_length (a : α) (bs : List (List α)) :
    (frame a bs).length = (lead a bs).length + 1 := by
  simp [frame]

theorem frame_take_length_lt (a : α) (bs : List (List α))
    {i j : Nat} (hij : i < j) (hj : j ≤ bs.length) :
    (frame a (bs.take i)).length < (frame a (bs.take j)).length := by
  have hsplit : bs.take j = bs.take i ++ (bs.drop i).take (j - i) := by
    have h := List.take_append_drop i (bs.take j)
    simpa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hij), List.drop_take] using h.symm
  rw [hsplit, frame_append]
  have hlen := length_le_lead a ((bs.drop i).take (j - i))
  have hparts := frame_length a ((bs.drop i).take (j - i))
  have hfirst := frame_length a (bs.take i)
  simp only [List.length_take, List.length_drop] at hlen
  simp only [List.length_append]
  omega

theorem frame_isSuffix (a : α) {xs ys : List (List α)}
    (h : xs <:+ ys) : frame a xs <:+ frame a ys := by
  rcases h with ⟨pre, rfl⟩
  exact ⟨lead a pre, (frame_append a pre xs).symm⟩

theorem frame_isPrefix_of_proper (a : α) {xs ys : List (List α)}
    (h : xs <+: ys) (hlt : xs.length < ys.length) :
    frame a xs <+: frame a ys := by
  rcases h with ⟨rest, rfl⟩
  cases rest with
  | nil => simp at hlt
  | cons b rest =>
      refine ⟨b ++ frame a rest, ?_⟩
      simp [frame, List.append_assoc]

theorem borderCopy_of_prefix_suffix {v w : List α}
    (hp : v <+: w) (hs : v <:+ w) : Word.BorderCopy w v.length := by
  unfold Word.BorderCopy Word.«prefix» Word.suffix
  exact (List.prefix_iff_eq_take.mp hp).symm.trans (List.suffix_iff_eq_drop.mp hs)

variable [DecidableEq α]

/-- The actual lengths of all nonempty proper borders, not a proxy measure. -/
def properBorderLengths (w : List α) : Finset Nat :=
  (Finset.range w.length).filter (fun b => 0 < b ∧ w.take b = w.drop (w.length - b))

def borderCount (w : List α) : Nat := (properBorderLengths w).card

/-- Include the empty suffix, whose border count is zero. -/
def suffixBorderRank (w : List α) : Nat :=
  (Finset.range (w.length + 1)).sup (fun j => borderCount (w.drop j))

theorem mem_properBorderLengths {w : List α} {b : Nat} :
    b ∈ properBorderLengths w ↔
      0 < b ∧ b < w.length ∧ Word.BorderCopy w b := by
  simp only [properBorderLengths, Finset.mem_filter, Finset.mem_range,
    Word.BorderCopy, Word.«prefix», Word.suffix]
  tauto

@[simp] theorem borderCount_nil : borderCount ([] : List α) = 0 := by
  simp [borderCount, properBorderLengths]

@[simp] theorem suffixBorderRank_nil : suffixBorderRank ([] : List α) = 0 := by
  simp [suffixBorderRank]

theorem frame_border_mem (a : α) {bs : List (List α)} {b : Nat}
    (hb : b ∈ properBorderLengths bs) :
    (frame a (bs.take b)).length ∈ properBorderLengths (frame a bs) := by
  obtain ⟨hpos, hlt, hcopy⟩ := mem_properBorderLengths.mp hb
  have htake : (bs.take b).length = b := by simp [Nat.min_eq_left hlt.le]
  have hs : bs.take b <:+ bs := by
    apply List.suffix_iff_eq_drop.mpr
    simpa only [htake] using hcopy
  have hp := frame_isPrefix_of_proper a (List.take_prefix b bs) (by omega)
  have hfs := frame_isSuffix a hs
  have hlen := frame_length a (bs.take b)
  have hstrict := frame_take_length_lt a bs hlt (Nat.le_refl bs.length)
  simp only [List.take_length] at hstrict
  exact mem_properBorderLengths.mpr
    ⟨by omega, hstrict, borderCopy_of_prefix_suffix hp hfs⟩

theorem one_mem_frame_borders (a : α) {bs : List (List α)} (hbs : bs ≠ []) :
    1 ∈ properBorderLengths (frame a bs) := by
  have hpos : 0 < bs.length := List.length_pos_iff.mpr hbs
  have hp := frame_isPrefix_of_proper a
    (show ([] : List (List α)) <+: bs from List.nil_prefix) (by simpa using hpos)
  have hs := frame_isSuffix a (show ([] : List (List α)) <:+ bs from List.nil_suffix)
  have hcopy := borderCopy_of_prefix_suffix hp hs
  have hlen := length_le_lead a bs
  have hframe := frame_length a bs
  apply mem_properBorderLengths.mpr
  exact ⟨by omega, by omega, by simpa using hcopy⟩

/-- Every block border lifts, and the single separator adds a distinct border.
No separator-freeness hypothesis on block contents is needed for this inequality. -/
theorem borderCount_add_one_le_frame (a : α) {bs : List (List α)} (hbs : bs ≠ []) :
    borderCount bs + 1 ≤ borderCount (frame a bs) := by
  let f : Nat → Nat := fun b => (frame a (bs.take b)).length
  have hinj : Set.InjOn f (properBorderLengths bs) := by
    intro i hi j hj heq
    have hi' := (mem_properBorderLengths.mp hi).2.1
    have hj' := (mem_properBorderLengths.mp hj).2.1
    rcases lt_trichotomy i j with hij | hij | hij
    · have := frame_take_length_lt a bs hij hj'.le
      change (frame a (bs.take i)).length = (frame a (bs.take j)).length at heq
      omega
    · exact hij
    · have := frame_take_length_lt a bs hij hi'.le
      change (frame a (bs.take i)).length = (frame a (bs.take j)).length at heq
      omega
  have hnot : 1 ∉ (properBorderLengths bs).image f := by
    intro hmem
    obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hmem
    obtain ⟨hpos, hlt, _⟩ := mem_properBorderLengths.mp hb
    have htake : (bs.take b).length = b := by simp [Nat.min_eq_left hlt.le]
    have hlead := length_le_lead a (bs.take b)
    have hframe := frame_length a (bs.take b)
    change (frame a (bs.take b)).length = 1 at heq
    omega
  have hsub : insert 1 ((properBorderLengths bs).image f) ⊆
      properBorderLengths (frame a bs) := by
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact one_mem_frame_borders a hbs
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
      exact frame_border_mem a hc
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_not_mem hnot, Finset.card_image_of_injOn hinj] at hcard
  exact hcard

theorem borderCount_le_rank_of_suffix {z w : List α} (h : z <:+ w) :
    borderCount z ≤ suffixBorderRank w := by
  rcases h with ⟨pre, rfl⟩
  have hi : pre.length ∈ Finset.range ((pre ++ z).length + 1) := by
    simp only [Finset.mem_range, List.length_append]
    omega
  have hle := Finset.le_sup (f := fun j => borderCount ((pre ++ z).drop j)) hi
  simpa [suffixBorderRank] using hle

theorem rank_mono_suffix {z w : List α} (h : z <:+ w) :
    suffixBorderRank z ≤ suffixBorderRank w := by
  apply Finset.sup_le
  intro j _
  exact borderCount_le_rank_of_suffix ((List.drop_suffix j z).trans h)

/-- A legal nonempty copied tail forces a positive value of the exact rank. -/
theorem occursSuffixAt_rank_pos (w : List α) (j t : Nat)
    (hjt : j < t) (ht : t < w.length) (hocc : OccursSuffixAt w j t) :
    0 < suffixBorderRank w := by
  have hper := (occursSuffixAt_iff_anchoredPeriod w j t hjt ht).mp hocc
  change Word.HasPeriod (w.drop j) (t - j) at hper
  have hcopy := (Word.hasPeriod_iff_borderCopy (w.drop j) (t - j) hper.1).mp hper
  have hmem : (w.drop j).length - (t - j) ∈ properBorderLengths (w.drop j) := by
    apply mem_properBorderLengths.mpr
    refine ⟨?_, ?_, hcopy⟩ <;> have := hper.1 <;> omega
  have hcount : 0 < borderCount (w.drop j) :=
    Finset.card_pos.mpr ⟨_, hmem⟩
  exact hcount.trans_le (borderCount_le_rank_of_suffix (List.drop_suffix j w))

/-- Rank zero discharges all positive-tail witnesses in the recursion's base case. -/
theorem rank_zero_no_occursSuffixAt (w : List α) (hzero : suffixBorderRank w = 0)
    (j t : Nat) (hjt : j < t) (ht : t < w.length) : ¬ OccursSuffixAt w j t := by
  intro hocc
  have := occursSuffixAt_rank_pos w j t hjt ht hocc
  omega

/-- Strict descent of the exact suffix-border rank on the nonempty block body. -/
theorem rank_add_one_le_frame (a : α) {bs : List (List α)} (hbs : bs ≠ []) :
    suffixBorderRank bs + 1 ≤ suffixBorderRank (frame a bs) := by
  have hwhole := borderCount_add_one_le_frame a hbs
  have hself := borderCount_le_rank_of_suffix (List.suffix_refl (frame a bs))
  have hpos : 1 ≤ suffixBorderRank (frame a bs) := by omega
  have hrank : suffixBorderRank bs ≤ suffixBorderRank (frame a bs) - 1 := by
    apply Finset.sup_le
    intro j _
    by_cases hz : bs.drop j = []
    · simp [hz]
    · have hlocal := borderCount_add_one_le_frame a hz
      have hupper := borderCount_le_rank_of_suffix
        (frame_isSuffix a (List.drop_suffix j bs))
      omega
  omega

/-- For `w = U₁ a U₂ a ... Uₘ a`, the encoded body is `[U₂,...,Uₘ]`.
The first block `U₁` is not part of that body. -/
theorem rank_add_one_le_decoded (a : α) (first : List α)
    {body : List (List α)} (hbody : body ≠ []) :
    suffixBorderRank body + 1 ≤ suffixBorderRank (first ++ frame a body) := by
  exact (rank_add_one_le_frame a hbody).trans
    (rank_mono_suffix (List.suffix_append first (frame a body)))

/-- The recursion's rank promise, including the one-block/empty-new-body case. -/
theorem rankBound_descent (a : α) (first : List α) (body : List (List α))
    {h : Nat} (hpos : 0 < h)
    (hbound : suffixBorderRank (first ++ frame a body) ≤ h) :
    suffixBorderRank body ≤ h - 1 := by
  by_cases hempty : body = []
  · simp [hempty]
  · have hstrict := rank_add_one_le_decoded a first hempty
    omega

/-- Append a separator to each block, retaining empty blocks. -/
def decodeBlocks (a : α) : List (List α) → List α
  | [] => []
  | b :: bs => b ++ a :: decodeBlocks a bs

omit [DecidableEq α] in
theorem frame_eq_cons_decode (a : α) (bs : List (List α)) :
    frame a bs = a :: decodeBlocks a bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      rw [show frame a (b :: bs) = (a :: b) ++ frame a bs by
        simp [frame, List.append_assoc], ih]
      rfl

omit [DecidableEq α] in
theorem decodeBlocks_cons (a : α) (first : List α) (body : List (List α)) :
    decodeBlocks a (first :: body) = first ++ frame a body := by
  rw [frame_eq_cons_decode]
  rfl

/-- Split the portion BEFORE the final separator. The result is always
nonempty, and a trailing empty block is a letter, not a missing block. -/
def split (a : α) : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
      if x = a then [] :: split a xs
      else match split a xs with
        | [] => [[x]]
        | b :: bs => (x :: b) :: bs

theorem split_ne_nil (a : α) (w : List α) : split a w ≠ [] := by
  cases w with
  | nil => simp [split]
  | cons x xs =>
      simp only [split]
      split
      · simp
      · split <;> simp

/-- The computable splitting operation reconstructs the full terminal word. -/
theorem decodeBlocks_split (a : α) (w : List α) :
    decodeBlocks a (split a w) = w ++ [a] := by
  induction w with
  | nil => simp [split, decodeBlocks]
  | cons x xs ih =>
      by_cases hx : x = a
      · subst x
        simpa [split, decodeBlocks] using congrArg (List.cons a) ih
      · cases hs : split a xs with
        | nil => exact False.elim (split_ne_nil a xs hs)
        | cons b bs =>
            simp only [split, if_neg hx, hs, decodeBlocks]
            simp only [hs, decodeBlocks] at ih
            simpa only [List.cons_append] using congrArg (List.cons x) ih

/-- The literal blocks produced by `split` contain no separator. -/
theorem separator_not_mem_split (a : α) (w : List α) :
    ∀ b ∈ split a w, a ∉ b := by
  induction w with
  | nil => simp [split]
  | cons x xs ih =>
      by_cases hx : x = a
      · subst x
        simpa [split] using ih
      · cases hs : split a xs with
        | nil => exact False.elim (split_ne_nil a xs hs)
        | cons b bs =>
            have hb : a ∉ b := ih b (by simp [hs])
            have hbs : ∀ c ∈ bs, a ∉ c := by
              intro c hc
              exact ih c (by simp [hs, hc])
            simpa [split, hx, hs, Ne.symm hx] using And.intro hb hbs

/-- The rank premise used by the actual terminal-letter split recursion. -/
theorem rankBound_split (a : α) (w : List α) {h : Nat} (hpos : 0 < h)
    (hbound : suffixBorderRank (w ++ [a]) ≤ h) :
    suffixBorderRank (split a w).tail ≤ h - 1 := by
  cases hs : split a w with
  | nil => exact False.elim (split_ne_nil a w hs)
  | cons first body =>
      have hdecode := decodeBlocks_split a w
      rw [hs, decodeBlocks_cons] at hdecode
      simp only [List.tail_cons]
      apply rankBound_descent a first body hpos
      simpa only [hdecode] using hbound

end NSSE.TerminalBorderRank
