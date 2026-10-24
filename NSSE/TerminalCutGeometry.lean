import NSSE.TerminalBorderRank

/-! # Exact terminal-block fibers of every positive-tail suffix occurrence

Cuts are positions in the original body. Empty blocks are retained. The
proof compares suffixes by prefix, so overlapping copies require no
disjoint-factor assumption.
-/

namespace NSSE.TerminalCutGeometry

open TerminalBorderRank

universe u
variable {D : Type u}

def NoA (a : D) (bs : List (List D)) : Prop := ∀ b ∈ bs, a ∉ b

@[simp] theorem noA_nil (a : D) : NoA a [] := by simp [NoA]

@[simp] theorem noA_cons (a : D) (U : List D) (bs : List (List D)) :
    NoA a (U :: bs) ↔ a ∉ U ∧ NoA a bs := by simp [NoA]

@[simp] theorem noA_append (a : D) (xs ys : List (List D)) :
    NoA a (xs ++ ys) ↔ NoA a xs ∧ NoA a ys := by simp [NoA, or_imp, forall_and]

@[simp] theorem decode_append (a : D) (xs ys : List (List D)) :
    decodeBlocks a (xs ++ ys) = decodeBlocks a xs ++ decodeBlocks a ys := by
  induction xs with
  | nil => rfl
  | cons U xs ih => simp only [List.cons_append, decodeBlocks, ih, List.append_assoc, List.cons_append]

theorem decode_prefix (a : D) {xs ys : List (List D)} (h : xs <+: ys) :
    decodeBlocks a xs <+: decodeBlocks a ys := by
  obtain ⟨rest, rfl⟩ := h
  exact ⟨decodeBlocks a rest, (decode_append a xs rest).symm⟩

/-- The first delimiter aligns, including an empty word on either side. -/
theorem first_separator_prefix (a : D) (S T x y : List D)
    (hS : a ∉ S) (hT : a ∉ T) :
    (S ++ a :: x) <+: (T ++ a :: y) ↔ S = T ∧ x <+: y := by
  induction S generalizing T with
  | nil =>
      cases T with
      | nil => simp
      | cons b T =>
          have hab : a ≠ b := fun h => hT (by simp [h])
          simp [hab]
  | cons b S ih =>
      have hba : b ≠ a := fun h => hS (by simp [h])
      have hs : a ∉ S := fun h => hS (List.mem_cons_of_mem b h)
      cases T with
      | nil => simp [hba]
      | cons c T =>
          have ht : a ∉ T := fun h => hT (List.mem_cons_of_mem c h)
          simp only [List.cons_append, List.cons_prefix_cons, List.cons.injEq, ih T hs ht]
          tauto

/-- Terminal block decoding reflects prefix, not just whole-word equality. -/
theorem decode_prefix_iff (a : D) (xs ys : List (List D))
    (hx : NoA a xs) (hy : NoA a ys) :
    decodeBlocks a xs <+: decodeBlocks a ys ↔ xs <+: ys := by
  induction xs generalizing ys with
  | nil => simp [decodeBlocks]
  | cons U xs ih =>
      obtain ⟨hU, hx⟩ := (noA_cons a U xs).mp hx
      cases ys with
      | nil => simp [decodeBlocks]
      | cons V ys =>
          obtain ⟨hV, hy⟩ := (noA_cons a V ys).mp hy
          change (U ++ a :: decodeBlocks a xs) <+: (V ++ a :: decodeBlocks a ys) ↔ _
          rw [first_separator_prefix a U V _ _ hU hV, ih ys hx hy, List.cons_prefix_cons]

/-- The occurrence equality is precisely prefix comparison of whole suffixes. -/
theorem occurs_iff_prefix (w : List D) (j t : Nat) :
    OccursSuffixAt w j t ↔ w.drop t <+: w.drop j := by
  unfold OccursSuffixAt Word.factor
  have ht : (w.drop t).take (w.length - t) = w.drop t := by
    apply List.take_of_length_le
    simp
  rw [ht, List.prefix_iff_eq_take]
  simp only [List.length_drop]
  exact eq_comm

/-- Every cut before EOF lies within one block, possibly at its right edge. -/
theorem locate_cut (a : D) (bs : List (List D)) (j : Nat)
    (hj : j < (decodeBlocks a bs).length) :
    ∃ A P S C, bs = A ++ (P ++ S) :: C ∧
      j = (decodeBlocks a A).length + P.length := by
  induction bs generalizing j with
  | nil => simp [decodeBlocks] at hj
  | cons U bs ih =>
      by_cases h : j ≤ U.length
      · refine ⟨[], U.take j, U.drop j, bs, ?_, ?_⟩
        · simp
        · simp [decodeBlocks, Nat.min_eq_left h]
      · have hrest : j - (U.length + 1) < (decodeBlocks a bs).length := by
          simp only [decodeBlocks, List.length_append, List.length_cons] at hj
          omega
        obtain ⟨A, P, S, C, hbs, hj'⟩ := ih _ hrest
        refine ⟨U :: A, P, S, C, ?_, ?_⟩
        · simp only [List.cons_append, hbs]
        · simp only [decodeBlocks, List.length_append, List.length_cons]
          omega

theorem drop_at_cut (a : D) (A C : List (List D)) (P S : List D) :
    (decodeBlocks a (A ++ (P ++ S) :: C)).drop
        ((decodeBlocks a A).length + P.length) = S ++ a :: decodeBlocks a C := by
  simp only [decode_append, decodeBlocks, List.append_assoc]
  rw [List.drop_append]
  simp

/-- Positive tail equality aligns the local suffix and all complete later blocks. -/
theorem located_occurs_iff (a : D) (bs : List (List D)) (hbs : NoA a bs)
    (A C B F : List (List D)) (P S Q T : List D)
    (hleft : bs = A ++ (P ++ S) :: C) (hright : bs = B ++ (Q ++ T) :: F) :
    OccursSuffixAt (decodeBlocks a bs)
      ((decodeBlocks a A).length + P.length) ((decodeBlocks a B).length + Q.length) ↔
        S = T ∧ F <+: C := by
  have hl := hbs
  rw [hleft, noA_append, noA_cons] at hl
  have hr := hbs
  rw [hright, noA_append, noA_cons] at hr
  have hS : a ∉ S := fun h => hl.2.1 (List.mem_append_right P h)
  have hT : a ∉ T := fun h => hr.2.1 (List.mem_append_right Q h)
  rw [occurs_iff_prefix]
  have hdropL := drop_at_cut a A C P S
  have hdropR := drop_at_cut a B F Q T
  rw [← hleft] at hdropL
  rw [← hright] at hdropR
  rw [hdropL, hdropR, first_separator_prefix a T S _ _ hT hS,
    decode_prefix_iff a F C hr.2.2 hl.2.2]
  exact and_congr eq_comm Iff.rfl

theorem earlier_block_ends_before (a : D) (bs A C B F : List (List D)) (U V : List D)
    (hleft : bs = A ++ U :: C) (hright : bs = B ++ V :: F) (hlt : A.length < B.length) :
    (decodeBlocks a A).length + U.length < (decodeBlocks a B).length := by
  have hp : A ++ [U] <+: bs := ⟨C, by simp [hleft, List.append_assoc]⟩
  have hq : B <+: bs := ⟨V :: F, hright.symm⟩
  have hsub := List.prefix_of_prefix_length_le hp hq (by simp; omega)
  have hlen := (decode_prefix a hsub).length_le
  simp only [decode_append, decodeBlocks, List.length_append, List.length_cons,
    List.length_nil] at hlen
  omega

/-- Equal local suffixes and increasing original cuts force increasing
block positions. Two different cuts cannot project to the same block. -/
theorem aligned_cuts_order (a : D) (bs A C B F : List (List D)) (P Q S : List D)
    (hleft : bs = A ++ (P ++ S) :: C) (hright : bs = B ++ (Q ++ S) :: F)
    (hlt : (decodeBlocks a A).length + P.length < (decodeBlocks a B).length + Q.length) :
    A.length < B.length := by
  by_contra h
  have hba : B.length ≤ A.length := by omega
  rcases lt_or_eq_of_le hba with hba | hba
  · have hbefore := earlier_block_ends_before a bs B F A C (Q ++ S) (P ++ S) hright hleft hba
    simp only [List.length_append] at hbefore
    omega
  · have hp : A <+: bs := ⟨(P ++ S) :: C, hleft.symm⟩
    have hq : B <+: bs := ⟨(Q ++ S) :: F, hright.symm⟩
    have hAB : A = B := (List.prefix_of_prefix_length_le hp hq (by omega)).eq_of_length (by omega)
    subst B
    have he := hleft.symm.trans hright
    have hPQ : P = Q := by simpa using (List.cons.inj (List.append_cancel_left he)).1
    subst Q
    omega

theorem ordered_decompositions (bs A C B F : List (List D)) (U V : List D)
    (hleft : bs = A ++ U :: C) (hright : bs = B ++ V :: F) (hlt : A.length < B.length) :
    ∃ M, B = A ++ U :: M ∧ C = M ++ V :: F := by
  have hp : A ++ [U] <+: bs := ⟨C, by simp [hleft, List.append_assoc]⟩
  have hq : B <+: bs := ⟨V :: F, hright.symm⟩
  obtain ⟨M, hM⟩ := List.prefix_of_prefix_length_le hp hq (by simp; omega)
  have hB : B = A ++ U :: M := by simpa [List.append_assoc] using hM.symm
  refine ⟨M, hB, ?_⟩
  have he := hleft.symm.trans hright
  rw [hB] at he
  simpa only [List.append_assoc, List.cons_append, List.append_cancel_left_eq,
    List.cons.injEq, true_and] using he

/-- On a block pair, the new copied tail may be empty, including when V
is the final block. It is the original OccursSuffixAt definition on bs.tail. -/
theorem block_pair_occurs (A M C : List (List D)) (U V : List D) :
    OccursSuffixAt (A ++ U :: (M ++ V :: C)).tail A.length (A.length + M.length + 1) ↔
      C <+: M ++ V :: C := by
  rw [occurs_iff_prefix, List.drop_tail, List.drop_tail]
  have hl : (A ++ U :: (M ++ V :: C)).drop (A.length + 1) = M ++ V :: C := by
    rw [List.drop_append]
    simp
  have hr : (A ++ U :: (M ++ V :: C)).drop (A.length + M.length + 1 + 1) = C := by
    rw [show A.length + M.length + 1 + 1 = A.length + (M.length + 2) by omega,
      List.drop_append]
    simp [List.drop_append]
  rw [hl, hr]

theorem block_pair_legal (A M C : List (List D)) (U V : List D) :
    A.length < A.length + M.length + 1 ∧
      A.length + M.length + 1 ≤ (A ++ U :: (M ++ V :: C)).tail.length := by
  simp only [List.length_tail, List.length_append, List.length_cons]
  omega

/-- The exact all-cut geometric fiber theorem. It projects every original
positive-tail occurrence and reconstructs every fiber witness, with the
same cuts j,t. All common suffix choices are retained existentially. -/
theorem occurs_iff_fiber (a : D) (bs : List (List D)) (hbs : NoA a bs)
    (j t : Nat) (hjt : j < t) (ht : t < (decodeBlocks a bs).length) :
    OccursSuffixAt (decodeBlocks a bs) j t ↔
      ∃ A P Q S M C,
        bs = A ++ (P ++ S) :: (M ++ (Q ++ S) :: C) ∧
        j = (decodeBlocks a A).length + P.length ∧
        t = (decodeBlocks a (A ++ (P ++ S) :: M)).length + Q.length ∧
        OccursSuffixAt bs.tail A.length (A.length + M.length + 1) := by
  constructor
  · intro hocc
    obtain ⟨A, P, S, C, hleft, hj⟩ := locate_cut a bs j (by omega)
    obtain ⟨B, Q, T, F, hright, ht'⟩ := locate_cut a bs t ht
    rw [hj, ht'] at hocc
    obtain ⟨hST, hFC⟩ := (located_occurs_iff a bs hbs A C B F P S Q T hleft hright).mp hocc
    subst T
    have hlt := aligned_cuts_order a bs A C B F P Q S hleft hright (by omega)
    obtain ⟨M, hB, hC⟩ := ordered_decompositions bs A C B F (P ++ S) (Q ++ S) hleft hright hlt
    refine ⟨A, P, Q, S, M, F, hleft.trans (by rw [hC]), hj, ?_, ?_⟩
    · simpa only [hB] using ht'
    · rw [hleft, hC, block_pair_occurs]
      simpa only [hC] using hFC
  · rintro ⟨A, P, Q, S, M, C, hsplit, rfl, rfl, hocc⟩
    have hleft := hsplit
    have hright : bs = (A ++ (P ++ S) :: M) ++ (Q ++ S) :: C := by
      simpa only [List.append_assoc, List.cons_append] using hsplit
    apply (located_occurs_iff a bs hbs A (M ++ (Q ++ S) :: C)
      (A ++ (P ++ S) :: M) C P S Q S hleft hright).mpr
    refine ⟨rfl, ?_⟩
    rw [hsplit, block_pair_occurs] at hocc
    exact hocc

theorem locate_letter {E : Type*} (xs : List E) (k : Nat) (hk : k < xs.length) :
    ∃ A U C, xs = A ++ U :: C ∧ A.length = k := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
      cases k with
      | zero => exact ⟨[], x, xs, rfl, rfl⟩
      | succ k =>
          obtain ⟨A, U, C, hxs, hA⟩ := ih k (by simpa using hk)
          exact ⟨x :: A, U, C, by simp [hxs], by simp [hA]⟩

/-- All legal cut pairs on the new body are precisely pairs of distinct
predecessor blocks. The right cut is allowed at the new body's EOF. -/
theorem locate_block_pair (bs : List (List D)) (j t : Nat)
    (hjt : j < t) (ht : t ≤ bs.tail.length) :
    ∃ A U M V C, bs = A ++ U :: (M ++ V :: C) ∧
      j = A.length ∧ t = A.length + M.length + 1 := by
  have ht' : t < bs.length := by
    simp only [List.length_tail] at ht
    omega
  obtain ⟨A, U, C, hleft, hA⟩ := locate_letter bs j (by omega)
  obtain ⟨B, V, F, hright, hB⟩ := locate_letter bs t ht'
  obtain ⟨M, hBM, hC⟩ := ordered_decompositions bs A C B F U V hleft hright (by omega)
  refine ⟨A, U, M, V, F, hleft.trans (by rw [hC]), hA.symm, ?_⟩
  rw [hBM] at hB
  simp only [List.length_append, List.length_cons] at hB
  omega

theorem old_pair_legal (a : D) (A M C : List (List D)) (P Q S : List D) :
    (decodeBlocks a A).length + P.length <
        (decodeBlocks a (A ++ (P ++ S) :: M)).length + Q.length ∧
    (decodeBlocks a (A ++ (P ++ S) :: M)).length + Q.length <
        (decodeBlocks a (A ++ (P ++ S) :: (M ++ (Q ++ S) :: C))).length := by
  simp only [decode_append, decodeBlocks, List.length_append, List.length_cons]
  omega

/-- The fiber's copy condition alone is an equivalence, with original cuts
explicit. No acceptance or guard hypothesis is hidden in this geometry. -/
theorem old_pair_occurs (a : D) (A M C : List (List D)) (P Q S : List D)
    (hNoA : NoA a (A ++ (P ++ S) :: (M ++ (Q ++ S) :: C))) :
    OccursSuffixAt (decodeBlocks a (A ++ (P ++ S) :: (M ++ (Q ++ S) :: C)))
      ((decodeBlocks a A).length + P.length)
      ((decodeBlocks a (A ++ (P ++ S) :: M)).length + Q.length) ↔
    OccursSuffixAt (A ++ (P ++ S) :: (M ++ (Q ++ S) :: C)).tail
      A.length (A.length + M.length + 1) := by
  have he : A ++ (P ++ S) :: (M ++ (Q ++ S) :: C) =
      (A ++ (P ++ S) :: M) ++ (Q ++ S) :: C := by simp [List.append_assoc]
  rw [located_occurs_iff a _ hNoA A (M ++ (Q ++ S) :: C)
    (A ++ (P ++ S) :: M) C P S Q S rfl he, block_pair_occurs]
  exact ⟨And.right, fun h => ⟨rfl, h⟩⟩

end NSSE.TerminalCutGeometry
