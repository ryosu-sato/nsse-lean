import NSSE

/-!
# Insertion algebra for guarded deletion squares

These are the free-monoid identities used in Sections 4 and 7.4 of the
SOA proof.  They deliberately contain no finite-control abstraction.
-/

namespace NSSE

universe u

namespace Word

def insertAt (s payload : Word α) (slot : Nat) : Word α :=
  s.take slot ++ payload ++ s.drop slot

theorem insertAt_length
    (w payload : Word α) {slot : Nat} (hslot : slot ≤ w.length) :
    (insertAt w payload slot).length =
      w.length + payload.length := by
  simp [insertAt, Nat.min_eq_left hslot]
  omega

theorem factor_insertAt_before
    (w payload : Word α) (slot start len : Nat)
    (hslot : slot ≤ start) (hstart : start ≤ w.length) :
    factor (insertAt w payload slot)
        (start + payload.length) len =
      factor w start len := by
  have hslotlen : slot ≤ w.length := Nat.le_trans hslot hstart
  let pre := w.take slot
  let tail := w.drop slot
  have hprelen : pre.length = slot := by
    simp [pre, Nat.min_eq_left hslotlen]
  have hw : w = pre ++ tail :=
    (List.take_append_drop slot w).symm
  have hstartSplit : slot + (start - slot) = start := by omega
  calc
    factor (insertAt w payload slot)
        (start + payload.length) len =
        factor tail (start - slot) len := by
          unfold insertAt
          rw [show w.take slot = pre by rfl,
            show w.drop slot = tail by rfl]
          have hshift :
              (pre ++ payload).length + (start - slot) =
                start + payload.length := by
            simp [hprelen]
            omega
          rw [← hshift, factor_prefix_shift]
    _ = factor w start len := by
      rw [hw]
      have hf :=
        factor_prefix_shift pre tail (start - slot) len
      simpa [hprelen, hstartSplit] using hf.symm

theorem take_insertAt_before
    (w payload : Word α) (slot cut : Nat)
    (hslot : slot ≤ cut) (hcut : cut ≤ w.length) :
    (insertAt w payload slot).take (cut + payload.length) =
      insertAt (w.take cut) payload slot := by
  have hslotlen : slot ≤ w.length := Nat.le_trans hslot hcut
  unfold insertAt
  have htakeSlot : (w.take slot).length = slot := by
    simp [Nat.min_eq_left hslotlen]
  have htotal :
      cut + payload.length =
        (w.take slot).length +
          (payload.length + (cut - slot)) := by
    rw [htakeSlot]
    omega
  rw [List.append_assoc, List.append_assoc]
  rw [htotal, List.take_append, List.take_append]
  have htakeTake : (w.take cut).take slot = w.take slot := by
    simp [List.take_take, Nat.min_eq_left hslot]
  have hdropTake :
      (w.take cut).drop slot =
        (w.drop slot).take (cut - slot) := by
    simp [List.drop_take]
  rw [htakeTake, hdropTake]

/--
An insertion weakly after a cut leaves the prefix through that cut
literally unchanged.
-/
theorem take_insertAt_after
    (w payload : Word α) (slot cut : Nat)
    (hcut : cut ≤ slot) (hslot : slot ≤ w.length) :
    (insertAt w payload slot).take cut = w.take cut := by
  unfold insertAt
  have htakeLength : (w.take slot).length = slot := by
    simp [Nat.min_eq_left hslot]
  rw [List.append_assoc]
  rw [List.take_append_of_le_length]
  · simp [List.take_take, Nat.min_eq_left hcut]
  · rw [htakeLength]
    exact hcut

theorem factor_take_of_add_le
    (w : Word α) (start len cut : Nat)
    (hinterval : start + len ≤ cut) :
    factor (w.take cut) start len = factor w start len := by
  unfold factor
  rw [List.drop_take, List.take_take]
  have hlen : len ≤ cut - start := by omega
  rw [Nat.min_eq_left hlen]

/--
An insertion after the end of a factor leaves that factor unchanged.
-/
theorem factor_insertAt_after
    (w payload : Word α) (slot start len : Nat)
    (hinterval : start + len ≤ slot)
    (hslot : slot ≤ w.length) :
    factor (insertAt w payload slot) start len =
      factor w start len := by
  calc
    factor (insertAt w payload slot) start len =
        factor ((insertAt w payload slot).take slot) start len := by
      exact (factor_take_of_add_le
        (insertAt w payload slot) start len slot hinterval).symm
    _ = factor (w.take slot) start len := by
      rw [take_insertAt_after w payload slot slot
        (Nat.le_refl slot) hslot]
    _ = factor w start len :=
      factor_take_of_add_le w start len slot hinterval

/--
An insertion weakly before the source cut of a suffix occurrence shifts
both cuts by the payload length and preserves the literal occurrence.
-/
theorem occursSuffixAt_insertAt_before
    (w payload : Word α) (slot j t : Nat)
    (hslot : slot ≤ j) (hjt : j < t) (ht : t < w.length)
    (hoccurs : OccursSuffixAt w j t) :
    OccursSuffixAt (insertAt w payload slot)
      (j + payload.length) (t + payload.length) := by
  have hjlen : j < w.length := Nat.lt_trans hjt ht
  have hslotlen : slot ≤ w.length := Nat.le_of_lt
    (Nat.lt_of_le_of_lt hslot hjlen)
  let pre := w.take slot
  let tail := w.drop slot
  have hprelen : pre.length = slot := by
    simp [pre, Nat.min_eq_left hslotlen]
  have hw : w = pre ++ tail := by
    exact (List.take_append_drop slot w).symm
  have hj : slot + (j - slot) = j := by omega
  have ht' : slot + (t - slot) = t := by omega
  have htail :
      OccursSuffixAt tail (j - slot) (t - slot) := by
    apply (occursSuffixAt_prefix_shift_iff
      pre tail (j - slot) (t - slot)).1
    simpa [hprelen, hj, ht'] using (hw ▸ hoccurs)
  have hlift :=
    occursSuffixAt_prefix_shift (pre ++ payload) tail
      (j - slot) (t - slot) htail
  have hjshift :
      slot + (j - slot + payload.length) =
        j + payload.length := by omega
  have htshift :
      slot + (t - slot + payload.length) =
        t + payload.length := by omega
  unfold insertAt
  rw [show w.take slot = pre by rfl,
    show w.drop slot = tail by rfl]
  simpa [List.length_append, hprelen, hjshift, htshift,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlift

theorem insertAt_left_decomposition
    (A T B X : Word α) :
    insertAt (A ++ T ++ B) X A.length = A ++ X ++ T ++ B := by
  simp [insertAt, List.take_append, List.drop_append, List.append_assoc]

theorem insertAt_right_decomposition
    (A T B X : Word α) :
    insertAt (A ++ T ++ B) X (A.length + T.length) =
      A ++ T ++ X ++ B := by
  simp [insertAt, List.take_append, List.drop_append, List.append_assoc]

theorem insertAt_append_middle
    (left middle right payload : Word α)
    (slot : Nat) (hslot : slot ≤ middle.length) :
    insertAt (left ++ middle ++ right) payload
        (left.length + slot) =
      left ++ insertAt middle payload slot ++ right := by
  simp [insertAt, List.take_append, List.drop_append,
    hslot, List.append_assoc]
  rw [List.take_append_of_le_length hslot,
    List.drop_append_of_le_length hslot]

/--
Restoring two disjoint payloads is independent of restoration order once
the second slot is shifted by the length of the first payload.
-/
theorem disjoint_insertions_commute
    (A T B X Y : Word α) :
    insertAt (insertAt (A ++ T ++ B) X A.length)
        Y (A.length + X.length + T.length) =
      insertAt (insertAt (A ++ T ++ B) Y (A.length + T.length))
        X A.length := by
  calc
    insertAt (insertAt (A ++ T ++ B) X A.length)
        Y (A.length + X.length + T.length) =
        insertAt (A ++ X ++ T ++ B)
          Y (A.length + X.length + T.length) := by
            rw [insertAt_left_decomposition]
    _ = A ++ X ++ T ++ Y ++ B := by
      have h := insertAt_right_decomposition (A ++ X) T B Y
      simpa [List.length_append, List.append_assoc] using h
    _ = insertAt (insertAt (A ++ T ++ B) Y (A.length + T.length))
          X A.length := by
      rw [insertAt_right_decomposition]
      have h := insertAt_left_decomposition A (T ++ Y) B X
      simpa [List.append_assoc] using h.symm

/--
Cancellation form of insertion-square holonomy:
putting the same payload on the two sides of `T` gives the same word
exactly when the payload commutes with `T`.
-/
theorem insertion_slots_equal_iff_commute
    (A T B X : Word α) :
    A ++ X ++ T ++ B = A ++ T ++ X ++ B ↔ X ++ T = T ++ X := by
  constructor
  · intro h
    have h₁ : X ++ T ++ B = T ++ X ++ B := by
      apply List.append_cancel_left (as := A)
      simpa [List.append_assoc] using h
    apply List.append_cancel_right (bs := B)
    simpa [List.append_assoc] using h₁
  · intro h
    simp [List.append_assoc, h]

theorem insertAt_two_slots_equal_iff_commute
    (A T B X : Word α) :
    insertAt (A ++ T ++ B) X A.length =
        insertAt (A ++ T ++ B) X (A.length + T.length) ↔
      X ++ T = T ++ X := by
  rw [insertAt_left_decomposition, insertAt_right_decomposition]
  exact insertion_slots_equal_iff_commute A T B X

end Word

end NSSE
