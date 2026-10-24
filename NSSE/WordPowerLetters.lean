import NSSE.FiniteBoundaryCover

/-!
# Letter lookup inside a finite word power

This is the concrete list-indexing bridge for powered zones of a linear
word family.
-/

namespace NSSE

universe u

namespace Word

theorem power_getElem?_copy_offset
    (word : Word α)
    (copies copy offset : Nat)
    (hcopy : copy < copies)
    (hoffset : offset < word.length) :
    (power word copies)[copy * word.length + offset]? =
      word[offset]? := by
  obtain ⟨rest, hcopies⟩ :
      ∃ rest, copies = copy + 1 + rest := by
    refine ⟨copies - (copy + 1), ?_⟩
    omega
  have hdecompose :
      power word copies =
        power word copy ++ (word ++ power word rest) := by
    rw [hcopies, Nat.add_assoc,
      power_add word copy (1 + rest),
      Nat.add_comm 1 rest, power_succ]
  rw [hdecompose]
  rw [List.getElem?_append_right]
  · rw [power_length, Nat.add_sub_cancel_left]
    exact List.getElem?_append_left hoffset
  · simp only [power_length]
    omega

end Word

end NSSE
