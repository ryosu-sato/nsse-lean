import NSSE.P0NestedRepeats

/-! Pigeonhole construction inside every interval. The bound uses the
exact finite enumeration of words of bounded length, including epsilon;
this is deliberately a larger recurrence than the paper's optimized one. -/
namespace NSSE.P0NestedSelection
open P0ProperMachine P0ProperWords P0LoopStreams P0NestedRepeats
variable {A : Type*} [DecidableEq A]

theorem separated (s B : Nat) (a l : Nat → Nat)
    (ha : ∀ i, s+i*(B+1) ≤ a i)
    (hl : ∀ i, a i+l i ≤ s+i*(B+1)+B)
    (i j : Nat) (hij : i < j) : a i+l i < a j := by
  have hmul := Nat.mul_le_mul_right (B+1) (show i+1 ≤ j by omega)
  rw [Nat.add_mul,Nat.one_mul] at hmul
  have hi := hl i
  have hj := ha j
  omega

theorem exists_nested (alphabet : Finset A) (z : Nat → A)
    (hz : ∀ i, z i ∈ alphabet) (k s : Nat) :
    ∃ a L, s ≤ a ∧ a+L ≤ s+bound alphabet k ∧ Nest z a L k := by
  classical
  induction k generalizing s with
  | zero => exact ⟨s,1,le_rfl,le_rfl,Nat.zero_lt_one⟩
  | succ k ih =>
    let B := bound alphabet k
    let C := (P0BoundedWords.words alphabet B).card
    have hall : ∀ i : Nat, ∃ a L, s+i*(B+1) ≤ a ∧
        a+L ≤ s+i*(B+1)+B ∧ Nest z a L k := fun i => ih (s+i*(B+1))
    choose a l ha hl hn using hall
    let profile := fun i => segment z (a i) (l i)
    have hm : ∀ i ∈ Finset.range (C+1), profile i ∈ P0BoundedWords.words alphabet B := by
      intro i _
      apply (P0BoundedWords.mem_words alphabet B (profile i)).mpr
      refine ⟨?_,segment_letters z alphabet hz (a i) (l i)⟩
      change (segment z (a i) (l i)).length ≤ B
      rw [segment_length]
      have h1 := ha i
      have h2 := hl i
      omega
    obtain ⟨i,hi,j,hj,hne,he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (show (P0BoundedWords.words alphabet B).card < (Finset.range (C+1)).card by
        rw [Finset.card_range]; dsimp [C]; omega) hm
    have hpair : ∃ i j, i < j ∧ j < C+1 ∧ profile i = profile j := by
      rcases lt_or_gt_of_ne hne with hij | hji
      · exact ⟨i,j,hij,Finset.mem_range.mp hj,he⟩
      · exact ⟨j,i,hji,Finset.mem_range.mp hi,he.symm⟩
    obtain ⟨i,j,hij,hj,he⟩ := hpair
    have hlen : l i = l j := by simpa only [profile,segment_length] using congrArg List.length he
    have hmatch : Match z (a i) (a j) (l i) := by
      apply segment_match
      simpa only [profile,hlen] using he
    have hsep := separated s B a l ha hl i j hij
    let d := a j-a i
    have hd : l i < d := by dsimp [d]; omega
    have had : a i+d = a j := by dsimp [d]; omega
    refine ⟨a i,d+l i,?_,?_,l i,d,hd,rfl,hn i,?_⟩
    · have := ha i
      omega
    · have hjmul := Nat.mul_le_mul_right (B+1) (show j+1 ≤ C+1 by omega)
      rw [Nat.add_mul,Nat.one_mul] at hjmul
      have hjend := hl j
      change a i+(d+l i) ≤ s+(C+1)*(B+1)
      omega
    · rwa [had]

end NSSE.P0NestedSelection
