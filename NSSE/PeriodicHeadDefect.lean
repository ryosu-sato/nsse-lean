import NSSE.PeriodicReaderFirstExit

/-! A forced head defect after a genuinely periodic finite-reader trace is
short. A changed last child index does not satisfy this trace premise. -/
namespace NSSE.PeriodicHeadDefect
variable {S H I : Type*}

theorem bounded_equal_shift (next : S → S) (run : Nat → S) (n : Nat)
    (hstep : ∀ k, k < n → run (k+1) = next (run k))
    (a b d : Nat) (ha : a+d ≤ n) (hb : b+d ≤ n)
    (hab : run a = run b) : run (a+d) = run (b+d) := by
  induction d with
  | zero => simpa using hab
  | succ d ih =>
    have he := ih (by omega) (by omega)
    rw [show a+(d+1) = (a+d)+1 by omega,
        show b+(d+1) = (b+d)+1 by omega,
        hstep (a+d) (by omega),hstep (b+d) (by omega),he]

theorem bounded_first_exit [Fintype S] (next : S → S) (run : Nat → S)
    (stop : S → Prop) (n : Nat)
    (hstep : ∀ k, k < n → run (k+1) = next (run k))
    (hend : stop (run n)) (hfirst : ∀ k, k < n → ¬ stop (run k)) :
    n+1 ≤ Fintype.card S := by
  have exclude : ∀ i j, i < j → j ≤ n → run i = run j → False := by
    intro i j hij hj he
    have shifted := bounded_equal_shift next run n hstep i j (n-j)
      (by omega) (by omega) he
    have heq : j+(n-j) = n := by omega
    rw [heq] at shifted
    exact hfirst (i+(n-j)) (by omega) (shifted ▸ hend)
  have injective : Function.Injective (fun k : Fin (n+1) => run k.val) := by
    intro a b heq
    have ha := a.isLt
    have hb := b.isLt
    apply Fin.ext
    by_contra h
    rcases Nat.lt_or_gt_of_ne h with hlt | hgt
    · exact exclude a.val b.val hlt (by omega) heq
    · exact exclude b.val a.val hgt (by omega) heq.symm
  simpa using Fintype.card_le_of_injective (fun k : Fin (n+1) => run k.val) injective

def advance (p : Nat) (hp : 0 < p) (phase : Fin p) : Fin p :=
  ⟨(phase.val+1)%p,Nat.mod_lt _ hp⟩

/-- The head at the end is forced by the reader state. Both heads AND
indices of all strict preceding positions follow the given periodic word.
No hypothesis about states beyond the defect is required. -/
theorem reader_defect_bound [Fintype S] (next : S → I → S) (label : S → H)
    (p : Nat) (hp : 0 < p) (word : Fin p → H × I)
    (states : Nat → S) (phases : Nat → Fin p) (r : Nat)
    (hnext : ∀ d, d < r → states (d+1) = next (states d) (word (phases d)).2)
    (hphase : ∀ d, d < r → phases (d+1) = advance p hp (phases d))
    (hhead : ∀ d, d < r → label (states d) = (word (phases d)).1)
    (hend : label (states r) ≠ (word (phases r)).1) :
    r+1 ≤ Fintype.card S * p := by
  let step : S × Fin p → S × Fin p := fun s =>
    (next s.1 (word s.2).2,advance p hp s.2)
  let run : Nat → S × Fin p := fun d => (states d,phases d)
  let stop : S × Fin p → Prop := fun s => label s.1 ≠ (word s.2).1
  have hs : ∀ d, d < r → run (d+1) = step (run d) := by
    intro d hd
    exact Prod.ext (hnext d hd) (hphase d hd)
  have he : stop (run r) := hend
  have hf : ∀ d, d < r → ¬ stop (run d) := by
    intro d hd hn
    exact hn (hhead d hd)
  simpa using bounded_first_exit step run stop r hs he hf

/-- For an old-source mismatch at a sufficiently late row, its target
birth must already be periodic, and its entire propagation is short. -/
theorem late_defect_short (T K b r : Nat)
    (hlate : T+K < b+r)
    (hdefect : b+r-max b T+1 ≤ K) : T < b ∧ r < K := by
  omega

end NSSE.PeriodicHeadDefect
