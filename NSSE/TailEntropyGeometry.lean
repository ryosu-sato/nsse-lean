import NSSE.BoundedPeriodAutomaton
import Lean.Elab.Tactic.Omega

/-!
# Word geometry for the Tail Entropy Theorem

These lemmas formalize the determinacy assertions used in the two cases of
`proofs_en.md`, Theorem 6.1.
-/

namespace NSSE

universe u

/-- For a fixed anchor and short positive period whose first block lies in
the common base, a completion is unique. This is the precise injectivity
fact behind the manuscript's `(j,p)` count. -/
theorem shortPeriod_completion_unique
    (base first second : Word α)
    (j p : Nat)
    (hp : 0 < p)
    (hj : j ≤ base.length)
    (hjpend : j + p ≤ base.length)
    (hlength : first.length = second.length)
    (hfirst :
      Word.HasPeriod ((base ++ first).drop j) p)
    (hsecond :
      Word.HasPeriod ((base ++ second).drop j) p) :
    first = second := by
  let x := (base ++ first).drop j
  let y := (base ++ second).drop j
  have hxyLength : x.length = y.length := by
    dsimp [x, y]
    simp [hlength]
  have hroot : x.take p = y.take p := by
    dsimp [x, y]
    rw [List.drop_append_of_le_length hj,
      List.drop_append_of_le_length hj]
    have hpdrop : p ≤ (base.drop j).length := by
      simp
      omega
    simp [List.take_append_of_le_length hpdrop]
  have hxy : x = y :=
    Word.eq_of_hasPeriod_of_length_eq_of_take_eq
      p hp x y hfirst hsecond hxyLength hroot
  have hwhole :
      base ++ first = base ++ second := by
    calc
      base ++ first =
          (base ++ first).take j ++ x := by
        dsimp [x]
        exact (List.take_append_drop j (base ++ first)).symm
      _ = base.take j ++ x := by
        rw [List.take_append_of_le_length hj]
      _ = base.take j ++ y := by rw [hxy]
      _ = (base ++ second).take j ++ y := by
        rw [List.take_append_of_le_length hj]
      _ = base ++ second := by
        dsimp [y]
        exact List.take_append_drop j (base ++ second)
  exact List.append_cancel_left hwhole

/-- The arithmetic hypotheses of the short-period case put the first
period block wholly inside the fixed base. -/
theorem shortPeriod_root_inside_prefix
    (prefixLength completionLength j p e : Nat)
    (hcompletion : completionLength = c + 1)
    (hwLength : j + p + e = prefixLength + completionLength)
    (he : c < e) :
    j + p ≤ prefixLength := by
  omega

/-- In the long-period case, the copied source ends inside the fixed
base. This is the endpoint bound behind the manuscript's linear count. -/
theorem longPeriod_source_ends_in_prefix
    (prefixLength completionLength j p e : Nat)
    (hcompletion : completionLength = c + 1)
    (hwLength : j + p + e = prefixLength + completionLength)
    (hp : c + 1 ≤ p) :
    j + e ≤ prefixLength := by
  omega

/-- If a copied suffix is at least as long as the completion and its source
ends inside the fixed base, the completion is exactly the final
`completion.length` letters of that source. -/
theorem completion_eq_source_factor
    (base completion : Word α)
    (j p e : Nat)
    (he : completion.length ≤ e)
    (hend : j + e ≤ base.length)
    (hcopy :
      Word.WitnessCopy (base ++ completion) j p e) :
    completion =
      Word.factor base (j + e - completion.length)
        completion.length := by
  let w := base ++ completion
  have hew : e ≤ w.length := by
    dsimp [w]
    simp
    omega
  have hfactorLength :
      (Word.factor w j e).length = e := by
    rw [Word.factor_length, Nat.min_eq_left]
    dsimp [w]
    simp
    omega
  have hsuffixFactor :
      Word.suffix (Word.factor w j e) completion.length =
        Word.factor w (j + e - completion.length)
          completion.length := by
    calc
      Word.suffix (Word.factor w j e) completion.length =
          Word.factor (Word.factor w j e)
            (e - completion.length) completion.length := by
        unfold Word.suffix
        rw [hfactorLength]
        unfold Word.factor
        apply (List.take_of_length_le ?_).symm
        simp
        omega
      _ = Word.factor w (j + (e - completion.length))
          (min completion.length
            (e - (e - completion.length))) :=
        Word.factor_factor w j e
          (e - completion.length) completion.length
      _ = Word.factor w (j + e - completion.length)
          completion.length := by
        have hsub : e - (e - completion.length) =
            completion.length := by omega
        rw [hsub, Nat.min_self]
        congr 1
        omega
  have hsuffixNested :
      Word.suffix (Word.suffix w e) completion.length =
        completion := by
    unfold Word.suffix
    have hsuffixLength : (w.drop (w.length - e)).length = e := by
      simp
      omega
    rw [hsuffixLength, List.drop_drop]
    have hoffset :
        w.length - e + (e - completion.length) =
          base.length := by
      dsimp [w]
      simp
      omega
    rw [hoffset]
    dsimp [w]
    simp
  have hs := congrArg
    (fun z => Word.suffix z completion.length) hcopy
  change
    Word.suffix (Word.factor w j e) completion.length =
      Word.suffix (Word.suffix w e) completion.length at hs
  rw [hsuffixFactor, hsuffixNested] at hs
  symm
  calc
    Word.factor base (j + e - completion.length)
        completion.length =
        Word.factor w (j + e - completion.length)
          completion.length := by
      dsimp [w]
      unfold Word.factor
      have hstart :
          j + e - completion.length ≤ base.length := by omega
      rw [List.drop_append_of_le_length hstart]
      have htake :
          completion.length ≤
            (base.drop (j + e - completion.length)).length := by
        simp
        omega
      rw [List.take_append_of_le_length htake]
    _ = completion := hs

/-- Long-period completions with the same source endpoint are equal. -/
theorem longPeriod_completion_unique
    (base first second : Word α)
    (j₁ p₁ e₁ j₂ p₂ e₂ : Nat)
    (hlength : first.length = second.length)
    (he₁ : first.length ≤ e₁)
    (he₂ : second.length ≤ e₂)
    (hend₁ : j₁ + e₁ ≤ base.length)
    (hend₂ : j₂ + e₂ ≤ base.length)
    (hsameEnd : j₁ + e₁ = j₂ + e₂)
    (hcopy₁ :
      Word.WitnessCopy (base ++ first) j₁ p₁ e₁)
    (hcopy₂ :
      Word.WitnessCopy (base ++ second) j₂ p₂ e₂) :
    first = second := by
  have hfirst :=
    completion_eq_source_factor base first
      j₁ p₁ e₁ he₁ hend₁ hcopy₁
  have hsecond :=
    completion_eq_source_factor base second
      j₂ p₂ e₂ he₂ hend₂ hcopy₂
  rw [hfirst, hsecond, hlength, hsameEnd]

end NSSE
