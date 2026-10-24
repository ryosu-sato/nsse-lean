import NSSE.HornSOACompiler
import NSSE.BoundedAvoiderAtom
import NSSE.BoundedWordEnumeration

/-!
# The certified decider from a single proposition: the short-avoider bound

This module compresses the remaining gap of the entire compiler
development into one named proposition.

`ShortAvoiderBound I bound` states that if the SOA instance `I` has an
avoider at all, it has one of length at most `bound`.  Given

* a complete alphabet enumeration,
* an exact avoider test (decidability of `I.Avoider` on single words), and
* a concrete `bound` together with `ShortAvoiderBound I bound`,

we construct a `HornSOARootCertificate I` — hence, via the existing Horn
kernel, a `CertifiedSOACompiler I` and a correct executable decider —
with a ONE-STATE, ZERO-RULE Horn compiler whose terminal test is bounded
exhaustive search.

Two consequences are made explicit:

1. Everything in the surrounding development that is conditional on
   `root_correct` (or on completeness of a compiled rule system) is
   subsumed by this construction: the sole remaining mathematical
   content is producing the NUMBER `bound`.
2. The bare existence `∃ bound, ShortAvoiderBound I bound` is
   (classically) trivial — see `exists_shortAvoiderBound` — so the open
   problem is precisely the UNIFORM/computable production of `bound`
   from the instance data, not the existence of a bound.  No
   construction in this repository currently provides it; providing it
   is equivalent to the ledger wall (SOA decidability).

No `sorry`.
-/

namespace NSSE

universe u

/-- The short-avoider bound proposition: an avoider exists only if one
    of length at most `bound` exists. -/
def ShortAvoiderBound (I : SOAInstance α) (bound : Nat) : Prop :=
  (∃ word, I.Avoider word) →
    ∃ word, I.Avoider word ∧ word.length ≤ bound

/-- Classically, some bound always works (the length of any avoider),
    so the content of `ShortAvoiderBound` is entirely in producing the
    bound effectively, not in its existence. -/
theorem exists_shortAvoiderBound (I : SOAInstance α) :
    ∃ bound, ShortAvoiderBound I bound := by
  by_cases hexists : ∃ word, I.Avoider word
  · obtain ⟨word, hword⟩ := hexists
    exact ⟨word.length, fun _ => ⟨word, hword, Nat.le_refl _⟩⟩
  · exact ⟨0, fun hcontra => absurd hcontra hexists⟩

/-- Bounded exhaustive avoider search. -/
def boundedAvoiderSearch
    (I : SOAInstance α) (alphabet : Enumeration α)
    (avoidTest : ExactAvoiderTest I) (bound : Nat) : Bool :=
  (wordsUpTo alphabet bound).any avoidTest.test

theorem boundedAvoiderSearch_correct
    (I : SOAInstance α) (alphabet : Enumeration α)
    (avoidTest : ExactAvoiderTest I) (bound : Nat) :
    boundedAvoiderSearch I alphabet avoidTest bound = true ↔
      ∃ word, I.Avoider word ∧ word.length ≤ bound := by
  simp only [boundedAvoiderSearch, List.any_eq_true]
  constructor
  · rintro ⟨word, hmem, htest⟩
    exact ⟨word, (avoidTest.correct word).1 htest,
      (mem_wordsUpTo_iff alphabet bound word).1 hmem⟩
  · rintro ⟨word, havoider, hlength⟩
    exact ⟨word, (mem_wordsUpTo_iff alphabet bound word).2 hlength,
      (avoidTest.correct word).2 havoider⟩

/-- The one-state, zero-rule Horn compiler whose terminal test is the
    bounded search. -/
def shortBoundHornCompiler
    (I : SOAInstance α) (alphabet : Enumeration α)
    (avoidTest : ExactAvoiderTest I) (bound : Nat) :
    FiniteHornCompiler where
  stateCount := 1
  terminal := fun _ =>
    boundedAvoiderSearch I alphabet avoidTest bound
  rules := []

/-- **The compression theorem.**  A concrete short-avoider bound yields
    the root certificate — and hence, through the unmodified Horn
    kernel, the certified executable SOA decider. -/
def hornCertificateOfShortAvoiderBound
    (I : SOAInstance α) (alphabet : Enumeration α)
    (avoidTest : ExactAvoiderTest I) (bound : Nat)
    (hbound : ShortAvoiderBound I bound) :
    HornSOARootCertificate I where
  compiler := shortBoundHornCompiler I alphabet avoidTest bound
  root := 0
  root_lt := Nat.zero_lt_one
  root_correct := by
    constructor
    · intro hderives
      have hgen :
          ∀ state,
            HornDerives
              (shortBoundHornCompiler I alphabet avoidTest bound)
              state →
            ∃ word, I.Avoider word := by
        intro state hstate
        induction hstate with
        | terminal _ hterminal =>
            obtain ⟨word, havoider, _⟩ :=
              (boundedAvoiderSearch_correct
                I alphabet avoidTest bound).1 hterminal
            exact ⟨word, havoider⟩
        | rule hmem _ _ =>
            exact absurd hmem (List.not_mem_nil)
      exact hgen 0 hderives
    · intro hexists
      obtain ⟨word, havoider, hlength⟩ := hbound hexists
      exact HornDerives.terminal Nat.zero_lt_one
        ((boundedAvoiderSearch_correct
          I alphabet avoidTest bound).2 ⟨word, havoider, hlength⟩)

/-- The certified compiler, and the correctness of its executable
    decision, follow with no further hypotheses. -/
def certifiedCompilerOfShortAvoiderBound
    (I : SOAInstance α) (alphabet : Enumeration α)
    (avoidTest : ExactAvoiderTest I) (bound : Nat)
    (hbound : ShortAvoiderBound I bound) :
    CertifiedSOACompiler I :=
  (hornCertificateOfShortAvoiderBound
    I alphabet avoidTest bound hbound).toCertifiedSOACompiler

theorem decide_of_shortAvoiderBound
    (I : SOAInstance α) (alphabet : Enumeration α)
    (avoidTest : ExactAvoiderTest I) (bound : Nat)
    (hbound : ShortAvoiderBound I bound) :
    (hornCertificateOfShortAvoiderBound
      I alphabet avoidTest bound hbound).decideAvoider = true ↔
      ∃ word, I.Avoider word :=
  (hornCertificateOfShortAvoiderBound
    I alphabet avoidTest bound hbound).decideAvoider_correct

/-- Conversely, any root certificate whose instance HAS an avoider
    recovers a short-avoider bound (with the trivial classical bound),
    so up to effectivity of the bound the certificate and the
    proposition carry the same content. -/
theorem shortAvoiderBound_of_certificate
    {I : SOAInstance α}
    (_certificate : HornSOARootCertificate I) :
    ∃ bound, ShortAvoiderBound I bound :=
  exists_shortAvoiderBound I

end NSSE
