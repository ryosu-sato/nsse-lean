import NSSE.TaggedCompiler

/-!
# Executable enumeration of bounded words

For a finite alphabet, words of each exact length and all words up to a
fixed bound are finite executable lists.  These lists supply the bounded
base-case IDs of the final compiler.
-/

namespace NSSE

universe u

def wordsOfLength (alphabet : Enumeration α) : Nat → List (Word α)
  | 0 => [[]]
  | n + 1 =>
      alphabet.values.flatMap fun letter =>
        (wordsOfLength alphabet n).map (letter :: ·)

theorem mem_wordsOfLength_iff
    (alphabet : Enumeration α) :
    ∀ (n : Nat) (word : Word α),
      word ∈ wordsOfLength alphabet n ↔ word.length = n := by
  intro n
  induction n with
  | zero =>
      intro word
      simp [wordsOfLength]
  | succ n ih =>
      intro word
      constructor
      · intro hmem
        simp only [wordsOfLength, List.mem_flatMap,
          List.mem_map] at hmem
        obtain ⟨letter, halphabet, tail, htail, rfl⟩ := hmem
        simp only [List.length_cons]
        rw [(ih tail).1 htail]
      · intro hlength
        cases word with
        | nil => simp at hlength
        | cons letter tail =>
            have htail : tail.length = n := by
              simp only [List.length_cons] at hlength
              omega
            simp only [wordsOfLength, List.mem_flatMap, List.mem_map]
            exact ⟨letter, alphabet.complete letter,
              tail, (ih tail).2 htail, rfl⟩

def wordsUpTo (alphabet : Enumeration α) (bound : Nat) :
    List (Word α) :=
  (List.range (bound + 1)).flatMap (wordsOfLength alphabet)

theorem mem_wordsUpTo_iff
    (alphabet : Enumeration α) (bound : Nat) (word : Word α) :
    word ∈ wordsUpTo alphabet bound ↔ word.length ≤ bound := by
  simp only [wordsUpTo, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨length, hlengthBound, hword⟩
    have hlength := (mem_wordsOfLength_iff alphabet length word).1 hword
    omega
  · intro hbound
    exact ⟨word.length, by omega,
      (mem_wordsOfLength_iff alphabet word.length word).2 rfl⟩

structure BoundedWord (α : Type u) (bound : Nat) where
  word : Word α
  length_le : word.length ≤ bound
deriving DecidableEq

def boundedWordEnumeration
    (alphabet : Enumeration α) (bound : Nat) :
    Enumeration (BoundedWord α bound) where
  values :=
    (wordsUpTo alphabet bound).attach.map fun word =>
      {
        word := word.1
        length_le :=
          (mem_wordsUpTo_iff alphabet bound word.1).1 word.2
      }
  complete := by
    intro bounded
    simp only [List.mem_map]
    let member :
        { word // word ∈ wordsUpTo alphabet bound } :=
      ⟨bounded.word,
        (mem_wordsUpTo_iff alphabet bound bounded.word).2
          bounded.length_le⟩
    refine ⟨member, ?_, ?_⟩
    · exact List.mem_attach _ _
    cases bounded
    rfl

end NSSE
