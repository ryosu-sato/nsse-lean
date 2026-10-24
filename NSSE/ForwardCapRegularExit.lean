import NSSE.ForwardCapAutomaton

/-! # A strict-cap forward automaton leaves its regular core in one letter

The core is the prefix-closed ordinary language plus prefixes of complete
anchor/root paths. It is the semantic regular core used by the finite cap
normalization; the theorem needs only StrictCap, not gap universality.
-/

namespace NSSE.ForwardCapAutomaton

open GuardedBlockRelation

variable {α : Type}

def RootPrefixCore (A : Input α) (xs : List α) : Prop :=
  ∃ q : Fin A.count, A.final q ∧
    Language.prefixClosure
      (Language.concat (anchorLanguage A q) (rootLanguage A q)) xs

def ForwardRegularCore (A : Input α) (xs : List α) : Prop :=
  PrefixCore A xs ∨ RootPrefixCore A xs

theorem rootPrefixCore_not_after_final_free (A : Input α)
    (hstrict : StrictCap A) (pref : List α) (letter : α)
    (hfree : ¬ ∃ r, (ordinary A).Runs A.start pref r ∧ A.final r) :
    ¬ RootPrefixCore A (pref ++ [letter]) := by
  rintro ⟨q, _, tail, hcat⟩
  obtain ⟨anchor, root, he, ha, source, hr, hp⟩ := hcat
  have hfull : (ordinary A).Runs A.start ((pref ++ [letter]) ++ tail) source := by
    rw [he]
    exact ha.append (ordinary A) hr
  have hsplit : (ordinary A).Runs A.start (pref ++ (letter :: tail)) source := by
    simpa only [List.append_assoc, List.singleton_append] using hfull
  obtain ⟨mid, hpre, hpost⟩ :=
    (runs_append_iff (ordinary A) A.start source pref (letter :: tail)).mp hsplit
  exact hfree ⟨mid, hpre, hstrict mid source q (letter :: tail)
    (by simp) hpost hp⟩

theorem forwardRegularCore_not_after_final_free (A : Input α)
    (hstrict : StrictCap A) (pref : List α) (letter : α)
    (hfree : ¬ ∃ r, (ordinary A).Runs A.start pref r ∧ A.final r) :
    ¬ ForwardRegularCore A (pref ++ [letter]) := by
  rintro (hk | hr)
  · have hp : pref <+: pref ++ [letter] := ⟨[letter], rfl⟩
    obtain ⟨r, hrun, hf⟩ := (ordinary_accepts A pref).mp (hk pref hp)
    exact hfree ⟨r, hrun, hf⟩
  · exact rootPrefixCore_not_after_final_free A hstrict pref letter hfree hr

end NSSE.ForwardCapAutomaton
