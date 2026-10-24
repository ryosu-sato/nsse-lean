import NSSE.CommonCutPairPreservation

/-! # Simultaneous small tuples from concrete finite summaries

The polynomial cut bound (q*q+1) replaces the sharper paper trie bound.
No supplied partition, shortener, or preservation interface is an input.
-/

namespace NSSE.CommonCutSmallTuple

open GuardedBlockRelation CombinedSuffixSummary CommonCutRefinement
open CommonCutWordReplacement CommonCutPairPreservation

universe u
variable {D : Type u} {k b q : Nat} (ns : Fin k → Nat)

noncomputable def shorten (G : (i : Fin k) → Data D (Fin (ns i)))
    (separators : Fin b → D) (w : List D) : List D := by
  classical
  exact if hw : w = [] then [] else
    Classical.choose (exists_short_same_summary ns G separators w hw)

theorem shorten_spec (G : (i : Fin k) → Data D (Fin (ns i)))
    (separators : Fin b → D) (w : List D) :
    (shorten ns G separators w).head? = w.head? ∧
      (shorten ns G separators w).length ≤ 2 ^ exponent (b := b) ns ∧
      (automaton ns G separators).eval (shorten ns G separators w) =
        (automaton ns G separators).eval w := by
  classical
  unfold shorten
  split_ifs with hw
  · subst w
    exact ⟨rfl, Nat.zero_le _, rfl⟩
  · have h := Classical.choose_spec (exists_short_same_summary ns G separators w hw)
    exact ⟨h.1, h.2.2.1, h.2.2.2⟩

/-- Every finite tuple has a bounded replacement preserving its equality,
all core relations, all reverse-data paths, and all supplied noA tests. -/
theorem exists_small_tuple (G : (i : Fin k) → Data D (Fin (ns i)))
    (separators : Fin b → D) (w : Fin q → List D) :
    ∃ v : Fin q → List D,
      (∀ i, (v i).length ≤ (q*q+1) * 2 ^ exponent (b := b) ns) ∧
      (∀ i j, v i = v j ↔ w i = w j) ∧
      (∀ a i j p, (G a).core p (v i) (v j) ↔ (G a).core p (w i) (w j)) ∧
      (∀ a i p r, (G a).T.Runs p (v i).reverse r ↔ (G a).T.Runs p (w i).reverse r) ∧
      (∀ j i, separators j ∉ v i ↔ separators j ∉ w i) := by
  classical
  let F := shorten ns G separators
  let gs := build (requests w)
  have hh : ∀ x, (F x).head? = x.head? := fun x => (shorten_spec ns G separators x).1
  have hl : ∀ x, (F x).length ≤ 2 ^ exponent (b := b) ns :=
    fun x => (shorten_spec ns G separators x).2.1
  have hm : ∀ x, (automaton ns G separators).eval (F x) = (automaton ns G separators).eval x :=
    fun x => (shorten_spec ns G separators x).2.2
  have hd : ∀ a x p r, (G a).T.Runs p (F x).reverse r ↔ (G a).T.Runs p x.reverse r := by
    intro a x p r
    exact same_summary_data ns G separators (F x) x (hm x) a p r
  have ht : ∀ a x p r,
      (G a).automaton.Runs p (SuffixTreeHReconstruction.diagonal (F x)) r ↔
        (G a).automaton.Runs p (SuffixTreeHReconstruction.diagonal x) r := by
    intro a x p r
    exact same_summary_diagonal ns G separators (F x) x (hm x) a p r
  have hn : ∀ j x, separators j ∉ F x ↔ separators j ∉ x := by
    intro j x
    exact same_summary_absent ns G separators (F x) x (hm x) j
  refine ⟨fun i => replace F gs (w i), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [gs, build_length, requests_length] using replace_length F _ hl gs (w i)
  · intro i j
    exact equality_replace F hh gs (w i) (w j) (pair_cut w i j)
  · intro a i j p
    exact core_replace (G a) F hh (hd a) (ht a) gs (w i) (w j) (pair_cut w i j) p
  · intro a i p r
    exact replace_reverse_runs (G a).T F (hd a) gs (w i) p r
  · intro j i
    exact replace_absent F (separators j) (hn j) gs (w i)

/-- The small-tuple theorem on the original (not reversed) block words
and the actual LiteralH relations of a finite family of symbolic rows. -/
theorem exists_small_literal_tuple
    {L : FirstOrder.Language} {P : Type*} [L.Structure D]
    (rows : (a : Fin k) → SymbolicGuardedBlocks.Row L P (ns a))
    (ends : (a : Fin k) → SymbolicGuardedBlocks.Ends (ns a))
    (seed last : P) (first : Fin k → Bool) (valuation : P → D)
    (separators : Fin b → D) (w : Fin q → List D) :
    ∃ v : Fin q → List D,
      (∀ i, (v i).length ≤ (q*q+1) * 2 ^ exponent (b := b) ns) ∧
      (∀ i j, v i = v j ↔ w i = w j) ∧
      (∀ a i j, (rows a).LiteralH (ends a) seed last (first a) valuation (v i) (v j) ↔
        (rows a).LiteralH (ends a) seed last (first a) valuation (w i) (w j)) ∧
      (∀ a i s t, ((rows a).dataNFA valuation).Runs s (v i) t ↔
        ((rows a).dataNFA valuation).Runs s (w i) t) ∧
      (∀ j i, separators j ∉ v i ↔ separators j ∉ w i) := by
  let G : (a : Fin k) → Data D (Fin (ns a)) :=
    fun a => (rows a).semantics (ends a) seed last (first a) valuation
  obtain ⟨v, hl, he, hc, hd, hn⟩ :=
    exists_small_tuple ns G separators (fun i => (w i).reverse)
  refine ⟨fun i => (v i).reverse, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [List.length_reverse] using hl i
  · intro i j
    simpa only [List.reverse_inj] using he i j
  · intro a i j
    rw [← (rows a).H_iff_literal, ← (rows a).H_iff_literal,
      (rows a).H_iff_core, (rows a).H_iff_core]
    simp only [List.reverse_reverse]
    apply exists_congr
    intro p
    exact and_congr_right (fun _ => hc a i j p)
  · intro a i s t
    simpa only [List.reverse_reverse] using hd a i s t
  · intro j i
    simpa only [List.mem_reverse] using hn j i

end NSSE.CommonCutSmallTuple
