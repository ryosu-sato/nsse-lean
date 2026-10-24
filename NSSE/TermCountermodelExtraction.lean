import NSSE.TermEntailmentDecision
import NSSE.FiniteCountermodelExtraction
import NSSE.RegularCountermodelExtraction

/-! # Total ORIGINAL term-input countermodel extraction

The certified flat programs are run on the computed flattening. Output
valuations/root pointers are restricted to the original input variables.
The failed inequality and unsafe word concern the actual evaluated TERMS.
-/

namespace NSSE.TermCountermodelExtraction

open SubtypeTerms SubtypeTermLayout SubtypeTermFlattening TermEntailmentDecision

variable {n d : Nat}

def extractFinite (Q : Query n d) (hd : 0 < d) : Option (FiniteCountermodelExtraction.Countermodel n d) :=
  (FiniteCountermodelExtraction.extract (flat Q hd) hd).map
    (fun c => ⟨c.side,c.word,(layout Q).restrict c.valuation⟩)

theorem extractFinite_none_iff (Q : Query n d) (hd : 0 < d) :
    extractFinite Q hd = none ↔ Entails (FiniteSubtypeTrees.constructor d) Q := by
  rw [extractFinite, Option.map_eq_none_iff, FiniteCountermodelExtraction.extract_none_iff]
  exact entails_iff (FiniteSubtypeTrees.constructor d) Q ⟨0,hd⟩

theorem extractFinite_correct (Q : Query n d) (hd : 0 < d)
    (c : FiniteCountermodelExtraction.Countermodel n d) (h : extractFinite Q hd = some c) :
    Satisfies (FiniteSubtypeTrees.constructor d) Q c.valuation ∧
      ¬ eval (FiniteSubtypeTrees.constructor d) c.valuation Q.left ≤
        eval (FiniteSubtypeTrees.constructor d) c.valuation Q.right ∧
      ¬ FiniteSubtypeSafety.Safe c.side (eval (FiniteSubtypeTrees.constructor d) c.valuation Q.left)
        (eval (FiniteSubtypeTrees.constructor d) c.valuation Q.right) c.word := by
  obtain ⟨fc,hf,rfl⟩ := Option.map_eq_some'.mp h
  obtain ⟨hφ,hu,hbad,_,_⟩ := FiniteCountermodelExtraction.extract_correct (flat Q hd) hd fc hf
  obtain ⟨ho,hl,hr⟩ := restriction_spec (FiniteSubtypeTrees.constructor d) Q ⟨0,hd⟩ fc.valuation hφ
  refine ⟨ho,?_,?_⟩
  · change ¬ eval (FiniteSubtypeTrees.constructor d) ((layout Q).restrict fc.valuation) Q.left ≤
      eval (FiniteSubtypeTrees.constructor d) ((layout Q).restrict fc.valuation) Q.right
    rw [hl,hr]
    exact hbad
  · change ¬ FiniteSubtypeSafety.Safe fc.side
      (eval (FiniteSubtypeTrees.constructor d) ((layout Q).restrict fc.valuation) Q.left)
      (eval (FiniteSubtypeTrees.constructor d) ((layout Q).restrict fc.valuation) Q.right) fc.word
    rw [hl,hr]
    exact hu

theorem extractFinite_height_bound (Q : Query n d) (hd : 0 < d)
    (c : FiniteCountermodelExtraction.Countermodel n d) (h : extractFinite Q hd = some c) (x : Fin n) :
    FiniteSubtypeTrees.height (c.valuation x) ≤ FiniteCountermodelExtraction.heightBound (flat Q hd) hd := by
  obtain ⟨fc,hf,rfl⟩ := Option.map_eq_some'.mp h
  exact FiniteCountermodelExtraction.extract_height_bound (flat Q hd) hd fc hf ((layout Q).old x)

theorem extractFinite_exists_iff_false (Q : Query n d) (hd : 0 < d) :
    (∃ c, extractFinite Q hd = some c) ↔ decideFinite Q hd = false := by
  rw [← Option.isSome_iff_exists, Option.isSome_iff_ne_none]
  change (¬ extractFinite Q hd = none) ↔ decideFinite Q hd = false
  rw [extractFinite_none_iff, ← decideFinite_correct Q hd]
  cases decideFinite Q hd <;> simp

structure GraphCountermodel (n d : Nat) where
  size : Nat
  side : ForwardTableAutomaton.Side
  word : List (Fin d)
  graph : RegularSubtypeTrees.Graph (Finset (Fin size)) d
  roots : Fin n → Finset (Fin size)

def GraphCountermodel.valuation (c : GraphCountermodel n d) (x : Fin n) : AbsorbingSubtypeTrees.Tree d :=
  c.graph.tree (c.roots x)

theorem GraphCountermodel.regular (c : GraphCountermodel n d) (x : Fin n) :
    RegularSubtypeTrees.Regular (c.valuation x) := c.graph.regular (c.roots x)

def extractRegular (Q : Query n d) (hd : 0 < d) : Option (GraphCountermodel n d) :=
  (RegularCountermodelExtraction.extract (flat Q hd) hd).map
    (fun c => ⟨(layout Q).count + FiniteUnsafetyCompiler.extra c.word,c.side,c.word,c.graph,
      fun x => c.roots ((layout Q).old x)⟩)

theorem extractRegular_none_iff_all (Q : Query n d) (hd : 0 < d) :
    extractRegular Q hd = none ↔ Entails (AbsorbingSubtypeTrees.constructor d) Q := by
  rw [extractRegular, Option.map_eq_none_iff, RegularCountermodelExtraction.extract_none_iff]
  exact entails_iff (AbsorbingSubtypeTrees.constructor d) Q ⟨0,hd⟩

theorem extractRegular_none_iff (Q : Query n d) (hd : 0 < d) :
    extractRegular Q hd = none ↔ SubtypeTermSemantics.RegularEntails Q :=
  (extractRegular_none_iff_all Q hd).trans (regular_entails_iff_all Q hd).symm

theorem extractRegular_correct (Q : Query n d) (hd : 0 < d)
    (c : GraphCountermodel n d) (h : extractRegular Q hd = some c) :
    (∀ x, RegularSubtypeTrees.Regular (c.valuation x)) ∧
      Satisfies (AbsorbingSubtypeTrees.constructor d) Q c.valuation ∧
      ¬ eval (AbsorbingSubtypeTrees.constructor d) c.valuation Q.left ≤
        eval (AbsorbingSubtypeTrees.constructor d) c.valuation Q.right ∧
      ¬ AbsorbingSubtypeSafety.Safe c.side (eval (AbsorbingSubtypeTrees.constructor d) c.valuation Q.left)
        (eval (AbsorbingSubtypeTrees.constructor d) c.valuation Q.right) c.word := by
  obtain ⟨fc,hf,rfl⟩ := Option.map_eq_some'.mp h
  obtain ⟨hreg,hφ,hu,hbad,_⟩ := RegularCountermodelExtraction.extract_correct (flat Q hd) hd fc hf
  obtain ⟨ho,hl,hr⟩ := restriction_spec (AbsorbingSubtypeTrees.constructor d) Q ⟨0,hd⟩ fc.valuation hφ
  refine ⟨fun x => hreg ((layout Q).old x),ho,?_,?_⟩
  · change ¬ eval (AbsorbingSubtypeTrees.constructor d) ((layout Q).restrict fc.valuation) Q.left ≤
      eval (AbsorbingSubtypeTrees.constructor d) ((layout Q).restrict fc.valuation) Q.right
    rw [hl,hr]
    exact hbad
  · change ¬ AbsorbingSubtypeSafety.Safe fc.side
      (eval (AbsorbingSubtypeTrees.constructor d) ((layout Q).restrict fc.valuation) Q.left)
      (eval (AbsorbingSubtypeTrees.constructor d) ((layout Q).restrict fc.valuation) Q.right) fc.word
    rw [hl,hr]
    exact hu

theorem extractRegular_state_bound (Q : Query n d) (hd : 0 < d)
    (c : GraphCountermodel n d) (h : extractRegular Q hd = some c) :
    Fintype.card (Finset (Fin c.size)) ≤ RegularCountermodelExtraction.stateBound (flat Q hd) hd := by
  obtain ⟨fc,hf,rfl⟩ := Option.map_eq_some'.mp h
  exact RegularCountermodelExtraction.extract_state_bound (flat Q hd) hd fc hf

theorem extractRegular_exists_iff_false (Q : Query n d) (hd : 0 < d) :
    (∃ c, extractRegular Q hd = some c) ↔ decideAll Q hd = false := by
  rw [← Option.isSome_iff_exists, Option.isSome_iff_ne_none]
  change (¬ extractRegular Q hd = none) ↔ decideAll Q hd = false
  rw [extractRegular_none_iff_all, ← decideAll_correct Q hd]
  cases decideAll Q hd <;> simp

end NSSE.TermCountermodelExtraction
