import NSSE.P0MarkerReader
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

/-! Exact regular-filter reduction to a concrete typed D-dead reader.
This is the reader-level half of x749 Lemma 1. Realizing the reader as an
original finite constraint input and proving its short-witness bound remain
separate formalization obligations. -/
namespace NSSE.P0RegularMarkerReduction
open P0ProperMachine P0ProperWords P0RegularProduct P0MarkerComparison P0DDeadReader
variable {Q S A H : Type*}

def target [DecidableEq Q] [DecidableEq S] (M : Machine Q A H)
    (vd : DecidablePred M.valid) (F : DFA A S) (fd : DecidablePred F.accept) :
    Reader (Q × S) (Option A) (H ⊕ Bool) :=
  P0MarkerReader.compile (erasedProduct M F) (fun q => vd q.1)
    (fun q => q.2 ∈ F.accept) (fun q => fd q.2)

def targetBirthDecision [DecidableEq Q] [DecidableEq S] (M : Machine Q A H)
    (vd : DecidablePred M.valid) (bd : DecidableRel M.birth)
    (F : DFA A S) (fd : DecidablePred F.accept) : DecidableRel (target M vd F fd).birth := by
  letI := bd
  intro q t
  cases q <;> cases t <;>
    dsimp [target,P0MarkerReader.compile,erasedProduct,product,eraseEqual] <;> infer_instance

theorem accepted_iff [DecidableEq Q] [DecidableEq S] (M : Machine Q A H)
    (vd : DecidablePred M.valid) (F : DFA A S) (fd : DecidablePred F.accept) (v : List (Option A)) :
    Accepted (target M vd F fd) v ↔ ∃ w, v = marked w ∧ GoodWord M w ∧ w ∈ F.accepts := by
  unfold target
  rw [P0MarkerReader.accepted_iff]
  simp_rw [goodWord_erasedProduct,final_filter]

theorem exists_iff [DecidableEq Q] [DecidableEq S] (M : Machine Q A H)
    (vd : DecidablePred M.valid) (F : DFA A S) (fd : DecidablePred F.accept) :
    (∃ v, Accepted (target M vd F fd) v) ↔ ∃ w, GoodWord M w ∧ w ∈ F.accepts := by
  simp_rw [accepted_iff]
  constructor
  · rintro ⟨v,w,_,h⟩
    exact ⟨w,h⟩
  · rintro ⟨w,h⟩
    exact ⟨marked w,w,rfl,h⟩

theorem bounded_exists_iff [DecidableEq Q] [DecidableEq S] (M : Machine Q A H)
    (vd : DecidablePred M.valid) (F : DFA A S) (fd : DecidablePred F.accept) (L : Nat) :
    (∃ v, Accepted (target M vd F fd) v ∧ v.length ≤ L) ↔
      ∃ w, GoodWord M w ∧ w ∈ F.accepts ∧ w.length+1 ≤ L := by
  constructor
  · rintro ⟨v,h,hL⟩
    obtain ⟨w,rfl,hg,hf⟩ := (accepted_iff M vd F fd v).mp h
    exact ⟨w,hg,hf,by simpa using hL⟩
  · rintro ⟨w,hg,hf,hL⟩
    exact ⟨marked w,(accepted_iff M vd F fd _).mpr ⟨w,rfl,hg,hf⟩,by simpa using hL⟩

theorem target_heads_distinct [DecidableEq Q] [DecidableEq S] (M : Machine Q A H)
    (vd : DecidablePred M.valid) (F : DFA A S) (fd : DecidablePred F.accept) :
    (target M vd F fd).endX ≠ (target M vd F fd).endY := by
  intro h
  cases h

theorem no_terminal_births [DecidableEq Q] [DecidableEq S] (M : Machine Q A H)
    (vd : DecidablePred M.valid) (F : DFA A S) (fd : DecidablePred F.accept) (q : Option (Q × S)) :
    ¬ (target M vd F fd).birth none q ∧ ¬ (target M vd F fd).birth q none := by
  cases q <;> exact ⟨id,id⟩

theorem erases_old_equal [DecidableEq Q] [DecidableEq S] (M : Machine Q A H)
    (vd : DecidablePred M.valid) (F : DFA A S) (fd : DecidablePred F.accept) (q : Q) (s t : S) :
    ¬ (target M vd F fd).birth (some (q,s)) (some (q,t)) := by
  intro h
  exact h.1.2 rfl

theorem card_target_states [Fintype Q] [Fintype S] :
    Fintype.card (Option (Q × S)) = Fintype.card Q * Fintype.card S + 1 := by
  simp

theorem card_target_alphabet [Fintype A] : Fintype.card (Option A) = Fintype.card A + 1 := by
  simp

end NSSE.P0RegularMarkerReduction
