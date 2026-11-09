import NSSE.P0RegularMarkerReduction
import NSSE.P0DDeadExistence

/-! Total existence decision for Good words under any supplied finite DFA
restriction. The actual fresh-marker reader and its proved length bound
are composed without a supplied regularity or short-witness premise. -/
namespace NSSE.P0RegularExistence
open P0ProperMachine P0ProperWords P0RegularMarkerReduction P0MarkerComparison
variable {Q S A H : Type*} [DecidableEq Q] [DecidableEq S] [DecidableEq A] [DecidableEq H]
variable [Fintype Q] [Fintype S]

def regularBound (Q S : Type*) [Fintype Q] [Fintype S] : Nat :=
  P0ColorBound.bound (Fintype.card Q * Fintype.card S + 1)-2

omit [DecidableEq A] [DecidableEq H] in
theorem exists_short (M : Machine Q A H) (vd : DecidablePred M.valid)
    (F : DFA A S) (fd : DecidablePred F.accept)
    (hex : ∃ w, GoodWord M w ∧ w ∈ F.accepts) :
    ∃ w, GoodWord M w ∧ w ∈ F.accepts ∧ w.length ≤ regularBound Q S := by
  have ht := (exists_iff M vd F fd).mpr hex
  obtain ⟨v,hv,hlen⟩ := P0ShortestWordBound.exists_short (target M vd F fd)
    (target_heads_distinct M vd F fd) ht
  obtain ⟨w,rfl,hw,hf⟩ := (accepted_iff M vd F fd v).mp hv
  refine ⟨w,hw,hf,?_⟩
  simp only [marked_length,Fintype.card_prod] at hlen
  unfold regularBound
  omega

omit [DecidableEq A] [DecidableEq H] in
theorem bounded_iff (M : Machine Q A H) (vd : DecidablePred M.valid)
    (F : DFA A S) (fd : DecidablePred F.accept) :
    (∃ w, GoodWord M w ∧ w ∈ F.accepts) ↔
      ∃ w, GoodWord M w ∧ w ∈ F.accepts ∧ w.length ≤ regularBound Q S :=
  ⟨exists_short M vd F fd,fun ⟨w,hg,hf,_⟩ => ⟨w,hg,hf⟩⟩

variable [Fintype A]

def decideExists (M : Machine Q A H) (vd : DecidablePred M.valid) (bd : DecidableRel M.birth)
    (F : DFA A S) (fd : DecidablePred F.accept) : Bool :=
  P0DDeadExistence.decideExists (target M vd F fd) (targetBirthDecision M vd bd F fd)

theorem decideExists_correct (M : Machine Q A H) (vd : DecidablePred M.valid)
    (bd : DecidableRel M.birth) (F : DFA A S) (fd : DecidablePred F.accept) :
    decideExists M vd bd F fd = true ↔ ∃ w, GoodWord M w ∧ w ∈ F.accepts :=
  (P0DDeadExistence.decideExists_correct (target M vd F fd)
    (targetBirthDecision M vd bd F fd) (target_heads_distinct M vd F fd)).trans
    (exists_iff M vd F fd)

def existenceDecision (M : Machine Q A H) (vd : DecidablePred M.valid)
    (bd : DecidableRel M.birth) (F : DFA A S) (fd : DecidablePred F.accept) :
    Decidable (∃ w, GoodWord M w ∧ w ∈ F.accepts) :=
  decidable_of_iff (decideExists M vd bd F fd = true) (decideExists_correct M vd bd F fd)

theorem decideExists_false (M : Machine Q A H) (vd : DecidablePred M.valid)
    (bd : DecidableRel M.birth) (F : DFA A S) (fd : DecidablePred F.accept) :
    decideExists M vd bd F fd = false ↔ ∀ w, ¬(GoodWord M w ∧ w ∈ F.accepts) := by
  rw [← Bool.not_eq_true,decideExists_correct,not_exists]

end NSSE.P0RegularExistence
