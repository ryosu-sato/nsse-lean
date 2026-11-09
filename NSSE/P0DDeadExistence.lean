import NSSE.P0ShortestWordBound
import NSSE.P0BoundedWords

/-! A total executable D-dead existence decision with no supplied bound
or shortening premise. The explicit bound is proved from actual cotrees.
This reader theorem is not yet the original multi-constructor decider. -/
namespace NSSE.P0DDeadExistence
open P0DDeadReader P0BoundedWords P0ShortestWordBound
variable {Q A H : Type*} [Fintype Q] [Fintype A]
variable [DecidableEq Q] [DecidableEq A] [DecidableEq H]

def witnessBound (Q : Type*) [Fintype Q] : Nat := P0ColorBound.bound (Fintype.card Q+1)-1

def decideExists (J : Reader Q A H) (bd : DecidableRel J.birth) : Bool :=
  search J bd Finset.univ (witnessBound Q)

theorem decideExists_correct (J : Reader Q A H) (bd : DecidableRel J.birth)
    (hends : J.endX ≠ J.endY) : decideExists J bd = true ↔ ∃ w, Accepted J w := by
  rw [decideExists,search_correct]
  constructor
  · rintro ⟨w,_,hw⟩
    exact ⟨w,hw⟩
  · intro hex
    obtain ⟨w,hw,hlen⟩ := exists_short J hends hex
    exact ⟨w,⟨hlen,fun a _ => Finset.mem_univ a⟩,hw⟩

def existenceDecision (J : Reader Q A H) (bd : DecidableRel J.birth)
    (hends : J.endX ≠ J.endY) : Decidable (∃ w, Accepted J w) :=
  decidable_of_iff (decideExists J bd = true) (decideExists_correct J bd hends)

theorem decideExists_false (J : Reader Q A H) (bd : DecidableRel J.birth)
    (hends : J.endX ≠ J.endY) : decideExists J bd = false ↔ ∀ w, ¬ Accepted J w := by
  rw [← Bool.not_eq_true,decideExists_correct J bd hends,not_exists]

end NSSE.P0DDeadExistence
