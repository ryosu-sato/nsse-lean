import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Fintype.Basic

/-! Computable exhaustive signature dispatch: select a positive-arity
head when one exists, otherwise prove every head nullary. -/
namespace NSSE.MultiConstructorSignature
variable {H : Type*}

def HasPositive (arity : H → Nat) : Prop := ∃ h, 0 < arity h

instance positiveDecision [Fintype H] (arity : H → Nat) : Decidable (HasPositive arity) := by
  unfold HasPositive
  infer_instance

def select [Encodable H] (arity : H → Nat) (hp : HasPositive arity) : {h : H // 0 < arity h} :=
  @Encodable.chooseX H (fun h => 0 < arity h) inferInstance (fun _ => inferInstance) hp

def child [Encodable H] (arity : H → Nat) (hp : HasPositive arity) : Fin (arity (select arity hp).val) :=
  ⟨0,(select arity hp).property⟩

theorem zero_of_negative (arity : H → Nat) (hn : ¬HasPositive arity) : ∀ h, arity h = 0 :=
  fun h => Nat.eq_zero_of_not_pos (fun hp => hn ⟨h,hp⟩)

end NSSE.MultiConstructorSignature
