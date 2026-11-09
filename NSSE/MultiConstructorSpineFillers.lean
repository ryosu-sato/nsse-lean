import NSSE.MultiConstructorSpineBoundary

/-! A filler cannot be confused with an original or spine position.
Only the Top filler is reachable from it, and only the Bottom filler
can reach it, in the corresponding directions of the certificate. -/
namespace NSSE.MultiConstructorSpineFillers
open MultiConstructorConstraints MultiConstructorSpineInput MultiConstructorSpineInput.Data
open MultiConstructorSpineTags MultiConstructorSpineRelation
variable {H : Type*} {arity : H → Nat} {n D : Nat}

theorem old_below (S : Data arity n D) (v : Fin n) : (S.old v).val < S.botVar.val := by
  have := v.isLt
  change v.val < n+2*S.word.length
  omega

theorem x_below (S : Data arity n D) (i : Fin (S.word.length+1)) : (S.xAt i).val < S.botVar.val := by
  by_cases hi : i.val = 0
  · simpa [xAt,hi] using old_below S S.left
  · rw [xAt,if_neg hi]
    have := i.isLt
    change n+i.val-1 < n+2*S.word.length
    omega

theorem y_below (S : Data arity n D) (i : Fin (S.word.length+1)) : (S.yAt i).val < S.botVar.val := by
  by_cases hi : i.val = 0
  · simpa [yAt,hi] using old_below S S.right
  · rw [yAt,if_neg hi]
    have := i.isLt
    change n+S.word.length+i.val-1 < n+2*S.word.length
    omega

theorem below_ne (S : Data arity n D) (v : Fin S.size) (hv : v.val < S.botVar.val) :
    v ≠ S.botVar ∧ v ≠ S.topVar := by
  have ht : S.topVar.val = S.botVar.val+1 := rfl
  constructor <;> intro he <;> have hh := congrArg Fin.val he <;> omega

theorem top_ne_bot (S : Data arity n D) : S.topVar ≠ S.botVar := by
  intro he
  have hh := congrArg Fin.val he
  change n+2*S.word.length+1 = n+2*S.word.length at hh
  omega

variable [DecidableEq H]

theorem top_only (phi : Constraints arity n) (S : Data arity n D) (v : Fin S.size)
    (hr : relation phi S S.topVar v) : v = S.topVar := by
  have hd : decode S v = .top := by
    change relationTag phi S (decode S (encode S .top)) (decode S v) at hr
    rw [decode_encode] at hr
    cases he : decode S v <;> simp_all [relationTag]
  rw [← encode_decode S v,hd]
  rfl

theorem bot_only (phi : Constraints arity n) (S : Data arity n D) (v : Fin S.size)
    (hr : relation phi S v S.botVar) : v = S.botVar := by
  have hd : decode S v = .bot := by
    change relationTag phi S (decode S v) (decode S (encode S .bot)) at hr
    rw [decode_encode] at hr
    cases he : decode S v <;> simp_all [relationTag]
  rw [← encode_decode S v,hd]
  rfl

end NSSE.MultiConstructorSpineFillers
