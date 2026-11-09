import NSSE.MultiConstructorSpineInput

/-! A disjoint coordinate description of every variable of the actual
spine extension. Root aliases remain old variables, not fresh rail nodes. -/
namespace NSSE.MultiConstructorSpineTags
open MultiConstructorSpineInput MultiConstructorSpineInput.Data
variable {H : Type*} {arity : H → Nat} {n D : Nat}

inductive Tag (n m : Nat)
  | old (v : Fin n)
  | x (k : Fin m)
  | y (k : Fin m)
  | bot
  | top
  deriving DecidableEq

def encode (S : Data arity n D) : Tag n S.word.length → Fin S.size
  | .old v => S.old v
  | .x k => S.xAt (S.after k)
  | .y k => S.yAt (S.after k)
  | .bot => S.botVar
  | .top => S.topVar

theorem x_val (S : Data arity n D) (k : Fin S.word.length) : (encode S (.x k)).val = n+k.val := by
  change (S.xAt (S.after k)).val = n+k.val
  rw [xAt,if_neg (by change ¬k.val+1 = 0; omega)]
  change n+(k.val+1)-1 = n+k.val
  omega

theorem y_val (S : Data arity n D) (k : Fin S.word.length) :
    (encode S (.y k)).val = n+S.word.length+k.val := by
  change (S.yAt (S.after k)).val = n+S.word.length+k.val
  rw [yAt,if_neg (by change ¬k.val+1 = 0; omega)]
  change n+S.word.length+(k.val+1)-1 = n+S.word.length+k.val
  omega

def decode (S : Data arity n D) (v : Fin S.size) : Tag n S.word.length :=
  if h : v.val < n then .old ⟨v.val,h⟩
  else if h : v.val < n+S.word.length then .x ⟨v.val-n,by omega⟩
  else if h : v.val < n+2*S.word.length then .y ⟨v.val-(n+S.word.length),by omega⟩
  else if v.val = n+2*S.word.length then .bot else .top

theorem decode_encode (S : Data arity n D) (t : Tag n S.word.length) : decode S (encode S t) = t := by
  cases t with
  | old v =>
    have hv : (encode S (.old v)).val = v.val := rfl
    rw [decode,dif_pos (by rw [hv]; exact v.isLt)]
    rfl
  | x k =>
    have hk := k.isLt
    rw [decode,dif_neg (by rw [x_val]; omega),dif_pos (by rw [x_val]; omega)]
    congr 1
    apply Fin.ext
    change (encode S (.x k)).val-n = k.val
    rw [x_val]
    omega
  | y k =>
    have hk := k.isLt
    rw [decode,dif_neg (by rw [y_val]; omega),dif_neg (by rw [y_val]; omega),
      dif_pos (by rw [y_val]; omega)]
    congr 1
    apply Fin.ext
    change (encode S (.y k)).val-(n+S.word.length) = k.val
    rw [y_val]
    omega
  | bot =>
    have hv : (encode S .bot).val = n+2*S.word.length := rfl
    rw [decode,dif_neg (by rw [hv]; omega),dif_neg (by rw [hv]; omega),
      dif_neg (by rw [hv]; omega),if_pos hv]
  | top =>
    have hv : (encode S .top).val = n+2*S.word.length+1 := rfl
    rw [decode,dif_neg (by rw [hv]; omega),dif_neg (by rw [hv]; omega),
      dif_neg (by rw [hv]; omega),if_neg (by rw [hv]; omega)]

theorem encode_decode (S : Data arity n D) (v : Fin S.size) : encode S (decode S v) = v := by
  have hv := v.isLt
  unfold size at hv
  unfold decode
  split_ifs with hn hx hy hb
  · apply Fin.ext; rfl
  · apply Fin.ext
    rw [x_val]
    dsimp only
    omega
  · apply Fin.ext
    rw [y_val]
    dsimp only
    omega
  · apply Fin.ext
    exact hb.symm
  · apply Fin.ext
    change n+2*S.word.length+1 = v.val
    omega

def equiv (S : Data arity n D) : Tag n S.word.length ≃ Fin S.size :=
  ⟨encode S,decode S,decode_encode S,encode_decode S⟩

theorem encode_injective (S : Data arity n D) : Function.Injective (encode S) := (equiv S).injective

end NSSE.MultiConstructorSpineTags
