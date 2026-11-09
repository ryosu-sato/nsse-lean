import NSSE.MultiConstructorSpineClosure
import NSSE.MultiConstructorSpineFillers

/-! Finite rail potentials are monotone in the certificate relation.
They count down to the corresponding filler along each new bound. -/
namespace NSSE.MultiConstructorSpinePotential
open MultiConstructorConstraints MultiConstructorSpineInput MultiConstructorSpineInput.Data
open MultiConstructorSpineTags MultiConstructorSpineRelation
variable {H : Type*} {arity : H → Nat} {n D : Nat}

def leftTag {n m : Nat} : Tag n m → Nat
  | .bot => 0
  | .x k => m-k.val
  | _ => m+1

def rightTag {n m : Nat} : Tag n m → Nat
  | .top => 0
  | .y k => m-k.val
  | _ => m+1

def left (S : Data arity n D) (v : Fin S.size) : Nat := leftTag (decode S v)
def right (S : Data arity n D) (v : Fin S.size) : Nat := rightTag (decode S v)

@[simp] theorem left_encode (S : Data arity n D) (t : Tag n S.word.length) :
    left S (encode S t) = leftTag t := by simp only [left,decode_encode]
@[simp] theorem right_encode (S : Data arity n D) (t : Tag n S.word.length) :
    right S (encode S t) = rightTag t := by simp only [right,decode_encode]
@[simp] theorem left_old (S : Data arity n D) (v : Fin n) : left S (S.old v) = S.word.length+1 :=
  left_encode S (.old v)
@[simp] theorem right_old (S : Data arity n D) (v : Fin n) : right S (S.old v) = S.word.length+1 :=
  right_encode S (.old v)
@[simp] theorem left_bot (S : Data arity n D) : left S S.botVar = 0 := left_encode S .bot
@[simp] theorem right_top (S : Data arity n D) : right S S.topVar = 0 := right_encode S .top

theorem left_bound (S : Data arity n D) (v : Fin S.size) : left S v ≤ S.word.length+1 := by
  unfold left
  cases decode S v <;> simp only [leftTag] <;> omega

theorem right_bound (S : Data arity n D) (v : Fin S.size) : right S v ≤ S.word.length+1 := by
  unfold right
  cases decode S v <;> simp only [rightTag] <;> omega

theorem left_x (S : Data arity n D) (i : Fin (S.word.length+1)) :
    left S (S.xAt i) = S.word.length+1-i.val := by
  by_cases hi : i.val = 0
  · have he : S.xAt i = S.old S.left := by simp [xAt,hi]
    simp only [he,left_old,hi,Nat.sub_zero]
  · let k : Fin S.word.length := ⟨i.val-1,by have := i.isLt; omega⟩
    have hk : S.after k = i := by apply Fin.ext; change i.val-1+1 = i.val; omega
    rw [← hk]
    change left S (encode S (.x k)) = _
    rw [left_encode]
    change S.word.length-k.val = S.word.length+1-(k.val+1)
    omega

theorem right_y (S : Data arity n D) (i : Fin (S.word.length+1)) :
    right S (S.yAt i) = S.word.length+1-i.val := by
  by_cases hi : i.val = 0
  · have he : S.yAt i = S.old S.right := by simp [yAt,hi]
    simp only [he,right_old,hi,Nat.sub_zero]
  · let k : Fin S.word.length := ⟨i.val-1,by have := i.isLt; omega⟩
    have hk : S.after k = i := by apply Fin.ext; change i.val-1+1 = i.val; omega
    rw [← hk]
    change right S (encode S (.y k)) = _
    rw [right_encode]
    change S.word.length-k.val = S.word.length+1-(k.val+1)
    omega

variable [DecidableEq H]

theorem left_relation (phi : Constraints arity n) (S : Data arity n D) (a b : Fin S.size)
    (hr : relation phi S a b) : left S a ≤ left S b := by
  unfold left
  change relationTag phi S (decode S a) (decode S b) at hr
  cases ha : decode S a <;> cases hb : decode S b <;> simp_all [relationTag,leftTag] <;> omega

theorem right_relation (phi : Constraints arity n) (S : Data arity n D) (a b : Fin S.size)
    (hr : relation phi S a b) : right S b ≤ right S a := by
  unfold right
  change relationTag phi S (decode S a) (decode S b) at hr
  cases ha : decode S a <;> cases hb : decode S b <;> simp_all [relationTag,rightTag] <;> omega

theorem left_support (phi : Constraints arity n) (S : Data arity n D) (a b : Fin S.size)
    (hs : Support (S.program phi) a b) : left S a ≤ left S b :=
  left_relation phi S a b (MultiConstructorSpineClosure.support phi S a b hs)

theorem right_support (phi : Constraints arity n) (S : Data arity n D) (a b : Fin S.size)
    (hs : Support (S.program phi) a b) : right S b ≤ right S a :=
  right_relation phi S a b (MultiConstructorSpineClosure.support phi S a b hs)

theorem maximal_original (phi : Constraints arity n) (S : Data arity n D) (a b : Fin S.size)
    (hs : Support (S.program phi) a b) (hl : left S a = S.word.length+1)
    (hu : right S b = S.word.length+1) : ∃ x y : Fin n, a = S.old x ∧ b = S.old y := by
  have hr := MultiConstructorSpineClosure.support phi S a b hs
  change relationTag phi S (decode S a) (decode S b) at hr
  change leftTag (decode S a) = _ at hl
  change rightTag (decode S b) = _ at hu
  have hd : ∃ x y : Fin n, decode S a = .old x ∧ decode S b = .old y := by
    cases ha : decode S a <;> cases hb : decode S b <;>
      simp_all [relationTag,leftTag,rightTag] <;> omega
  obtain ⟨x,y,hx,hy⟩ := hd
  refine ⟨x,y,?_,?_⟩
  · rw [← encode_decode S a,hx]; rfl
  · rw [← encode_decode S b,hy]; rfl

end NSSE.MultiConstructorSpinePotential
