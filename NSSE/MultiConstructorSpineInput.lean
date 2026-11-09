import NSSE.MultiConstructorInputMap
import NSSE.MultiConstructorUnifiedWords

/-! A concrete original flat extension for a supplied unified assignment.
Only lower X and upper Y spines are added; roots alias the original query. -/
namespace NSSE.MultiConstructorSpineInput
open MultiConstructorConstraints MultiConstructorTrees
variable {H : Type*} {arity : H → Nat} {n D : Nat}

structure Data (arity : H → Nat) (n D : Nat) where
  left : Fin n
  right : Fin n
  word : List (Fin D)
  heads : Fin word.length → H
  endX : Label H
  endY : Label H

namespace Data

def size (S : Data arity n D) : Nat := n+2*S.word.length+2

def old (S : Data arity n D) (x : Fin n) : Fin S.size := ⟨x.val,by have := x.isLt; unfold size; omega⟩

def xAt (S : Data arity n D) (k : Fin (S.word.length+1)) : Fin S.size :=
  if k.val = 0 then S.old S.left else ⟨n+k.val-1,by have := k.isLt; unfold size; omega⟩

def yAt (S : Data arity n D) (k : Fin (S.word.length+1)) : Fin S.size :=
  if k.val = 0 then S.old S.right else ⟨n+S.word.length+k.val-1,by have := k.isLt; unfold size; omega⟩

def botVar (S : Data arity n D) : Fin S.size := ⟨n+2*S.word.length,by unfold size; omega⟩
def topVar (S : Data arity n D) : Fin S.size := ⟨n+2*S.word.length+1,by unfold size; omega⟩
def last (S : Data arity n D) : Fin (S.word.length+1) := ⟨S.word.length,by omega⟩
def here (S : Data arity n D) (k : Fin S.word.length) : Fin (S.word.length+1) := ⟨k.val,by have := k.isLt; omega⟩
def after (S : Data arity n D) (k : Fin S.word.length) : Fin (S.word.length+1) := ⟨k.val+1,by have := k.isLt; omega⟩

theorem x_zero (S : Data arity n D) : S.xAt ⟨0,by omega⟩ = S.old S.left := by simp [xAt]
theorem y_zero (S : Data arity n D) : S.yAt ⟨0,by omega⟩ = S.old S.right := by simp [yAt]

def lower (S : Data arity n D) (k : Fin S.word.length) : Bound arity S.size :=
  ⟨S.xAt (S.here k),S.heads k,fun i => if i.val = S.word[k.val].val then S.xAt (S.after k) else S.botVar⟩

def upper (S : Data arity n D) (k : Fin S.word.length) : Bound arity S.size :=
  ⟨S.yAt (S.here k),S.heads k,fun i => if i.val = S.word[k.val].val then S.yAt (S.after k) else S.topVar⟩

def lowerEnd (S : Data arity n D) : List (Bound arity S.size) :=
  match S.endX with
  | .node h => [⟨S.xAt S.last,h,fun _ => S.botVar⟩]
  | _ => []

def upperEnd (S : Data arity n D) : List (Bound arity S.size) :=
  match S.endY with
  | .node h => [⟨S.yAt S.last,h,fun _ => S.topVar⟩]
  | _ => []

def endBots (S : Data arity n D) : List (Fin S.size) :=
  match S.endY with | .bot => [S.yAt S.last] | _ => []

def endTops (S : Data arity n D) : List (Fin S.size) :=
  match S.endX with | .top => [S.xAt S.last] | _ => []

def seeds (S : Data arity n D) : Constraints arity S.size :=
  ⟨List.ofFn S.upper ++ S.upperEnd,List.ofFn S.lower ++ S.lowerEnd,
    S.botVar::S.endBots,S.topVar::S.endTops⟩

def program (S : Data arity n D) (phi : Constraints arity n) : Constraints arity S.size :=
  MultiConstructorInputMap.append (MultiConstructorInputMap.rename phi S.old) S.seeds

theorem lower_mem (S : Data arity n D) (k : Fin S.word.length) : S.lower k ∈ S.seeds.lower := by
  exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨k,rfl⟩)

theorem upper_mem (S : Data arity n D) (k : Fin S.word.length) : S.upper k ∈ S.seeds.upper := by
  exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨k,rfl⟩)

theorem lower_end_mem (S : Data arity n D) (h : H) (hx : S.endX = .node h) :
    (⟨S.xAt S.last,h,fun _ => S.botVar⟩ : Bound arity S.size) ∈ S.seeds.lower := by
  apply List.mem_append_right
  simp only [lowerEnd,hx,List.mem_singleton]

theorem upper_end_mem (S : Data arity n D) (h : H) (hy : S.endY = .node h) :
    (⟨S.yAt S.last,h,fun _ => S.topVar⟩ : Bound arity S.size) ∈ S.seeds.upper := by
  apply List.mem_append_right
  simp only [upperEnd,hy,List.mem_singleton]

theorem top_end_mem (S : Data arity n D) (hx : S.endX = .top) : S.xAt S.last ∈ S.seeds.top := by
  exact List.mem_cons_of_mem _ (by simp only [endTops,hx,List.mem_singleton])

theorem bot_end_mem (S : Data arity n D) (hy : S.endY = .bot) : S.yAt S.last ∈ S.seeds.bot := by
  exact List.mem_cons_of_mem _ (by simp only [endBots,hy,List.mem_singleton])

end Data
end NSSE.MultiConstructorSpineInput
