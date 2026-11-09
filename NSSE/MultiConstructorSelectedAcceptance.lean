import NSSE.MultiConstructorSelectorHeads

/-! Original unified assignments with the computed heads and proper
selector states are accepted by the actual full D/Z branch. -/
namespace NSSE.MultiConstructorSelectedAcceptance
open MultiConstructorConstraints MultiConstructorTrees MultiConstructorRawTrace MultiConstructorRawValidity
open MultiConstructorBranch MultiConstructorBranchTrace MultiConstructorBranchLocal
open MultiConstructorUnifiedWords MultiConstructorUnifiedBranch
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

theorem assignment_complete (C : Parameters arity n) (w : List (Fin D)) (hw : w ≠ [])
    (ha : Assignment C.input C.left C.right w (selectedHeads C w) C.endX C.endY)
    (hp : ∀ k, k < w.length → Proper C.input (walk C (branch C D).initial (w.take k)).2) :
    MultiConstructorBranchAssignment.Assignment C w := by
  constructor
  · apply (local_iff_pointwise C w (branch C D).initial).mpr
    refine ⟨hw,?_,?_⟩
    · intro k hk
      have hl := ha.1 ⟨k,hk⟩
      have he : (walk C (branch C D).initial (w.take k)).1 = row C.input C.left C.right w k :=
        walk_raw C _ _
      refine ⟨⟨?_,hp k hk,?_⟩,hl.2.2⟩
      · rw [he]
        exact hl.1
      · rw [he]
        exact hl.2.1
    · change EndValid C (rawWord C (initial C.input C.left C.right) w)
      simpa only [Final,row,List.take_length] using ha.2.1
  · intro a han b hbn hb l hln hal hbl hm
    rw [← value_eq,← value_eq]
    exact ha.2.2 ⟨a,by omega⟩ ⟨b,by omega⟩ ⟨l,by omega⟩ hb hal hbl hm

theorem accepted (C : Parameters arity n) (w : List (Fin D)) (hw : w ≠ [])
    (ha : Assignment C.input C.left C.right w (selectedHeads C w) C.endX C.endY)
    (hp : ∀ k, k < w.length → Proper C.input (walk C (branch C D).initial (w.take k)).2) :
    P0DZBranch.Accepted (branch C D) w :=
  (MultiConstructorBranchAssignment.accepted_iff C w).mpr (assignment_complete C w hw ha hp)

def config (phi : Constraints arity n) (x y : Fin n) (reset : Row n) (fallback : H)
    (ex ey : Label H) : Parameters arity n := ⟨phi,x,y,reset,fallback,ex,ey⟩

theorem realized (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D)) (hw : w ≠ [])
    (heads : Fin w.length → H) (ex ey : Label H) (ha : Assignment phi x y w heads ex ey)
    (reset : Row n) (fallback : H)
    (hs : ∀ k : Fin w.length, MultiConstructorSelectorHead.choose phi
      (MultiConstructorSelectorTrace.trace phi x y reset w k.val) fallback = heads k)
    (hp : ∀ k : Fin w.length, Proper phi (MultiConstructorSelectorTrace.trace phi x y reset w k.val)) :
    P0DZBranch.Accepted (branch (config phi x y reset fallback ex ey) D) w := by
  let C := config phi x y reset fallback ex ey
  have he (k : Nat) : (walk C (branch C D).initial (w.take k)).2 =
      MultiConstructorSelectorTrace.trace phi x y reset w k :=
    MultiConstructorSelectorTrace.walk_selector C _ _
  have hh : selectedHeads C w = heads := by
    funext k
    change MultiConstructorSelectorHead.choose phi (walk C (branch C D).initial (w.take k.val)).2 fallback = heads k
    rw [he]
    exact hs k
  apply accepted C w hw
  · change Assignment phi x y w (selectedHeads C w) ex ey
    rw [hh]
    exact ha
  · intro k hk
    change Proper phi (walk C (branch C D).initial (w.take k)).2
    rw [he]
    exact hp ⟨k,hk⟩

end NSSE.MultiConstructorSelectedAcceptance
