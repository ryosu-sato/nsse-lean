import NSSE.MultiConstructorSpineFillers
import NSSE.MultiConstructorSpineMembership

/-! Literal head demands have only four origins on either side. Spine
demands retain their supplied labels; they do not assert a model. -/
namespace NSSE.MultiConstructorSpineDemands
open MultiConstructorTrees MultiConstructorConstraints MultiConstructorUnifiedWords
open MultiConstructorSpineInput MultiConstructorSpineInput.Data MultiConstructorSpineMembership
open MultiConstructorSpineFillers
variable {H : Type*} {arity : H → Nat} {n D : Nat}

inductive Lower (phi : Constraints arity n) (S : Data arity n D) : Fin S.size → Label H → Prop
  | original (a : Bound arity n) (ha : a ∈ phi.lower) : Lower phi S (S.old a.parent) (.node a.head)
  | extreme (v : Fin n) (hv : v ∈ phi.top) : Lower phi S (S.old v) .top
  | spine (i : Fin (S.word.length+1)) :
      Lower phi S (S.xAt i) (value S.word S.heads S.endX S.endY false i.val)
  | filler : Lower phi S S.topVar .top

inductive Upper (phi : Constraints arity n) (S : Data arity n D) : Fin S.size → Label H → Prop
  | original (a : Bound arity n) (ha : a ∈ phi.upper) : Upper phi S (S.old a.parent) (.node a.head)
  | extreme (v : Fin n) (hv : v ∈ phi.bot) : Upper phi S (S.old v) .bot
  | spine (i : Fin (S.word.length+1)) :
      Upper phi S (S.yAt i) (value S.word S.heads S.endX S.endY true i.val)
  | filler : Upper phi S S.botVar .bot

theorem lower_view (phi : Constraints arity n) (S : Data arity n D) (a : Bound arity S.size)
    (ha : a ∈ (S.program phi).lower) : Lower phi S a.parent (.node a.head) := by
  rcases lower_cases phi S a ha with ⟨a,hoa,rfl⟩ | ⟨k,rfl⟩ | ⟨h,hx,rfl⟩
  · exact Lower.original a hoa
  · simpa only [value,here,dif_pos k.isLt] using Lower.spine (phi := phi) (S := S) (S.here k)
  · simpa [value,last,hx] using Lower.spine (phi := phi) (S := S) S.last

theorem upper_view (phi : Constraints arity n) (S : Data arity n D) (a : Bound arity S.size)
    (ha : a ∈ (S.program phi).upper) : Upper phi S a.parent (.node a.head) := by
  rcases upper_cases phi S a ha with ⟨a,hoa,rfl⟩ | ⟨k,rfl⟩ | ⟨h,hy,rfl⟩
  · exact Upper.original a hoa
  · simpa only [value,here,dif_pos k.isLt] using Upper.spine (phi := phi) (S := S) (S.here k)
  · simpa [value,last,hy] using Upper.spine (phi := phi) (S := S) S.last

theorem top_view (phi : Constraints arity n) (S : Data arity n D) (v : Fin S.size)
    (hv : v ∈ (S.program phi).top) : Lower phi S v .top := by
  rcases top_cases phi S v hv with ⟨u,hu,rfl⟩ | rfl | ⟨hx,rfl⟩
  · exact Lower.extreme u hu
  · exact Lower.filler
  · simpa [value,last,hx] using Lower.spine (phi := phi) (S := S) S.last

theorem bot_view (phi : Constraints arity n) (S : Data arity n D) (v : Fin S.size)
    (hv : v ∈ (S.program phi).bot) : Upper phi S v .bot := by
  rcases bot_cases phi S v hv with ⟨u,hu,rfl⟩ | rfl | ⟨hy,rfl⟩
  · exact Upper.extreme u hu
  · exact Upper.filler
  · simpa [value,last,hy] using Upper.spine (phi := phi) (S := S) S.last

theorem lower_ne_bot (phi : Constraints arity n) (S : Data arity n D) {v : Fin S.size} {e : Label H}
    (hl : Lower phi S v e) : v ≠ S.botVar := by
  cases hl with
  | original a _ => exact (below_ne S _ (old_below S a.parent)).1
  | extreme u _ => exact (below_ne S _ (old_below S u)).1
  | spine i => exact (below_ne S _ (x_below S i)).1
  | filler => exact top_ne_bot S

theorem upper_ne_top (phi : Constraints arity n) (S : Data arity n D) {v : Fin S.size} {e : Label H}
    (hu : Upper phi S v e) : v ≠ S.topVar := by
  cases hu with
  | original a _ => exact (below_ne S _ (old_below S a.parent)).2
  | extreme u _ => exact (below_ne S _ (old_below S u)).2
  | spine i => exact (below_ne S _ (y_below S i)).2
  | filler => exact (top_ne_bot S).symm

end NSSE.MultiConstructorSpineDemands
