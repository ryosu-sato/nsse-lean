import NSSE.MultiConstructorSelectorCoverage

/-! Proper assignments include a common proper terminal head. They need
no terminal inequality and are the actual-word interpretation of Good. -/
namespace NSSE.MultiConstructorCommonWord
open MultiConstructorConstraints MultiConstructorTrees MultiConstructorRawValidity
open MultiConstructorUnifiedWords MultiConstructorUnifiedRays
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

def Common (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (h : H) : Prop :=
  Local phi x y w heads ∧ Valid phi (row phi x y w w.length) ∧
    Compatible phi (row phi x y w w.length) h ∧ Rays phi x y w heads (.node h) (.node h)

theorem rays_active_agree (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (ex ey : Label H) (hr : Rays phi x y w heads ex ey)
    (N k j : Nat) (hk : k ≤ w.length) (hj : j ≤ w.length)
    (hact : GeneralCopyGrid.Active (annotation phi x y w) N k j) :
    P0DZBranch.Agree (value w heads ex ey false j) (value w heads ex ey true k) := by
  obtain ⟨_,a,b,l,haj,hbk,hrr⟩ := (GeneralCopyGrid.active_iff_ray _ N k j).mp hact
  obtain ⟨hb,hm⟩ := (ray_exact phi x y w a b l).mp hrr
  have he := hr ⟨a,by omega⟩ ⟨b,by omega⟩ ⟨l,by omega⟩ hb
    (by change a+l ≤ w.length; omega) (by change b+l ≤ w.length; omega) hm
  simpa only [haj,hbk] using he

omit [DecidableEq H] in
theorem value_terminal (w : List (Fin D)) (heads : Fin w.length → H) (ex ey : Label H) (s : Bool) :
    value w heads ex ey s w.length = if s then ey else ex := by
  rw [value,dif_neg (Nat.lt_irrefl _)]

end NSSE.MultiConstructorCommonWord
