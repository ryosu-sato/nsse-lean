import NSSE.MultiConstructorEmptyTail

/-! First unified words retain a forward old ray across the entire empty
proper tail. Both birth origins precede every earlier joint-empty row. -/
namespace NSSE.MultiConstructorFirstRay
open MultiConstructorConstraints MultiConstructorTokens MultiConstructorTrees
open MultiConstructorUnifiedWords MultiConstructorUnifiedPrefix MultiConstructorUnifiedRays
open MultiConstructorIsolatedPrefix MultiConstructorEmptyTail
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

theorem first_prefix (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (hw : Witness phi x y w) : ∃ m, m ≤ w.length ∧ First phi x y (w.take m) := by
  classical
  have hex : ∃ m, m ≤ w.length ∧ Witness phi x y (w.take m) :=
    ⟨w.length,le_rfl,by simpa only [List.take_length] using hw⟩
  let m := Nat.find hex
  have hs := Nat.find_spec hex
  refine ⟨m,hs.1,hs.2,?_⟩
  intro k hk hkw
  have hkm : k < m := by simp only [List.length_take] at hk; omega
  have hkw' : Witness phi x y (w.take k) := by
    simpa only [List.take_take,Nat.min_eq_left (Nat.le_of_lt hkm)] using hkw
  exact Nat.find_min hex hkm ⟨by omega,hkw'⟩

theorem surviving (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (hf : First phi x y w) (heads : Fin w.length → H) (ex ey : Label H)
    (ha : Assignment phi x y w heads ex ey) (J : Nat) (hJ : J < w.length)
    (he : row phi x y w J = (∅,∅)) :
    ∃ a b l, a < b ∧ b < J ∧ b+l = w.length-1 ∧
      Born phi x y w a b ∧ P0ProperWords.WordMatch w a b l := by
  have hn : 0 < w.length := by omega
  have hm : w.length-1 < w.length := by omega
  have hemp := empty_after phi x y w J (w.length-1) he (by omega) (by omega)
  have hp : lowerPins phi (row phi x y w (w.length-1)).2 = ∅ := by
    rw [hemp]
    exact lowerPins_empty phi
  obtain ⟨j,hact⟩ := first_lower_incident phi x y w hf heads ex ey ha (w.length-1) hm hp
  have hne : j ≠ w.length-1 := by
    intro hj
    subst j
    exact no_active_diagonal phi x y w heads ex ey ha _ _ (by omega) hact
  obtain ⟨hj,a,b,l,haj,hbl,hr⟩ :=
    (GeneralCopyGrid.active_iff_ray _ (w.length-1) (w.length-1) j).mp hact
  obtain ⟨hb,hw⟩ := (ray_exact phi x y w a b l).mp hr
  have hab := birth_before_empty phi x y w J a b he (by omega) (by omega) hb
  exact ⟨a,b,l,by omega,hab.2,hbl,hb,hw⟩

end NSSE.MultiConstructorFirstRay
