import NSSE.SubtypeLowerGraft
import NSSE.SubtypePathBounds

/-! # A lower-only fresh graft preserves all old-to-old path bounds

Upper traces starting old remain old; lower traces ending old were old
throughout. This is a general arbitrary-word theorem, not a length check.
-/

namespace NSSE.SubtypeLowerGraftPaths

open SubtypeConstraints SubtypeConstraintOperations SubtypeLowerGraft SubtypePathBounds

variable {n m d : Nat}
variable (φ : Constraints n d) (added : List (BoundLiteral (n + m) d))
variable (bots tops : List (Fin (n + m))) (hc : FreshChildren added)
include hc

local notation "Ψ" => graft φ added bots tops

theorem no_upper_old_fresh (x : Fin n) (y : Fin m) (i : Fin d) :
    ¬ SupportedUpper Ψ (Fin.castAdd m x) i (Fin.natAdd n y) := by
  rintro ⟨a,ha,_,hs⟩
  change a ∈ φ.upper.map (renameBound (Fin.castAdd m)) at ha
  obtain ⟨a₀,_,rfl⟩ := List.mem_map.mp ha
  exact no_old_fresh φ added bots tops hc (a₀.2 i) y hs

theorem no_lower_fresh_old (x : Fin m) (y : Fin n) (i : Fin d) :
    ¬ SupportedLower Ψ (Fin.natAdd n x) i (Fin.castAdd m y) := by
  rintro ⟨a,ha,hy,hx⟩
  change a ∈ φ.lower.map (renameBound (Fin.castAdd m)) ++ added at ha
  rcases List.mem_append.mp ha with ho | hn
  · obtain ⟨a₀,_,rfl⟩ := List.mem_map.mp ho
    exact no_old_fresh φ added bots tops hc a₀.1 x hx
  · obtain ⟨z,hz⟩ := hc a hn i
    rw [hz] at hy
    exact no_old_fresh φ added bots tops hc y z hy

theorem upper_child_old (x y : Fin n) (i : Fin d)
    (h : SupportedUpper Ψ (Fin.castAdd m x) i (Fin.castAdd m y)) : SupportedUpper φ x i y := by
  obtain ⟨a,ha,hx,hy⟩ := h
  change a ∈ φ.upper.map (renameBound (Fin.castAdd m)) at ha
  obtain ⟨a₀,ha₀,rfl⟩ := List.mem_map.mp ha
  exact ⟨a₀,ha₀,(support_old_iff φ added bots tops hc _ _).mp hx,
    (support_old_iff φ added bots tops hc _ _).mp hy⟩

theorem lower_child_old (x y : Fin n) (i : Fin d)
    (h : SupportedLower Ψ (Fin.castAdd m x) i (Fin.castAdd m y)) : SupportedLower φ x i y := by
  obtain ⟨a,ha,hy,hx⟩ := h
  change a ∈ φ.lower.map (renameBound (Fin.castAdd m)) ++ added at ha
  rcases List.mem_append.mp ha with ho | hn
  · obtain ⟨a₀,ha₀,rfl⟩ := List.mem_map.mp ho
    exact ⟨a₀,ha₀,(support_old_iff φ added bots tops hc _ _).mp hy,
      (support_old_iff φ added bots tops hc _ _).mp hx⟩
  · obtain ⟨z,hz⟩ := hc a hn i
    rw [hz] at hy
    exact False.elim (no_old_fresh φ added bots tops hc y z hy)

theorem upper_step_from_old (x : Fin n) (z : Fin (n + m)) (i : Fin d)
    (h : SupportedUpper Ψ (Fin.castAdd m x) i z) :
    ∃ y : Fin n, z = Fin.castAdd m y ∧ SupportedUpper φ x i y := by
  induction z using Fin.addCases with
  | left y => exact ⟨y,rfl,upper_child_old φ added bots tops hc x y i h⟩
  | right y => exact False.elim (no_upper_old_fresh φ added bots tops hc x y i h)

theorem lower_step_to_old (z : Fin (n + m)) (y : Fin n) (i : Fin d)
    (h : SupportedLower Ψ z i (Fin.castAdd m y)) :
    ∃ x : Fin n, z = Fin.castAdd m x ∧ SupportedLower φ x i y := by
  induction z using Fin.addCases with
  | left x => exact ⟨x,rfl,lower_child_old φ added bots tops hc x y i h⟩
  | right x => exact False.elim (no_lower_fresh_old φ added bots tops hc x y i h)

theorem upper_path_from_old (path : List (Fin d)) (x : Fin n) (z : Fin (n + m))
    (h : UpperPath Ψ (Fin.castAdd m x) path z) :
    ∃ y : Fin n, z = Fin.castAdd m y ∧ UpperPath φ x path y := by
  induction path generalizing x z with
  | nil =>
      cases h with
      | nil hs =>
          induction z using Fin.addCases with
          | left y => exact ⟨y,rfl,.nil ((support_old_iff φ added bots tops hc x y).mp hs)⟩
          | right y => exact False.elim (no_old_fresh φ added bots tops hc x y hs)
  | cons i path ih =>
      cases h with
      | cons hs ht =>
          obtain ⟨a,rfl,ha⟩ := upper_step_from_old φ added bots tops hc x _ i hs
          obtain ⟨y,hy,hp⟩ := ih a z ht
          exact ⟨y,hy,.cons ha hp⟩

theorem lower_path_to_old (path : List (Fin d)) (z : Fin (n + m)) (y : Fin n)
    (h : LowerPath Ψ z path (Fin.castAdd m y)) :
    ∃ x : Fin n, z = Fin.castAdd m x ∧ LowerPath φ x path y := by
  induction path generalizing z y with
  | nil =>
      cases h with
      | nil hs =>
          induction z using Fin.addCases with
          | left x => exact ⟨x,rfl,.nil ((support_old_iff φ added bots tops hc y x).mp hs)⟩
          | right x => exact False.elim (no_old_fresh φ added bots tops hc y x hs)
  | cons i path ih =>
      cases h with
      | cons hs ht =>
          obtain ⟨a,rfl,ha⟩ := ih _ y ht
          obtain ⟨x,hx,hp⟩ := lower_step_to_old φ added bots tops hc z a i hs
          exact ⟨x,hx,.cons hp ha⟩

theorem upper_path_old_iff (x y : Fin n) (path : List (Fin d)) :
    UpperPath Ψ (Fin.castAdd m x) path (Fin.castAdd m y) ↔ UpperPath φ x path y := by
  constructor
  · intro h
    obtain ⟨y',hy,hp⟩ := upper_path_from_old φ added bots tops hc path x _ h
    have he : y = y' := Fin.ext (congrArg (fun z : Fin (n + m) => z.val) hy)
    subst y'
    exact hp
  · apply upper_path_map φ Ψ (Fin.castAdd m)
    · intro a ha
      exact List.mem_append_left _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
    · intro a ha
      exact List.mem_map.mpr ⟨a,ha,rfl⟩

theorem lower_path_old_iff (x y : Fin n) (path : List (Fin d)) :
    LowerPath Ψ (Fin.castAdd m x) path (Fin.castAdd m y) ↔ LowerPath φ x path y := by
  constructor
  · intro h
    obtain ⟨x',hx,hp⟩ := lower_path_to_old φ added bots tops hc path _ y h
    have he : x = x' := Fin.ext (congrArg (fun z : Fin (n + m) => z.val) hx)
    subst x'
    exact hp
  · apply lower_path_map φ Ψ (Fin.castAdd m)
    · intro a ha
      exact List.mem_append_left _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
    · intro a ha
      exact List.mem_map.mpr ⟨a,ha,rfl⟩

end NSSE.SubtypeLowerGraftPaths
