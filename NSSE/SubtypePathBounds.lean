import NSSE.SubtypeSupportOperations

/-! # Arbitrary-word syntactic upper and lower bounds

The empty path has variable Support, not equality. LowerPath x p y means
p(y) <= x. Concatenation and cancellation are derivation theorems.
-/

namespace NSSE.SubtypePathBounds

open SubtypeConstraints SubtypeConstraintOperations SubtypeSupportOperations

variable {n m d : Nat}

inductive UpperPath (φ : Constraints n d) : Fin n → List (Fin d) → Fin n → Prop
  | nil {x y} : Support φ x y → UpperPath φ x [] y
  | cons {x y z i path} : SupportedUpper φ x i y → UpperPath φ y path z → UpperPath φ x (i :: path) z

inductive LowerPath (φ : Constraints n d) : Fin n → List (Fin d) → Fin n → Prop
  | nil {x y} : Support φ y x → LowerPath φ x [] y
  | cons {x y z i path} : SupportedLower φ x i y → LowerPath φ y path z → LowerPath φ x (i :: path) z

theorem upper_pre (φ : Constraints n d) {x y z : Fin n} {path : List (Fin d)}
    (h : Support φ x y) (hp : UpperPath φ y path z) : UpperPath φ x path z := by
  cases hp with
  | nil hs => exact .nil (h.trans hs)
  | cons hs ht =>
      obtain ⟨a,ha,hya,haz⟩ := hs
      exact .cons ⟨a,ha,h.trans hya,haz⟩ ht

theorem upper_post (φ : Constraints n d) {x y z : Fin n} {path : List (Fin d)}
    (hp : UpperPath φ x path y) (h : Support φ y z) : UpperPath φ x path z := by
  induction hp with
  | nil hs => exact .nil (hs.trans h)
  | cons hs _ ih => exact .cons hs (ih h)

theorem lower_pre (φ : Constraints n d) {x y z : Fin n} {path : List (Fin d)}
    (h : Support φ x y) (hp : LowerPath φ x path z) : LowerPath φ y path z := by
  cases hp with
  | nil hs => exact .nil (hs.trans h)
  | cons hs ht =>
      obtain ⟨a,ha,hza,hax⟩ := hs
      exact .cons ⟨a,ha,hza,hax.trans h⟩ ht

theorem lower_post (φ : Constraints n d) {x y z : Fin n} {path : List (Fin d)}
    (hp : LowerPath φ x path y) (h : Support φ z y) : LowerPath φ x path z := by
  induction hp with
  | nil hs => exact .nil (h.trans hs)
  | cons hs _ ih => exact .cons hs (ih h)

theorem upper_one (φ : Constraints n d) (x y : Fin n) (i : Fin d) :
    UpperPath φ x [i] y ↔ SupportedUpper φ x i y := by
  constructor
  · intro h
    cases h with
    | cons hs ht =>
        cases ht with
        | nil hxy =>
            obtain ⟨a,ha,hx,hz⟩ := hs
            exact ⟨a,ha,hx,hz.trans hxy⟩
  · intro h; exact .cons h (.nil (.refl _))

theorem lower_one (φ : Constraints n d) (x y : Fin n) (i : Fin d) :
    LowerPath φ x [i] y ↔ SupportedLower φ x i y := by
  constructor
  · intro h
    cases h with
    | cons hs ht =>
        cases ht with
        | nil hxy =>
            obtain ⟨a,ha,hz,hx⟩ := hs
            exact ⟨a,ha,hxy.trans hz,hx⟩
  · intro h; exact .cons h (.nil (.refl _))

theorem upper_append (φ : Constraints n d) {x y z : Fin n} {p q : List (Fin d)}
    (hp : UpperPath φ x p y) (hq : UpperPath φ y q z) : UpperPath φ x (p ++ q) z := by
  induction hp with
  | nil hs => exact upper_pre φ hs hq
  | cons hs _ ih => exact .cons hs (ih hq)

theorem lower_append (φ : Constraints n d) {x y z : Fin n} {p q : List (Fin d)}
    (hp : LowerPath φ x p y) (hq : LowerPath φ y q z) : LowerPath φ x (p ++ q) z := by
  induction hp with
  | nil hs => exact lower_pre φ hs hq
  | cons hs _ ih => exact .cons hs (ih hq)

theorem upper_split (φ : Constraints n d) (p : List (Fin d)) {q : List (Fin d)}
    {x z : Fin n} (h : UpperPath φ x (p ++ q) z) :
    ∃ y, UpperPath φ x p y ∧ UpperPath φ y q z := by
  induction p generalizing x z with
  | nil => exact ⟨x,.nil (.refl _),h⟩
  | cons i p ih =>
      cases h with
      | cons hs ht =>
          obtain ⟨y,hp,hq⟩ := ih ht
          exact ⟨y,.cons hs hp,hq⟩

theorem lower_split (φ : Constraints n d) (p : List (Fin d)) {q : List (Fin d)}
    {x z : Fin n} (h : LowerPath φ x (p ++ q) z) :
    ∃ y, LowerPath φ x p y ∧ LowerPath φ y q z := by
  induction p generalizing x z with
  | nil => exact ⟨x,.nil (.refl _),h⟩
  | cons i p ih =>
      cases h with
      | cons hs ht =>
          obtain ⟨y,hp,hq⟩ := ih ht
          exact ⟨y,.cons hs hp,hq⟩

/-- Literal journal Table 5 snoc rule, equivalent to the cons definition. -/
theorem upper_snoc_iff (φ : Constraints n d) (x z : Fin n) (p : List (Fin d)) (i : Fin d) :
    UpperPath φ x (p ++ [i]) z ↔
      ∃ a ∈ φ.upper, UpperPath φ x p a.1 ∧ Support φ (a.2 i) z := by
  constructor
  · intro h
    obtain ⟨y,hp,hi⟩ := upper_split φ p h
    obtain ⟨a,ha,hy,hz⟩ := (upper_one φ y z i).mp hi
    exact ⟨a,ha,upper_post φ hp hy,hz⟩
  · rintro ⟨a,ha,hp,hz⟩
    exact upper_append φ hp ((upper_one φ a.1 z i).mpr ⟨a,ha,.refl _,hz⟩)

theorem lower_snoc_iff (φ : Constraints n d) (x z : Fin n) (p : List (Fin d)) (i : Fin d) :
    LowerPath φ x (p ++ [i]) z ↔
      ∃ a ∈ φ.lower, LowerPath φ x p a.1 ∧ Support φ z (a.2 i) := by
  constructor
  · intro h
    obtain ⟨y,hp,hi⟩ := lower_split φ p h
    obtain ⟨a,ha,hz,hy⟩ := (lower_one φ y z i).mp hi
    exact ⟨a,ha,lower_post φ hp hy,hz⟩
  · rintro ⟨a,ha,hp,hz⟩
    exact lower_append φ hp ((lower_one φ a.1 z i).mpr ⟨a,ha,hz,.refl _⟩)

theorem child_decomp (φ : Constraints n d) {x a b : Fin n} {i : Fin d}
    (hl : SupportedLower φ x i a) (hu : SupportedUpper φ x i b) : Support φ a b := by
  obtain ⟨l,hl,hal,hlx⟩ := hl
  obtain ⟨u,hu,hxu,hub⟩ := hu
  exact hal.trans ((Support.decomp hl hu (hlx.trans hxu) i).trans hub)

theorem cancel_lower_upper (φ : Constraints n d) (p : List (Fin d))
    {x a b : Fin n} {q : List (Fin d)}
    (hl : LowerPath φ x p a) (hu : UpperPath φ x (p ++ q) b) : UpperPath φ a q b := by
  induction p generalizing x a b with
  | nil => cases hl with | nil hs => exact upper_pre φ hs hu
  | cons i p ih =>
      cases hl with
      | cons hs ht =>
          cases hu with
          | cons hu hv => exact ih ht (upper_pre φ (child_decomp φ hs hu) hv)

theorem cancel_upper_lower (φ : Constraints n d) (p : List (Fin d))
    {x a b : Fin n} {q : List (Fin d)}
    (hu : UpperPath φ x p a) (hl : LowerPath φ x (p ++ q) b) : LowerPath φ a q b := by
  induction p generalizing x a b with
  | nil => cases hu with | nil hs => exact lower_pre φ hs hl
  | cons i p ih =>
      cases hu with
      | cons hs ht =>
          cases hl with
          | cons hu hv => exact ih ht (lower_pre φ (child_decomp φ hu hs) hv)

theorem upper_child_map (φ : Constraints n d) (ψ : Constraints m d) (f : Fin n → Fin m)
    (hl : ∀ a ∈ φ.lower, renameBound f a ∈ ψ.lower)
    (hu : ∀ a ∈ φ.upper, renameBound f a ∈ ψ.upper)
    {x y : Fin n} {i : Fin d} (h : SupportedUpper φ x i y) : SupportedUpper ψ (f x) i (f y) := by
  obtain ⟨a,ha,hx,hy⟩ := h
  exact ⟨renameBound f a,hu a ha,support_map φ ψ f hl hu hx,support_map φ ψ f hl hu hy⟩

theorem lower_child_map (φ : Constraints n d) (ψ : Constraints m d) (f : Fin n → Fin m)
    (hl : ∀ a ∈ φ.lower, renameBound f a ∈ ψ.lower)
    (hu : ∀ a ∈ φ.upper, renameBound f a ∈ ψ.upper)
    {x y : Fin n} {i : Fin d} (h : SupportedLower φ x i y) : SupportedLower ψ (f x) i (f y) := by
  obtain ⟨a,ha,hx,hy⟩ := h
  exact ⟨renameBound f a,hl a ha,support_map φ ψ f hl hu hx,support_map φ ψ f hl hu hy⟩

theorem upper_path_map (φ : Constraints n d) (ψ : Constraints m d) (f : Fin n → Fin m)
    (hl : ∀ a ∈ φ.lower, renameBound f a ∈ ψ.lower)
    (hu : ∀ a ∈ φ.upper, renameBound f a ∈ ψ.upper)
    {x y : Fin n} {path : List (Fin d)} (h : UpperPath φ x path y) : UpperPath ψ (f x) path (f y) := by
  induction h with
  | nil hs => exact .nil (support_map φ ψ f hl hu hs)
  | cons hs _ ih => exact .cons (upper_child_map φ ψ f hl hu hs) ih

theorem lower_path_map (φ : Constraints n d) (ψ : Constraints m d) (f : Fin n → Fin m)
    (hl : ∀ a ∈ φ.lower, renameBound f a ∈ ψ.lower)
    (hu : ∀ a ∈ φ.upper, renameBound f a ∈ ψ.upper)
    {x y : Fin n} {path : List (Fin d)} (h : LowerPath φ x path y) : LowerPath ψ (f x) path (f y) := by
  induction h with
  | nil hs => exact .nil (support_map φ ψ f hl hu hs)
  | cons hs _ ih => exact .cons (lower_child_map φ ψ f hl hu hs) ih

end NSSE.SubtypePathBounds
