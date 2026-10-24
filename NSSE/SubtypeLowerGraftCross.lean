import NSSE.SubtypeLowerGraftPaths

/-! # Exact fresh-to-old support and upper paths in a lower-only graft

Every new-to-old relation comes from an actual added-literal path beginning
at an old root, matched by an original upper path with the SAME word.
-/

namespace NSSE.SubtypeLowerGraftCross

open SubtypeConstraints SubtypeConstraintOperations SubtypeLowerGraft SubtypePathBounds
open SubtypeLowerGraftPaths

variable {n m d : Nat}

inductive Origin (added : List (BoundLiteral (n + m) d)) : Fin n → List (Fin d) → Fin m → Prop
  | first {a : BoundLiteral (n + m) d} {x : Fin n} {u : Fin m} {i : Fin d}
      (ha : a ∈ added) (hp : a.1 = Fin.castAdd m x) (hc : a.2 i = Fin.natAdd n u) :
      Origin added x [i] u
  | snoc {a : BoundLiteral (n + m) d} {x : Fin n} {u v : Fin m} {word : List (Fin d)} {i : Fin d}
      (h : Origin added x word u) (ha : a ∈ added)
      (hp : a.1 = Fin.natAdd n u) (hc : a.2 i = Fin.natAdd n v) : Origin added x (word ++ [i]) v

def Cross (φ : Constraints n d) (added : List (BoundLiteral (n + m) d)) (u : Fin m) (y : Fin n) : Prop :=
  ∃ x word, Origin added x word u ∧ UpperPath φ x word y

theorem origin_nonempty {added : List (BoundLiteral (n + m) d)} {x u word}
    (h : Origin added x word u) : word ≠ [] := by
  cases h <;> simp

theorem origin_lower (φ : Constraints n d) (added : List (BoundLiteral (n + m) d))
    (bots tops : List (Fin (n + m))) {x u word} (h : Origin added x word u) :
    LowerPath (graft φ added bots tops) (Fin.castAdd m x) word (Fin.natAdd n u) := by
  induction h with
  | @first a x u i ha hp hc =>
      apply LowerPath.cons ?_ (.nil (.refl _))
      refine ⟨a,List.mem_append_right _ ha,?_,?_⟩
      · rw [hc]; exact .refl _
      · rw [hp]; exact .refl _
  | @snoc a x u v word i _ ha hp hc ih =>
      apply lower_append _ ih
      apply LowerPath.cons ?_ (.nil (.refl _))
      refine ⟨a,List.mem_append_right _ ha,?_,?_⟩
      · rw [hc]; exact .refl _
      · rw [hp]; exact .refl _

section Graft

variable (φ : Constraints n d) (added : List (BoundLiteral (n + m) d))
variable (bots tops : List (Fin (n + m))) (hc : FreshChildren added)
include hc

local notation "Ψ" => graft φ added bots tops

theorem support_cross {a b : Fin (n + m)} (h : Support Ψ a b) :
    ∀ u y, a = Fin.natAdd n u → b = Fin.castAdd m y → Cross φ added u y := by
  induction h with
  | refl a =>
      intro u y ha hb
      have he := congrArg (fun z : Fin (n + m) => z.val) (ha.symm.trans hb)
      have hy := y.isLt
      change n + u.val = y.val at he
      omega
  | @trans a b c h₁ h₂ ih₁ ih₂ =>
      rintro u y rfl rfl
      induction b using Fin.addCases with
      | left z =>
          obtain ⟨x,word,ho,hu⟩ := ih₁ u z rfl rfl
          exact ⟨x,word,ho,upper_post φ hu ((support_old_iff φ added bots tops hc z y).mp h₂)⟩
      | right z =>
          obtain rfl := (support_fresh_iff φ added bots tops hc u z).mp h₁
          exact ih₂ u y rfl rfl
  | @decomp a b ha hb hp i ih =>
      intro u y heL heR
      change b ∈ φ.upper.map (renameBound (Fin.castAdd m)) at hb
      obtain ⟨b₀,hb₀,rfl⟩ := List.mem_map.mp hb
      have hey : b₀.2 i = y := Fin.ext (congrArg (fun z : Fin (n + m) => z.val) heR)
      subst y
      change a ∈ φ.lower.map (renameBound (Fin.castAdd m)) ++ added at ha
      rcases List.mem_append.mp ha with haOld | haNew
      · obtain ⟨a₀,_,rfl⟩ := List.mem_map.mp haOld
        have he := congrArg (fun z : Fin (n + m) => z.val) heL
        have hx := (a₀.2 i).isLt
        change (a₀.2 i).val = n + u.val at he
        omega
      · generalize hparent : a.1 = parent at hp ih
        induction parent using Fin.addCases with
        | left x =>
            refine ⟨x,[i],Origin.first haNew hparent heL,?_⟩
            exact .cons ⟨b₀,hb₀,(support_old_iff φ added bots tops hc x b₀.1).mp hp,.refl _⟩ (.nil (.refl _))
        | right v =>
            obtain ⟨x,word,ho,hu⟩ := ih v b₀.1 rfl rfl
            refine ⟨x,word ++ [i],Origin.snoc ho haNew hparent heL,?_⟩
            exact upper_append φ hu (.cons ⟨b₀,hb₀,.refl _,.refl _⟩ (.nil (.refl _)))

theorem cross_support (u : Fin m) (y : Fin n) (h : Cross φ added u y) :
    Support Ψ (Fin.natAdd n u) (Fin.castAdd m y) := by
  obtain ⟨x,word,ho,hu⟩ := h
  have hl := origin_lower φ added bots tops ho
  have hu' := (upper_path_old_iff φ added bots tops hc x y word).mpr hu
  have hz : UpperPath Ψ (Fin.natAdd n u) [] (Fin.castAdd m y) :=
    cancel_lower_upper Ψ word hl (by simpa only [List.append_nil] using hu')
  cases hz with | nil hs => exact hs

theorem fresh_old_support_iff (u : Fin m) (y : Fin n) :
    Support Ψ (Fin.natAdd n u) (Fin.castAdd m y) ↔ Cross φ added u y :=
  ⟨fun h => support_cross φ added bots tops hc h u y rfl rfl,
    cross_support φ added bots tops hc u y⟩

theorem fresh_upper_iff (u : Fin m) (y : Fin n) (path : List (Fin d)) :
    UpperPath Ψ (Fin.natAdd n u) path (Fin.castAdd m y) ↔
      ∃ x word, Origin added x word u ∧ UpperPath φ x (word ++ path) y := by
  constructor
  · intro h
    cases h with
    | nil hs =>
        simpa only [List.append_nil, Cross] using (fresh_old_support_iff φ added bots tops hc u y).mp hs
    | @cons _ z _ i path hs ht =>
        obtain ⟨a,ha,hsrc,hend⟩ := hs
        change a ∈ φ.upper.map (renameBound (Fin.castAdd m)) at ha
        obtain ⟨a₀,ha₀,rfl⟩ := List.mem_map.mp ha
        obtain ⟨x,word,ho,hu⟩ := (fresh_old_support_iff φ added bots tops hc u a₀.1).mp hsrc
        obtain ⟨z₀,rfl,hz⟩ := upper_path_from_old φ added bots tops hc [] (a₀.2 i) z (.nil hend)
        cases hz with
        | nil hchild =>
            have ht' := (upper_path_old_iff φ added bots tops hc z₀ y path).mp ht
            exact ⟨x,word,ho,upper_append φ hu (.cons ⟨a₀,ha₀,.refl _,hchild⟩ ht')⟩
  · rintro ⟨x,word,ho,hu⟩
    have hl := origin_lower φ added bots tops ho
    have hu' := (upper_path_old_iff φ added bots tops hc x y (word ++ path)).mpr hu
    exact cancel_lower_upper Ψ word hl hu'

end Graft

end NSSE.SubtypeLowerGraftCross
