import NSSE.SubtypeLowerGraftCross

/-! # Mixed lower paths split with a common actual-Origin suffix

The first old/fresh crossing proves the paper v1346 normal form. Once a
lower path is fresh, every step is an actual added edge, not just support.
-/

namespace NSSE.SubtypeLowerGraftSuffix

open SubtypeConstraints SubtypeConstraintOperations SubtypePathBounds
open SubtypeLowerGraft SubtypeLowerGraftPaths SubtypeLowerGraftCross

variable {n m d : Nat}

inductive AddedWalk (added : List (BoundLiteral (n + m) d)) :
    Fin m → List (Fin d) → Fin m → Prop
  | nil (u : Fin m) : AddedWalk added u [] u
  | cons {a : BoundLiteral (n + m) d} {u v z : Fin m} {i : Fin d} {word : List (Fin d)}
      (ha : a ∈ added) (hp : a.1 = Fin.natAdd n u) (hc : a.2 i = Fin.natAdd n v)
      (h : AddedWalk added v word z) : AddedWalk added u (i :: word) z

theorem origin_append {added : List (BoundLiteral (n + m) d)} {x u v word tail}
    (ho : Origin added x word u) (hw : AddedWalk added u tail v) :
    Origin added x (word ++ tail) v := by
  induction hw generalizing x word with
  | nil u => simpa only [List.append_nil] using ho
  | cons ha hp hc _ ih =>
      simpa only [List.append_assoc, List.singleton_append] using ih (Origin.snoc ho ha hp hc)

theorem first_walk {added : List (BoundLiteral (n + m) d)}
    {a : BoundLiteral (n + m) d} {x u v i tail}
    (ha : a ∈ added) (hp : a.1 = Fin.castAdd m x) (hc : a.2 i = Fin.natAdd n u)
    (hw : AddedWalk added u tail v) : Origin added x (i :: tail) v :=
  origin_append (Origin.first ha hp hc) hw

theorem walk_lower (φ : Constraints n d) (added : List (BoundLiteral (n + m) d))
    (bots tops : List (Fin (n + m))) {u v word} (hw : AddedWalk added u word v) :
    LowerPath (graft φ added bots tops) (Fin.natAdd n u) word (Fin.natAdd n v) := by
  induction hw with
  | nil u => exact .nil (.refl _)
  | cons ha hp hc _ ih =>
      refine .cons ⟨_,List.mem_append_right _ ha,?_,?_⟩ ih
      · rw [hc]; exact .refl _
      · rw [hp]; exact .refl _

section Graft

variable (φ : Constraints n d) (added : List (BoundLiteral (n + m) d))
variable (bots tops : List (Fin (n + m))) (hc : FreshChildren added)
include hc

local notation "Ψ" => graft φ added bots tops

theorem fresh_child_iff (u v : Fin m) (i : Fin d) :
    SupportedLower Ψ (Fin.natAdd n u) i (Fin.natAdd n v) ↔
      ∃ a ∈ added, a.1 = Fin.natAdd n u ∧ a.2 i = Fin.natAdd n v := by
  constructor
  · rintro ⟨a,ha,hv,hp⟩
    change a ∈ φ.lower.map (renameBound (Fin.castAdd m)) ++ added at ha
    rcases List.mem_append.mp ha with ho | hn
    · obtain ⟨a₀,_,rfl⟩ := List.mem_map.mp ho
      exact False.elim (no_old_fresh φ added bots tops hc a₀.1 u hp)
    · obtain ⟨z,hz⟩ := hc a hn i
      rw [hz] at hv
      have hvz := (support_fresh_iff φ added bots tops hc v z).mp hv
      have hchild := hz.trans (congrArg (Fin.natAdd n) hvz.symm)
      generalize hparent : a.1 = parent at hp
      induction parent using Fin.addCases with
      | left x => exact False.elim (no_old_fresh φ added bots tops hc x u hp)
      | right t =>
          have htu := (support_fresh_iff φ added bots tops hc t u).mp hp
          exact ⟨a,hn,hparent.trans (congrArg (Fin.natAdd n) htu),hchild⟩
  · rintro ⟨a,ha,hp,hchild⟩
    refine ⟨a,List.mem_append_right _ ha,?_,?_⟩
    · rw [hchild]; exact .refl _
    · rw [hp]; exact .refl _

theorem fresh_path_iff (u v : Fin m) (path : List (Fin d)) :
    LowerPath Ψ (Fin.natAdd n u) path (Fin.natAdd n v) ↔ AddedWalk added u path v := by
  constructor
  · intro h
    induction path generalizing u v with
    | nil =>
        cases h with
        | nil hs =>
            obtain rfl := (support_fresh_iff φ added bots tops hc v u).mp hs
            exact .nil _
    | cons i path ih =>
        cases h with
        | @cons _ z _ _ _ hs ht =>
            induction z using Fin.addCases with
            | left x => exact False.elim (no_lower_fresh_old φ added bots tops hc u x i hs)
            | right z =>
                obtain ⟨a,ha,hp,hchild⟩ := (fresh_child_iff φ added bots tops hc u z i).mp hs
                exact .cons ha hp hchild (ih z v ht)
  · exact walk_lower φ added bots tops

theorem mixed_lower_exists (path : List (Fin d)) (y : Fin n) (u : Fin m)
    (h : LowerPath Ψ (Fin.castAdd m y) path (Fin.natAdd n u)) :
    ∃ x a b r z, Origin added x (a ++ r) u ∧ UpperPath φ x a z ∧
      LowerPath φ y b z ∧ path = b ++ r := by
  induction path generalizing y u with
  | nil =>
      cases h with
      | nil hs =>
          obtain ⟨x,a,ho,hu⟩ := (fresh_old_support_iff φ added bots tops hc u y).mp hs
          exact ⟨x,a,[],[],y,by simpa only [List.append_nil] using ho,hu,.nil (.refl _),rfl⟩
  | cons i path ih =>
      cases h with
      | @cons _ v _ _ _ hs ht =>
          induction v using Fin.addCases with
          | left v =>
              obtain ⟨x,a,b,r,z,ho,hu,hl,he⟩ := ih v u ht
              exact ⟨x,a,i :: b,r,z,ho,hu,
                .cons (lower_child_old φ added bots tops hc y v i hs) hl,
                by simp only [he, List.cons_append]⟩
          | right v =>
              have hw := (fresh_path_iff φ added bots tops hc v u path).mp ht
              obtain ⟨l,hl,hv,hy⟩ := hs
              change l ∈ φ.lower.map (renameBound (Fin.castAdd m)) ++ added at hl
              rcases List.mem_append.mp hl with ho | hn
              · obtain ⟨l₀,hl₀,rfl⟩ := List.mem_map.mp ho
                obtain ⟨x,a,ho,hu⟩ := (fresh_old_support_iff φ added bots tops hc v (l₀.2 i)).mp hv
                refine ⟨x,a,[i],path,l₀.2 i,origin_append ho hw,hu,?_,rfl⟩
                exact .cons ⟨l₀,hl₀,.refl _,(support_old_iff φ added bots tops hc l₀.1 y).mp hy⟩
                  (.nil (.refl _))
              · obtain ⟨v',hv'⟩ := hc l hn i
                rw [hv'] at hv
                have hvv := (support_fresh_iff φ added bots tops hc v v').mp hv
                have hchild := hv'.trans (congrArg (Fin.natAdd n) hvv.symm)
                generalize hparent : l.1 = parent at hy
                induction parent using Fin.addCases with
                | left x =>
                    exact ⟨x,[],[],i :: path,x,first_walk hn hparent hchild hw,.nil (.refl _),
                      .nil ((support_old_iff φ added bots tops hc x y).mp hy),rfl⟩
                | right t =>
                    obtain ⟨x,a,ho,hu⟩ := (fresh_old_support_iff φ added bots tops hc t y).mp hy
                    refine ⟨x,a,[],i :: path,y,?_,hu,.nil (.refl _),rfl⟩
                    simpa only [List.append_assoc, List.singleton_append] using
                      origin_append (Origin.snoc ho hn hparent hchild) hw

/-- The SAME suffix occurs in the literal added Origin and in the lower
path. No SAT, acyclicity, positive arity, or word-length premise is used. -/
theorem fresh_lower_iff (u : Fin m) (y : Fin n) (path : List (Fin d)) :
    LowerPath Ψ (Fin.castAdd m y) path (Fin.natAdd n u) ↔
      ∃ x a b r z, Origin added x (a ++ r) u ∧ UpperPath φ x a z ∧
        LowerPath φ y b z ∧ path = b ++ r := by
  constructor
  · exact mixed_lower_exists φ added bots tops hc path y u
  · rintro ⟨x,a,b,r,z,ho,hu,hl,rfl⟩
    have ho' := origin_lower φ added bots tops ho
    have hu' := (upper_path_old_iff φ added bots tops hc x z a).mpr hu
    have hr := cancel_upper_lower Ψ a hu' ho'
    exact lower_append Ψ ((lower_path_old_iff φ added bots tops hc y z b).mpr hl) hr

end Graft

end NSSE.SubtypeLowerGraftSuffix
