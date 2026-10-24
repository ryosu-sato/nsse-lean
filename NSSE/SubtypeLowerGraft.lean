import NSSE.SubtypeSupportOperations

/-! # Lower-only fresh-child grafts preserve all old variable support

The invariant separates old/old, old/fresh, fresh/old and fresh/fresh.
No satisfiability or semantic-entailment conservation is claimed here.
-/

namespace NSSE.SubtypeLowerGraft

open SubtypeConstraints SubtypeConstraintOperations SubtypeSupportOperations

variable {n m d : Nat}

def graft (φ : Constraints n d) (added : List (BoundLiteral (n + m) d))
    (bots tops : List (Fin (n + m))) : Constraints (n + m) d where
  upper := φ.upper.map (renameBound (Fin.castAdd m))
  lower := φ.lower.map (renameBound (Fin.castAdd m)) ++ added
  bot := φ.bot.map (Fin.castAdd m) ++ bots
  top := φ.top.map (Fin.castAdd m) ++ tops

def FreshChildren (added : List (BoundLiteral (n + m) d)) : Prop :=
  ∀ a ∈ added, ∀ i, ∃ z : Fin m, a.2 i = Fin.natAdd n z

def Relation (φ : Constraints n d) (a b : Fin (n + m)) : Prop :=
  Fin.addCases
    (fun x => Fin.addCases (fun y => Support φ x y) (fun _ => False) b)
    (fun u => Fin.addCases (fun _ => True) (fun v => u = v) b) a

@[simp] theorem relation_old_old (φ : Constraints n d) (x y : Fin n) :
    Relation φ (Fin.castAdd m x) (Fin.castAdd m y) ↔ Support φ x y := by
  simp only [Relation, Fin.addCases_left]

@[simp] theorem relation_old_fresh (φ : Constraints n d) (x : Fin n) (y : Fin m) :
    Relation φ (Fin.castAdd m x) (Fin.natAdd n y) ↔ False := by
  simp only [Relation, Fin.addCases_left, Fin.addCases_right]

@[simp] theorem relation_fresh_old (φ : Constraints n d) (x : Fin m) (y : Fin n) :
    Relation φ (Fin.natAdd n x) (Fin.castAdd m y) := by
  simp only [Relation, Fin.addCases_left, Fin.addCases_right]

@[simp] theorem relation_fresh_fresh (φ : Constraints n d) (x y : Fin m) :
    Relation φ (Fin.natAdd n x) (Fin.natAdd n y) ↔ x = y := by
  simp only [Relation, Fin.addCases_right]

theorem relation_refl (φ : Constraints n d) (a : Fin (n + m)) : Relation φ a a := by
  induction a using Fin.addCases with
  | left x => exact (relation_old_old φ x x).mpr (.refl _)
  | right x => exact (relation_fresh_fresh φ x x).mpr rfl

theorem relation_trans (φ : Constraints n d) (a b c : Fin (n + m)) :
    Relation φ a b → Relation φ b c → Relation φ a c := by
  induction a using Fin.addCases with
  | left x =>
      induction b using Fin.addCases with
      | left y =>
          induction c using Fin.addCases with
          | left z =>
              intro h₁ h₂
              exact (relation_old_old φ x z).mpr (.trans
                ((relation_old_old φ x y).mp h₁) ((relation_old_old φ y z).mp h₂))
          | right z => intro _ h₂; exact False.elim ((relation_old_fresh φ y z).mp h₂)
      | right y => intro h₁ _; exact False.elim ((relation_old_fresh φ x y).mp h₁)
  | right x =>
      induction b using Fin.addCases with
      | left y =>
          induction c using Fin.addCases with
          | left z => intro _ _; exact relation_fresh_old φ x z
          | right z => intro _ h₂; exact False.elim ((relation_old_fresh φ y z).mp h₂)
      | right y =>
          intro h₁ h₂
          obtain rfl := (relation_fresh_fresh φ x y).mp h₁
          exact h₂

theorem support_relation (φ : Constraints n d) (added : List (BoundLiteral (n + m) d))
    (bots tops : List (Fin (n + m))) (hc : FreshChildren added)
    {a b : Fin (n + m)} (h : Support (graft φ added bots tops) a b) : Relation φ a b := by
  induction h with
  | refl a => exact relation_refl φ a
  | trans _ _ ih₁ ih₂ => exact relation_trans φ _ _ _ ih₁ ih₂
  | @decomp a b ha hb _ i ih =>
      change b ∈ φ.upper.map (renameBound (Fin.castAdd m)) at hb
      obtain ⟨b₀,hb₀,rfl⟩ := List.mem_map.mp hb
      change a ∈ φ.lower.map (renameBound (Fin.castAdd m)) ++ added at ha
      rcases List.mem_append.mp ha with haOld | haNew
      · obtain ⟨a₀,ha₀,rfl⟩ := List.mem_map.mp haOld
        exact (relation_old_old φ _ _).mpr (.decomp ha₀ hb₀ ((relation_old_old φ _ _).mp ih) i)
      · obtain ⟨z,hz⟩ := hc a haNew i
        rw [hz]
        exact relation_fresh_old φ z (b₀.2 i)

theorem support_lift (φ : Constraints n d) (added : List (BoundLiteral (n + m) d))
    (bots tops : List (Fin (n + m))) {x y : Fin n} (h : Support φ x y) :
    Support (graft φ added bots tops) (Fin.castAdd m x) (Fin.castAdd m y) := by
  apply support_map φ _ (Fin.castAdd m) ?_ ?_ h
  · intro a ha
    exact List.mem_append_left _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
  · intro a ha
    exact List.mem_map.mpr ⟨a,ha,rfl⟩

theorem support_old_iff (φ : Constraints n d) (added : List (BoundLiteral (n + m) d))
    (bots tops : List (Fin (n + m))) (hc : FreshChildren added) (x y : Fin n) :
    Support (graft φ added bots tops) (Fin.castAdd m x) (Fin.castAdd m y) ↔ Support φ x y :=
  ⟨fun h => (relation_old_old φ x y).mp (support_relation φ added bots tops hc h),
    support_lift φ added bots tops⟩

theorem no_old_fresh (φ : Constraints n d) (added : List (BoundLiteral (n + m) d))
    (bots tops : List (Fin (n + m))) (hc : FreshChildren added) (x : Fin n) (y : Fin m) :
    ¬ Support (graft φ added bots tops) (Fin.castAdd m x) (Fin.natAdd n y) :=
  fun h => (relation_old_fresh φ x y).mp (support_relation φ added bots tops hc h)

theorem support_fresh_iff (φ : Constraints n d) (added : List (BoundLiteral (n + m) d))
    (bots tops : List (Fin (n + m))) (hc : FreshChildren added) (x y : Fin m) :
    Support (graft φ added bots tops) (Fin.natAdd n x) (Fin.natAdd n y) ↔ x = y := by
  constructor
  · intro h
    exact (relation_fresh_fresh φ x y).mp (support_relation φ added bots tops hc h)
  · rintro rfl
    exact .refl _

end NSSE.SubtypeLowerGraft
