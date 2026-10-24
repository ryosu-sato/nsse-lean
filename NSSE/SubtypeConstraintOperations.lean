import NSSE.SubtypeConstraints

/-! # Literal constraint renaming and conjunction, with exact semantics -/

namespace NSSE.SubtypeConstraintOperations

open SubtypeConstraints

variable {n m d : Nat}

def renameBound (f : Fin n → Fin m) (a : BoundLiteral n d) : BoundLiteral m d :=
  (f a.1, fun i => f (a.2 i))

def rename (φ : Constraints n d) (f : Fin n → Fin m) : Constraints m d where
  upper := φ.upper.map (renameBound f)
  lower := φ.lower.map (renameBound f)
  bot := φ.bot.map f
  top := φ.top.map f

def combine (φ ψ : Constraints n d) : Constraints n d where
  upper := φ.upper ++ ψ.upper
  lower := φ.lower ++ ψ.lower
  bot := φ.bot ++ ψ.bot
  top := φ.top ++ ψ.top

variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

theorem satisfies_rename (F : Constructor T d) (φ : Constraints n d) (f : Fin n → Fin m)
    (ρ : Fin m → T) : Satisfies F (rename φ f) ρ ↔ Satisfies F φ (fun x => ρ (f x)) := by
  constructor
  · intro h
    exact ⟨fun a ha => h.1 _ (List.mem_map.mpr ⟨a,ha,rfl⟩),
      fun a ha => h.2.1 _ (List.mem_map.mpr ⟨a,ha,rfl⟩),
      fun x hx => h.2.2.1 _ (List.mem_map.mpr ⟨x,hx,rfl⟩),
      fun x hx => h.2.2.2 _ (List.mem_map.mpr ⟨x,hx,rfl⟩)⟩
  · intro h
    refine ⟨?_,?_,?_,?_⟩
    · intro a ha
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      exact h.1 b hb
    · intro a ha
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      exact h.2.1 b hb
    · intro x hx
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
      exact h.2.2.1 y hy
    · intro x hx
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
      exact h.2.2.2 y hy

theorem satisfies_combine (F : Constructor T d) (φ ψ : Constraints n d) (ρ : Fin n → T) :
    Satisfies F (combine φ ψ) ρ ↔ Satisfies F φ ρ ∧ Satisfies F ψ ρ := by
  simp only [combine, Satisfies, List.mem_append, or_imp, forall_and]
  tauto

end NSSE.SubtypeConstraintOperations
