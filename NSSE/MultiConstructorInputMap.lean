import NSSE.MultiConstructorConstraints

/-! Renaming and conjunction preserve the actual four-form input
semantics for every constructor algebra, including both original tree models. -/
namespace NSSE.MultiConstructorInputMap
open MultiConstructorConstraints
variable {H : Type*} {arity : H → Nat} {n m : Nat}

def bound (f : Fin n → Fin m) (a : Bound arity n) : Bound arity m :=
  ⟨f a.parent,a.head,fun i => f (a.children i)⟩

def rename (phi : Constraints arity n) (f : Fin n → Fin m) : Constraints arity m :=
  ⟨phi.upper.map (bound f),phi.lower.map (bound f),phi.bot.map f,phi.top.map f⟩

def append (phi psi : Constraints arity n) : Constraints arity n :=
  ⟨phi.upper++psi.upper,phi.lower++psi.lower,phi.bot++psi.bot,phi.top++psi.top⟩

variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

theorem rename_iff (F : Algebra (arity := arity) T) (phi : Constraints arity n) (f : Fin n → Fin m)
    (rho : Fin m → T) : Satisfies F (rename phi f) rho ↔ Satisfies F phi (fun x => rho (f x)) := by
  constructor
  · intro hs
    exact ⟨fun a ha => hs.1 (bound f a) (List.mem_map_of_mem ha),
      fun a ha => hs.2.1 (bound f a) (List.mem_map_of_mem ha),
      fun x hx => hs.2.2.1 (f x) (List.mem_map_of_mem hx),
      fun x hx => hs.2.2.2 (f x) (List.mem_map_of_mem hx)⟩
  · intro hs
    refine ⟨?_,?_,?_,?_⟩
    · intro a ha
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      exact hs.1 b hb
    · intro a ha
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      exact hs.2.1 b hb
    · intro x hx
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
      exact hs.2.2.1 y hy
    · intro x hx
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
      exact hs.2.2.2 y hy

theorem append_iff (F : Algebra (arity := arity) T) (phi psi : Constraints arity n) (rho : Fin n → T) :
    Satisfies F (append phi psi) rho ↔ Satisfies F phi rho ∧ Satisfies F psi rho := by
  simp only [Satisfies,append,List.mem_append,or_imp,forall_and]
  tauto

end NSSE.MultiConstructorInputMap
