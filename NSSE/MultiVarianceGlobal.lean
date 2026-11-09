import NSSE.MultiVarianceFlatSpine

/-!
A globally indexed ACTUAL four-form input for every finite signed spine.

At depth d the variables are x_0,y_0,...,x_d,y_d,B,T, numbered
0,...,2*d+3. The genuine lower/upper/extremal lists are remapped from
the already kernel-checked six-slot and four-slot local templates.
This module introduces no independently split positive/negative values.

The next obligation is the semantic theorem relating satisfiability of
the SINGLE global Constraints object to the compositional FlatSpine.Formula.
-/
namespace NSSE.MultiVarianceGlobal
open MultiConstructorConstraints (Bound Constraints)
open MultiVarianceConstraints MultiVarianceEncoding MultiVarianceTrees
open MultiVarianceSpineSeparation
variable {H : Type*} {arity : H → Nat}
variable (pol : Polarity arity)

def mapBound {m k : Nat} (f : Fin m → Fin k)
    (b : Bound arity m) : Bound arity k :=
  ⟨f b.parent, b.head, fun i => f (b.children i)⟩

def remap {m k : Nat} (f : Fin m → Fin k)
    (phi : Constraints arity m) : Constraints arity k :=
  ⟨phi.upper.map (mapBound f), phi.lower.map (mapBound f),
    phi.bot.map f, phi.top.map f⟩

theorem satisfies_remap {m k : Nat} (f : Fin m → Fin k)
    (phi : Constraints arity m) (rho : Fin k → Tree pol) :
    Satisfies (remap f phi) rho ↔ Satisfies phi (fun x => rho (f x)) := by
  simp [Satisfies, remap, mapBound]

def combine {m : Nat} (a b : Constraints arity m) : Constraints arity m :=
  ⟨a.upper ++ b.upper, a.lower ++ b.lower, a.bot ++ b.bot, a.top ++ b.top⟩

theorem satisfies_combine {m : Nat} (a b : Constraints arity m)
    (rho : Fin m → Tree pol) :
    Satisfies (combine a b) rho ↔ Satisfies a rho ∧ Satisfies b rho := by
  unfold Satisfies
  simp only [combine, List.mem_append, or_imp, forall_and]
  tauto

/-- Two rails at each of d+1 levels and two shared extremal variables. -/
def width (d : Nat) : Nat := 2*d+4

@[simp] theorem width_zero : width 0 = 4 := rfl
@[simp] theorem width_succ (d : Nat) : width (d+1) = width d+2 := by
  simp [width]; omega

def rootX (d : Nat) : Fin (width d) := ⟨0,by simp [width]⟩
def rootY (d : Nat) : Fin (width d) := ⟨1,by simp [width]⟩
def bottomAt (d : Nat) : Fin (width d) :=
  ⟨2*d+2,by simp [width]⟩
def topAt (d : Nat) : Fin (width d) :=
  ⟨2*d+3,by simp [width]⟩

/-- Previous tail levels begin at the next pair. Its extrema also shift. -/
def shift (d : Nat) (k : Fin (width d)) : Fin (width (d+1)) :=
  ⟨k.val+2,by have h := k.isLt; simp only [width] at h ⊢; omega⟩

/-- A six-slot local step: slots 0..3 stay, slots 4,5 use shared B,T. -/
def stepEmbed (d : Nat) (k : Fin 6) : Fin (width (d+1)) :=
  if hk : k.val < 4 then
    ⟨k.val,by simp only [width]; omega⟩
  else
    ⟨k.val+2*d,by have h:=k.isLt; simp only [width] at h ⊢; omega⟩

@[simp] theorem shift_rootX (d : Nat) :
    shift d (rootX d) = (⟨2,by simp [width]⟩ : Fin (width (d+1))) := by
  apply Fin.ext
  rfl

@[simp] theorem shift_rootY (d : Nat) :
    shift d (rootY d) = (⟨3,by simp [width]⟩ : Fin (width (d+1))) := by
  apply Fin.ext
  rfl

@[simp] theorem shift_bottom (d : Nat) :
    shift d (bottomAt d) = bottomAt (d+1) := by
  apply Fin.ext
  dsimp [shift, bottomAt]
  omega

@[simp] theorem shift_top (d : Nat) :
    shift d (topAt d) = topAt (d+1) := by
  apply Fin.ext
  dsimp [shift, topAt]
  omega

@[simp] theorem stepEmbed_bot (d : Nat) :
    stepEmbed d 4 = bottomAt (d+1) := by
  apply Fin.ext
  change 4 + 2*d = 2*(d+1)+2
  omega

@[simp] theorem stepEmbed_top (d : Nat) :
    stepEmbed d 5 = topAt (d+1) := by
  apply Fin.ext
  change 5 + 2*d = 2*(d+1)+3
  omega

/-- A SINGLE ordinary four-form Constraints object, with a Fin index type
whose size is determined only by the number of proper spine steps. -/
def compile : (s : Spine arity) → Constraints arity (width s.depth)
  | .stop a b => MultiVarianceFlatStop.stopConstraints pol a b
  | .step h i s =>
      combine
        (remap (stepEmbed s.depth) (MultiVarianceFlatStep.stepConstraints pol h i))
        (remap (shift s.depth) (compile s))

theorem compile_step (h : H) (i : Fin (arity h)) (s : Spine arity) :
    compile pol (.step h i s) =
      combine
        (remap (stepEmbed s.depth) (MultiVarianceFlatStep.stepConstraints pol h i))
        (remap (shift s.depth) (compile pol s)) := rfl

end NSSE.MultiVarianceGlobal
