import NSSE.MultiVarianceGlobalComplete

/-! One actual signed four-form extension of the ORIGINAL input.
The two spine roots alias the query variables, even when those coincide.
Exactly 2*depth+2 variables are fresh; original values are retained literally. -/
namespace NSSE.MultiVarianceOriginalSpine
open MultiConstructorConstraints (Constraints Query)
open MultiVarianceEncoding MultiVarianceTrees MultiVarianceConstraints
open MultiVarianceSpineSeparation MultiVarianceGlobal
variable {H : Type*} {arity : H → Nat} {n : Nat}

def count (n d : Nat) : Nat := n+2*d+2

def old (d : Nat) (x : Fin n) : Fin (count n d) :=
  ⟨x.val, by have hx := x.isLt; simp only [count]; omega⟩

/-- The first two slots are the actual query roots; every other slot is fresh. -/
def slot (x y : Fin n) (d : Nat) (k : Fin (width d)) : Fin (count n d) :=
  if k.val = 0 then old d x else if k.val = 1 then old d y
  else ⟨n+(k.val-2), by have hk := k.isLt; simp only [count, width] at *; omega⟩

@[simp] theorem slot_rootX (x y : Fin n) (d : Nat) :
    slot x y d (rootX d) = old d x := rfl

@[simp] theorem slot_rootY (x y : Fin n) (d : Nat) :
    slot x y d (rootY d) = old d y := rfl

variable (pol : Polarity arity)

def glue {d : Nat} (rho : Fin n → Tree pol) (sigma : Fin (width d) → Tree pol)
    (k : Fin (count n d)) : Tree pol :=
  if hk : k.val < n then rho ⟨k.val,hk⟩
  else sigma ⟨k.val-n+2, by have hi := k.isLt; simp only [count, width] at *; omega⟩

@[simp] theorem glue_old {d : Nat} (rho : Fin n → Tree pol)
    (sigma : Fin (width d) → Tree pol) (x : Fin n) :
    glue pol rho sigma (old d x) = rho x := by
  simp only [glue, old, x.isLt, dif_pos]

theorem glue_slot {d : Nat} (x y : Fin n) (rho : Fin n → Tree pol)
    (sigma : Fin (width d) → Tree pol)
    (hx : sigma (rootX d) = rho x) (hy : sigma (rootY d) = rho y) :
    (fun k => glue pol rho sigma (slot x y d k)) = sigma := by
  funext k
  by_cases h0 : k.val = 0
  · have he : k = rootX d := Fin.ext h0
    subst k
    rw [slot_rootX, glue_old, hx]
  by_cases h1 : k.val = 1
  · have he : k = rootY d := Fin.ext h1
    subst k
    rw [slot_rootY, glue_old, hy]
  have hn : ¬ n+(k.val-2) < n := by omega
  simp only [slot, h0, h1, if_false, glue, hn, dif_neg]
  apply congrArg sigma
  apply Fin.ext
  simp only [Fin.val_mk]
  omega

def extension (Q : Query arity n) (s : Spine arity) : Constraints arity (count n s.depth) :=
  combine (remap (old s.depth) Q.constraints)
    (remap (slot Q.left Q.right s.depth) (compile pol s))

theorem extension_parts (Q : Query arity n) (s : Spine arity)
    (rho : Fin (count n s.depth) → Tree pol) :
    Satisfies (extension pol Q s) rho ↔
      Satisfies Q.constraints (fun x => rho (old s.depth x)) ∧
      Satisfies (compile pol s) (fun k => rho (slot Q.left Q.right s.depth k)) := by
  rw [extension, satisfies_combine, satisfies_remap, satisfies_remap]

theorem extension_to_formula (Q : Query arity n) (s : Spine arity)
    (rho : Fin (count n s.depth) → Tree pol) (hs : Satisfies (extension pol Q s) rho) :
    MultiVarianceFlatSpine.Formula (pol := pol) s
      (rho (old s.depth Q.left)) (rho (old s.depth Q.right)) := by
  have hc := ((extension_parts pol Q s rho).mp hs).2
  simpa only [slot_rootX, slot_rootY] using
    MultiVarianceGlobalSound.compile_to_formula pol s _ hc

theorem extension_countermodel (Q : Query arity n) (s : Spine arity) (hv : s.Valid)
    (rho : Fin (count n s.depth) → Tree pol) (hs : Satisfies (extension pol Q s) rho) :
    Satisfies Q.constraints (fun x => rho (old s.depth x)) ∧
      ¬rho (old s.depth Q.left) ≤ rho (old s.depth Q.right) :=
  ⟨((extension_parts pol Q s rho).mp hs).1,
    MultiVarianceFlatSpine.formula_not_ordered pol s hv _ _
      (extension_to_formula pol Q s rho hs)⟩

theorem extend_model (Q : Query arity n) (s : Spine arity)
    (rho : Fin n → Tree pol) (hr : Satisfies Q.constraints rho)
    (hf : MultiVarianceFlatSpine.Formula (pol := pol) s (rho Q.left) (rho Q.right)) :
    ∃ tau : Fin (count n s.depth) → Tree pol,
      Satisfies (extension pol Q s) tau ∧ ∀ x, tau (old s.depth x) = rho x := by
  obtain ⟨sigma,hs,hx,hy⟩ :=
    MultiVarianceGlobalComplete.formula_to_compile pol s _ _ hf
  refine ⟨glue pol rho sigma, ?_, glue_old pol rho sigma⟩
  apply (extension_parts pol Q s _).mpr
  constructor
  · simpa only [glue_old] using hr
  · rw [glue_slot pol Q.left Q.right rho sigma hx hy]
    exact hs

theorem satisfiable_extension_iff (Q : Query arity n) (s : Spine arity) :
    Satisfiable pol (extension pol Q s) ↔
      ∃ rho : Fin n → Tree pol, Satisfies Q.constraints rho ∧
        MultiVarianceFlatSpine.Formula (pol := pol) s (rho Q.left) (rho Q.right) := by
  constructor
  · rintro ⟨rho,hs⟩
    exact ⟨fun x => rho (old s.depth x), ((extension_parts pol Q s rho).mp hs).1,
      extension_to_formula pol Q s rho hs⟩
  · rintro ⟨rho,hr,hf⟩
    obtain ⟨tau,hs,_⟩ := extend_model pol Q s rho hr hf
    exact ⟨tau,hs⟩

/-- Original nonentailment is exactly existence of a satisfiable ACTUAL
four-form signed spine extension. The spine quantifier is still unbounded. -/
theorem not_entails_iff_extension (Q : Query arity n) :
    ¬ Entails pol Q ↔ ∃ s : Spine arity, s.Valid ∧ Satisfiable pol (extension pol Q s) := by
  constructor
  · intro hn
    obtain ⟨rho,hr,s,hv,hf⟩ := (MultiVarianceFlatSpine.not_entails_iff_formula pol Q).mp hn
    exact ⟨s,hv,(satisfiable_extension_iff pol Q s).mpr ⟨rho,hr,hf⟩⟩
  · rintro ⟨s,hv,rho,hs⟩ he
    obtain ⟨hr,hn⟩ := extension_countermodel pol Q s hv rho hs
    exact hn (he _ hr)

theorem self_extension_unsatisfiable (Q : Query arity n) (he : Q.left = Q.right)
    (s : Spine arity) (hv : s.Valid) : ¬Satisfiable pol (extension pol Q s) := by
  rintro ⟨rho,hs⟩
  have hn := (extension_countermodel pol Q s hv rho hs).2
  rw [he] at hn
  exact hn le_rfl

end NSSE.MultiVarianceOriginalSpine
