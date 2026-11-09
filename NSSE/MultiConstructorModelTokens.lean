import NSSE.MultiConstructorUnifiedPrefix
import NSSE.MultiConstructorFirstPath

/-! Original token rows carry actual tree inequalities along every
finite word. This semantic invariant does not assume an admissible word. -/
namespace NSSE.MultiConstructorModelTokens
open MultiConstructorTrees MultiConstructorConstraints MultiConstructorTokens
open MultiConstructorUnifiedWords MultiConstructorUnifiedPrefix
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

omit [DecidableEq H] in
theorem project_nil (t : Tree arity) : MultiConstructorTrees.Tree.project t [] = t := by
  apply MultiConstructorTrees.Tree.ext
  intro w
  rfl

omit [DecidableEq H] in
theorem project_append (t : Tree arity) (p q : List Nat) :
    MultiConstructorTrees.Tree.project t (p++q) =
      MultiConstructorTrees.Tree.project (MultiConstructorTrees.Tree.project t p) q := by
  apply MultiConstructorTrees.Tree.ext
  intro w
  exact congrArg t.label (List.append_assoc p q w)

def along (rho : Fin n → Tree arity) (x : Fin n) (w : List (Fin D)) (k : Nat) : Tree arity :=
  MultiConstructorTrees.Tree.project (rho x) ((w.take k).map Fin.val)

omit [DecidableEq H] in
theorem at_zero (rho : Fin n → Tree arity) (x : Fin n) (w : List (Fin D)) : along rho x w 0 = rho x :=
  project_nil (rho x)

omit [DecidableEq H] in
theorem at_succ (rho : Fin n → Tree arity) (x : Fin n) (w : List (Fin D)) (k : Nat) (hk : k < w.length) :
    along rho x w (k+1) = MultiConstructorTrees.Tree.project (along rho x w k) [w[k].val] := by
  simp only [along,List.take_succ_eq_append_getElem hk,List.map_append,List.map_cons,List.map_nil]
  exact project_append _ _ _

theorem upper_step (phi : Constraints arity n) (rho : Fin n → Tree arity) (hs : Satisfies allAlgebra phi rho)
    (t : Tree arity) (S : Tokens n) (hu : ∀ u ∈ S, t ≤ rho u) (i : Nat) :
    ∀ v ∈ upperNext phi S i, MultiConstructorTrees.Tree.project t [i] ≤ rho v := by
  intro v hv
  obtain ⟨a,ha,⟨u,huS,hua⟩,j,hji,hjv⟩ := (mem_upperNext phi S i v).mp hv
  have h := MultiConstructorTrees.Tree.project_mono
    ((hu u huS).trans ((support_sound allAlgebra phi rho hs hua).trans (hs.1 a ha))) [j.val]
  change MultiConstructorTrees.Tree.project t [j.val] ≤
    MultiConstructorTrees.Tree.project (MultiConstructorTrees.Tree.node a.head (fun j => rho (a.children j))) [j.val] at h
  rw [MultiConstructorTrees.Tree.project_node] at h
  rw [hji] at h
  exact h.trans (support_sound allAlgebra phi rho hs hjv)

theorem lower_step (phi : Constraints arity n) (rho : Fin n → Tree arity) (hs : Satisfies allAlgebra phi rho)
    (t : Tree arity) (S : Tokens n) (hl : ∀ v ∈ S, rho v ≤ t) (i : Nat) :
    ∀ u ∈ lowerNext phi S i, rho u ≤ MultiConstructorTrees.Tree.project t [i] := by
  intro u hu
  obtain ⟨a,ha,⟨v,hvS,hav⟩,j,hji,huj⟩ := (mem_lowerNext phi S i u).mp hu
  have h := MultiConstructorTrees.Tree.project_mono
    ((hs.2.1 a ha).trans ((support_sound allAlgebra phi rho hs hav).trans (hl v hvS))) [j.val]
  change MultiConstructorTrees.Tree.project
    (MultiConstructorTrees.Tree.node a.head (fun j => rho (a.children j))) [j.val] ≤
      MultiConstructorTrees.Tree.project t [j.val] at h
  rw [MultiConstructorTrees.Tree.project_node] at h
  rw [hji] at h
  exact (support_sound allAlgebra phi rho hs huj).trans h

theorem row_bounds (phi : Constraints arity n) (rho : Fin n → Tree arity) (hs : Satisfies allAlgebra phi rho)
    (x y : Fin n) (w : List (Fin D)) (k : Nat) (hk : k ≤ w.length) :
    (∀ u ∈ (row phi x y w k).1, along rho x w k ≤ rho u) ∧
    (∀ v ∈ (row phi x y w k).2, rho v ≤ along rho y w k) := by
  induction k with
  | zero =>
    rw [at_zero,at_zero]
    constructor
    · intro u hu
      obtain ⟨t,ht,htu⟩ := (mem_up phi {x} u).mp hu
      have he : t = x := Finset.mem_singleton.mp ht
      subst t
      exact support_sound allAlgebra phi rho hs htu
    · intro v hv
      obtain ⟨t,ht,hvt⟩ := (mem_down phi {y} v).mp hv
      have he : t = y := Finset.mem_singleton.mp ht
      subst t
      exact support_sound allAlgebra phi rho hs hvt
  | succ k ih =>
    have hkn : k < w.length := by omega
    have hb := ih (by omega)
    rw [row_succ phi x y w k hkn,at_succ rho x w k hkn,at_succ rho y w k hkn]
    exact ⟨upper_step phi rho hs _ _ hb.1 _,lower_step phi rho hs _ _ hb.2 _⟩

end NSSE.MultiConstructorModelTokens
