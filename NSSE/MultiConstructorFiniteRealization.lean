import NSSE.MultiConstructorSpineCycles
import NSSE.MultiConstructorFiniteDecision
import NSSE.MultiConstructorSpineRealization

/-! A finite-SAT original input and a successful U-assignment produce an
actual finite original countermodel through the concrete spine extension. -/
namespace NSSE.MultiConstructorFiniteRealization
open MultiConstructorConstraints MultiConstructorUnifiedWords MultiConstructorFiniteTrees
open MultiConstructorSpineInput MultiConstructorSpineInput.Data
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

def model (phi : Constraints arity n) (S : Data arity n D) (v : Fin n) : Tree arity :=
  MultiConstructorShapeGrammar.model (S.program phi) (S.old v)

theorem extension_satisfies (phi : Constraints arity n) (S : Data arity n D)
    (hs : Satisfiable finiteAlgebra phi)
    (ha : Assignment phi S.left S.right S.word S.heads S.endX S.endY) :
    Satisfies finiteAlgebra (S.program phi) (MultiConstructorShapeGrammar.model (S.program phi)) := by
  obtain ⟨hn,hc⟩ := (MultiConstructorFiniteModel.satisfiable_iff phi).mp hs
  exact MultiConstructorFiniteModel.satisfies _ (MultiConstructorSpineClash.no_clash phi S hn ha)
    (MultiConstructorSpineCycles.no_cycle phi S hc)

theorem assignment_countermodel (phi : Constraints arity n) (S : Data arity n D)
    (hs : Satisfiable finiteAlgebra phi)
    (ha : Assignment phi S.left S.right S.word S.heads S.endX S.endY) :
    Satisfies finiteAlgebra phi (model phi S) ∧ ¬model phi S S.left ≤ model phi S S.right :=
  MultiConstructorSpineSemantics.original_countermodel finiteAlgebra S phi _ (extension_satisfies phi S hs ha)
    (MultiConstructorSpineSemantics.assignment_requirements S phi ha)

theorem height_bound (phi : Constraints arity n) (S : Data arity n D)
    (hs : Satisfiable finiteAlgebra phi)
    (ha : Assignment phi S.left S.right S.word S.heads S.endX S.endY) (v : Fin n) :
    height (model phi S v) ≤ S.size*S.size :=
  (MultiConstructorFiniteModel.small_model _ ⟨_,extension_satisfies phi S hs ha⟩).2 (S.old v)

theorem word_countermodel (phi : Constraints arity n) (x y : Fin n)
    (hs : Satisfiable finiteAlgebra phi) (w : List (Fin D)) (hw : Witness phi x y w) :
    ∃ rho : Fin n → Tree arity, Satisfies finiteAlgebra phi rho ∧ ¬rho x ≤ rho y := by
  obtain ⟨heads,ex,ey,ha⟩ := hw
  exact ⟨model phi ⟨x,y,w,heads,ex,ey⟩,assignment_countermodel phi ⟨x,y,w,heads,ex,ey⟩ hs ha⟩

theorem countermodel_transfer (Q : Query arity n) (hD : ∀ h, arity h ≤ D)
    (hs : Satisfiable finiteAlgebra Q.constraints) (hn : ¬Entails allAlgebra Q) :
    ¬Entails finiteAlgebra Q := by
  obtain ⟨_,w,hw⟩ := (MultiConstructorSpineRealization.countermodel_iff Q hD).mp hn
  obtain ⟨rho,hr,hxy⟩ := word_countermodel Q.constraints Q.left Q.right hs w hw
  exact fun hq => hxy (hq rho hr)

omit [DecidableEq H] in
theorem all_entails_finite (Q : Query arity n) (he : Entails allAlgebra Q) : Entails finiteAlgebra Q := by
  intro rho hs
  exact (embed_le_embed _ _).mp (he (fun x => embed (rho x)) ((finite_satisfies_iff _ rho).mpr hs))

theorem entailment_iff (Q : Query arity n) (hD : ∀ h, arity h ≤ D) :
    Entails finiteAlgebra Q ↔ ¬Satisfiable finiteAlgebra Q.constraints ∨ Entails allAlgebra Q := by
  constructor
  · intro he
    by_cases hs : Satisfiable finiteAlgebra Q.constraints
    · right
      by_contra hn
      exact countermodel_transfer Q hD hs hn he
    · exact Or.inl hs
  · rintro (hs | he)
    · exact entails_of_unsatisfiable finiteAlgebra Q hs
    · exact all_entails_finite Q he

theorem bounded_countermodel (Q : Query arity n) (hD : ∀ h, arity h ≤ D)
    (hs : Satisfiable finiteAlgebra Q.constraints) (hn : ¬Entails allAlgebra Q) :
    ∃ S : Data arity n D, S.left = Q.left ∧ S.right = Q.right ∧
      S.word.length ≤ MultiConstructorUnifiedBound.bound n D ∧
      Satisfies finiteAlgebra Q.constraints (model Q.constraints S) ∧
      ¬model Q.constraints S Q.left ≤ model Q.constraints S Q.right ∧
      ∀ v, height (model Q.constraints S v) ≤ (n+2*MultiConstructorUnifiedBound.bound n D+2)^2 := by
  obtain ⟨_,hw⟩ := (MultiConstructorSpineRealization.countermodel_iff Q hD).mp hn
  obtain ⟨w,⟨heads,ex,ey,ha⟩,hb⟩ := MultiConstructorUnifiedBound.exists_short Q.constraints Q.left Q.right hw
  let S : Data arity n D := ⟨Q.left,Q.right,w,heads,ex,ey⟩
  have hm := assignment_countermodel Q.constraints S hs ha
  refine ⟨S,rfl,rfl,hb,hm.1,hm.2,?_⟩
  intro v
  have hh := height_bound Q.constraints S hs ha v
  have hsize : S.size ≤ n+2*MultiConstructorUnifiedBound.bound n D+2 := by dsimp [S,size]; omega
  exact hh.trans (by simpa only [pow_two] using Nat.mul_le_mul hsize hsize)

end NSSE.MultiConstructorFiniteRealization
