import NSSE.MultiConstructorSpineClash
import NSSE.MultiConstructorSpineSemantics
import NSSE.MultiConstructorCanonicalModel
import NSSE.MultiConstructorCountermodelWord

/-! Successful U-assignments now yield actual original countermodels by
unfolding a concrete finite graph. The original input must be clash-free;
the extension's satisfiability is proved, not supplied as an interface. -/
namespace NSSE.MultiConstructorSpineRealization
open MultiConstructorTrees MultiConstructorConstraints MultiConstructorUnifiedWords
open MultiConstructorSpineInput MultiConstructorSpineInput.Data
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

def model (phi : Constraints arity n) (S : Data arity n D) (v : Fin n) : Tree arity :=
  MultiConstructorCanonicalModel.model (S.program phi) (S.old v)

theorem extension_satisfies (phi : Constraints arity n) (S : Data arity n D) (hn : ¬LabelClash phi)
    (ha : Assignment phi S.left S.right S.word S.heads S.endX S.endY) :
    Satisfies allAlgebra (S.program phi) (MultiConstructorCanonicalModel.model (S.program phi)) :=
  MultiConstructorCanonicalModel.satisfies _ (MultiConstructorSpineClash.no_clash phi S hn ha)

theorem assignment_countermodel (phi : Constraints arity n) (S : Data arity n D) (hn : ¬LabelClash phi)
    (ha : Assignment phi S.left S.right S.word S.heads S.endX S.endY) :
    Satisfies allAlgebra phi (model phi S) ∧ ¬model phi S S.left ≤ model phi S S.right :=
  MultiConstructorSpineSemantics.original_countermodel allAlgebra S phi _ (extension_satisfies phi S hn ha)
    (MultiConstructorSpineSemantics.assignment_requirements S phi ha)

theorem word_countermodel (phi : Constraints arity n) (x y : Fin n) (hn : ¬LabelClash phi)
    (w : List (Fin D)) (hw : Witness phi x y w) :
    ∃ rho : Fin n → Tree arity, Satisfies allAlgebra phi rho ∧ ¬rho x ≤ rho y := by
  obtain ⟨heads,ex,ey,ha⟩ := hw
  exact ⟨model phi ⟨x,y,w,heads,ex,ey⟩,assignment_countermodel phi ⟨x,y,w,heads,ex,ey⟩ hn ha⟩

theorem countermodel_iff (Q : Query arity n) (hD : ∀ h, arity h ≤ D) :
    ¬Entails allAlgebra Q ↔ ¬LabelClash Q.constraints ∧
      ∃ w : List (Fin D), Witness Q.constraints Q.left Q.right w := by
  constructor
  · intro hn
    simp only [Entails,not_forall,_root_.not_imp] at hn
    obtain ⟨rho,hs,hxy⟩ := hn
    exact ⟨no_label_clash allAlgebra Q.constraints rho hs,
      MultiConstructorCountermodelWord.countermodel_word Q.constraints rho hs Q.left Q.right hD hxy⟩
  · rintro ⟨hn,w,hw⟩ hq
    obtain ⟨rho,hs,hxy⟩ := word_countermodel Q.constraints Q.left Q.right hn w hw
    exact hxy (hq rho hs)

theorem bounded_countermodel (Q : Query arity n) (hD : ∀ h, arity h ≤ D) (hn : ¬Entails allAlgebra Q) :
    ∃ S : Data arity n D, S.left = Q.left ∧ S.right = Q.right ∧
      S.word.length ≤ MultiConstructorUnifiedBound.bound n D ∧
      Satisfies allAlgebra Q.constraints (model Q.constraints S) ∧
      ¬model Q.constraints S Q.left ≤ model Q.constraints S Q.right := by
  obtain ⟨hc,hw⟩ := (countermodel_iff Q hD).mp hn
  obtain ⟨w,⟨heads,ex,ey,ha⟩,hb⟩ := MultiConstructorUnifiedBound.exists_short Q.constraints Q.left Q.right hw
  exact ⟨⟨Q.left,Q.right,w,heads,ex,ey⟩,rfl,rfl,hb,
    assignment_countermodel Q.constraints ⟨Q.left,Q.right,w,heads,ex,ey⟩ hc ha⟩

end NSSE.MultiConstructorSpineRealization
