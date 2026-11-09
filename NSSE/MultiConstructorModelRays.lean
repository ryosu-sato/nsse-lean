import NSSE.MultiConstructorModelDomains

/-! Actual support births and equal literal factors propagate genuine
tree inequalities. Allowed endpoint labels turn those inequalities into Agree. -/
namespace NSSE.MultiConstructorModelRays
open MultiConstructorTrees MultiConstructorConstraints MultiConstructorUnifiedWords MultiConstructorModelTokens
open P0ProperWords
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

omit [DecidableEq H] in
theorem along_label (rho : Fin n → Tree arity) (x : Fin n) (w : List (Fin D)) (k : Nat) :
    (along rho x w k).label [] = (rho x).label ((w.take k).map Fin.val) := by
  simp only [along,MultiConstructorTrees.Tree.project_label,List.append_nil]

omit [DecidableEq H] in
theorem match_order (rho : Fin n → Tree arity) (x y : Fin n) (w : List (Fin D))
    (a b l : Nat) (ha : a+l ≤ w.length) (hb : b+l ≤ w.length)
    (hm : WordMatch w a b l) (hab : along rho x w a ≤ along rho y w b) :
    along rho x w (a+l) ≤ along rho y w (b+l) := by
  induction l with
  | zero => exact hab
  | succ l ih =>
    have hal : a+l < w.length := by omega
    have hbl : b+l < w.length := by omega
    have he : w[a+l] = w[b+l] := by
      simpa only [List.getElem?_eq_getElem hal,List.getElem?_eq_getElem hbl,Option.some.injEq]
        using hm l (by omega)
    have hh := ih (by omega) (by omega) (fun i hi => hm i (by omega))
    rw [Nat.add_succ,Nat.add_succ,at_succ rho x w (a+l) hal,at_succ rho y w (b+l) hbl,← he]
    exact MultiConstructorTrees.Tree.project_mono hh _

theorem ray_order (phi : Constraints arity n) (rho : Fin n → Tree arity) (hs : Satisfies allAlgebra phi rho)
    (x y : Fin n) (w : List (Fin D)) (a b l : Nat) (ha : a+l ≤ w.length) (hb : b+l ≤ w.length)
    (hborn : Born phi x y w a b) (hm : WordMatch w a b l) :
    along rho x w (a+l) ≤ along rho y w (b+l) := by
  obtain ⟨u,hu,v,hv,huv⟩ := hborn
  have hU := (row_bounds phi rho hs x y w a (by omega)).1 u hu
  have hL := (row_bounds phi rho hs x y w b (by omega)).2 v hv
  exact match_order rho x y w a b l ha hb hm
    (hU.trans ((support_sound allAlgebra phi rho hs huv).trans hL))

omit [DecidableEq H] in
theorem label_agree (ex ey : Label H) (hx : ex ≠ .bot) (hy : ey ≠ .top) (hle : ex ≤ ey) :
    P0DZBranch.Agree ex ey := by
  rcases hle with he | he | he
  · exact False.elim (hx he)
  · exact False.elim (hy he)
  · subst ey
    cases ex with
    | bot => exact False.elim (hx rfl)
    | top => exact False.elim (hy rfl)
    | node _ => rfl

end NSSE.MultiConstructorModelRays
