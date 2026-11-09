import NSSE.MultiConstructorModelRays
import NSSE.MultiConstructorUnifiedExistence

/-! An actual original countermodel supplies a unified word. Thus a
negative U-existence decision proves original arbitrary-tree entailment. -/
namespace NSSE.MultiConstructorCountermodelWord
open MultiConstructorTrees MultiConstructorConstraints MultiConstructorUnifiedWords
open MultiConstructorRawValidity MultiConstructorModelTokens MultiConstructorModelDomains MultiConstructorModelRays
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

def Heads (rho : Fin n → Tree arity) (x y : Fin n) (w : List (Fin D)) (heads : Fin w.length → H) : Prop :=
  ∀ k, (along rho x w k.val).label [] = .node (heads k) ∧
    (along rho y w k.val).label [] = .node (heads k) ∧ w[k.val].val < arity (heads k)

omit [DecidableEq H] in
theorem endpoint_constraints (rho : Fin n → Tree arity) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (hh : Heads rho x y w heads)
    (hb : ¬(along rho x w w.length).label [] ≤ (along rho y w w.length).label [])
    (k : Nat) (hk : k ≤ w.length) :
    (along rho x w k).label [] ≠ .bot ∧ (along rho y w k).label [] ≠ .top := by
  by_cases hlt : k < w.length
  · have ht := hh ⟨k,hlt⟩
    rw [ht.1,ht.2.1]
    constructor <;> intro h <;> cases h
  · have he : k = w.length := by omega
    subst k
    change ¬Label.Below _ _ at hb
    exact ⟨fun h => hb (Or.inl h),fun h => hb (Or.inr (Or.inl h))⟩

omit [DecidableEq H] in
theorem value_actual (rho : Fin n → Tree arity) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (hh : Heads rho x y w heads) (k : Nat) (hk : k ≤ w.length) (side : Bool) :
    value w heads ((along rho x w w.length).label []) ((along rho y w w.length).label []) side k =
      (along rho (if side then y else x) w k).label [] := by
  by_cases hlt : k < w.length
  · rw [value,dif_pos hlt]
    cases side
    · exact (hh ⟨k,hlt⟩).1.symm
    · exact (hh ⟨k,hlt⟩).2.1.symm
  · have he : k = w.length := by omega
    subst k
    rw [value,dif_neg (Nat.lt_irrefl _)]
    cases side <;> rfl

theorem assignment (phi : Constraints arity n) (rho : Fin n → Tree arity) (hs : Satisfies allAlgebra phi rho)
    (x y : Fin n) (w : List (Fin D)) (heads : Fin w.length → H) (hh : Heads rho x y w heads)
    (hb : ¬(along rho x w w.length).label [] ≤ (along rho y w w.length).label []) :
    Assignment phi x y w heads ((along rho x w w.length).label []) ((along rho y w w.length).label []) := by
  have he := endpoint_constraints rho x y w heads hh hb
  have hd (k : Nat) (hk : k ≤ w.length) := valid_domains phi rho hs (row phi x y w k)
    (along rho x w k) (along rho y w k) (row_bounds phi rho hs x y w k hk).1
    (row_bounds phi rho hs x y w k hk).2 (he k hk).1 (he k hk).2
  refine ⟨?_,?_,?_⟩
  · intro k
    have hl := hd k.val k.isLt.le
    have ht := hh k
    rw [ht.1,ht.2.1] at hl
    exact ⟨hl.1,(common_domains phi _ _).mp hl.2,ht.2.2⟩
  · have hl := hd w.length le_rfl
    exact ⟨hl.1,hl.2.1,hl.2.2,fun h => hb (le_of_eq h)⟩
  · intro a b l hborn ha hb' hm
    rw [value_actual rho x y w heads hh _ ha false,value_actual rho x y w heads hh _ hb' true]
    exact label_agree _ _ (he _ ha).1 (he _ hb').2 ((ray_order phi rho hs x y w a b l ha hb' hborn hm) [])

theorem path_witness (phi : Constraints arity n) (rho : Fin n → Tree arity) (hs : Satisfies allAlgebra phi rho)
    (x y : Fin n) (w : List (Fin D)) (hp : MultiConstructorFirstPath.Path D (rho x) (rho y) w) : Witness phi x y w := by
  obtain ⟨heads,hh⟩ := MultiConstructorFirstPath.proper_heads hp
  have hheads : Heads rho x y w heads := by
    intro k
    simpa only [along_label] using hh k
  have hb : ¬(along rho x w w.length).label [] ≤ (along rho y w w.length).label [] := by
    simpa only [along_label,List.take_length] using MultiConstructorFirstPath.terminal_bad hp
  exact ⟨heads,_,_,assignment phi rho hs x y w heads hheads hb⟩

theorem countermodel_word (phi : Constraints arity n) (rho : Fin n → Tree arity) (hs : Satisfies allAlgebra phi rho)
    (x y : Fin n) (hD : ∀ h, arity h ≤ D) (hn : ¬rho x ≤ rho y) :
    ∃ w : List (Fin D), Witness phi x y w := by
  obtain ⟨w,hw⟩ := MultiConstructorFirstPath.of_not_le hD (rho x) (rho y) hn
  exact ⟨w,path_witness phi rho hs x y w hw⟩

theorem no_word_entails (Q : Query arity n) (hD : ∀ h, arity h ≤ D)
    (hn : ∀ w : List (Fin D), ¬Witness Q.constraints Q.left Q.right w) : Entails allAlgebra Q := by
  intro rho hs
  by_contra h
  obtain ⟨w,hw⟩ := countermodel_word Q.constraints rho hs Q.left Q.right hD h
  exact hn w hw

theorem negative_entails [Fintype H] (Q : Query arity n)
    (hn : MultiConstructorUnifiedExistence.decideExists Q.constraints Q.left Q.right
      (MultiConstructorFirstPath.alphabetSize arity) = false) : Entails allAlgebra Q :=
  no_word_entails Q MultiConstructorFirstPath.arity_le_alphabet
    ((MultiConstructorUnifiedExistence.decideExists_false _ _ _ _).mp hn)

omit [DecidableEq H] in
theorem all_entails_finite (Q : Query arity n) (hq : Entails allAlgebra Q) : Entails finiteAlgebra Q := by
  intro rho hs
  have hh := hq (fun x => MultiConstructorFiniteTrees.embed (rho x))
    ((finite_satisfies_iff Q.constraints rho).mpr hs)
  exact MultiConstructorFiniteTrees.le_of_embed_le hh

theorem negative_entails_finite [Fintype H] (Q : Query arity n)
    (hn : MultiConstructorUnifiedExistence.decideExists Q.constraints Q.left Q.right
      (MultiConstructorFirstPath.alphabetSize arity) = false) : Entails finiteAlgebra Q :=
  all_entails_finite Q (negative_entails Q hn)

end NSSE.MultiConstructorCountermodelWord
