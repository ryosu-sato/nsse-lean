import NSSE.MultiConstructorSpineInput

/-! Every actual model of the concrete one-sided spine extension is an
original countermodel. This theorem does not assume or prove extension SAT. -/
namespace NSSE.MultiConstructorSpineSemantics
open MultiConstructorTrees MultiConstructorConstraints MultiConstructorSpineInput MultiConstructorSpineInput.Data
variable {H : Type*} {arity : H → Nat} {n D : Nat}
variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

def Requirements (S : Data arity n D) : Prop :=
  (∀ k : Fin S.word.length, S.word[k.val].val < arity (S.heads k)) ∧
    S.endX ≠ .bot ∧ S.endY ≠ .top ∧ S.endX ≠ S.endY

theorem assignment_requirements [DecidableEq H] (S : Data arity n D) (phi : Constraints arity n)
    (ha : MultiConstructorUnifiedWords.Assignment phi S.left S.right S.word S.heads S.endX S.endY) :
    Requirements S := by
  refine ⟨fun k => (ha.1 k).2.2,?_,?_,ha.2.1.2.2.2⟩
  · intro he
    have hh := ha.2.1.2.1
    rw [he] at hh
    exact hh
  · intro he
    have hh := ha.2.1.2.2.1
    rw [he] at hh
    exact hh

theorem original_and_seeds (F : Algebra (arity := arity) T) (S : Data arity n D)
    (phi : Constraints arity n) (rho : Fin S.size → T) (hs : Satisfies F (S.program phi) rho) :
    Satisfies F phi (fun x => rho (S.old x)) ∧ Satisfies F S.seeds rho := by
  obtain ⟨ho,hseed⟩ := (MultiConstructorInputMap.append_iff F _ _ rho).mp hs
  exact ⟨(MultiConstructorInputMap.rename_iff F phi S.old rho).mp ho,hseed⟩

theorem ordered_next (F : Algebra (arity := arity) T) (S : Data arity n D) (rho : Fin S.size → T)
    (hs : Satisfies F S.seeds rho) (k : Fin S.word.length)
    (hi : S.word[k.val].val < arity (S.heads k))
    (ho : rho (S.xAt (S.here k)) ≤ rho (S.yAt (S.here k))) :
    rho (S.xAt (S.after k)) ≤ rho (S.yAt (S.after k)) := by
  have h := (hs.2.1 (S.lower k) (lower_mem S k)).trans (ho.trans (hs.1 (S.upper k) (upper_mem S k)))
  have hc := (F.node_le_node (S.heads k) _ _).mp h ⟨S.word[k.val].val,hi⟩
  simpa only [lower,upper,if_pos rfl] using hc

theorem ordered_terminal (F : Algebra (arity := arity) T) (S : Data arity n D) (rho : Fin S.size → T)
    (hs : Satisfies F S.seeds rho) (hr : Requirements S)
    (ho : rho (S.old S.left) ≤ rho (S.old S.right)) : rho (S.xAt S.last) ≤ rho (S.yAt S.last) := by
  have h : ∀ k, ∀ hk : k ≤ S.word.length,
      rho (S.xAt ⟨k,by omega⟩) ≤ rho (S.yAt ⟨k,by omega⟩) := by
    intro k
    induction k with
    | zero => intro hk; simpa only [x_zero,y_zero] using ho
    | succ k ih =>
      intro hk
      exact ordered_next F S rho hs ⟨k,by omega⟩ (hr.1 ⟨k,by omega⟩) (ih (by omega))
  exact h S.word.length le_rfl

theorem terminal_not_ordered (F : Algebra (arity := arity) T) (S : Data arity n D) (rho : Fin S.size → T)
    (hs : Satisfies F S.seeds rho) (hr : Requirements S) : ¬rho (S.xAt S.last) ≤ rho (S.yAt S.last) := by
  intro ho
  cases hx : S.endX with
  | bot => exact hr.2.1 hx
  | top =>
    have htop := hs.2.2.2 _ (top_end_mem S hx)
    cases hy : S.endY with
    | top => exact hr.2.2.1 hy
    | bot =>
      have hbot := hs.2.2.1 _ (bot_end_mem S hy)
      rw [htop,hbot] at ho
      exact F.top_not_le_bot ho
    | node g =>
      have hu := hs.1 _ (upper_end_mem S g hy)
      rw [htop] at ho
      exact F.top_not_le_node g _ (ho.trans hu)
  | node h =>
    have hl := hs.2.1 _ (lower_end_mem S h hx)
    cases hy : S.endY with
    | top => exact hr.2.2.1 hy
    | bot =>
      have hbot := hs.2.2.1 _ (bot_end_mem S hy)
      rw [hbot] at ho
      exact F.node_not_le_bot h _ (hl.trans ho)
    | node g =>
      have hu := hs.1 _ (upper_end_mem S g hy)
      have he : h = g := F.head_eq _ _ _ _ (hl.trans (ho.trans hu))
      exact hr.2.2.2 (hx.trans ((congrArg Label.node he).trans hy.symm))

theorem seed_countermodel (F : Algebra (arity := arity) T) (S : Data arity n D) (rho : Fin S.size → T)
    (hs : Satisfies F S.seeds rho) (hr : Requirements S) : ¬rho (S.old S.left) ≤ rho (S.old S.right) :=
  fun ho => terminal_not_ordered F S rho hs hr (ordered_terminal F S rho hs hr ho)

theorem original_countermodel (F : Algebra (arity := arity) T) (S : Data arity n D)
    (phi : Constraints arity n) (rho : Fin S.size → T) (hs : Satisfies F (S.program phi) rho)
    (hr : Requirements S) :
    Satisfies F phi (fun x => rho (S.old x)) ∧ ¬rho (S.old S.left) ≤ rho (S.old S.right) := by
  have hh := original_and_seeds F S phi rho hs
  exact ⟨hh.1,seed_countermodel F S rho hh.2 hr⟩

theorem extension_not_entails (F : Algebra (arity := arity) T) (S : Data arity n D)
    (phi : Constraints arity n) (hr : Requirements S) (he : Satisfiable F (S.program phi)) :
    ¬Entails F (⟨phi,S.left,S.right⟩ : Query arity n) := by
  rintro hen
  obtain ⟨rho,hs⟩ := he
  have hh := original_countermodel F S phi rho hs hr
  exact hh.2 (hen _ hh.1)

end NSSE.MultiConstructorSpineSemantics
