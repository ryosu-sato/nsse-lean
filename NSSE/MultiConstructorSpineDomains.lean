import NSSE.MultiConstructorSpineBoundary

/-! A successful U-assignment controls original literal demands at every
bounded position, including the two distinct terminal domains. -/
namespace NSSE.MultiConstructorSpineDomains
open MultiConstructorTrees MultiConstructorConstraints MultiConstructorTokens MultiConstructorRawValidity
open MultiConstructorUnifiedWords MultiConstructorSpineInput MultiConstructorSpineInput.Data
open MultiConstructorSpineRelation MultiConstructorSpineBoundary
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

theorem facts (phi : Constraints arity n) (S : Data arity n D)
    (ha : Assignment phi S.left S.right S.word S.heads S.endX S.endY) (i : Fin (S.word.length+1)) :
    Valid phi (row phi S.left S.right S.word i.val) ∧
    UpperDomain phi (row phi S.left S.right S.word i.val) (value S.word S.heads S.endX S.endY false i.val) ∧
    LowerDomain phi (row phi S.left S.right S.word i.val) (value S.word S.heads S.endX S.endY true i.val) := by
  by_cases hi : i.val < S.word.length
  · have hd := (common_domains phi _ (S.heads ⟨i.val,hi⟩)).mpr (ha.1 ⟨i.val,hi⟩).2.1
    simpa only [value,dif_pos hi] using And.intro (ha.1 ⟨i.val,hi⟩).1 hd
  · have he : i.val = S.word.length := by have := i.isLt; omega
    rw [he]
    simpa [value] using And.intro ha.2.1.1 (And.intro ha.2.1.2.1 ha.2.1.2.2.1)

theorem upper_domain_pin (phi : Constraints arity n) (s : MultiConstructorRawTrace.Row n)
    (e : Label H) (hd : UpperDomain phi s e) (h : H) (hp : h ∈ upperPins phi s.1) : e ≤ .node h := by
  cases e with
  | bot => exact False.elim hd
  | top => rw [hd] at hp; exact False.elim (Finset.not_mem_empty _ hp)
  | node g => exact (Label.node_le_node g h).mpr (hd h hp).symm

theorem lower_domain_pin (phi : Constraints arity n) (s : MultiConstructorRawTrace.Row n)
    (e : Label H) (hd : LowerDomain phi s e) (h : H) (hp : h ∈ lowerPins phi s.2) : .node h ≤ e := by
  cases e with
  | bot => rw [hd] at hp; exact False.elim (Finset.not_mem_empty _ hp)
  | top => exact False.elim hd
  | node g => exact (Label.node_le_node h g).mpr (hd h hp)

theorem x_original (phi : Constraints arity n) (S : Data arity n D)
    (ha : Assignment phi S.left S.right S.word S.heads S.endX S.endY)
    (i : Fin (S.word.length+1)) (b : Bound arity n) (hb : b ∈ phi.upper)
    (hr : relation phi S (S.xAt i) (S.old b.parent)) :
    value S.word S.heads S.endX S.endY false i.val ≤ .node b.head := by
  apply upper_domain_pin phi _ _ (facts phi S ha i).2.1 b.head
  exact (mem_upperPins phi _ _).mpr ⟨b,hb,⟨b.parent,(x_old phi S _ _).mp hr,.refl _⟩,rfl⟩

theorem original_y (phi : Constraints arity n) (S : Data arity n D)
    (ha : Assignment phi S.left S.right S.word S.heads S.endX S.endY)
    (a : Bound arity n) (ha' : a ∈ phi.lower) (j : Fin (S.word.length+1))
    (hr : relation phi S (S.old a.parent) (S.yAt j)) :
    .node a.head ≤ value S.word S.heads S.endX S.endY true j.val := by
  apply lower_domain_pin phi _ _ (facts phi S ha j).2.2 a.head
  exact (mem_lowerPins phi _ _).mpr ⟨a,ha',⟨a.parent,(old_y phi S _ _).mp hr,.refl _⟩,rfl⟩

theorem x_no_bot (phi : Constraints arity n) (S : Data arity n D)
    (ha : Assignment phi S.left S.right S.word S.heads S.endX S.endY)
    (i : Fin (S.word.length+1)) (v : Fin n) (hv : v ∈ phi.bot) :
    ¬relation phi S (S.xAt i) (S.old v) := by
  intro hr
  exact (facts phi S ha i).1.2.2.1 v ((x_old phi S _ _).mp hr) v hv (.refl _)

theorem no_top_y (phi : Constraints arity n) (S : Data arity n D)
    (ha : Assignment phi S.left S.right S.word S.heads S.endX S.endY)
    (v : Fin n) (hv : v ∈ phi.top) (j : Fin (S.word.length+1)) :
    ¬relation phi S (S.old v) (S.yAt j) := by
  intro hr
  exact (facts phi S ha j).1.2.2.2 v ((old_y phi S _ _).mp hr) v hv (.refl _)

omit [DecidableEq H] in
theorem agree_below (a b : Label H) (ha : P0DZBranch.Agree a b) : a ≤ b := by
  cases a <;> cases b <;> simp_all [P0DZBranch.Agree,Label.node_le_node]

theorem x_y_labels (phi : Constraints arity n) (S : Data arity n D)
    (ha : Assignment phi S.left S.right S.word S.heads S.endX S.endY)
    (i j : Fin (S.word.length+1)) (hr : relation phi S (S.xAt i) (S.yAt j)) :
    value S.word S.heads S.endX S.endY false i.val ≤ value S.word S.heads S.endX S.endY true j.val := by
  apply agree_below
  exact MultiConstructorUnifiedRays.active_agree phi S.left S.right S.word S.heads S.endX S.endY ha
    S.word.length j.val i.val (by have := j.isLt; omega) (by have := i.isLt; omega)
    ((x_y phi S i j).mp hr)

end NSSE.MultiConstructorSpineDomains
