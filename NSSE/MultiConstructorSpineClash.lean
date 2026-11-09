import NSSE.MultiConstructorSpineClosure
import NSSE.MultiConstructorSpineDemands
import NSSE.MultiConstructorSpineDomains

/-! A successful U-assignment over a clash-free original input makes the
actual one-sided extension clash-free. All four literal clash forms are
excluded by their demands and the proved support certificate. -/
namespace NSSE.MultiConstructorSpineClash
open MultiConstructorTrees MultiConstructorConstraints MultiConstructorUnifiedWords
open MultiConstructorSpineInput MultiConstructorSpineInput.Data MultiConstructorSpineRelation
open MultiConstructorSpineBoundary MultiConstructorSpineFillers MultiConstructorSpineDemands
open MultiConstructorSpineDomains
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

theorem demands_compatible (phi : Constraints arity n) (S : Data arity n D) (hn : ¬LabelClash phi)
    (ha : Assignment phi S.left S.right S.word S.heads S.endX S.endY)
    {x y : Fin S.size} {e f : Label H} (hl : Lower phi S x e) (hu : Upper phi S y f)
    (hr : relation phi S x y) : e ≤ f := by
  cases hl with
  | original a hoa =>
    cases hu with
    | original b hob =>
      apply (Label.node_le_node _ _).mpr
      by_contra hne
      exact hn (Or.inr (Or.inr (Or.inr ⟨a,hoa,b,hob,(old_old phi S _ _).mp hr,hne⟩)))
    | extreme v hv => exact False.elim (hn (Or.inr (Or.inr (Or.inl ⟨a,hoa,v,hv,(old_old phi S _ _).mp hr⟩))))
    | spine j => exact original_y phi S ha a hoa j hr
    | filler => exact False.elim ((below_ne S _ (old_below S a.parent)).1 (bot_only phi S _ hr))
  | extreme u hut =>
    cases hu with
    | original b hob => exact False.elim (hn (Or.inr (Or.inl ⟨u,hut,b,hob,(old_old phi S _ _).mp hr⟩)))
    | extreme v hv => exact False.elim (hn (Or.inl ⟨u,hut,v,hv,(old_old phi S _ _).mp hr⟩))
    | spine j => exact False.elim (no_top_y phi S ha u hut j hr)
    | filler => exact False.elim ((below_ne S _ (old_below S u)).1 (bot_only phi S _ hr))
  | spine i =>
    cases hu with
    | original b hob => exact x_original phi S ha i b hob hr
    | extreme v hv => exact False.elim (x_no_bot phi S ha i v hv hr)
    | spine j => exact x_y_labels phi S ha i j hr
    | filler => exact False.elim ((below_ne S _ (x_below S i)).1 (bot_only phi S _ hr))
  | filler => exact False.elim (upper_ne_top phi S hu (top_only phi S _ hr))

theorem no_clash (phi : Constraints arity n) (S : Data arity n D) (hn : ¬LabelClash phi)
    (ha : Assignment phi S.left S.right S.word S.heads S.endX S.endY) : ¬LabelClash (S.program phi) := by
  rintro (⟨x,hx,y,hy,hxy⟩ | ⟨x,hx,b,hb,hxb⟩ | ⟨a,ha',y,hy,hay⟩ | ⟨a,ha',b,hb,hab,hne⟩)
  · have hh := demands_compatible phi S hn ha (top_view phi S x hx) (bot_view phi S y hy)
      (MultiConstructorSpineClosure.support phi S _ _ hxy)
    change Label.Below .top .bot at hh
    simp [Label.Below] at hh
  · exact Label.top_not_le_node b.head (demands_compatible phi S hn ha
      (top_view phi S x hx) (upper_view phi S b hb) (MultiConstructorSpineClosure.support phi S _ _ hxb))
  · exact Label.node_not_le_bot a.head (demands_compatible phi S hn ha
      (lower_view phi S a ha') (bot_view phi S y hy) (MultiConstructorSpineClosure.support phi S _ _ hay))
  · exact hne ((Label.node_le_node _ _).mp (demands_compatible phi S hn ha
      (lower_view phi S a ha') (upper_view phi S b hb) (MultiConstructorSpineClosure.support phi S _ _ hab)))

end NSSE.MultiConstructorSpineClash
