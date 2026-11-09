import NSSE.P0ProfileConfiguration

/-! Position sets indexed by normalized children, with a finite code for
the actual colors of the parent node. Codes reflect equality on that node. -/
namespace NSSE.P0ChildProfiles
open P0Cotree P0CotreeNormalize P0CotreeColors
variable {C : Type*}

theorem color_code (col : Nat → C) (U : Finset Nat) (k : Nat) (hk : 0 < k)
    [DecidableEq C] (hsize : (U.image col).card ≤ k) :
    ∃ code : Nat → Fin k, ∀ a ∈ U, ∀ b ∈ U, code a = code b ↔ col a = col b := by
  classical
  let P := U.image col
  let e := Fintype.equivFin {c // c ∈ P}
  have hb : Fintype.card {c // c ∈ P} ≤ k := by simpa only [Fintype.card_coe] using hsize
  let f : {c // c ∈ P} → Fin k := fun c => Fin.castLE hb (e c)
  have hf : Function.Injective f := (Fin.castLE_injective hb).comp e.injective
  let code : Nat → Fin k := fun a => if ha : col a ∈ P then f ⟨col a,ha⟩ else ⟨0,hk⟩
  refine ⟨code,?_⟩
  intro a ha b hb'
  have hpa : col a ∈ P := Finset.mem_image.mpr ⟨a,ha,rfl⟩
  have hpb : col b ∈ P := Finset.mem_image.mpr ⟨b,hb',rfl⟩
  simp only [code,dif_pos hpa,dif_pos hpb]
  constructor
  · intro he; exact congrArg Subtype.val (hf he)
  · intro he; exact congrArg f (Subtype.ext he)

def child (L : List (Tree Nat)) (i : Nat) : Tree Nat := L[i]?.getD (.leaf 0)

theorem child_eq (L : List (Tree Nat)) (i : Nat) (hi : i < L.length) :
    child L i = L[i] := by simp only [child,List.getElem?_eq_getElem hi,Option.getD_some]

theorem child_mem (L : List (Tree Nat)) (i : Nat) (hi : i < L.length) : child L i ∈ L := by
  rw [child_eq L i hi]
  exact List.getElem_mem hi

def sizeClass (L : List (Tree Nat)) (s : Nat) : Finset Nat :=
  (Finset.range L.length).filter (fun i => (leaves (child L i)).card = s)

theorem class_mem (L : List (Tree Nat)) (s i : Nat) :
    i ∈ sizeClass L s ↔ i < L.length ∧ (leaves (child L i)).card = s := by
  simp only [sizeClass,Finset.mem_filter,Finset.mem_range]

theorem children_disjoint (edge : Nat → Nat → Prop) (j : Bool) (l r : Tree Nat)
    (ht : Valid edge (.fork j l r)) (a b : Nat)
    (ha : a < (children (.fork j l r)).length) (hb : b < (children (.fork j l r)).length)
    (hne : a ≠ b) :
    Disjoint (leaves (child (children (.fork j l r)) a))
      (leaves (child (children (.fork j l r)) b)) := by
  have hh := List.pairwise_iff_getElem.mp (children_pairwise edge j l r ht)
  rw [child_eq _ a ha,child_eq _ b hb]
  rcases lt_or_gt_of_ne hne with hab | hba
  · exact (hh a b ha hb hab).1
  · exact (hh b a hb ha hba).1.symm

theorem children_inside (j : Bool) (l r : Tree Nat) (i : Nat)
    (hi : i < (children (.fork j l r)).length) :
    leaves (child (children (.fork j l r)) i) ⊆ leaves (.fork j l r) :=
  below_subset (children_below j l r _ (child_mem _ i hi))

end NSSE.P0ChildProfiles
