import NSSE.MultiConstructorSpineTags
import NSSE.MultiConstructorUnifiedRays

/-! A candidate support relation on actual spine variables. Its only
nontrivial fresh-to-fresh block consists of original XY copy rays. -/
namespace NSSE.MultiConstructorSpineRelation
open MultiConstructorConstraints MultiConstructorTokens MultiConstructorUnifiedWords MultiConstructorUnifiedPrefix
open MultiConstructorSpineInput MultiConstructorSpineInput.Data MultiConstructorSpineTags
open GeneralCopyGrid
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

def ray (phi : Constraints arity n) (S : Data arity n D) (i j : Nat) : Prop :=
  Active (MultiConstructorUnifiedRays.annotation phi S.left S.right S.word) S.word.length j i

def relationTag (phi : Constraints arity n) (S : Data arity n D) :
    Tag n S.word.length → Tag n S.word.length → Prop
  | .bot, _ => True
  | _, .top => True
  | .old u, .old v => Support phi u v
  | .x i, .old v => v ∈ (row phi S.left S.right S.word (i.val+1)).1
  | .old u, .y j => u ∈ (row phi S.left S.right S.word (j.val+1)).2
  | .x i, .y j => ray phi S (i.val+1) (j.val+1)
  | .x i, .x j => i = j
  | .y i, .y j => i = j
  | _, _ => False

def relation (phi : Constraints arity n) (S : Data arity n D) (a b : Fin S.size) : Prop :=
  relationTag phi S (decode S a) (decode S b)

theorem relation_encode (phi : Constraints arity n) (S : Data arity n D) (a b : Tag n S.word.length) :
    relation phi S (encode S a) (encode S b) ↔ relationTag phi S a b := by
  rw [relation,decode_encode,decode_encode]

theorem direct (phi : Constraints arity n) (S : Data arity n D) (i j : Nat) (hi : i ≤ S.word.length)
    (v : Fin n) (hu : v ∈ (row phi S.left S.right S.word i).1)
    (hl : v ∈ (row phi S.left S.right S.word j).2) : ray phi S i j := by
  apply (active_iff_ray _ S.word.length j i).mpr
  refine ⟨hi,i,j,0,by omega,by omega,?_,?_⟩
  · exact ⟨v,hu,hl⟩
  · intro k hk
    omega

theorem tag_refl (phi : Constraints arity n) (S : Data arity n D) (a : Tag n S.word.length) :
    relationTag phi S a a := by
  cases a <;> simp only [relationTag]
  exact Support.refl _

theorem tag_trans (phi : Constraints arity n) (S : Data arity n D) (a b c : Tag n S.word.length)
    (hab : relationTag phi S a b) (hbc : relationTag phi S b c) : relationTag phi S a c := by
  cases a <;> cases b <;> cases c <;> simp_all [relationTag]
  all_goals first
    | exact Support.trans hab hbc
    | exact (row_closed phi S.left S.right S.word _).1 _ hab _ hbc
    | exact (row_closed phi S.left S.right S.word _).2 _ hbc _ hab
    | exact direct phi S _ _ (by omega) _ hab hbc

theorem refl (phi : Constraints arity n) (S : Data arity n D) (a : Fin S.size) : relation phi S a a :=
  tag_refl phi S (decode S a)

theorem trans (phi : Constraints arity n) (S : Data arity n D) (a b c : Fin S.size)
    (hab : relation phi S a b) (hbc : relation phi S b c) : relation phi S a c :=
  tag_trans phi S (decode S a) (decode S b) (decode S c) hab hbc

end NSSE.MultiConstructorSpineRelation
