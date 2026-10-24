import NSSE.SubtypePathBounds

/-! # Upper-only extension over an explicit ambient base predicate

Unused fresh slots may already belong to the ambient finite type. All
original constructor literals are contained in `Base`; added upper
children are outside it. No false ambient freshness premise is needed.
-/

namespace NSSE.SubtypeUpperExtension

open SubtypeConstraints SubtypeConstraintOperations SubtypePathBounds

variable {n d : Nat}

def graft (φ : Constraints n d) (added : List (BoundLiteral n d))
    (bots tops : List (Fin n)) : Constraints n d where
  upper := φ.upper ++ added
  lower := φ.lower
  bot := φ.bot ++ bots
  top := φ.top ++ tops

def Contained (φ : Constraints n d) (Base : Fin n → Prop) : Prop :=
  (∀ a ∈ φ.lower, Base a.1 ∧ ∀ i, Base (a.2 i)) ∧
  (∀ a ∈ φ.upper, Base a.1 ∧ ∀ i, Base (a.2 i))

def FreshChildren (added : List (BoundLiteral n d)) (Base : Fin n → Prop) : Prop :=
  ∀ a ∈ added, ∀ i, ¬ Base (a.2 i)

def Relation (φ : Constraints n d) (Base : Fin n → Prop) (a b : Fin n) : Prop :=
  (Base a ∧ Base b ∧ Support φ a b) ∨
  (Base a ∧ ¬ Base b) ∨ (¬ Base a ∧ ¬ Base b ∧ a = b)

theorem relation_refl (φ : Constraints n d) (Base : Fin n → Prop) (a : Fin n) :
    Relation φ Base a a := by
  by_cases ha : Base a
  · exact Or.inl ⟨ha,ha,.refl _⟩
  · exact Or.inr (Or.inr ⟨ha,ha,rfl⟩)

theorem relation_trans (φ : Constraints n d) (Base : Fin n → Prop)
    {a b c : Fin n} (h : Relation φ Base a b) (k : Relation φ Base b c) :
    Relation φ Base a c := by
  rcases h with ⟨ha,hb,hs⟩ | ⟨ha,hb⟩ | ⟨ha,hb,rfl⟩
  · rcases k with ⟨_,hc,ht⟩ | ⟨_,hc⟩ | ⟨hn,_,_⟩
    · exact Or.inl ⟨ha,hc,hs.trans ht⟩
    · exact Or.inr (Or.inl ⟨ha,hc⟩)
    · exact False.elim (hn hb)
  · rcases k with ⟨hb',_,_⟩ | ⟨hb',_⟩ | ⟨_,hc,_⟩
    · exact False.elim (hb hb')
    · exact False.elim (hb hb')
    · exact Or.inr (Or.inl ⟨ha,hc⟩)
  · exact k

theorem relation_base (φ : Constraints n d) (Base : Fin n → Prop)
    {a b : Fin n} (ha : Base a) (hb : Base b) (h : Relation φ Base a b) : Support φ a b := by
  rcases h with ⟨_,_,hs⟩ | ⟨_,hn⟩ | ⟨hn,_,_⟩
  · exact hs
  · exact False.elim (hn hb)
  · exact False.elim (hn ha)

section Extension

variable (φ : Constraints n d) (added : List (BoundLiteral n d))
variable (bots tops : List (Fin n)) (Base : Fin n → Prop)
variable (hc : Contained φ Base) (hf : FreshChildren added Base)
include hc hf

local notation "Ψ" => graft φ added bots tops

theorem support_relation {a b : Fin n} (h : Support Ψ a b) : Relation φ Base a b := by
  induction h with
  | refl a => exact relation_refl φ Base a
  | trans _ _ ih₁ ih₂ => exact relation_trans φ Base ih₁ ih₂
  | @decomp a b ha hb _ i ih =>
      change a ∈ φ.lower at ha
      change b ∈ φ.upper ++ added at hb
      rcases List.mem_append.mp hb with hb | hb
      · exact Or.inl ⟨(hc.1 a ha).2 i,(hc.2 b hb).2 i,
          .decomp ha hb (relation_base φ Base (hc.1 a ha).1 (hc.2 b hb).1 ih) i⟩
      · exact Or.inr (Or.inl ⟨(hc.1 a ha).2 i,hf b hb i⟩)

omit hc hf in
theorem support_lift {a b : Fin n} (h : Support φ a b) : Support Ψ a b := by
  induction h with
  | refl a => exact .refl _
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | decomp ha hb _ i ih => exact Support.decomp (φ := Ψ) ha (List.mem_append_left _ hb) ih i

theorem support_base_iff {a b : Fin n} (ha : Base a) (hb : Base b) :
    Support Ψ a b ↔ Support φ a b :=
  ⟨fun h => relation_base φ Base ha hb (support_relation φ added bots tops Base hc hf h),
    support_lift φ added bots tops⟩

theorem no_fresh_base {a b : Fin n} (ha : ¬ Base a) (hb : Base b) : ¬ Support Ψ a b := by
  intro h
  rcases support_relation φ added bots tops Base hc hf h with ⟨ha',_,_⟩ | ⟨ha',_⟩ | ⟨_,hb',_⟩
  · exact ha ha'
  · exact ha ha'
  · exact hb' hb

theorem support_fresh_iff {a b : Fin n} (ha : ¬ Base a) (hb : ¬ Base b) :
    Support Ψ a b ↔ a = b := by
  constructor
  · intro h
    rcases support_relation φ added bots tops Base hc hf h with ⟨ha',_,_⟩ | ⟨ha',_⟩ | ⟨_,_,he⟩
    · exact False.elim (ha ha')
    · exact False.elim (ha ha')
    · exact he
  · rintro rfl; exact .refl _

omit hc hf in
theorem lower_path_lift {a b : Fin n} {word : List (Fin d)} (h : LowerPath φ a word b) :
    LowerPath Ψ a word b := by
  apply lower_path_map φ Ψ id ?_ ?_ h
  · intro a ha; exact ha
  · intro a ha; exact List.mem_append_left _ ha

end Extension

inductive Origin (Base : Fin n → Prop) (added : List (BoundLiteral n d)) :
    Fin n → List (Fin d) → Fin n → Prop
  | first {a z r i} (ha : a ∈ added) (hp : a.1 = z) (hb : Base z) (hr : a.2 i = r) :
      Origin Base added z [i] r
  | snoc {a z u r word i} (h : Origin Base added z word u)
      (ha : a ∈ added) (hp : a.1 = u) (hr : a.2 i = r) :
      Origin Base added z (word ++ [i]) r

theorem origin_fresh {Base : Fin n → Prop} {added : List (BoundLiteral n d)}
    (hf : FreshChildren added Base) {z word r} (h : Origin Base added z word r) : ¬ Base r := by
  cases h with
  | first ha _ _ hr => rw [← hr]; exact hf _ ha _
  | snoc _ ha _ hr => rw [← hr]; exact hf _ ha _

theorem origin_base {Base : Fin n → Prop} {added : List (BoundLiteral n d)}
    {z word r} (h : Origin Base added z word r) : Base z := by
  induction h with
  | first _ _ hb _ => exact hb
  | snoc _ _ _ _ ih => exact ih

theorem origin_upper (φ : Constraints n d) (added : List (BoundLiteral n d))
    (bots tops : List (Fin n)) {Base : Fin n → Prop} {z word r}
    (h : Origin Base added z word r) : UpperPath (graft φ added bots tops) z word r := by
  induction h with
  | first ha hp _ hr =>
      apply UpperPath.cons ?_ (.nil (.refl _))
      refine ⟨_,List.mem_append_right _ ha,?_,?_⟩
      · rw [hp]; exact .refl _
      · rw [hr]; exact .refl _
  | snoc _ ha hp hr ih =>
      apply upper_append _ ih
      apply UpperPath.cons ?_ (.nil (.refl _))
      refine ⟨_,List.mem_append_right _ ha,?_,?_⟩
      · rw [hp]; exact .refl _
      · rw [hr]; exact .refl _

def Cross (φ : Constraints n d) (Base : Fin n → Prop) (added : List (BoundLiteral n d))
    (a r : Fin n) : Prop := ∃ z word, Origin Base added z word r ∧ LowerPath φ z word a

section Cross

variable (φ : Constraints n d) (added : List (BoundLiteral n d))
variable (bots tops : List (Fin n)) (Base : Fin n → Prop)
variable (hc : Contained φ Base) (hf : FreshChildren added Base)
include hc hf

local notation "Ψ" => graft φ added bots tops

theorem support_cross {a r : Fin n} (h : Support Ψ a r) :
    Base a → ¬ Base r → Cross φ Base added a r := by
  induction h with
  | refl a => intro ha hr; exact False.elim (hr ha)
  | @trans a b c h₁ h₂ ih₁ ih₂ =>
      intro ha hr
      by_cases hb : Base b
      · obtain ⟨z,word,ho,hl⟩ := ih₂ hb hr
        exact ⟨z,word,ho,lower_post φ hl
          ((support_base_iff φ added bots tops Base hc hf ha hb).mp h₁)⟩
      · obtain rfl := (support_fresh_iff φ added bots tops Base hc hf hb hr).mp h₂
        exact ih₁ ha hr
  | @decomp a b ha hb hp i ih =>
      intro _ hr
      change a ∈ φ.lower at ha
      change b ∈ φ.upper ++ added at hb
      rcases List.mem_append.mp hb with hb | hb
      · exact False.elim (hr ((hc.2 b hb).2 i))
      · by_cases hbp : Base b.1
        · refine ⟨b.1,[i],Origin.first hb rfl hbp rfl,?_⟩
          exact .cons ⟨a,ha,.refl _,
            (support_base_iff φ added bots tops Base hc hf (hc.1 a ha).1 hbp).mp hp⟩ (.nil (.refl _))
        · obtain ⟨z,word,ho,hl⟩ := ih (hc.1 a ha).1 hbp
          refine ⟨z,word ++ [i],Origin.snoc ho hb rfl rfl,?_⟩
          exact lower_append φ hl (.cons ⟨a,ha,.refl _,.refl _⟩ (.nil (.refl _)))

omit hc hf in
theorem cross_support {a r : Fin n} (h : Cross φ Base added a r) : Support Ψ a r := by
  obtain ⟨z,word,ho,hl⟩ := h
  have hu := origin_upper φ added bots tops ho
  have hl' := lower_path_lift φ added bots tops hl
  have hz : LowerPath Ψ r [] a := cancel_upper_lower Ψ word hu (by simpa using hl')
  cases hz with | nil hs => exact hs

theorem base_fresh_support_iff {a r : Fin n} (ha : Base a) (hr : ¬ Base r) :
    Support Ψ a r ↔ Cross φ Base added a r :=
  ⟨fun h => support_cross φ added bots tops Base hc hf h ha hr,
    cross_support φ added bots tops Base⟩

end Cross

end NSSE.SubtypeUpperExtension
