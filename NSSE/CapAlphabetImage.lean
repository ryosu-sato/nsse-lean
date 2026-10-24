import NSSE.CountedCapEvaluation

/-! Alphabet-image transport for the literal cap semantics. -/

namespace NSSE.CapAlphabetImage

variable {α β : Type*} (f : α → β)

def image (L : Language α) : Language β := fun ys => ∃ xs, L xs ∧ xs.map f = ys

theorem concat_image (L M : Language α) (ys : List β) :
    Language.concat (image f L) (image f M) ys ↔ image f (Language.concat L M) ys := by
  constructor
  · rintro ⟨u,v,rfl,⟨x,hx,rfl⟩,⟨y,hy,rfl⟩⟩
    exact ⟨x++y,⟨x,y,rfl,hx,hy⟩,List.map_append⟩
  · rintro ⟨xs,⟨x,y,rfl,hx,hy⟩,rfl⟩
    exact ⟨x.map f,y.map f,List.map_append,⟨x,hx,rfl⟩,⟨y,hy,rfl⟩⟩

theorem prefix_image (L : Language α) (ys : List β) :
    Language.prefixClosure (image f L) ys ↔ image f (Language.prefixClosure L) ys := by
  constructor
  · rintro ⟨tail,ws,hw,he⟩
    obtain ⟨u,v,huv,hu,hv⟩ := List.map_eq_append_iff.mp he
    exact ⟨u,⟨v,by simpa only [← huv] using hw⟩,hu⟩
  · rintro ⟨xs,⟨tail,ht⟩,rfl⟩
    exact ⟨tail.map f,xs++tail,ht,List.map_append⟩

theorem power_map (xs : List α) (k : Nat) :
    (Language.wordPower xs k).map f = Language.wordPower (xs.map f) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Language.wordPower_succ, List.map_append, ih]

theorem cap_image (L : Language α) (ys : List β) :
    Language.cap (image f L) ys ↔ image f (Language.cap L) ys := by
  constructor
  · rintro ⟨mu,k,tail,⟨root,hr,rfl⟩,he⟩
    rw [← power_map] at he
    obtain ⟨u,v,huv,hu,hv⟩ := List.map_eq_append_iff.mp he
    exact ⟨u,⟨root,k,v,hr,huv⟩,hu⟩
  · rintro ⟨xs,⟨mu,k,tail,hm,he⟩,rfl⟩
    refine ⟨mu.map f,k,tail.map f,⟨mu,hm,rfl⟩,?_⟩
    rw [← power_map, he, List.map_append]

def component (c : CapComponent α) : CapComponent β := ⟨image f c.left,image f c.right⟩

theorem component_image (c : CapComponent α) (ys : List β) :
    capComponentCovers (component f c) ys ↔ image f (capComponentCovers c) ys := by
  have hcap : Language.cap (image f c.right) = image f (Language.cap c.right) :=
    funext (fun w => propext (cap_image f c.right w))
  have hconcat : Language.concat (image f c.left) (image f (Language.cap c.right)) =
      image f (Language.concat c.left (Language.cap c.right)) :=
    funext (fun w => propext (concat_image f _ _ w))
  change Language.prefixClosure (Language.concat (image f c.left) (Language.cap (image f c.right))) ys ↔ _
  rw [hcap,hconcat,prefix_image]
  rfl

theorem image_at_map (hf : Function.Injective f) (L : Language α) (xs : List α) :
    image f L (xs.map f) ↔ L xs := by
  constructor
  · rintro ⟨ys,hy,he⟩
    have h := (List.map_injective_iff.mpr hf) he
    simpa only [h] using hy
  · intro hx; exact ⟨xs,hx,rfl⟩

end NSSE.CapAlphabetImage
