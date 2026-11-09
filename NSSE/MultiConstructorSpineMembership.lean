import NSSE.MultiConstructorSpineInput

/-! Exhaustive literal origins in the actual extension, including epsilon
and constructor/extreme terminals. -/
namespace NSSE.MultiConstructorSpineMembership
open MultiConstructorConstraints MultiConstructorSpineInput MultiConstructorSpineInput.Data
open MultiConstructorInputMap
variable {H : Type*} {arity : H → Nat} {n D : Nat}

theorem lower_cases (phi : Constraints arity n) (S : Data arity n D) (a : Bound arity S.size)
    (ha : a ∈ (S.program phi).lower) :
    (∃ b ∈ phi.lower, a = bound S.old b) ∨ (∃ k, a = S.lower k) ∨
      ∃ h, S.endX = .node h ∧ a = ⟨S.xAt S.last,h,fun _ => S.botVar⟩ := by
  change a ∈ phi.lower.map (bound S.old) ++ (List.ofFn S.lower ++ S.lowerEnd) at ha
  rcases List.mem_append.mp ha with ho | hs
  · obtain ⟨b,hb,he⟩ := List.mem_map.mp ho
    exact Or.inl ⟨b,hb,he.symm⟩
  · rcases List.mem_append.mp hs with hp | ht
    · obtain ⟨k,he⟩ := List.mem_ofFn.mp hp
      exact Or.inr (Or.inl ⟨k,he.symm⟩)
    · cases he : S.endX with
      | bot => simp [lowerEnd,he] at ht
      | top => simp [lowerEnd,he] at ht
      | node h => exact Or.inr (Or.inr ⟨h,rfl,by simpa [lowerEnd,he] using ht⟩)

theorem upper_cases (phi : Constraints arity n) (S : Data arity n D) (a : Bound arity S.size)
    (ha : a ∈ (S.program phi).upper) :
    (∃ b ∈ phi.upper, a = bound S.old b) ∨ (∃ k, a = S.upper k) ∨
      ∃ h, S.endY = .node h ∧ a = ⟨S.yAt S.last,h,fun _ => S.topVar⟩ := by
  change a ∈ phi.upper.map (bound S.old) ++ (List.ofFn S.upper ++ S.upperEnd) at ha
  rcases List.mem_append.mp ha with ho | hs
  · obtain ⟨b,hb,he⟩ := List.mem_map.mp ho
    exact Or.inl ⟨b,hb,he.symm⟩
  · rcases List.mem_append.mp hs with hp | ht
    · obtain ⟨k,he⟩ := List.mem_ofFn.mp hp
      exact Or.inr (Or.inl ⟨k,he.symm⟩)
    · cases he : S.endY with
      | bot => simp [upperEnd,he] at ht
      | top => simp [upperEnd,he] at ht
      | node h => exact Or.inr (Or.inr ⟨h,rfl,by simpa [upperEnd,he] using ht⟩)

theorem top_cases (phi : Constraints arity n) (S : Data arity n D) (v : Fin S.size)
    (hv : v ∈ (S.program phi).top) :
    (∃ u ∈ phi.top, v = S.old u) ∨ v = S.topVar ∨ S.endX = .top ∧ v = S.xAt S.last := by
  change v ∈ phi.top.map S.old ++ (S.topVar::S.endTops) at hv
  rcases List.mem_append.mp hv with ho | hs
  · obtain ⟨u,hu,he⟩ := List.mem_map.mp ho
    exact Or.inl ⟨u,hu,he.symm⟩
  · rcases List.mem_cons.mp hs with he | ht
    · exact Or.inr (Or.inl he)
    · cases he : S.endX with
      | bot => simp [endTops,he] at ht
      | node h => simp [endTops,he] at ht
      | top => exact Or.inr (Or.inr ⟨rfl,by simpa [endTops,he] using ht⟩)

theorem bot_cases (phi : Constraints arity n) (S : Data arity n D) (v : Fin S.size)
    (hv : v ∈ (S.program phi).bot) :
    (∃ u ∈ phi.bot, v = S.old u) ∨ v = S.botVar ∨ S.endY = .bot ∧ v = S.yAt S.last := by
  change v ∈ phi.bot.map S.old ++ (S.botVar::S.endBots) at hv
  rcases List.mem_append.mp hv with ho | hs
  · obtain ⟨u,hu,he⟩ := List.mem_map.mp ho
    exact Or.inl ⟨u,hu,he.symm⟩
  · rcases List.mem_cons.mp hs with he | ht
    · exact Or.inr (Or.inl he)
    · cases he : S.endY with
      | top => simp [endBots,he] at ht
      | node h => simp [endBots,he] at ht
      | bot => exact Or.inr (Or.inr ⟨rfl,by simpa [endBots,he] using ht⟩)

end NSSE.MultiConstructorSpineMembership
