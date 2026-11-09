import NSSE.MultiConstructorShapeTokens

/-! The finite shape grammar selects extremes whenever one-sided demands
allow them. Finite joins make its head monotone even on incoherent states;
on coherent clash-free states, two nonempty pin sets give their unique head. -/
namespace NSSE.MultiConstructorShapeHead
open MultiConstructorTrees MultiConstructorConstraints MultiConstructorTokens MultiConstructorShapeTokens
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

def head (phi : Constraints arity n) (s : State n) : Label H :=
  if lowerPins phi s.1 = ∅ then
    if upperPins phi s.2 = ∅ then
      if @decide (BottomHit phi s.2) (bottomDecision phi s.2) then .bot else .top
    else .bot
  else if upperPins phi s.2 = ∅ then .top else (lowerPins phi s.1).sup Label.node

theorem empty_lower_upper (phi : Constraints arity n) (s : State n)
    (hl : lowerPins phi s.1 = ∅) (hu : upperPins phi s.2 ≠ ∅) : head phi s = .bot := by
  simp only [head,if_pos hl,if_neg hu]

theorem nonempty_lower_no_upper (phi : Constraints arity n) (s : State n)
    (hl : lowerPins phi s.1 ≠ ∅) (hu : upperPins phi s.2 = ∅) : head phi s = .top := by
  simp only [head,if_neg hl,if_pos hu]

theorem both_nonempty (phi : Constraints arity n) (s : State n)
    (hl : lowerPins phi s.1 ≠ ∅) (hu : upperPins phi s.2 ≠ ∅) :
    head phi s = (lowerPins phi s.1).sup Label.node := by
  simp only [head,if_neg hl,if_neg hu]

theorem empty_lower_bottom (phi : Constraints arity n) (s : State n)
    (hl : lowerPins phi s.1 = ∅) (hb : BottomHit phi s.2) : head phi s = .bot := by
  letI := bottomDecision phi s.2
  by_cases hu : upperPins phi s.2 = ∅ <;> simp [head,hl,hu,decide_eq_true hb]

theorem no_upper_no_bottom (phi : Constraints arity n) (s : State n)
    (hu : upperPins phi s.2 = ∅) (hb : ¬BottomHit phi s.2) : head phi s = .top := by
  letI := bottomDecision phi s.2
  by_cases hl : lowerPins phi s.1 = ∅ <;> simp [head,hl,hu,decide_eq_false hb]

theorem monotone (phi : Constraints arity n) (s t : State n) (hst : Refines s t) : head phi s ≤ head phi t := by
  have hlm := MultiConstructorLowerHead.pins_mono phi s.1 t.1 hst.1
  have hum := upper_pins_mono phi t.2 s.2 hst.2
  have hbm := bottom_mono phi t.2 s.2 hst.2
  by_cases hls : lowerPins phi s.1 = ∅
  · by_cases hus : upperPins phi s.2 = ∅
    · by_cases hbs : BottomHit phi s.2
      · rw [empty_lower_bottom phi s hls hbs]
        exact bot_le
      · have hut : upperPins phi t.2 = ∅ := Finset.subset_empty.mp (by simpa only [hus] using hum)
        have hbt : ¬BottomHit phi t.2 := fun h => hbs (hbm h)
        rw [no_upper_no_bottom phi s hus hbs,no_upper_no_bottom phi t hut hbt]
    · rw [empty_lower_upper phi s hls hus]
      exact bot_le
  · have hlt : lowerPins phi t.1 ≠ ∅ := by
      intro he
      exact hls (Finset.subset_empty.mp (by simpa only [he] using hlm))
    by_cases hut : upperPins phi t.2 = ∅
    · rw [nonempty_lower_no_upper phi t hlt hut]
      exact le_top
    · have hus : upperPins phi s.2 ≠ ∅ := by
        intro he
        exact hut (Finset.subset_empty.mp (by simpa only [he] using hum))
      rw [both_nonempty phi s hls hus,both_nonempty phi t hlt hut]
      exact Label.join_heads_mono _ _ hlm

theorem node_nonempty (phi : Constraints arity n) (s : State n) (h : H) (hh : head phi s = .node h) :
    (lowerPins phi s.1).Nonempty ∧ (upperPins phi s.2).Nonempty := by
  have hl : lowerPins phi s.1 ≠ ∅ := by
    intro hl
    rw [head,if_pos hl] at hh
    split_ifs at hh
  have hu : upperPins phi s.2 ≠ ∅ := by
    intro hu
    rw [nonempty_lower_no_upper phi s hl hu] at hh
    cases hh
  exact ⟨Finset.nonempty_iff_ne_empty.mpr hl,Finset.nonempty_iff_ne_empty.mpr hu⟩

theorem node_of_pins (phi : Constraints arity n) (hn : ¬LabelClash phi) (s : State n) (hs : Coherent phi s)
    (h : H) (hl : h ∈ lowerPins phi s.1) (hu : h ∈ upperPins phi s.2) : head phi s = .node h := by
  rw [both_nonempty phi s (Finset.nonempty_iff_ne_empty.mp ⟨h,hl⟩) (Finset.nonempty_iff_ne_empty.mp ⟨h,hu⟩)]
  exact le_antisymm (Label.join_heads_le _ h (fun g hg => pins_equal phi hn s hs g h hg hu))
    (Label.node_le_join_heads _ h hl)

theorem pins_of_node (phi : Constraints arity n) (hn : ¬LabelClash phi) (s : State n) (hs : Coherent phi s)
    (h : H) (hh : head phi s = .node h) : h ∈ lowerPins phi s.1 ∧ h ∈ upperPins phi s.2 := by
  have hp := node_nonempty phi s h hh
  obtain ⟨g,hg⟩ := hp.1
  obtain ⟨k,hk⟩ := hp.2
  have hgh := Label.node_le_join_heads (lowerPins phi s.1) g hg
  rw [← both_nonempty phi s hp.1.ne_empty hp.2.ne_empty,hh] at hgh
  have hge : g = h := (Label.node_le_node g h).mp hgh
  have hke : k = h := (pins_equal phi hn s hs g k hg hk).symm.trans hge
  exact ⟨hge ▸ hg,hke ▸ hk⟩

theorem node_iff (phi : Constraints arity n) (hn : ¬LabelClash phi) (s : State n) (hs : Coherent phi s) (h : H) :
    head phi s = .node h ↔ h ∈ lowerPins phi s.1 ∧ h ∈ upperPins phi s.2 :=
  ⟨pins_of_node phi hn s hs h,fun hp => node_of_pins phi hn s hs h hp.1 hp.2⟩

end NSSE.MultiConstructorShapeHead
