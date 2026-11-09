import NSSE.P0DZVirtualTrace

/-! Actual virtual D-path clashes. Proper heads are common to both rails,
so existentially forgetting the rail pair and symmetrizing births is
exact for head clashes. Actual Z acceptance rules out every earlier
virtual clash, regardless of the final-state birth table. -/
namespace NSSE.P0DZFirstClash
open P0DZBranch P0DZTrace P0DZVirtualTrace P0ProperWords P0SuffixRank
variable {Q Z A H : Type*}

def dState (J : Branch Q Z A H) (w : List A) (k : Nat) : Q := (properAt J w k).getD J.initial

theorem proper_eq_state (J : Branch Q Z A H) (w : List A) (hc : DComplete J w) (k : Nat) :
    properAt J w k = some (dState J w k) := by
  obtain ⟨q,hq⟩ := d_prefix J w hc k
  simp only [dState,hq,Option.getD_some]

theorem states_of_proper (J : Branch Q Z A H) (w : List A) (a b : Nat)
    (h : properAt J w a = properAt J w b) : dState J w a = dState J w b :=
  congrArg (fun q => q.getD J.initial) h

theorem matched_states (J : Branch Q Z A H) (w : List A) (hc : DComplete J w) (a b l : Nat)
    (ha : a+l ≤ w.length) (hb : b+l ≤ w.length) (he : dState J w a = dState J w b)
    (hm : WordMatch w a b l) : dState J w (a+l) = dState J w (b+l) := by
  apply states_of_proper
  apply proper_equal J w a b l ha hb ?_ hm
  rw [proper_eq_state J w hc a,proper_eq_state J w hc b,he]

def Born (J : Branch Q Z A H) (q r : Q) : Prop :=
  (∃ s t, J.birth (.inl q) s (.inl r) t) ∨ (∃ s t, J.birth (.inl r) s (.inl q) t)

theorem born_symm (J : Branch Q Z A H) (q r : Q) (h : Born J q r) : Born J r q := h.symm

structure Clash (J : Branch Q Z A H) (w : List A) (a b l : Nat) : Prop where
  left_bound : a+l ≤ w.length
  right_bound : b+l ≤ w.length
  born : Born J (dState J w a) (dState J w b)
  letters : WordMatch w a b l
  bad : J.head (dState J w (a+l)) ≠ J.head (dState J w (b+l))

theorem clash_symm (J : Branch Q Z A H) (w : List A) (a b l : Nat) (h : Clash J w a b l) :
    Clash J w b a l :=
  ⟨h.right_bound,h.left_bound,born_symm J _ _ h.born,fun i hi => (h.letters i hi).symm,Ne.symm h.bad⟩

theorem clash_origins_ne (J : Branch Q Z A H) (w : List A) (a b l : Nat) (h : Clash J w a b l) : a ≠ b := by
  intro he
  subst b
  exact h.bad rfl

structure FirstUnsafe (J : Branch Q Z A H) (w : List A) : Prop where
  complete : DComplete J w
  witness : ∃ a b l, Clash J w a b l
  first : ∀ a b l, Clash J w a b l → max (a+l) (b+l) = w.length

theorem no_earlier (J : Branch Q Z A H) (w : List A) (hf : FirstUnsafe J w)
    (a b l : Nat) (ha : a+l < w.length) (hb : b+l < w.length) : ¬ Clash J w a b l := by
  intro hh
  have he := hf.first a b l hh
  omega

theorem ordered_witness (J : Branch Q Z A H) (w : List A) (hf : FirstUnsafe J w) :
    ∃ a b l, a < b ∧ b+l = w.length ∧ Clash J w a b l := by
  obtain ⟨a,b,l,h⟩ := hf.witness
  have hn := clash_origins_ne J w a b l h
  have hend := hf.first a b l h
  rcases lt_or_gt_of_ne hn with hab | hba
  · exact ⟨a,b,l,hab,by omega,h⟩
  · exact ⟨b,a,l,hba,by omega,clash_symm J w a b l h⟩

theorem proper_state_at (J : Branch Q Z A H) (w : List A) (hc : DComplete J w)
    (a : Nat) (ha : a < w.length) : stateAt J w a = some (.inl (dState J w a)) := by
  rw [proper_state J w a ha]
  change (properAt J w a).map Sum.inl = _
  rw [proper_eq_state J w hc a]
  rfl

theorem accepted_agreement (J : Branch Q Z A H) (w : List A) (hw : Accepted J w)
    (hc : DComplete J w) (a b l : Nat) (ha : a+l < w.length) (hb : b+l < w.length)
    (hne : a ≠ b) (s t : Bool) (hborn : J.birth (.inl (dState J w a)) s (.inl (dState J w b)) t)
    (hm : WordMatch w a b l) : J.head (dState J w (a+l)) = J.head (dState J w (b+l)) := by
  have hborn' : bornAt J w a s b t := ⟨.inl (dState J w a),.inl (dState J w b),
    proper_state_at J w hc a (by omega),proper_state_at J w hc b (by omega),hborn⟩
  have hh := hw.2 a (by omega) b (by omega) s t (Or.inl hne) hborn' l (by omega)
    (by omega) (by omega) hm
  rw [label_proper J w (a+l) ha _ (proper_eq_state J w hc (a+l)) s,
    label_proper J w (b+l) hb _ (proper_eq_state J w hc (b+l)) t] at hh
  exact hh

theorem accepted_first (J : Branch Q Z A H) (w : List A) (hw : Accepted J w)
    (hc : DComplete J w) (hu : ∃ a b l, Clash J w a b l) : FirstUnsafe J w := by
  refine ⟨hc,hu,?_⟩
  intro a b l h
  have ha := h.left_bound
  have hb := h.right_bound
  by_contra hn
  have hal : a+l < w.length := by omega
  have hbl : b+l < w.length := by omega
  have hne := clash_origins_ne J w a b l h
  rcases h.born with ⟨s,t,hborn⟩ | ⟨s,t,hborn⟩
  · exact h.bad (accepted_agreement J w hw hc a b l hal hbl hne s t hborn h.letters)
  · exact h.bad (accepted_agreement J w hw hc b a l hbl hal (Ne.symm hne) s t hborn
      (fun i hi => (h.letters i hi).symm)).symm

end NSSE.P0DZFirstClash
