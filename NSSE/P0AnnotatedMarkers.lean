import NSSE.P0NestedSelection
import NSSE.P0ProperLiveness

/-! Nested repetitions of actual state/letter annotations force a stable
marker. All extensions preserve a supplied earlier history. -/
namespace NSSE.P0AnnotatedMarkers
open P0ProperMachine P0ProperWords P0LoopStreams P0PairImages P0NestedRepeats
variable {Q A H : Type*}

def annotated (M : Machine Q A H) (z : Nat → A) (k : Nat) : Q × A :=
  (run M z k,z k)

def Pumped (M : Machine Q A H) (z : Nat → A) (m b : Nat) : Prop :=
  ∃ a d z', m ≤ a ∧ a+d ≤ b ∧ 0 < d ∧ Good M z' ∧
    Spells z' (prefixWord z m) ∧ Function.Periodic (fun k => z' (a+k)) d

theorem spells_shorter (z z' : Nat → A) (m n : Nat) (hm : m ≤ n)
    (hz : Spells z' (prefixWord z n)) : Spells z' (prefixWord z m) := by
  intro k hk
  have hk' : k < m := by simpa using hk
  have he := hz k (by simp; omega)
  rw [spells_prefix z n k (by simp; omega)] at he
  rw [spells_prefix z m k hk]
  exact he

variable [DecidableEq Q] [Fintype Q] [DecidableEq H]
variable (M : Machine Q A H) [DecidablePred M.valid]

theorem factor_image_positive (z : Nat → A) (n : Nat) (hg : GoodUpTo M z n)
    (a L : Nat) (ha : a+L ≤ n) : 0 < (image M (segment z a L)).card := by
  have hw : GoodWord M (prefixWord z (a+L)) :=
    (goodWord_prefix M z (a+L)).mpr (goodUpTo_mono M z (a+L) n ha hg)
  obtain ⟨p,hp⟩ := good_nonempty M _ hw
  have hs := suffix_subset M (segment z 0 a) (segment z a L)
  have he : segment z 0 (a+L) = segment z 0 a ++ segment z a L := by
    simpa only [Nat.zero_add] using segment_append z 0 a L
  rw [← he] at hs
  have hp' : p ∈ image M (segment z 0 (a+L)) := by
    simpa only [P0LoopStreams.segment,Nat.zero_add] using hp
  exact Finset.card_pos.mpr ⟨p,hs hp'⟩

theorem marker_pumps (z : Nat → A) (n : Nat) (hg : GoodUpTo M z n)
    (m b a d L : Nat) (hma : m ≤ a) (he : a+d+L ≤ b) (hbn : b ≤ n) (hd : 0 < d)
    (hm : Match z a (a+d) L) (hq : run M z a = run M z (a+d))
    (hc : (image M (segment z a (d+L))).card = (image M (segment z a L)).card) :
    Pumped M z m b := by
  let w := prefixWord z (a+d+L)
  have hwlen : w.length = a+d+L := prefix_length z _
  have hwsp : Spells z w := spells_prefix z _
  have hwgood : GoodWord M w :=
    (goodWord_prefix M z _).mpr (goodUpTo_mono M z _ n (by omega) hg)
  have hwm : WordMatch w a (a+d) L :=
    (match_iff w z hwsp a (a+d) L (by omega) (by omega)).mpr hm
  have hwq : state M w a = state M w (a+d) := by
    rwa [state_eq_run M w z hwsp a (by omega),state_eq_run M w z hwsp (a+d) (by omega)]
  have hwc : (image M ((w.drop a).take (L+d))).card =
      (image M ((w.drop a).take L)).card := by
    rw [← P0WordLoop.segment_of_spells w z hwsp a (L+d) (by omega),
      ← P0WordLoop.segment_of_spells w z hwsp a L (by omega)]
    simpa only [Nat.add_comm L d] using hc
  obtain ⟨z',hz',hsp',hp'⟩ := P0WordMarker.exists_extension M w a d L hd hwlen hwgood hwm hwq hwc
  exact ⟨a,d,z',hma,by omega,hd,hz',spells_shorter z z' m (a+d+L) (by omega) hsp',hp'⟩

theorem nested_or_bound (z : Nat → A) (n : Nat) (hg : GoodUpTo M z n)
    (m b a L k : Nat) (hma : m ≤ a) (he : a+L ≤ b) (hbn : b ≤ n)
    (hn : Nest (annotated M z) a L k) :
    Pumped M z m b ∨ k+(image M (segment z a L)).card ≤ Fintype.card Q^2 := by
  induction k generalizing L with
  | zero => exact Or.inr (by simpa only [Nat.zero_add] using card_bound M (segment z a L))
  | succ k ih =>
    obtain ⟨l,d,hld,rfl,hn,hm⟩ := hn
    rcases ih l (by omega) hn with hp | hsmall
    · exact Or.inl hp
    · have hl : 0 < l := nest_positive (annotated M z) a l k hn
      have hq : run M z a = run M z (a+d) := by
        simpa only [annotated,Nat.add_zero] using congrArg Prod.fst (hm 0 hl)
      have hm' : Match z a (a+d) l := fun i hi => congrArg Prod.snd (hm i hi)
      have hs : image M (segment z a (d+l)) ⊆ image M (segment z a l) := by
        rw [segment_append]
        have hh := suffix_subset M (segment z a d) (segment z (a+d) l)
        intro p hp
        have hp' := hh hp
        rwa [← segment_eq z a (a+d) l hm'] at hp'
      have hle := Finset.card_le_card hs
      by_cases hc : (image M (segment z a (d+l))).card = (image M (segment z a l)).card
      · exact Or.inl (marker_pumps M z n hg m b a d l hma (by omega) hbn (by omega) hm' hq hc)
      · exact Or.inr (by omega)

theorem nested_pumps (z : Nat → A) (n : Nat) (hg : GoodUpTo M z n)
    (m b a L : Nat) (hma : m ≤ a) (he : a+L ≤ b) (hbn : b ≤ n)
    (hn : Nest (annotated M z) a L (Fintype.card Q^2)) : Pumped M z m b := by
  rcases nested_or_bound M z n hg m b a L (Fintype.card Q^2) hma he hbn hn with hp | hcard
  · exact hp
  · have hpos := factor_image_positive M z n hg a L (by omega)
    omega

end NSSE.P0AnnotatedMarkers
