import NSSE.MultiVarianceWordPrefix
import NSSE.MultiVarianceSelectorHead

/-! First accepted prefixes retain their actual head/child stream while
allowing EVERY separating terminal pair. At an empty proper cut, a
missing physical Y incident ray would give an earlier accepted witness. -/
namespace NSSE.MultiVarianceFirstPrefix
open MultiConstructorConstraints (Query)
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceTokenExact
open MultiVarianceWordReader MultiVarianceWordPrefix MultiVarianceSelectorHead
open P0ProperWords (WordMatch)
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

def First (Q : Query arity n) (w : List (Letter arity)) : Prop :=
  Witness pol Q w ∧ ∀ m, m<w.length → ¬Witness pol Q (w.take m)

theorem first_prefix (Q : Query arity n) (w : List (Letter arity)) (hw : Witness pol Q w) :
    ∃ m, m ≤ w.length ∧ First pol Q (w.take m) := by
  classical
  have hex : ∃ m, m ≤ w.length ∧ Witness pol Q (w.take m) :=
    ⟨w.length,le_rfl,by simpa only [List.take_length] using hw⟩
  let m := Nat.find hex
  have hs := Nat.find_spec hex
  refine ⟨m,hs.1,hs.2,?_⟩
  intro k hk hkw
  have hkm : k<m := by simp only [List.length_take] at hk; omega
  have hkw' : Witness pol Q (w.take k) := by
    simpa only [List.take_take,Nat.min_eq_left (Nat.le_of_lt hkm)] using hkw
  exact Nat.find_min hex hkm ⟨by omega,hkw'⟩

def SymBorn (Q : Query arity n) (w : List (Letter arity)) (a : Nat) (s : Bool) (b : Nat) (t : Bool) : Prop :=
  Born pol Q w a s b t ∨ Born pol Q w b t a s

def IncidentY (Q : Query arity n) (w : List (Letter arity)) (m : Nat) : Prop :=
  ∃ a b l side, a+l ≤ m ∧ b+l=m ∧ SymBorn pol Q w a side b true ∧ WordMatch w a b l

def yExtreme (sign : Bool) : Label H := if sign then .top else .bot

theorem isolated_accepted (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H)
    (ha : Accepted pol Q w ex ey) (m : Nat) (hm : m<w.length)
    (he : Empty (frame pol Q w m)) (hi : ¬IncidentY pol Q w m) :
    Accepted pol Q (w.take m) (.node w[m].1) (yExtreme (frame pol Q w m).sign) := by
  have hlen : (w.take m).length=m := List.length_take_of_le (by omega)
  refine ⟨?_,ha.2.1,?_,?_⟩
  · unfold ValidEnd
    rw [hlen,frame_prefix pol Q w m m le_rfl]
    cases hsign : (frame pol Q w m).sign <;>
      simp [yExtreme,hsign,MultiConstructorTrees.Label.Below]
  · intro k hk side
    have hkm : k ≤ m := by simpa only [hlen] using hk
    rw [frame_prefix pol Q w m k hkm]
    by_cases hlt : k<m
    · rw [value_prefix w m k hlt ex ey _ _ side (by omega)]
      exact ha.2.2.1 k (by omega) side
    · have hke : k=m := by omega
      subst k
      have ht : tokensOf (frame pol Q w m) side=∅ := by
        cases side
        · exact he.1
        · exact he.2
      intro z hz
      rw [ht] at hz
      exact False.elim (Finset.not_mem_empty _ hz)
  · intro a hab b hbb s t hb l hal hbl hmatch
    have ham : a+l ≤ m := by simpa only [hlen] using hal
    have hbm : b+l ≤ m := by simpa only [hlen] using hbl
    have hb' := (born_prefix pol Q w m a b (by omega) (by omega) s t).mp hb
    have hm' := (match_prefix w m a b l ham hbm).mp hmatch
    have hs : s=true → a+l ≠ m := by
      intro hs heq
      subst s
      exact hi ⟨b,a,l,t,hbm,heq,Or.inr hb',fun k hk => (hm' k hk).symm⟩
    have ht : t=true → b+l ≠ m := by
      intro ht heq
      subst t
      exact hi ⟨a,b,l,s,ham,heq,Or.inl hb',hm'⟩
    rw [value_isolated w m (a+l) hm ham ex ey _ s hs,
      value_isolated w m (b+l) hm hbm ex ey _ t ht]
    exact ha.2.2.2 a (by omega) b (by omega) s t hb' l (by omega) (by omega) hm'

theorem first_empty_incident (Q : Query arity n) (w : List (Letter arity)) (hf : First pol Q w)
    (ex ey : Label H) (ha : Accepted pol Q w ex ey) (m : Nat) (hm : m<w.length)
    (he : Empty (frame pol Q w m)) : IncidentY pol Q w m := by
  by_contra hi
  exact hf.2 m hm ⟨_,_,isolated_accepted pol Q w ex ey ha m hm he hi⟩

end NSSE.MultiVarianceFirstPrefix
