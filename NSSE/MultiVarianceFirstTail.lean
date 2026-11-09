import NSSE.MultiVarianceWordEmptyTail

/-! A first accepted signed word with an empty proper tail has a
surviving old comparison. It copies every remaining proper head and
every NONFINAL current-head/child letter, with positive lag below J. -/
namespace NSSE.MultiVarianceFirstTail
open MultiConstructorConstraints (Query)
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceSpineTokens
open MultiVarianceWordReader MultiVarianceFirstPrefix MultiVarianceWordEmptyTail MultiVarianceSelectorHead
open P0ProperWords (WordMatch)
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

theorem surviving (Q : Query arity n) (w : List (Letter arity)) (hf : First pol Q w)
    (ex ey : Label H) (ha : Accepted pol Q w ex ey) (J : Nat) (hJ : J<w.length)
    (he : Empty (frame pol Q w J)) :
    ∃ a b l side, a<b ∧ b<J ∧ b+l=w.length-1 ∧ SymBorn pol Q w a side b true ∧ WordMatch w a b l := by
  have hm : w.length-1<w.length := by omega
  have hemp := empty_after pol Q w J (w.length-1) he (by omega) (by omega)
  obtain ⟨a,b,l,side,hal,hbl,hb,hw⟩ := first_empty_incident pol Q w hf ex ey ha (w.length-1) hm hemp
  have hbefore := symBorn_before_empty pol Q w J a b he (by omega) (by omega) side true hb
  have hne : a ≠ b := by
    intro hab
    subst b
    exact no_diagonal_symBorn pol Q w ex ey ha a (by omega) side true hb
  exact ⟨a,b,l,side,by omega,hbefore.2,hbl,hb,hw⟩

theorem ray_heads (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H)
    (ha : Accepted pol Q w ex ey) (a b l : Nat) (s t : Bool)
    (hb : SymBorn pol Q w a s b t) (hm : WordMatch w a b l)
    (hal : a+l<w.length) (hbl : b+l<w.length) : w[a+l].1=w[b+l].1 := by
  rcases hb with hb | hb
  · have hh := ha.2.2.2 a (by omega) b (by omega) s t hb l (by omega) (by omega) hm
    simpa only [value,List.getElem?_eq_getElem hal,List.getElem?_eq_getElem hbl,P0DZBranch.Agree] using hh
  · have hh := ha.2.2.2 b (by omega) a (by omega) t s hb l (by omega) (by omega) (fun k hk => (hm k hk).symm)
    have hh' : w[b+l].1=w[a+l].1 := by
      simpa only [value,List.getElem?_eq_getElem hal,List.getElem?_eq_getElem hbl,P0DZBranch.Agree] using hh
    exact hh'.symm

omit [DecidableEq H] in
def Copied (w : List (Letter arity)) (J d : Nat) : Prop :=
  (∀ k, J ≤ k → k+1<w.length → w[k-d]?=w[k]?) ∧
    ∀ k, ∀ hk : k<w.length, J ≤ k →
      (w[k-d]'(lt_of_le_of_lt (Nat.sub_le _ _) hk)).1=w[k].1

theorem copies (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H)
    (ha : Accepted pol Q w ex ey) (J a b l : Nat) (side : Bool)
    (hab : a<b) (hbJ : b<J) (hbl : b+l=w.length-1)
    (hb : SymBorn pol Q w a side b true) (hm : WordMatch w a b l) : Copied w J (b-a) := by
  constructor
  · intro k hJk hkn
    have hil : k-b<l := by omega
    have hei : a+(k-b)=k-(b-a) := by omega
    have hej : b+(k-b)=k := by omega
    simpa only [hei,hej] using hm (k-b) hil
  · intro k hk hJk
    have hleft : a+(k-b)<w.length := by omega
    have hright : b+(k-b)<w.length := by omega
    have hmatch : WordMatch w a b (k-b) := fun i hi => hm i (by omega)
    have hh := ray_heads pol Q w ex ey ha a b (k-b) side true hb hmatch hleft hright
    have hei : a+(k-b)=k-(b-a) := by omega
    have hej : b+(k-b)=k := by omega
    simpa only [hei,hej] using hh

theorem first_period (Q : Query arity n) (w : List (Letter arity)) (hf : First pol Q w)
    (ex ey : Label H) (ha : Accepted pol Q w ex ey) (J : Nat) (hJ : J<w.length)
    (he : Empty (frame pol Q w J)) : ∃ d, 0<d ∧ d<J ∧ Copied w J d := by
  obtain ⟨a,b,l,side,hab,hbJ,hbl,hb,hm⟩ := surviving pol Q w hf ex ey ha J hJ he
  exact ⟨b-a,by omega,by omega,copies pol Q w ex ey ha J a b l side hab hbJ hbl hb hm⟩

end NSSE.MultiVarianceFirstTail
