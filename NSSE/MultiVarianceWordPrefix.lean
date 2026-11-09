import NSSE.MultiVarianceWordReader

/-! Literal prefix restriction of the actual signed reader. Frames and
births are independent of terminal choices; proper labels and matching
current-head factors are preserved at every retained position. -/
namespace NSSE.MultiVarianceWordPrefix
open MultiConstructorConstraints (Query)
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceWordReader
open P0ProperWords (WordMatch)
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

theorem frame_prefix (Q : Query arity n) (w : List (Letter arity)) (m k : Nat) (hk : k ≤ m) :
    frame pol Q (w.take m) k = frame pol Q w k := by
  simp only [frame,List.take_take,Nat.min_eq_left hk]

theorem born_prefix (Q : Query arity n) (w : List (Letter arity)) (m a b : Nat)
    (ha : a ≤ m) (hb : b ≤ m) (s t : Bool) :
    Born pol Q (w.take m) a s b t ↔ Born pol Q w a s b t := by
  simp only [Born,frame_prefix pol Q w m a ha,frame_prefix pol Q w m b hb]

omit [DecidableEq H] in
theorem value_prefix (w : List (Letter arity)) (m k : Nat) (hk : k<m)
    (ex ey ex' ey' : Label H) (side : Bool) (hm : m ≤ w.length) :
    value (w.take m) ex' ey' side k = value w ex ey side k := by
  have hkn : k<w.length := by omega
  rw [value,List.getElem?_take_of_lt hk,value,List.getElem?_eq_getElem hkn]

omit [DecidableEq H] in
theorem match_prefix {A : Type*} (w : List A) (m a b l : Nat) (ha : a+l ≤ m) (hb : b+l ≤ m) :
    WordMatch (w.take m) a b l ↔ WordMatch w a b l := by
  unfold WordMatch
  have he (i : Nat) (hi : i<l) :
      (w.take m)[a+i]?=w[a+i]? ∧ (w.take m)[b+i]?=w[b+i]? :=
    ⟨List.getElem?_take_of_lt (by omega),List.getElem?_take_of_lt (by omega)⟩
  exact ⟨fun h i hi => by simpa only [(he i hi).1,(he i hi).2] using h i hi,
    fun h i hi => by simpa only [(he i hi).1,(he i hi).2] using h i hi⟩

omit [DecidableEq H] in
theorem value_isolated (w : List (Letter arity)) (m k : Nat) (hm : m<w.length) (hk : k ≤ m)
    (ex ey ey' : Label H) (side : Bool) (hs : side=true → k ≠ m) :
    value (w.take m) (.node w[m].1) ey' side k=value w ex ey side k := by
  by_cases hkm : k<m
  · exact value_prefix w m k hkm ex ey _ _ side (by omega)
  · have he : k=m := by omega
    subst k
    have hside : side=false := by cases side <;> simp_all
    have hlen : (w.take m).length=m := List.length_take_of_le (by omega)
    have hn : (w.take m)[m]?=none := List.getElem?_eq_none (by omega)
    rw [value,hn,hside,value,List.getElem?_eq_getElem hm]
    rfl

end NSSE.MultiVarianceWordPrefix
