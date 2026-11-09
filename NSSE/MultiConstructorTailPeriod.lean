import NSSE.MultiConstructorFirstRay

/-! A surviving original comparison copies every proper head in the empty
tail and every nonfinal letter. The final letter is deliberately excluded. -/
namespace NSSE.MultiConstructorTailPeriod
open MultiConstructorConstraints MultiConstructorTrees MultiConstructorUnifiedWords
open MultiConstructorIsolatedPrefix MultiConstructorFirstRay
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

omit [DecidableEq H] in
def Copied (w : List (Fin D)) (heads : Fin w.length → H) (J d : Nat) : Prop :=
  (∀ k, J ≤ k → k+1 < w.length → w[k-d]? = w[k]?) ∧
  (∀ k : Fin w.length, J ≤ k.val → heads ⟨k.val-d,lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ = heads k)

theorem ray_heads (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (ex ey : Label H) (ha : Assignment phi x y w heads ex ey)
    (a b l : Nat) (hb : Born phi x y w a b) (hw : P0ProperWords.WordMatch w a b l)
    (hal : a+l < w.length) (hbl : b+l < w.length) :
    heads ⟨a+l,hal⟩ = heads ⟨b+l,hbl⟩ := by
  have h := ha.2.2 ⟨a,by omega⟩ ⟨b,by omega⟩ ⟨l,by omega⟩ hb
    (by change a+l ≤ w.length; omega) (by change b+l ≤ w.length; omega) hw
  change P0DZBranch.Agree (value w heads ex ey false (a+l)) (value w heads ex ey true (b+l)) at h
  simpa only [value,dif_pos hal,dif_pos hbl,P0DZBranch.Agree] using h

theorem copies (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (ex ey : Label H) (ha : Assignment phi x y w heads ex ey)
    (J a b l : Nat) (hab : a < b) (hbJ : b < J) (hbl : b+l = w.length-1)
    (hb : Born phi x y w a b) (hw : P0ProperWords.WordMatch w a b l) :
    Copied w heads J (b-a) := by
  constructor
  · intro k hJk hkn
    have hil : k-b < l := by omega
    have hei : a+(k-b) = k-(b-a) := by omega
    have hej : b+(k-b) = k := by omega
    simpa only [hei,hej] using hw (k-b) hil
  · intro k hJk
    have hleft : a+(k.val-b) < w.length := by have := k.isLt; omega
    have hright : b+(k.val-b) < w.length := by have := k.isLt; omega
    have hm : P0ProperWords.WordMatch w a b (k.val-b) := by
      intro i hi
      exact hw i (by have := k.isLt; omega)
    have h := ray_heads phi x y w heads ex ey ha a b (k.val-b) hb hm hleft hright
    have hei : a+(k.val-b) = k.val-(b-a) := by omega
    have hej : b+(k.val-b) = k.val := by omega
    simpa only [hei,hej] using h

theorem first_period (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (hf : First phi x y w) (heads : Fin w.length → H) (ex ey : Label H)
    (ha : Assignment phi x y w heads ex ey) (J : Nat) (hJ : J < w.length)
    (he : row phi x y w J = (∅,∅)) :
    ∃ d, 0 < d ∧ d < J ∧ Copied w heads J d := by
  obtain ⟨a,b,l,hab,hbJ,hbl,hb,hw⟩ := surviving phi x y w hf heads ex ey ha J hJ he
  exact ⟨b-a,by omega,by omega,copies phi x y w heads ex ey ha J a b l hab hbJ hbl hb hw⟩

end NSSE.MultiConstructorTailPeriod
