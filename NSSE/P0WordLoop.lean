import NSSE.P0LoopStreams

/-! The literal ultimately periodic stream constructed from a finite
word. A repeated suffix marker preserves the entire word, even on overlap. -/
namespace NSSE.P0WordLoop
open P0ProperWords P0LoopStreams
variable {A : Type*}

def index (a d k : Nat) : Nat := if k < a then k else a+(k-a)%d

theorem index_lt (a d : Nat) (hd : 0 < d) (k : Nat) : index a d k < a+d := by
  unfold index
  split_ifs with hk
  · omega
  · have := Nat.mod_lt (k-a) hd
    omega

def stream (w : List A) (a d : Nat) (hd : 0 < d) (hw : a+d ≤ w.length) (k : Nat) : A :=
  w[index a d k]'(by have := index_lt a d hd k; omega)

theorem index_initial (a d k : Nat) (hk : k < a+d) : index a d k = k := by
  unfold index
  split_ifs with hka
  · rfl
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

theorem initial (w : List A) (a d : Nat) (hd : 0 < d) (hw : a+d ≤ w.length)
    (k : Nat) (hk : k < a+d) : w[k]? = some (stream w a d hd hw k) := by
  unfold stream
  simp only [index_initial a d k hk]
  exact List.getElem?_eq_getElem (show k < w.length by omega)

theorem periodic (w : List A) (a d : Nat) (hd : 0 < d) (hw : a+d ≤ w.length) :
    Function.Periodic (fun k => stream w a d hd hw (a+k)) d := by
  intro k
  unfold stream
  have he : index a d (a+(k+d)) = index a d (a+k) := by
    simp [index,Nat.add_mod]
  simp only [he]

theorem spells (w : List A) (a d L : Nat) (hd : 0 < d)
    (hlen : w.length = a+d+L)
    (hm : WordMatch w a (a+d) L) :
    Spells (stream w a d hd (by omega)) w := by
  let z := stream w a d hd (by omega)
  have hp := periodic w a d hd (show a+d ≤ w.length by omega)
  intro k hk
  change w[k]? = some (z k)
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hkb : k < a+d
    · exact initial w a d hd (by omega) k hkb
    · have hkL : k-(a+d) < L := by omega
      have hcopy := hm (k-(a+d)) hkL
      have he1 : a+(k-(a+d)) = k-d := by omega
      have he2 : a+d+(k-(a+d)) = k := by omega
      rw [he1,he2] at hcopy
      have hprev := ih (k-d) (by omega) (by omega)
      have hz : z (k-d) = z k := by
        have he := hp (k-d-a)
        change z (a+(k-d-a+d)) = z (a+(k-d-a)) at he
        have ha : a+(k-d-a) = k-d := by omega
        have hb : a+(k-d-a+d) = k := by omega
        rw [ha,hb] at he
        exact he.symm
      exact hcopy.symm.trans (hprev.trans (congrArg some hz))

theorem segment_of_spells (w : List A) (z : Nat → A) (hz : Spells z w)
    (a L : Nat) (h : a+L ≤ w.length) :
    segment z a L = (w.drop a).take L := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < L
  · have hs := segment_spells z a L k (by simpa using hk)
    rw [hs,List.getElem?_take_of_lt hk,List.getElem?_drop,hz (a+k) (by omega)]
  · have hn : (segment z a L)[k]? = none :=
      List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hk)
    rw [hn]
    symm
    apply List.getElem?_eq_none
    simp only [List.length_take]
    omega

end NSSE.P0WordLoop
