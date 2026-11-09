import NSSE.P0PeriodicInspectionDecision
import NSSE.P0WordLoop

/-! Actual finite blocks of a supplied literal cycle. Appending whole
cycles leaves the subsequent infinite stream unchanged, without primitivity. -/
namespace NSSE.P0PeriodicBlocks
open P0ProperWords P0PeriodicDriver P0PeriodicInspectionDecision
variable {A : Type*} {r : Nat}

def block (hr : 0 < r) (cycle : Fin r → A) (k : Nat) : List A :=
  prefixWord (fun n => cycle (phase r hr n)) (k*r)

@[simp] theorem block_length (hr : 0 < r) (cycle : Fin r → A) (k : Nat) :
    (block hr cycle k).length = k*r := prefix_length _ _

theorem lasso_spells (stem : List A) (hr : 0 < r) (cycle : Fin r → A) :
    Spells (lasso stem hr cycle) stem := by
  intro k hk
  rw [List.getElem?_eq_getElem hk]
  simp only [lasso,hk,dif_pos]

theorem append_spells (stem : List A) (hr : 0 < r) (cycle : Fin r → A) (k : Nat) :
    Spells (lasso stem hr cycle) (stem ++ block hr cycle k) := by
  intro n hn
  by_cases hs : n < stem.length
  · rw [List.getElem?_append_left hs,List.getElem?_eq_getElem hs]
    simp only [lasso,hs,dif_pos]
  · have hb : n-stem.length < (block hr cycle k).length := by
      simp only [List.length_append] at hn
      omega
    rw [List.getElem?_append_right (by omega)]
    have he := spells_prefix (fun j => cycle (phase r hr j)) (k*r) (n-stem.length) hb
    change (block hr cycle k)[n-stem.length]? = some _ at he
    simpa only [lasso,hs,dif_neg] using he

theorem append_prefix (stem : List A) (hr : 0 < r) (cycle : Fin r → A) (k : Nat) :
    stem ++ block hr cycle k =
      prefixWord (lasso stem hr cycle) (stem.length+k*r) := by
  have he := P0WordLoop.segment_of_spells (stem++block hr cycle k) (lasso stem hr cycle)
    (append_spells stem hr cycle k) 0 (stem++block hr cycle k).length (by omega)
  simp only [P0LoopStreams.segment,Nat.zero_add,List.drop_zero] at he
  rw [List.take_length] at he
  simpa only [List.length_append,block_length] using he.symm

theorem lasso_append (stem : List A) (hr : 0 < r) (cycle : Fin r → A) (k : Nat) :
    lasso (stem++block hr cycle k) hr cycle = lasso stem hr cycle := by
  funext n
  by_cases hn : n < (stem++block hr cycle k).length
  · have he := append_spells stem hr cycle k n hn
    rw [List.getElem?_eq_getElem hn] at he
    rw [lasso,dif_pos hn]
    exact Option.some.inj he
  · have hlen : (stem++block hr cycle k).length = stem.length+k*r := by simp
    have hs : ¬n < stem.length := by omega
    rw [lasso,dif_neg hn,lasso,dif_neg hs]
    congr 1
    apply Fin.ext
    change (n-(stem++block hr cycle k).length)%r = (n-stem.length)%r
    rw [hlen]
    have he : n-stem.length = (n-(stem.length+k*r))+k*r := by omega
    rw [he]
    simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.mul_zero,Nat.zero_mod,
      Nat.add_zero,Nat.mod_mod]

end NSSE.P0PeriodicBlocks
