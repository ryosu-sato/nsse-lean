import NSSE.P0PairStreams
import Mathlib.Data.Nat.Periodic

/-! Literal segments and exact one-loop origin representatives. A loop
in the state trace gives the same period to the complete future state trace. -/
namespace NSSE.P0LoopStreams
open P0ProperMachine P0ProperWords P0PairStreams
variable {Q A H : Type*}

def segment (z : Nat → A) (a l : Nat) : List A :=
  prefixWord (fun k => z (a+k)) l

@[simp] theorem segment_length (z : Nat → A) (a l : Nat) :
    (segment z a l).length = l := prefix_length _ _

theorem segment_spells (z : Nat → A) (a l : Nat) :
    Spells (fun k => z (a+k)) (segment z a l) := spells_prefix _ _

theorem segment_append (z : Nat → A) (a l k : Nat) :
    segment z a (l+k) = segment z a l ++ segment z (a+l) k := by
  unfold segment prefixWord
  rw [List.ofFn_add]
  congr 1
  apply congrArg List.ofFn
  funext i
  change z (a+(l+i.val)) = z ((a+l)+i.val)
  rw [Nat.add_assoc]

theorem segment_eq (z : Nat → A) (a b l : Nat) (h : Match z a b l) :
    segment z a l = segment z b l := by
  apply congrArg List.ofFn
  funext i
  exact h i.val i.isLt

theorem periodic_eq {T : Type*} (f : Nat → T) (d : Nat)
    (hp : Function.Periodic f d) (i j : Nat) (he : i%d = j%d) : f i = f j :=
  (hp.map_mod_nat i).symm.trans ((congrArg f he).trans (hp.map_mod_nat j))

theorem state_periodic (M : Machine Q A H) (z : Nat → A) (a d : Nat)
    (hp : Function.Periodic (fun k => z (a+k)) d)
    (hq : run M z a = run M z (a+d)) :
    Function.Periodic (fun k => run M z (a+k)) d := by
  intro k
  have hm : Match z a (a+d) k := by
    intro t _
    simpa only [Nat.add_assoc,Nat.add_comm d t] using (hp t).symm
  have he := run_equal M z a (a+d) k hq hm
  simpa only [Nat.add_assoc,Nat.add_comm d k] using he.symm

theorem origin_representative (M : Machine Q A H) (z : Nat → A) (a d : Nat)
    (hd : 0 < d) (hp : Function.Periodic (fun k => z (a+k)) d)
    (hq : run M z a = run M z (a+d)) (x : Nat) :
    ∃ y, y < a+d ∧ y ≤ x ∧
      ∀ k, run M z (y+k) = run M z (x+k) ∧ z (y+k) = z (x+k) := by
  by_cases hx : x < a
  · exact ⟨x,by omega,by omega,fun _ => ⟨rfl,rfl⟩⟩
  · let j := x-a
    have hxj : a+j = x := by dsimp [j]; omega
    have hj : j%d < d := Nat.mod_lt j hd
    have hjle : j%d ≤ j := Nat.mod_le j d
    refine ⟨a+j%d,by omega,by omega,?_⟩
    intro k
    have he : (j%d+k)%d = (j+k)%d := Nat.mod_add_mod j d k
    have hs := periodic_eq (fun t => run M z (a+t)) d
      (state_periodic M z a d hp hq) (j%d+k) (j+k) he
    have hl := periodic_eq (fun t => z (a+t)) d hp (j%d+k) (j+k) he
    simpa only [← Nat.add_assoc,hxj] using And.intro hs hl

theorem rotation_copies (z : Nat → A) (a d L : Nat)
    (hp : Function.Periodic (fun k => z (a+k)) d) :
    Copies (fun k => z (a+d+L+k)) (segment z (a+L) d) := by
  intro i k hk
  have hkd : k < d := by simpa using hk
  have hs := segment_spells z (a+L) d k (by simpa using hkd)
  rw [hs,segment_length]
  congr 1
  have he := periodic_eq (fun t => z (a+t)) d hp (L+k) (d+L+(i*d+k))
    (by simp [Nat.add_mod,Nat.mul_mod,Nat.add_assoc])
  simpa only [Nat.add_assoc] using he

theorem rotated_suffix (z : Nat → A) (a d L : Nat)
    (hp : Function.Periodic (fun k => z (a+k)) d) :
    segment z a L ++ segment z (a+L) d =
      segment z a d ++ segment z a L := by
  rw [← segment_append,show L+d = d+L by omega,segment_append]
  congr 1
  apply segment_eq
  intro k _
  simpa only [Nat.add_assoc,Nat.add_comm d k] using hp k

end NSSE.P0LoopStreams
