import NSSE.P0PairImages

/-! A closed finite pair image protects an actual infinite repetition.
The statement includes every intermediate position within each block. -/
namespace NSSE.P0PairStreams
open P0ProperMachine P0ProperWords P0SafePairs P0PairImages
variable {Q A H : Type*}

def pairRun (M : Machine Q A H) (z : Nat → A) (p : Q × Q) : Nat → Q × Q
  | 0 => p
  | k+1 => move M (z k) (pairRun M z p k)

@[simp] theorem pairRun_zero (M : Machine Q A H) (z : Nat → A) (p : Q × Q) :
    pairRun M z p 0 = p := rfl

@[simp] theorem pairRun_succ (M : Machine Q A H) (z : Nat → A) (p : Q × Q) (k : Nat) :
    pairRun M z p (k+1) = move M (z k) (pairRun M z p k) := rfl

theorem pairRun_add (M : Machine Q A H) (z : Nat → A) (p : Q × Q) (a b : Nat) :
    pairRun M z p (a+b) = pairRun M (fun k => z (a+k)) (pairRun M z p a) b := by
  induction b with
  | zero => simp
  | succ b ih => rw [Nat.add_succ,pairRun_succ,pairRun_succ,ih]

theorem finish_spells (M : Machine Q A H) (z : Nat → A) (w : List A)
    (hz : Spells z w) (p : Q × Q) (k : Nat) (hk : k ≤ w.length) :
    finish M (w.take k) p = pairRun M z p k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkl : k < w.length := by omega
    have hletter : w[k] = z k := by
      simpa only [List.getElem?_eq_getElem hkl,Option.some.injEq] using hz k hkl
    rw [List.take_succ_eq_append_getElem hkl,finish_append]
    change move M w[k] (finish M (w.take k) p) = _
    rw [ih (by omega),hletter,pairRun_succ]

theorem matched_pair (M : Machine Q A H) (z : Nat → A) (a b l : Nat)
    (hm : Match z a b l) :
    pairRun M (fun k => z (b+k)) (run M z a,run M z b) l =
      (run M z (a+l),run M z (b+l)) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [pairRun_succ,ih (match_mono z a b (l+1) l (by omega) hm)]
    simp only [Nat.add_succ,run_succ,move]
    rw [hm l (by omega)]

def Copies (z : Nat → A) (c : List A) : Prop :=
  ∀ i, Spells (fun k => z (i*c.length+k)) c

def copiesWord (c : List A) : Nat → List A
  | 0 => []
  | k+1 => c ++ copiesWord c k

variable [DecidableEq Q] [Fintype Q] [DecidableEq H]
variable (M : Machine Q A H) [DecidablePred M.valid]

theorem stable_repeat (r c : List A)
    (hsuffix : ∃ u, r ++ c = u ++ r)
    (hcard : (image M (r ++ c)).card = (image M r).card)
    (k : Nat) (p : Q × Q) (hp : p ∈ image M r) :
    Safe M (copiesWord c k) p ∧ finish M (copiesWord c k) p ∈ image M r := by
  induction k generalizing p with
  | zero => exact ⟨image_valid M r p hp,hp⟩
  | succ k ih =>
    have hc := stable_total M r c hcard p hp
    obtain ⟨hs,he⟩ := ih (finish M c p) (stable_closed M r c hsuffix hcard p hp)
    exact ⟨(safe_append M c (copiesWord c k) p).mpr ⟨hc,hs⟩,
      by simpa only [copiesWord,finish_append] using he⟩

theorem stable_stream (r c : List A) (hc : 0 < c.length)
    (hsuffix : ∃ u, r ++ c = u ++ r)
    (hcard : (image M (r ++ c)).card = (image M r).card)
    (z : Nat → A) (hz : Copies z c) (p : Q × Q) (hp : p ∈ image M r) :
    ∀ k, ValidPair M (pairRun M z p k) := by
  have hblock : ∀ i, pairRun M z p (i*c.length) ∈ image M r := by
    intro i
    induction i with
    | zero => simpa using hp
    | succ i ih =>
      rw [Nat.succ_mul,pairRun_add]
      have he := finish_spells M (fun k => z (i*c.length+k)) c (hz i)
        (pairRun M z p (i*c.length)) c.length (by omega)
      rw [List.take_length] at he
      rw [← he]
      exact stable_closed M r c hsuffix hcard _ ih
  intro k
  let i := k / c.length
  let j := k % c.length
  have hj : j < c.length := Nat.mod_lt k hc
  have he : i*c.length+j = k := by
    dsimp [i,j]
    simpa only [Nat.mul_comm] using Nat.div_add_mod k c.length
  have hs := stable_total M r c hcard _ (hblock i)
  have hv := safe_at M c _ hs j
  rw [finish_spells M (fun t => z (i*c.length+t)) c (hz i) _ j (by omega),
    ← pairRun_add,he] at hv
  exact hv

end NSSE.P0PairStreams
