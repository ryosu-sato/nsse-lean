import NSSE.P0DZBranch

/-! Actual D/Z path facts: every strict prefix is proper, the final state
ID occurs only at the endpoint, and proper equal-factor runs agree. -/
namespace NSSE.P0DZTrace
open P0DZBranch P0ProperWords
variable {Q Z A H : Type*}

theorem proper_append (J : Branch Q Z A H) (q : Q) (u v : List A) :
    properFrom J q (u++v) = (properFrom J q u).bind (fun r => properFrom J r v) := by
  simp only [properFrom,List.foldl_append]
  cases he : u.foldl (advance J) (some q)
  · exact fold_failure J v
  · rfl

theorem finish_cons (J : Branch Q Z A H) (q : Q) (a : A) (v : List A) (hv : v ≠ []) :
    finishFrom J q (a::v) = (J.next q a).bind (fun r => finishFrom J r v) := by
  cases v with
  | nil => exact False.elim (hv rfl)
  | cons b v => rfl

theorem finish_split (J : Branch Q Z A H) (q : Q) (u v : List A) (hv : v ≠ []) :
    finishFrom J q (u++v) = (properFrom J q u).bind (fun r => finishFrom J r v) := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih =>
    have huv : u++v ≠ [] := fun he => hv (List.append_eq_nil_iff.mp he).2
    rw [List.cons_append,finish_cons J q a (u++v) huv,proper_cons]
    simp only [ih,Option.bind_assoc]

def properAt (J : Branch Q Z A H) (w : List A) (k : Nat) : Option Q :=
  properFrom J J.initial (w.take k)

theorem complete_prefix (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (k : Nat) (hk : k < w.length) : ∃ q, properAt J w k = some q := by
  have hv : w.drop k ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [List.length_drop,List.length_nil] at hh
    omega
  have hs := finish_split J J.initial (w.take k) (w.drop k) hv
  rw [List.take_append_drop] at hs
  change (finishFrom J J.initial w).isSome = true at hc
  rw [hs] at hc
  cases he : properFrom J J.initial (w.take k) with
  | none => simp [he] at hc
  | some q => exact ⟨q,he⟩

theorem complete_terminal (J : Branch Q Z A H) (w : List A) (hc : Complete J w) :
    ∃ z, terminal J w = some z := by
  cases he : terminal J w with
  | none => simp only [Complete,he,Option.isSome_none,Bool.false_eq_true] at hc
  | some z => exact ⟨z,rfl⟩

theorem terminal_unique (J : Branch Q Z A H) (w : List A) (k : Nat) (hk : k ≤ w.length)
    (z : Z) (he : stateAt J w k = some (.inr z)) : k = w.length := by
  by_contra hn
  rw [proper_state J w k (by omega)] at he
  cases hq : properFrom J J.initial (w.take k) <;> simp [hq] at he

theorem initial_state (J : Branch Q Z A H) (w : List A) (hc : Complete J w) :
    stateAt J w 0 = some (.inl J.initial) := by
  have hp : 0 < w.length := List.length_pos_iff.mpr (complete_nonempty J w hc)
  rw [proper_state J w 0 hp]
  rfl

theorem proper_succ (J : Branch Q Z A H) (w : List A) (k : Nat) (hk : k < w.length) :
    properAt J w (k+1) = advance J (properAt J w k) w[k] := by
  simp only [properAt,properFrom,List.take_succ_eq_append_getElem hk,List.foldl_append,
    List.foldl_cons,List.foldl_nil]

theorem proper_equal (J : Branch Q Z A H) (w : List A) (a b l : Nat)
    (ha : a+l ≤ w.length) (hb : b+l ≤ w.length)
    (he : properAt J w a = properAt J w b) (hm : WordMatch w a b l) :
    properAt J w (a+l) = properAt J w (b+l) := by
  induction l with
  | zero => simpa using he
  | succ l ih =>
    have hmatch : WordMatch w a b l := fun k hk => hm k (by omega)
    have hl := hm l (by omega)
    rw [List.getElem?_eq_getElem (by omega),List.getElem?_eq_getElem (by omega),Option.some.injEq] at hl
    rw [Nat.add_succ,Nat.add_succ,proper_succ J w (a+l) (by omega),
      proper_succ J w (b+l) (by omega),ih (by omega) (by omega) hmatch,hl]

theorem label_proper (J : Branch Q Z A H) (w : List A) (k : Nat) (hk : k < w.length)
    (q : Q) (hq : properAt J w k = some q) (s : Bool) : labelAt J w s k = .node (J.head q) := by
  unfold labelAt
  rw [proper_state J w k hk]
  dsimp only [properAt] at hq
  rw [hq]
  rfl

theorem label_terminal (J : Branch Q Z A H) (w : List A) (hc : Complete J w) (s : Bool) :
    labelAt J w s w.length = endpoint J s := by
  obtain ⟨z,hz⟩ := complete_terminal J w hc
  unfold labelAt
  rw [terminal_state,hz]
  rfl

theorem agree_eq {a b : MultiConstructorTrees.Label H} (h : Agree a b) : a = b := by
  cases a <;> cases b <;> simp_all [Agree]

theorem no_diagonal_cross (J : Branch Q Z A H) (w : List A) (hends : J.endX ≠ J.endY)
    (hw : Accepted J w) (a : Nat) (ha : a ≤ w.length) (s t : Bool) (hst : s ≠ t) :
    ¬ bornAt J w a s a t := by
  intro hborn
  have hc := hw.2 a ha a ha s t (Or.inr hst) hborn (w.length-a)
    (by omega) (by omega) (by omega) (fun _ _ => rfl)
  rw [show a+(w.length-a) = w.length by omega,label_terminal J w hw.1 s,
    label_terminal J w hw.1 t] at hc
  have he := agree_eq hc
  cases s <;> cases t <;> simp_all [endpoint]

end NSSE.P0DZTrace
