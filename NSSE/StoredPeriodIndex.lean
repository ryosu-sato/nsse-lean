import NSSE.StoredPeriodEnumeration
import NSSE.StoredFiniteRelations

namespace NSSE.StoredPeriodIndex
variable {d n p : Nat}
abbrev State := PeriodMonitorState (Fin d) (Fin n) p
local instance : BEq (State (d := d) (n := n) (p := p)) := instBEqOfDecidableEq

def equal (s t : State (d := d) (n := n) (p := p)) : Bool × Nat :=
  let b := StoredFiniteRelations.equal s.buffer.word t.buffer.word
  let q := StoredForwardPedge.equal s.rootState t.rootState
  let o := StoredForwardPedge.equal s.offset t.offset
  (b.1 && q.1 && o.1 && (s.valid == t.valid) && (s.pastRoot == t.pastRoot),
    5+b.2+q.2+o.2)

theorem equal_value (s t : State (d := d) (n := n) (p := p)) :
    (equal s t).1=true ↔ s=t := by
  simp only [equal,Bool.and_eq_true,StoredFiniteRelations.equal_correct,
    StoredForwardPedge.equal_value,beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨⟨hb,hq⟩,ho⟩,hv⟩,hr⟩
    cases s with | mk sb sq so sv sr =>
      cases t with | mk tb tq ot tv tr =>
        cases sb; cases tb
        cases hb; cases hq; cases ho; cases hv; cases hr; rfl
  · rintro rfl; exact ⟨⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩

def equalBudget (d n p : Nat) := 8+p*(d+2)+n+p

theorem equal_bound (s t : State (d := d) (n := n) (p := p)) :
    (equal s t).2 ≤ equalBudget d n p := by
  have hb := StoredFiniteRelations.equal_bound s.buffer.word t.buffer.word
  have hq := StoredForwardPedge.equal_bound s.rootState t.rootState
  have ho := StoredForwardPedge.equal_bound s.offset t.offset
  have hl := Nat.mul_le_mul_right (d+2) s.buffer.length_le
  simp only [equal,equalBudget]
  nlinarith

def index (s : State (d := d) (n := n) (p := p)) : List (State (d := d) (n := n) (p := p)) → Nat × Nat
  | [] => (0,1)
  | t::ts => let e := equal s t
            if e.1 then (0,1+e.2)
            else let r := index s ts; (r.1+1,2+e.2+r.2)

theorem index_value (s : State (d := d) (n := n) (p := p)) (ts : List (State (d := d) (n := n) (p := p))) :
    (index s ts).1 = ts.idxOf s := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have he : (equal s t).1=decide (s=t) := Bool.eq_iff_iff.mpr (by simp only [equal_value,decide_eq_true_eq])
    simp only [index,he,ih]
    by_cases h : s=t
    · subst t; simp
    · simp only [h,decide_false,Bool.false_eq_true,↓reduceIte]
      exact (List.idxOf_cons_ne ts (Ne.symm h)).symm

def budget (d n p k : Nat) := 1+k*(2+equalBudget d n p)

theorem bound (s : State (d := d) (n := n) (p := p)) (ts : List (State (d := d) (n := n) (p := p))) :
    (index s ts).2 ≤ budget d n p ts.length := by
  induction ts with
  | nil => simp [index,budget]
  | cons t ts ih =>
    have he := equal_bound s t
    simp only [index,budget,List.length_cons] at *
    split <;> nlinarith
end NSSE.StoredPeriodIndex
