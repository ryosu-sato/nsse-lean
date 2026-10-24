import NSSE.BitMachine
import NSSE.RawQueryCodec

/-! # The query parser on the bit machine

Stage three of the machine realisation. The term component of v1632 is used at
four call sites — the two sides of a premise and the two query terms — each
with its own copy of the component's states and its own exit continuation, so
no return address has to be stored. The premise list is a loop driven by the
continuation bit; the tag bit (`≤` or `=`) is pushed on stack B, so the parse
is recorded rather than merely accepted.

`query_run` proves that the machine, started on the code of a well-formed
query, halts with the rest of the input untouched and stack A empty again,
within `queryTime`, and `queryTime_le` bounds that by a constant multiple of
the code length: the whole front end of the pipeline is LINEAR-time on a
machine whose every step reads or moves one bit.
-/

namespace NSSE.BitMachineQuery

open RawBitNumeral RawTermCodec RawQueryCodec BitMachine

/-- The four places a term is parsed. -/
inductive Site
  | p1
  | p2
  | q1
  | q2
  deriving DecidableEq

inductive QSt
  | pre
  | tag
  | tagT
  | tagF
  | sent (s : Site)
  | trm (s : Site) (x : TSt)
  | done
  | fail
  deriving DecidableEq

def exitOf : Site → QSt
  | .p1 => .sent .p2
  | .p2 => .pre
  | .q1 => .sent .q2
  | .q2 => .done

def queryProg (d : Nat) : QSt → Instr QSt
  | .pre => .read .tag (.sent .q1) .fail
  | .tag => .read .tagT .tagF .fail
  | .tagT => .pushB true (.sent .p1)
  | .tagF => .pushB false (.sent .p1)
  | .sent s => .pushA false (.trm s .tok)
  | .trm s x => termCode d (fun y => QSt.trm s y) (exitOf s) .fail x
  | .done => .halt
  | .fail => .halt

/-! ## Step counts -/

def litTime (d : Nat) : RawLit → Nat
  | .le a b => 5+termTime d a+termTime d b
  | .eq a b => 5+termTime d a+termTime d b

def queryTime (d : Nat) (Q : RawQuery) : Nat :=
  3+(Q.premises.map (litTime d)).sum+termTime d Q.left+termTime d Q.right

/-! ## The term component at each site -/

theorem site_code (d : Nat) (s : Site) (x : TSt) :
    queryProg d (QSt.trm s x) = termCode d (fun y => QSt.trm s y) (exitOf s) .fail x := rfl

theorem term_at (d : Nat) (hd : 0 < d) (s : Site) (t : Raw) (h : WellFormed d t)
    (rest A b : List Bool) : ∃ b',
    iter (queryProg d) (termTime d t) ⟨.trm s .tok,enc t ++ rest,false :: A,b⟩
      = ⟨exitOf s,rest,A,b'⟩ := by
  obtain ⟨b',hb⟩ := (term_component (queryProg d) d (fun y => QSt.trm s y) (exitOf s) .fail hd
    (site_code d s)).1 t h rest (false :: A) b
  exact ⟨b',by simpa only [afterState, List.tail] using hb⟩

/-! ## One premise -/

theorem lit_run (d : Nat) (hd : 0 < d) (l : RawLit) (h : WellFormedLit d l)
    (rest A b : List Bool) : ∃ b',
    iter (queryProg d) (litTime d l) ⟨.pre,true :: (encLit l ++ rest),A,b⟩
      = ⟨.pre,rest,A,b'⟩ := by
  cases l with
  | le x y =>
    obtain ⟨hx,hy⟩ := h
    have he : litTime d (.le x y) = 1+(1+(1+(1+(termTime d x+(1+termTime d y))))) := by
      simp only [litTime]; ring
    rw [he]
    simp only [encLit, List.cons_append]
    rw [iter_step' (queryProg d) (c' := ⟨.tag,false :: (enc x ++ enc y ++ rest),A,b⟩) rfl]
    rw [iter_step' (queryProg d) (c' := ⟨.tagF,enc x ++ enc y ++ rest,A,b⟩) rfl]
    rw [iter_step' (queryProg d) (c' := ⟨.sent .p1,enc x ++ enc y ++ rest,A,false :: b⟩) rfl]
    rw [iter_step' (queryProg d)
      (c' := ⟨.trm .p1 .tok,enc x ++ enc y ++ rest,false :: A,false :: b⟩) rfl]
    obtain ⟨b1,hb1⟩ := term_at d hd .p1 x hx (enc y ++ rest) A (false :: b)
    rw [List.append_assoc, iter_add, hb1]
    simp only [exitOf]
    rw [iter_step' (queryProg d) (c' := ⟨.trm .p2 .tok,enc y ++ rest,false :: A,b1⟩) rfl]
    obtain ⟨b2,hb2⟩ := term_at d hd .p2 y hy rest A b1
    exact ⟨b2,by simpa only [exitOf] using hb2⟩
  | eq x y =>
    obtain ⟨hx,hy⟩ := h
    have he : litTime d (.eq x y) = 1+(1+(1+(1+(termTime d x+(1+termTime d y))))) := by
      simp only [litTime]; ring
    rw [he]
    simp only [encLit, List.cons_append]
    rw [iter_step' (queryProg d) (c' := ⟨.tag,true :: (enc x ++ enc y ++ rest),A,b⟩) rfl]
    rw [iter_step' (queryProg d) (c' := ⟨.tagT,enc x ++ enc y ++ rest,A,b⟩) rfl]
    rw [iter_step' (queryProg d) (c' := ⟨.sent .p1,enc x ++ enc y ++ rest,A,true :: b⟩) rfl]
    rw [iter_step' (queryProg d)
      (c' := ⟨.trm .p1 .tok,enc x ++ enc y ++ rest,false :: A,true :: b⟩) rfl]
    obtain ⟨b1,hb1⟩ := term_at d hd .p1 x hx (enc y ++ rest) A (true :: b)
    rw [List.append_assoc, iter_add, hb1]
    simp only [exitOf]
    rw [iter_step' (queryProg d) (c' := ⟨.trm .p2 .tok,enc y ++ rest,false :: A,b1⟩) rfl]
    obtain ⟨b2,hb2⟩ := term_at d hd .p2 y hy rest A b1
    exact ⟨b2,by simpa only [exitOf] using hb2⟩

/-! ## The premise list -/

theorem premises_run (d : Nat) (hd : 0 < d) (ls : List RawLit)
    (h : ∀ l ∈ ls, WellFormedLit d l) (rest A b : List Bool) : ∃ b',
    iter (queryProg d) ((ls.map (litTime d)).sum+1)
        ⟨.pre,encPremises ls ++ rest,A,b⟩
      = ⟨.sent .q1,rest,A,b'⟩ := by
  induction ls generalizing b with
  | nil =>
    refine ⟨b,?_⟩
    simp only [List.map_nil, List.sum_nil, Nat.zero_add, encPremises, List.cons_append,
      List.nil_append]
    rw [iter_one (queryProg d) (c' := ⟨.sent .q1,rest,A,b⟩) rfl]
  | cons l ls ih =>
    have hl : WellFormedLit d l := h l (by simp)
    have hls : ∀ u ∈ ls, WellFormedLit d u := fun u hu => h u (by simp [hu])
    simp only [List.map_cons, List.sum_cons, encPremises, List.cons_append, List.append_assoc]
    obtain ⟨b1,hb1⟩ := lit_run d hd l hl (encPremises ls ++ rest) A b
    rw [show litTime d l+(ls.map (litTime d)).sum+1
      = litTime d l+((ls.map (litTime d)).sum+1) from by ring]
    rw [iter_add, hb1]
    exact ih hls b1

/-! ## The whole query -/

theorem query_run (d : Nat) (hd : 0 < d) (Q : RawQuery) (h : WellFormedQuery d Q)
    (rest b : List Bool) : ∃ b',
    iter (queryProg d) (queryTime d Q) ⟨.pre,encQuery Q ++ rest,[],b⟩
      = ⟨.done,rest,[],b'⟩ := by
  obtain ⟨hp,hl,hr⟩ := h
  have he : queryTime d Q
      = ((Q.premises.map (litTime d)).sum+1)+(1+(termTime d Q.left+(1+termTime d Q.right))) := by
    simp only [queryTime]; ring
  rw [he]
  simp only [encQuery, List.append_assoc]
  obtain ⟨b1,hb1⟩ := premises_run d hd Q.premises hp (enc Q.left ++ (enc Q.right ++ rest)) [] b
  rw [iter_add, hb1]
  rw [iter_step' (queryProg d)
    (c' := ⟨.trm .q1 .tok,enc Q.left ++ (enc Q.right ++ rest),[false],b1⟩) rfl]
  obtain ⟨b2,hb2⟩ := term_at d hd .q1 Q.left hl (enc Q.right ++ rest) [] b1
  rw [iter_add, hb2]
  simp only [exitOf]
  rw [iter_step' (queryProg d) (c' := ⟨.trm .q2 .tok,enc Q.right ++ rest,[false],b2⟩) rfl]
  obtain ⟨b3,hb3⟩ := term_at d hd .q2 Q.right hr rest [] b2
  exact ⟨b3,by simpa only [exitOf] using hb3⟩

/-! ## Linear time -/

theorem litTime_le (d : Nat) (l : RawLit) : litTime d l ≤ (d+6)*(encLit l).length+5 := by
  cases l with
  | le a b =>
    have ha := termTime_le d a
    have hb := termTime_le d b
    have hmul : (d+6)*((enc a).length+(enc b).length+1)
        = (d+6)*(enc a).length+(d+6)*(enc b).length+(d+6) := by ring
    simp only [litTime, encLit, List.length_cons, List.length_append]
    omega
  | eq a b =>
    have ha := termTime_le d a
    have hb := termTime_le d b
    have hmul : (d+6)*((enc a).length+(enc b).length+1)
        = (d+6)*(enc a).length+(d+6)*(enc b).length+(d+6) := by ring
    simp only [litTime, encLit, List.length_cons, List.length_append]
    omega

theorem premisesTime_le (d : Nat) (ls : List RawLit) :
    (ls.map (litTime d)).sum ≤ (d+6)*(encPremises ls).length+5*ls.length := by
  induction ls with
  | nil => simp [encPremises]
  | cons l ls ih =>
    have hl := litTime_le d l
    have hmul : (d+6)*((encLit l).length+(encPremises ls).length+1)
        = (d+6)*(encLit l).length+(d+6)*(encPremises ls).length+(d+6) := by ring
    simp only [List.map_cons, List.sum_cons, encPremises, List.length_cons, List.length_append,
      List.length_append]
    omega

/-- The front end is linear: parsing a whole query costs at most a constant
(depending on the arity alone) times the length of its code. -/
theorem queryTime_le (d : Nat) (Q : RawQuery) :
    queryTime d Q ≤ (d+11)*(encQuery Q).length+3 := by
  have hp := premisesTime_le d Q.premises
  have hl := termTime_le d Q.left
  have hr := termTime_le d Q.right
  have hlen : Q.premises.length ≤ (encPremises Q.premises).length := by
    induction Q.premises with
    | nil => simp [encPremises]
    | cons l ls ih =>
      simp only [List.length_cons, encPremises, List.length_append]
      omega
  have hmul : (d+11)*((encPremises Q.premises).length+(enc Q.left).length+(enc Q.right).length)
      = (d+6)*(encPremises Q.premises).length+5*(encPremises Q.premises).length
        +(d+6)*(enc Q.left).length+5*(enc Q.left).length
        +(d+6)*(enc Q.right).length+5*(enc Q.right).length := by ring
  simp only [queryTime, encQuery, List.length_append]
  omega

end NSSE.BitMachineQuery
