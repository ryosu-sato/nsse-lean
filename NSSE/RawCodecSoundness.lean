import NSSE.RawQueryCodec

/-! # What a successful parse guarantees

The round trips of v1622/v1623 say what happens on strings that ARE codes. For
a complexity statement about an arbitrary input one also needs to know what a
successful parse of an arbitrary string yields:

* the decoded term has exactly `d` children at every node, so it is a legal
  term of the signature (`decTerm_sound`, `decode_sound`);
* its symbol count, plus whatever is left unconsumed, is at most the length of
  the input — so the decoded query is never larger than the string it came
  from (`qsize ≤ |w|`).

Together with `decode_cost` this makes every quantity downstream a function of
the input length alone.
-/

namespace NSSE.RawCodecSoundness

open RawBitNumeral RawTermCodec RawQueryCodec

/-! ## Terms -/

theorem dec_sound (d : Nat) : ∀ fuel : Nat,
    (∀ (w : List Bool) (t : Raw) (rest : List Bool), (decTerm d fuel w).1 = some (t,rest) →
        WellFormed d t ∧ size t+rest.length ≤ w.length) ∧
    (∀ (k : Nat) (w : List Bool) (ts : List Raw) (rest : List Bool),
        (decTerms d fuel k w).1 = some (ts,rest) →
        ts.length = k ∧ (∀ t ∈ ts, WellFormed d t) ∧
          (ts.map size).sum+rest.length ≤ w.length) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    · intro w t rest h; simp [decTerm] at h
    · intro k
      induction k with
      | zero =>
        intro w ts rest h
        simp only [decTerms, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        simp
      | succ k _ =>
        intro w ts rest h
        have h0 : decTerm d 0 w = (none,1) := by simp [decTerm]
        simp [decTerms, h0] at h
  | succ f ihf =>
    have hterm : ∀ (w : List Bool) (t : Raw) (rest : List Bool),
        (decTerm d (f+1) w).1 = some (t,rest) →
          WellFormed d t ∧ size t+rest.length ≤ w.length := by
      intro w t rest h
      match w with
      | [] => simp [decTerm] at h
      | [_] => simp [decTerm] at h
      | false :: false :: w' =>
        simp only [decTerm, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        exact ⟨by simp [WellFormed],by simp only [size, List.length_cons]; omega⟩
      | false :: true :: w' =>
        simp only [decTerm, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        exact ⟨by simp [WellFormed],by simp only [size, List.length_cons]; omega⟩
      | true :: true :: w' =>
        have hr := decNat_rem w'
        simp only [decTerm] at h
        cases hc : (decNat w').1 with
        | none => simp [hc] at h
        | some p =>
          obtain ⟨i,v⟩ := p
          simp only [hc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          simp only [hc, remLen] at hr
          obtain ⟨rfl,rfl⟩ := h
          exact ⟨by simp [WellFormed],by simp only [size, List.length_cons]; omega⟩
      | true :: false :: w' =>
        simp only [decTerm] at h
        cases hc : (decTerms d f d w').1 with
        | none => simp [hc] at h
        | some p =>
          obtain ⟨ts,v⟩ := p
          simp only [hc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hlen,hwf,hsz⟩ := ihf.2 d w' ts v hc
          obtain ⟨rfl,rfl⟩ := h
          have hnode : WellFormed d (Raw.node ts) := by
            simp only [WellFormed]
            exact ⟨hlen,hwf⟩
          refine ⟨hnode,?_⟩
          simp only [size, List.length_cons]
          omega
    refine ⟨hterm,?_⟩
    intro k
    induction k with
    | zero =>
      intro w ts rest h
      simp only [decTerms, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      simp
    | succ k ih =>
      intro w ts rest h
      simp only [decTerms] at h
      cases hc : (decTerm d (f+1) w).1 with
      | none => simp [hc] at h
      | some p =>
        obtain ⟨t,w'⟩ := p
        simp only [hc] at h
        obtain ⟨hwf,hsz⟩ := hterm w t w' hc
        cases hc' : (decTerms d (f+1) k w').1 with
        | none => simp [hc'] at h
        | some q =>
          obtain ⟨us,v⟩ := q
          simp only [hc', Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hlen,hwfs,hszs⟩ := ih w' us v hc'
          obtain ⟨rfl,rfl⟩ := h
          refine ⟨by simp [hlen],?_,?_⟩
          · intro u hu
            rcases List.mem_cons.mp hu with rfl | hu
            · exact hwf
            · exact hwfs u hu
          · simp only [List.map_cons, List.sum_cons]
            omega

theorem decTerm_sound (d fuel : Nat) (w : List Bool) (t : Raw) (rest : List Bool)
    (h : (decTerm d fuel w).1 = some (t,rest)) :
    WellFormed d t ∧ size t+rest.length ≤ w.length :=
  (dec_sound d fuel).1 w t rest h

/-! ## Queries -/

theorem decLit_sound (d fuel : Nat) (w : List Bool) (l : RawLit) (rest : List Bool)
    (h : (decLit d fuel w).1 = some (l,rest)) :
    WellFormedLit d l ∧ litSize l+rest.length ≤ w.length := by
  match w with
  | [] => simp [decLit] at h
  | b :: w' =>
    simp only [decLit] at h
    cases hc : (decTerm d fuel w').1 with
    | none => simp [hc] at h
    | some p =>
      obtain ⟨a,w''⟩ := p
      simp only [hc] at h
      obtain ⟨hwa,hsa⟩ := decTerm_sound d fuel w' a w'' hc
      cases hc' : (decTerm d fuel w'').1 with
      | none => simp [hc'] at h
      | some q =>
        obtain ⟨c,w'''⟩ := q
        simp only [hc', Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hwc,hsc⟩ := decTerm_sound d fuel w'' c w''' hc'
        obtain ⟨rfl,rfl⟩ := h
        have hl : litSize (if b then RawLit.eq a c else RawLit.le a c) = 1+size a+size c := by
          cases b <;> simp [litSize]
        refine ⟨by cases b <;> exact ⟨hwa,hwc⟩,?_⟩
        rw [hl]
        simp only [List.length_cons]
        omega

theorem decPremises_sound (d fuel : Nat) : ∀ (budget : Nat) (w : List Bool)
    (ls : List RawLit) (rest : List Bool), (decPremises d fuel budget w).1 = some (ls,rest) →
    (∀ l ∈ ls, WellFormedLit d l) ∧ (ls.map litSize).sum+1+rest.length ≤ w.length := by
  intro budget
  induction budget with
  | zero => intro w ls rest h; cases w <;> simp [decPremises] at h
  | succ b ih =>
    intro w ls rest h
    match w with
    | [] => simp [decPremises] at h
    | false :: w' =>
      simp only [decPremises, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨by simp,by simp only [List.map_nil, List.sum_nil, List.length_cons]; omega⟩
    | true :: w' =>
      simp only [decPremises] at h
      cases hc : (decLit d fuel w').1 with
      | none => simp [hc] at h
      | some p =>
        obtain ⟨l,w''⟩ := p
        simp only [hc] at h
        obtain ⟨hwl,hsl⟩ := decLit_sound d fuel w' l w'' hc
        cases hc' : (decPremises d fuel b w'').1 with
        | none => exact absurd h (by simp [hc'])
        | some q =>
          obtain ⟨us,v⟩ := q
          simp only [hc', Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hws,hss⟩ := ih w'' us v hc'
          obtain ⟨rfl,rfl⟩ := h
          refine ⟨?_,?_⟩
          · intro u hu
            rcases List.mem_cons.mp hu with rfl | hu
            · exact hwl
            · exact hws u hu
          · simp only [List.map_cons, List.sum_cons, List.length_cons]
            omega

theorem decQuery_sound (d fuel : Nat) (w : List Bool) (Q : RawQuery) (rest : List Bool)
    (h : (decQuery d fuel w).1 = some (Q,rest)) :
    WellFormedQuery d Q ∧ qsize Q+rest.length ≤ w.length := by
  simp only [decQuery] at h
  cases hc : (decPremises d fuel fuel w).1 with
  | none => simp [hc] at h
  | some p =>
    obtain ⟨ls,w1⟩ := p
    simp only [hc] at h
    obtain ⟨hwl,hsl⟩ := decPremises_sound d fuel fuel w ls w1 hc
    cases hc1 : (decTerm d fuel w1).1 with
    | none => simp [hc1] at h
    | some q =>
      obtain ⟨a,w2⟩ := q
      simp only [hc1] at h
      obtain ⟨hwa,hsa⟩ := decTerm_sound d fuel w1 a w2 hc1
      cases hc2 : (decTerm d fuel w2).1 with
      | none => simp [hc2] at h
      | some s =>
        obtain ⟨c,w3⟩ := s
        simp only [hc2] at h
        obtain ⟨hwc,hsc⟩ := decTerm_sound d fuel w2 c w3 hc2
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        exact ⟨⟨hwl,hwa,hwc⟩,by simp only [qsize]; omega⟩

/-- Everything a successful decode guarantees: the query is legal for the
signature, and its symbol count is bounded by the input length. -/
theorem decode_sound (d : Nat) (w : List Bool) (Q : RawQuery)
    (h : (RawQueryCodec.decode d w).1 = some Q) :
    WellFormedQuery d Q ∧ qsize Q ≤ w.length := by
  simp only [RawQueryCodec.decode] at h
  cases hc : (decQuery d w.length w).1 with
  | none => simp [hc] at h
  | some p =>
    obtain ⟨R,rest⟩ := p
    simp only [hc] at h
    cases rest with
    | nil =>
      simp only [Option.some.injEq] at h
      obtain rfl := h
      have := decQuery_sound d w.length w R [] hc
      simpa using this
    | cons b rest => simp at h

end NSSE.RawCodecSoundness
