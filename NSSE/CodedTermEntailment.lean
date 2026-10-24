import NSSE.CodedQueryConversion
import NSSE.StoredTermFiniteEntailment
import NSSE.StoredTermRegularEntailment

/-! # Original term entailment decided from an encoded input string

The counted deciders of v1618/v1620 consume an inductive query and are bounded
by seven exponentials of a polynomial in `StoredQuerySize.size`, which charges
the declared variable universe and the variable names in unary. v1621 removed
that from the semantics, v1622/v1623 supplied a bit code, v1624 the soundness
of its parser and the conversion into a dense typed query. This file composes
them:

* `decideFinite`/`decideAll` take a BIT STRING, decode it, convert it and run
  the complete counted decision;
* on the code of a query they answer the original entailment question for
  finite, regular and arbitrary trees (`finite_correct`, `arbitrary_correct`,
  `regular_correct`);
* on EVERY bit string, the total counter — decoding included — is at most
  `tower 7` of a polynomial in the input LENGTH (`finite_bound`, `all_bound`).

What remains open: the counted step measure is not yet a proved machine-time
bound. 7-EXPTIME is therefore still not claimed.
-/

namespace NSSE.CodedTermEntailment

open DirectRankStateTower DirectRankFormulaTower
open RawTermCodec RawQueryCodec RawCodecSoundness CodedQueryConversion SubtypeTerms SubtypeTermCompaction

variable {n d : Nat}

/-! ## Towers dominate their argument -/

theorem self_le_tower (k x : Nat) : x ≤ tower k x := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact ih.trans (self_le_exp _)

/-! ## The converted query is small -/

theorem list_bridge {α : Type*} (D : Nat) (g : α → Nat) (dflt : α) (ts : List α)
    (h : ts.length = D) :
    (List.finRange D).map (fun i : Fin D => g (ts[i.val]?.getD dflt)) = ts.map g := by
  apply List.ext_getElem
  · simp [h]
  · intro j h1 h2
    simp only [List.getElem_map, List.getElem_finRange]
    congr 1
    rw [List.getElem?_eq_getElem (by simp only [List.length_map] at h2; omega)]
    rfl

theorem sum_succ_map {α : Type*} (g : α → Nat) (ts : List α) :
    (ts.map (fun t => 1+g t)).sum = ts.length+(ts.map g).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons] at *
    omega

theorem unitSize_toTerm (d : Nat) (vs : List Nat) :
    (∀ r : Raw, WellFormed d r → unitSizeTerm (toTerm d vs r) ≤ (d+1)*size r) ∧
    (∀ cs : List Raw, (∀ c ∈ cs, WellFormed d c) →
      (cs.map (fun c => unitSizeTerm (toTerm d vs c))).sum ≤ (d+1)*(cs.map size).sum) := by
  refine rec2 (P := fun r => WellFormed d r → unitSizeTerm (toTerm d vs r) ≤ (d+1)*size r)
    (Q := fun cs => (∀ c ∈ cs, WellFormed d c) →
      (cs.map (fun c => unitSizeTerm (toTerm d vs c))).sum ≤ (d+1)*(cs.map size).sum)
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro i _
    by_cases h : vs.idxOf i < vs.length <;>
      simp only [toTerm, h, dif_pos, dif_neg, not_false_iff, unitSizeTerm, size] <;> omega
  · intro _; simp only [toTerm, unitSizeTerm, size]; omega
  · intro _; simp only [toTerm, unitSizeTerm, size]; omega
  · intro cs ih hw
    simp only [WellFormed] at hw
    obtain ⟨hlen,hch⟩ := hw
    have hts : (cs.map (toTerm d vs)).length = d := by simp [hlen]
    have hb := list_bridge d (fun t => 1+unitSizeTerm t) (Term.bot) (cs.map (toTerm d vs)) hts
    have hsum := ih hch
    have hcount : ((cs.map (toTerm d vs)).map (fun t => 1+unitSizeTerm t)).sum
        = cs.length+(cs.map (fun c => unitSizeTerm (toTerm d vs c))).sum := by
      have h0 := sum_succ_map unitSizeTerm (cs.map (toTerm d vs))
      have h1 : (cs.map (toTerm d vs)).map unitSizeTerm
          = cs.map (fun c => unitSizeTerm (toTerm d vs c)) := by
        simp [List.map_map, Function.comp_def]
      have h2 : (cs.map (toTerm d vs)).length = cs.length := by simp
      rw [h1, h2] at h0
      exact h0
    have hmul : (d+1)*(1+(cs.map size).sum) = (d+1)+(d+1)*(cs.map size).sum := by ring
    simp only [toTerm, unitSizeTerm, size, hb]
    omega
  · intro _; simp
  · intro c cs hc hcs hw
    have h1 := hc (hw c (by simp))
    have h2 := hcs (fun u hu => hw u (by simp [hu]))
    have hmul : (d+1)*(size c+(cs.map size).sum) = (d+1)*size c+(d+1)*(cs.map size).sum := by ring
    simp only [List.map_cons, List.sum_cons]
    omega

theorem unitSize_toLit (d : Nat) (vs : List Nat) (l : RawLit) (h : WellFormedLit d l) :
    unitSizeLiteral (toLit d vs l) ≤ (d+1)*litSize l := by
  cases l with
  | le a b =>
    obtain ⟨ha,hb⟩ := h
    have h1 := (unitSize_toTerm d vs).1 a ha
    have h2 := (unitSize_toTerm d vs).1 b hb
    have hmul : (d+1)*(1+size a+size b) = (d+1)+(d+1)*size a+(d+1)*size b := by ring
    simp only [toLit, unitSizeLiteral, litSize]
    omega
  | eq a b =>
    obtain ⟨ha,hb⟩ := h
    have h1 := (unitSize_toTerm d vs).1 a ha
    have h2 := (unitSize_toTerm d vs).1 b hb
    have hmul : (d+1)*(1+size a+size b) = (d+1)+(d+1)*size a+(d+1)*size b := by ring
    simp only [toLit, unitSizeLiteral, litSize]
    omega

theorem unitSize_toQuery (d : Nat) (Q : RawQuery) (h : WellFormedQuery d Q) :
    unitSize (toQuery d Q) ≤ (d+1)*qsize Q := by
  obtain ⟨hp,hl,hr⟩ := h
  have h1 := (unitSize_toTerm d (queryIds Q)).1 Q.left hl
  have h2 := (unitSize_toTerm d (queryIds Q)).1 Q.right hr
  have h3 : (Q.premises.map (fun l => unitSizeLiteral (toLit d (queryIds Q) l))).sum
      ≤ (d+1)*(Q.premises.map litSize).sum := by
    have hstep := List.sum_le_sum (l := Q.premises)
      (f := fun l => unitSizeLiteral (toLit d (queryIds Q) l))
      (g := fun l => (d+1)*litSize l) (fun l hl' => unitSize_toLit d _ l (hp l hl'))
    rwa [List.sum_map_mul_left] at hstep
  have hmul : (d+1)*(1+(Q.premises.map litSize).sum+size Q.left+size Q.right)
      = (d+1)+(d+1)*(Q.premises.map litSize).sum+(d+1)*size Q.left+(d+1)*size Q.right := by ring
  simp only [unitSize, toQuery, toQueryOn, qsize, List.map_map, Function.comp_def]
  omega

theorem termIds_length (r : Raw) : (termIds r).length ≤ size r := by
  refine (rec2 (P := fun r => (termIds r).length ≤ size r)
    (Q := fun cs => (cs.flatMap termIds).length ≤ (cs.map size).sum) ?_ ?_ ?_ ?_ ?_ ?_).1 r
  · intro i; simp [termIds, size]
  · simp [termIds, size]
  · simp [termIds, size]
  · intro cs h; simp only [termIds, size]; omega
  · simp
  · intro t ts ht hts
    simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
    omega

theorem litIds_length (l : RawLit) : (litIds l).length ≤ litSize l := by
  cases l with
  | le a b =>
    have ha := termIds_length a
    have hb := termIds_length b
    simp only [litIds, litSize, List.length_append]; omega
  | eq a b =>
    have ha := termIds_length a
    have hb := termIds_length b
    simp only [litIds, litSize, List.length_append]; omega

theorem queryIds_length (Q : RawQuery) : (queryIds Q).length ≤ qsize Q := by
  have hd := (List.dedup_sublist (Q.premises.flatMap litIds ++ termIds Q.left ++
    termIds Q.right)).length_le
  have hl := termIds_length Q.left
  have hr := termIds_length Q.right
  have hp : (Q.premises.flatMap litIds).length ≤ (Q.premises.map litSize).sum := by
    simp only [List.length_flatMap]
    exact List.sum_le_sum (fun l _ => litIds_length l)
  simp only [List.length_append] at hd
  simp only [queryIds, qsize]
  omega

/-- The stored structural size of the converted query is quadratic in the raw
query's symbol count, with no dependence on identifiers. -/
theorem size_pack_toQuery (d : Nat) (Q : RawQuery) (h : WellFormedQuery d Q) :
    StoredQuerySize.size (StoredTermQuery.packQuery (toQuery d Q)) ≤ (d+1)*(qsize Q+1)^2 := by
  have h1 := size_pack_le (toQuery d Q)
  have h2 := unitSize_toQuery d Q h
  have h3 := queryIds_length Q
  calc StoredQuerySize.size (StoredTermQuery.packQuery (toQuery d Q))
      ≤ ((queryIds Q).length+1)*unitSize (toQuery d Q) := h1
    _ ≤ (qsize Q+1)*((d+1)*qsize Q) := Nat.mul_le_mul (by omega) h2
    _ ≤ (d+1)*(qsize Q+1)^2 := by
        have : (qsize Q+1)*((d+1)*qsize Q) = (d+1)*((qsize Q+1)*qsize Q) := by ring
        rw [this]
        refine Nat.mul_le_mul_left _ ?_
        have : (qsize Q+1)^2 = (qsize Q+1)*(qsize Q+1) := by ring
        rw [this]
        exact Nat.mul_le_mul_left _ (by omega)

/-! ## The decision on an encoded input -/

def decideFinite (d : Nat) (w : List Bool) (hd : 0 < d) : Option Bool × Nat :=
  let r := RawQueryCodec.decode d w
  match r.1 with
  | none => (none,1+r.2)
  | some Q =>
    let s := StoredTermFiniteEntailment.decide (StoredTermQuery.packQuery (toQuery d Q))
      (StoredQueryWellFormed.packed (toQuery d Q)) hd
    (some s.1,1+r.2+s.2)

def decideAll (d : Nat) (w : List Bool) (hd : 0 < d) : Option Bool × Nat :=
  let r := RawQueryCodec.decode d w
  match r.1 with
  | none => (none,1+r.2)
  | some Q =>
    let s := StoredTermRegularEntailment.decide (StoredTermQuery.packQuery (toQuery d Q))
      (StoredQueryWellFormed.packed (toQuery d Q)) hd
    (some s.1,1+r.2+s.2)

/-! ## Correctness on the code of a query -/

theorem finite_correct (Q : Query n d) (hd : 0 < d) :
    (decideFinite d (encQuery (rawOfQuery Q)) hd).1 = some true ↔
      Entails (FiniteSubtypeTrees.constructor d) Q := by
  have hdec := decode_enc d (rawOfQuery Q) (rawOfQuery_wf Q)
  simp only [decideFinite, hdec]
  rw [Option.some.injEq, StoredTermFiniteEntailment.correct (toQuery d (rawOfQuery Q)) hd,
    entails_toQuery (FiniteSubtypeTrees.constructor d) Q]

theorem arbitrary_correct (Q : Query n d) (hd : 0 < d) :
    (decideAll d (encQuery (rawOfQuery Q)) hd).1 = some true ↔
      Entails (AbsorbingSubtypeTrees.constructor d) Q := by
  have hdec := decode_enc d (rawOfQuery Q) (rawOfQuery_wf Q)
  simp only [decideAll, hdec]
  rw [Option.some.injEq, StoredTermRegularEntailment.correct (toQuery d (rawOfQuery Q)) hd,
    entails_toQuery (AbsorbingSubtypeTrees.constructor d) Q]

theorem regular_correct (Q : Query n d) (hd : 0 < d) :
    (decideAll d (encQuery (rawOfQuery Q)) hd).1 = some true ↔
      SubtypeTermSemantics.RegularEntails Q := by
  rw [arbitrary_correct Q hd, TermEntailmentDecision.regular_entails_iff_all Q hd]

/-! ## The bound, in the input length, for every input -/

def argument (L d : Nat) :=
  16*((d+1)*(L+1)^2)^4+40*((d+1)*(L+1)^2)^3+53*((d+1)*(L+1)^2)^2+34*((d+1)*(L+1)^2)+d+74426

theorem decode_le_argument (d L : Nat) : (d+5)*L+6 ≤ argument L d := by
  have h1 : L ≤ (L+1)^2 := by nlinarith
  have h2 : (d+5)*L ≤ 5*((d+1)*(L+1)^2) := by nlinarith
  have h3 : 5*((d+1)*(L+1)^2) ≤ 34*((d+1)*(L+1)^2) := by omega
  unfold argument
  omega

theorem finite_bound (d : Nat) (w : List Bool) (hd : 0 < d) :
    (decideFinite d w hd).2 ≤ tower 7 (argument w.length d+1) := by
  have hdc := decode_cost d w
  have hstep := TowerExpression.double_step 6 (argument w.length d)
  have hself := self_le_tower 7 (argument w.length d)
  have hdle := decode_le_argument d w.length
  change 2*tower 7 (argument w.length d) ≤ tower 7 (argument w.length d+1) at hstep
  simp only [decideFinite]
  cases hc : (RawQueryCodec.decode d w).1 with
  | none => simp only [hc]; omega
  | some Q =>
    obtain ⟨hwf,hq⟩ := decode_sound d w Q hc
    have hsz := size_pack_toQuery d Q hwf
    have hb := StoredTermFiniteEntailment.bound_explicit (StoredTermQuery.packQuery (toQuery d Q))
      (StoredQueryWellFormed.packed (toQuery d Q)) hd
    have hmono : 16*(StoredQuerySize.size (StoredTermQuery.packQuery (toQuery d Q)))^4+
        40*(StoredQuerySize.size (StoredTermQuery.packQuery (toQuery d Q)))^3+
        53*(StoredQuerySize.size (StoredTermQuery.packQuery (toQuery d Q)))^2+
        34*StoredQuerySize.size (StoredTermQuery.packQuery (toQuery d Q))+d+74426
          ≤ argument w.length d := by
      have hle : StoredQuerySize.size (StoredTermQuery.packQuery (toQuery d Q))
          ≤ (d+1)*(w.length+1)^2 := by
        refine hsz.trans (Nat.mul_le_mul_left _ ?_)
        exact Nat.pow_le_pow_left (by omega) 2
      have p4 := Nat.pow_le_pow_left hle 4
      have p3 := Nat.pow_le_pow_left hle 3
      have p2 := Nat.pow_le_pow_left hle 2
      unfold argument
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.mul_le_mul_left 16 p4) (Nat.mul_le_mul_left 40 p3)) (Nat.mul_le_mul_left 53 p2))
        (Nat.mul_le_mul_left 34 hle)) le_rfl) le_rfl
    have hb' := hb.trans (tower_mono 7 hmono)
    simp only [hc]
    omega

theorem all_bound (d : Nat) (w : List Bool) (hd : 0 < d) :
    (decideAll d w hd).2 ≤ tower 7 (argument w.length d+1) := by
  have hdc := decode_cost d w
  have hstep := TowerExpression.double_step 6 (argument w.length d)
  have hself := self_le_tower 7 (argument w.length d)
  have hdle := decode_le_argument d w.length
  change 2*tower 7 (argument w.length d) ≤ tower 7 (argument w.length d+1) at hstep
  simp only [decideAll]
  cases hc : (RawQueryCodec.decode d w).1 with
  | none => simp only [hc]; omega
  | some Q =>
    obtain ⟨hwf,hq⟩ := decode_sound d w Q hc
    have hsz := size_pack_toQuery d Q hwf
    have hb := StoredTermRegularEntailment.bound_explicit (StoredTermQuery.packQuery (toQuery d Q))
      (StoredQueryWellFormed.packed (toQuery d Q)) hd
    have hmono : 16*(StoredQuerySize.size (StoredTermQuery.packQuery (toQuery d Q)))^4+
        40*(StoredQuerySize.size (StoredTermQuery.packQuery (toQuery d Q)))^3+
        53*(StoredQuerySize.size (StoredTermQuery.packQuery (toQuery d Q)))^2+
        34*StoredQuerySize.size (StoredTermQuery.packQuery (toQuery d Q))+d+74426
          ≤ argument w.length d := by
      have hle : StoredQuerySize.size (StoredTermQuery.packQuery (toQuery d Q))
          ≤ (d+1)*(w.length+1)^2 := by
        refine hsz.trans (Nat.mul_le_mul_left _ ?_)
        exact Nat.pow_le_pow_left (by omega) 2
      have p4 := Nat.pow_le_pow_left hle 4
      have p3 := Nat.pow_le_pow_left hle 3
      have p2 := Nat.pow_le_pow_left hle 2
      unfold argument
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.mul_le_mul_left 16 p4) (Nat.mul_le_mul_left 40 p3)) (Nat.mul_le_mul_left 53 p2))
        (Nat.mul_le_mul_left 34 hle)) le_rfl) le_rfl
    have hb' := hb.trans (tower_mono 7 hmono)
    simp only [hc]
    omega

/-- Everything at once: on the code of an original query the decision answers
the original entailment question in all three semantics, and on EVERY input
string the total counter, decoding included, is at most seven exponentials of a
polynomial in the input length. -/
theorem coded_decision (Q : Query n d) (hd : 0 < d) :
    ((decideFinite d (encQuery (rawOfQuery Q)) hd).1 = some true ↔
        Entails (FiniteSubtypeTrees.constructor d) Q) ∧
      ((decideAll d (encQuery (rawOfQuery Q)) hd).1 = some true ↔
        Entails (AbsorbingSubtypeTrees.constructor d) Q) ∧
      ((decideAll d (encQuery (rawOfQuery Q)) hd).1 = some true ↔
        SubtypeTermSemantics.RegularEntails Q) ∧
      (∀ w : List Bool, (decideFinite d w hd).2 ≤ tower 7 (argument w.length d+1)) ∧
      (∀ w : List Bool, (decideAll d w hd).2 ≤ tower 7 (argument w.length d+1)) :=
  ⟨finite_correct Q hd,arbitrary_correct Q hd,regular_correct Q hd,
    fun w => finite_bound d w hd,fun w => all_bound d w hd⟩

end NSSE.CodedTermEntailment
