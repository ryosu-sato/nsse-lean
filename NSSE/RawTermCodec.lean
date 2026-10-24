import NSSE.RawBitNumeral

/-! # A bit-level codec for original nested terms

The counted term deciders consume an inductive query; a complexity statement in
the ENCODED INPUT LENGTH needs an actual string. This file supplies the term
half: a prefix code over bits, a counted parser, the exact round trip, and the
two size facts needed later —

* every symbol of the term costs at least two bits (`size_le_enc`), so a
  structural measure of the decoded term is bounded by the input length;
* the parser's cost obeys the consumption invariant
  `cost + K*(remaining) ≤ K*(input length)+1` with `K = d+2`, hence is linear in
  the input length.

The code: `00` bottom, `01` top, `11` followed by a self-delimiting numeral a
variable, `10` followed by exactly `d` encoded children a node. Arity is fixed
by the signature, so no terminator is needed.
-/

namespace NSSE.RawTermCodec

open RawBitNumeral

/-- Terms as they appear in an input string: variable identifiers are plain
naturals, and the arity is checked when the term is converted. -/
inductive Raw where
  | var (id : Nat)
  | bot
  | top
  | node (children : List Raw)

/-- The two-motive induction principle of the nested inductive. -/
theorem rec2 {P : Raw → Prop} {Q : List Raw → Prop}
    (hvar : ∀ i, P (.var i)) (hbot : P .bot) (htop : P .top)
    (hnode : ∀ cs, Q cs → P (.node cs)) (hnil : Q [])
    (hcons : ∀ t ts, P t → Q ts → Q (t :: ts)) : (∀ t, P t) ∧ (∀ ts, Q ts) := by
  have h1 : ∀ t, P t := fun t =>
    Raw.rec (motive_1 := P) (motive_2 := Q) hvar hbot htop hnode hnil hcons t
  refine ⟨h1,fun ts => ?_⟩
  induction ts with
  | nil => exact hnil
  | cons t ts ih => exact hcons t ts (h1 t) ih

/-- Arity check: every node has exactly `d` children. -/
def WellFormed (d : Nat) : Raw → Prop
  | .var _ => True
  | .bot => True
  | .top => True
  | .node cs => cs.length = d ∧ ∀ t ∈ cs, WellFormed d t

/-- Symbol count. -/
def size : Raw → Nat
  | .var _ => 1
  | .bot => 1
  | .top => 1
  | .node cs => 1+(cs.map size).sum

/-! ## The code -/

def enc : Raw → List Bool
  | .bot => [false,false]
  | .top => [false,true]
  | .var i => true :: true :: encNat i
  | .node cs => true :: false :: cs.flatMap enc

theorem size_le_enc : (∀ t : Raw, 2*size t ≤ (enc t).length) ∧
    (∀ cs : List Raw, 2*(cs.map size).sum ≤ (cs.flatMap enc).length) := by
  refine rec2 (P := fun t => 2*size t ≤ (enc t).length)
    (Q := fun cs => 2*(cs.map size).sum ≤ (cs.flatMap enc).length) ?_ ?_ ?_ ?_ ?_ ?_
  · intro i; simp only [size, enc, List.length_cons]; omega
  · simp [size, enc]
  · simp [size, enc]
  · intro cs h
    simp only [size, enc, List.length_cons] at h ⊢
    omega
  · simp
  · intro t ts ht hts
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]
    omega

/-! ## The counted parser -/

mutual

def decTerm (d fuel : Nat) (w : List Bool) : Option (Raw × List Bool) × Nat :=
  match fuel, w with
  | 0, _ => (none,1)
  | _+1, [] => (none,1)
  | _+1, [_] => (none,1)
  | _+1, false :: false :: w' => (some (.bot,w'),1)
  | _+1, false :: true :: w' => (some (.top,w'),1)
  | _+1, true :: true :: w' =>
    let r := decNat w'
    (r.1.map (fun p => (Raw.var p.1,p.2)),1+r.2)
  | f+1, true :: false :: w' =>
    let r := decTerms d f d w'
    (r.1.map (fun p => (Raw.node p.1,p.2)),1+r.2)
termination_by (fuel,0)

def decTerms (d fuel k : Nat) (w : List Bool) : Option (List Raw × List Bool) × Nat :=
  match k with
  | 0 => (some ([],w),1)
  | k+1 =>
    let h := decTerm d fuel w
    match h.1 with
    | none => (none,1+h.2)
    | some (t,w') =>
      let r := decTerms d fuel k w'
      (r.1.map (fun p => (t :: p.1,p.2)),1+h.2+r.2)
termination_by (fuel,k+1)

end

/-! ## Round trip -/

theorem dec_enc (d : Nat) :
    (∀ t : Raw, WellFormed d t → ∀ fuel w, size t ≤ fuel →
        (decTerm d fuel (enc t ++ w)).1 = some (t,w)) ∧
      (∀ cs : List Raw, (∀ t ∈ cs, WellFormed d t) → ∀ fuel w, (cs.map size).sum ≤ fuel →
        (decTerms d fuel cs.length (cs.flatMap enc ++ w)).1 = some (cs,w)) := by
  refine rec2 (P := fun t => WellFormed d t → ∀ fuel w, size t ≤ fuel →
      (decTerm d fuel (enc t ++ w)).1 = some (t,w))
    (Q := fun cs => (∀ t ∈ cs, WellFormed d t) → ∀ fuel w, (cs.map size).sum ≤ fuel →
      (decTerms d fuel cs.length (cs.flatMap enc ++ w)).1 = some (cs,w)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro i _ fuel w hf
    obtain ⟨f,rfl⟩ : ∃ f, fuel = f+1 := ⟨fuel-1,by simp only [size] at hf; omega⟩
    simp [enc, decTerm, decNat_value i w]
  · intro _ fuel w hf
    obtain ⟨f,rfl⟩ : ∃ f, fuel = f+1 := ⟨fuel-1,by simp only [size] at hf; omega⟩
    simp [enc, decTerm]
  · intro _ fuel w hf
    obtain ⟨f,rfl⟩ : ∃ f, fuel = f+1 := ⟨fuel-1,by simp only [size] at hf; omega⟩
    simp [enc, decTerm]
  · intro cs ih hw fuel w hf
    simp only [WellFormed] at hw
    obtain ⟨hlen,hch⟩ := hw
    simp only [size] at hf
    obtain ⟨f,rfl⟩ : ∃ f, fuel = f+1 := ⟨fuel-1,by omega⟩
    have hrec := ih hch f (w) (by omega)
    rw [← hlen] at hrec ⊢
    simp [enc, decTerm, List.append_assoc, hrec]
  · intro _ fuel w _
    simp [decTerms]
  · intro t ts iht ihts hw fuel w hf
    have hwt : WellFormed d t := hw t (by simp)
    have hwts : ∀ u ∈ ts, WellFormed d u := fun u hu => hw u (by simp [hu])
    simp only [List.map_cons, List.sum_cons] at hf
    have h1 := iht hwt fuel (ts.flatMap enc ++ w) (by omega)
    have h2 := ihts hwts fuel w (by omega)
    simp [List.flatMap_cons, List.append_assoc, decTerms, h1, h2]

theorem decTerm_enc (d : Nat) (t : Raw) (h : WellFormed d t) (fuel : Nat) (hf : size t ≤ fuel)
    (w : List Bool) : (decTerm d fuel (enc t ++ w)).1 = some (t,w) :=
  (dec_enc d).1 t h fuel w hf

/-! ## Costs: linear in the input length -/

theorem dec_cost (d : Nat) : ∀ fuel : Nat,
    (∀ w : List Bool,
      (decTerm d fuel w).2+(d+2)*remLen (decTerm d fuel w).1 ≤ (d+2)*w.length+1) ∧
    (∀ k : Nat, ∀ w : List Bool,
      (decTerms d fuel k w).2+(d+2)*remLen (decTerms d fuel k w).1
        ≤ (d+2)*w.length+2*k+1) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨fun w => by simp only [decTerm, remLen]; omega,?_⟩
    intro k
    induction k with
    | zero => intro w; simp only [decTerms, remLen]; omega
    | succ k ih =>
      intro w
      have h0 : decTerm d 0 w = (none,1) := by simp [decTerm]
      have hk := ih w
      simp only [decTerms, h0, remLen, Nat.mul_zero]
      omega
  | succ f ihf =>
    have hterm : ∀ w : List Bool,
        (decTerm d (f+1) w).2+(d+2)*remLen (decTerm d (f+1) w).1 ≤ (d+2)*w.length+1 := by
      intro w
      match w with
      | [] => simp only [decTerm, remLen]; omega
      | [_] => simp only [decTerm, remLen]; omega
      | false :: false :: w' =>
        have hx : (d+2)*(w'.length+1+1) = (d+2)*w'.length+(2*d+4) := by ring
        simp only [decTerm, remLen, List.length_cons]
        omega
      | false :: true :: w' =>
        have hx : (d+2)*(w'.length+1+1) = (d+2)*w'.length+(2*d+4) := by ring
        simp only [decTerm, remLen, List.length_cons]
        omega
      | true :: true :: w' =>
        have hn := decNat_cost w'
        have hr := decNat_rem w'
        have hx : (d+2)*(w'.length+1+1) = (d+2)*w'.length+(2*d+4) := by ring
        have hy : (d+2)*w'.length = 2*w'.length+d*w'.length := by ring
        have hk : (d+2)*remLen (decNat w').1
            = 2*remLen (decNat w').1+d*remLen (decNat w').1 := by ring
        have hd : d*remLen (decNat w').1 ≤ d*w'.length := Nat.mul_le_mul_left d hr
        simp only [decTerm, remLen_map, List.length_cons]
        omega
      | true :: false :: w' =>
        have h := ihf.2 d w'
        have hx : (d+2)*(w'.length+1+1) = (d+2)*w'.length+(2*d+4) := by ring
        simp only [decTerm, remLen_map, List.length_cons]
        omega
    refine ⟨hterm,?_⟩
    intro k
    induction k with
    | zero => intro w; simp only [decTerms, remLen]; omega
    | succ k ih =>
      intro w
      have hh := hterm w
      simp only [decTerms]
      cases hc : (decTerm d (f+1) w).1 with
      | none =>
        rw [hc] at hh
        simp only [remLen] at hh ⊢
        omega
      | some p =>
        obtain ⟨t,w'⟩ := p
        have hr := ih w'
        rw [hc] at hh
        simp only [remLen] at hh
        simp only [remLen_map]
        omega

theorem decTerm_cost (d fuel : Nat) (w : List Bool) :
    (decTerm d fuel w).2 ≤ (d+2)*w.length+1 := by
  have h := (dec_cost d fuel).1 w
  omega

end NSSE.RawTermCodec
