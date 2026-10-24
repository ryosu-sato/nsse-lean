import NSSE.RawTermCodec

/-! # The query level of the input codec

A whole entailment question is one string: the premises, each introduced by a
continuation bit and tagged `0` for `≤` and `1` for `=`, then a `0` closing the
list, then the two query terms. Decoding is counted and must consume the whole
input.

Proved here: the exact round trip `decode d (encQuery Q) = some Q` for
well-formed queries, the symbol count bounded by the input length
(`qsize_le_enc`), and a decoding cost linear in the input length
(`decode_cost`). The conversion of a decoded raw query into a TYPED query over
a dense variable universe, and the composition with the seven-exponential
bound, are the next unit.
-/

namespace NSSE.RawQueryCodec

open RawBitNumeral RawTermCodec

inductive RawLit where
  | le (a b : Raw)
  | eq (a b : Raw)

structure RawQuery where
  premises : List RawLit
  left : Raw
  right : Raw

def WellFormedLit (d : Nat) : RawLit → Prop
  | .le a b => WellFormed d a ∧ WellFormed d b
  | .eq a b => WellFormed d a ∧ WellFormed d b

def WellFormedQuery (d : Nat) (Q : RawQuery) : Prop :=
  (∀ l ∈ Q.premises, WellFormedLit d l) ∧ WellFormed d Q.left ∧ WellFormed d Q.right

def litSize : RawLit → Nat
  | .le a b => 1+size a+size b
  | .eq a b => 1+size a+size b

def qsize (Q : RawQuery) : Nat :=
  1+(Q.premises.map litSize).sum+size Q.left+size Q.right

/-! ## The code -/

def encLit : RawLit → List Bool
  | .le a b => false :: (enc a ++ enc b)
  | .eq a b => true :: (enc a ++ enc b)

def encPremises : List RawLit → List Bool
  | [] => [false]
  | l :: ls => true :: (encLit l ++ encPremises ls)

def encQuery (Q : RawQuery) : List Bool :=
  encPremises Q.premises ++ enc Q.left ++ enc Q.right

theorem litSize_le_enc (l : RawLit) : litSize l ≤ (encLit l).length := by
  cases l with
  | le a b =>
    have ha := size_le_enc.1 a
    have hb := size_le_enc.1 b
    simp only [litSize, encLit, List.length_cons, List.length_append]
    omega
  | eq a b =>
    have ha := size_le_enc.1 a
    have hb := size_le_enc.1 b
    simp only [litSize, encLit, List.length_cons, List.length_append]
    omega

theorem premises_le_enc (ls : List RawLit) :
    1+(ls.map litSize).sum ≤ (encPremises ls).length := by
  induction ls with
  | nil => simp [encPremises]
  | cons l ls ih =>
    have h := litSize_le_enc l
    simp only [encPremises, List.map_cons, List.sum_cons, List.length_cons, List.length_append]
    omega

/-- The symbol count of a query never exceeds its encoded length. -/
theorem qsize_le_enc (Q : RawQuery) : qsize Q ≤ (encQuery Q).length := by
  have hp := premises_le_enc Q.premises
  have hl := size_le_enc.1 Q.left
  have hr := size_le_enc.1 Q.right
  simp only [qsize, encQuery, List.length_append]
  omega

/-! ## The counted parser -/

def decLit (d fuel : Nat) (w : List Bool) : Option (RawLit × List Bool) × Nat :=
  match w with
  | [] => (none,1)
  | b :: w' =>
    let h := decTerm d fuel w'
    match h.1 with
    | none => (none,1+h.2)
    | some (a,w'') =>
      let r := decTerm d fuel w''
      match r.1 with
      | none => (none,1+h.2+r.2)
      | some (c,w''') => (some (if b then RawLit.eq a c else RawLit.le a c,w'''),1+h.2+r.2)

def decPremises (d fuel : Nat) : Nat → List Bool → Option (List RawLit × List Bool) × Nat
  | _, [] => (none,1)
  | 0, _ => (none,1)
  | _+1, false :: w => (some ([],w),1)
  | b+1, true :: w =>
    let h := decLit d fuel w
    match h.1 with
    | none => (none,1+h.2)
    | some (l,w') =>
      let r := decPremises d fuel b w'
      (r.1.map (fun p => (l :: p.1,p.2)),1+h.2+r.2)

def decQuery (d fuel : Nat) (w : List Bool) : Option (RawQuery × List Bool) × Nat :=
  let p := decPremises d fuel fuel w
  match p.1 with
  | none => (none,1+p.2)
  | some (ls,w1) =>
    let a := decTerm d fuel w1
    match a.1 with
    | none => (none,1+p.2+a.2)
    | some (l,w2) =>
      let b := decTerm d fuel w2
      match b.1 with
      | none => (none,1+p.2+a.2+b.2)
      | some (r,w3) => (some (⟨ls,l,r⟩,w3),1+p.2+a.2+b.2)

/-- The input must be consumed exactly. -/
def decode (d : Nat) (w : List Bool) : Option RawQuery × Nat :=
  let r := decQuery d w.length w
  match r.1 with
  | some (Q,[]) => (some Q,1+r.2)
  | _ => (none,1+r.2)

/-! ## Round trip -/

theorem decLit_enc (d : Nat) (l : RawLit) (h : WellFormedLit d l) (fuel : Nat)
    (hf : litSize l ≤ fuel) (w : List Bool) : (decLit d fuel (encLit l ++ w)).1 = some (l,w) := by
  cases l with
  | le a b =>
    obtain ⟨ha,hb⟩ := h
    simp only [litSize] at hf
    have h1 := decTerm_enc d a ha fuel (by omega) (enc b ++ w)
    have h2 := decTerm_enc d b hb fuel (by omega) w
    simp [encLit, decLit, List.append_assoc, h1, h2]
  | eq a b =>
    obtain ⟨ha,hb⟩ := h
    simp only [litSize] at hf
    have h1 := decTerm_enc d a ha fuel (by omega) (enc b ++ w)
    have h2 := decTerm_enc d b hb fuel (by omega) w
    simp [encLit, decLit, List.append_assoc, h1, h2]

theorem decPremises_enc (d : Nat) (ls : List RawLit) (h : ∀ l ∈ ls, WellFormedLit d l)
    (fuel : Nat) (hf : (ls.map litSize).sum ≤ fuel) (budget : Nat) (hb : ls.length < budget)
    (w : List Bool) : (decPremises d fuel budget (encPremises ls ++ w)).1 = some (ls,w) := by
  induction ls generalizing budget with
  | nil =>
    obtain ⟨b,rfl⟩ : ∃ b, budget = b+1 := ⟨budget-1,by omega⟩
    simp [encPremises, decPremises]
  | cons l ls ih =>
    have hl : WellFormedLit d l := h l (by simp)
    have hls : ∀ u ∈ ls, WellFormedLit d u := fun u hu => h u (by simp [hu])
    simp only [List.map_cons, List.sum_cons] at hf
    simp only [List.length_cons] at hb
    obtain ⟨b,rfl⟩ : ∃ b, budget = b+1 := ⟨budget-1,by omega⟩
    have h1 := decLit_enc d l hl fuel (by omega) (encPremises ls ++ w)
    have h2 := ih hls (by omega) b (by omega)
    simp [encPremises, decPremises, List.append_assoc, h1, h2]

theorem decQuery_enc (d : Nat) (Q : RawQuery) (h : WellFormedQuery d Q) (fuel : Nat)
    (hf : qsize Q ≤ fuel) (w : List Bool) :
    (decQuery d fuel (encQuery Q ++ w)).1 = some (Q,w) := by
  obtain ⟨hp,hl,hr⟩ := h
  simp only [qsize] at hf
  have hlen : Q.premises.length < fuel := by
    have h1 (xs : List RawLit) : xs.length ≤ (xs.map litSize).sum := by
      induction xs with
      | nil => simp
      | cons x xs ih =>
        have hx : 1 ≤ litSize x := by cases x <;> simp only [litSize] <;> omega
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        omega
    have := h1 Q.premises
    omega
  have h1 := decPremises_enc d Q.premises hp fuel (by omega) fuel hlen
    (enc Q.left ++ (enc Q.right ++ w))
  have h2 := decTerm_enc d Q.left hl fuel (by omega) (enc Q.right ++ w)
  have h3 := decTerm_enc d Q.right hr fuel (by omega) w
  simp [encQuery, List.append_assoc, decQuery, h1, h2, h3]

theorem decode_enc (d : Nat) (Q : RawQuery) (h : WellFormedQuery d Q) :
    (decode d (encQuery Q)).1 = some Q := by
  have hq := decQuery_enc d Q h (encQuery Q).length (qsize_le_enc Q) []
  simp only [List.append_nil] at hq
  simp only [decode, hq]

/-! ## Costs: linear in the input length -/

theorem decLit_cost (d fuel : Nat) (w : List Bool) :
    (decLit d fuel w).2+(d+2)*remLen (decLit d fuel w).1 ≤ (d+2)*w.length+3 := by
  match w with
  | [] => simp only [decLit, remLen]; omega
  | b :: w' =>
    have hh := (dec_cost d fuel).1 w'
    have hx : (d+2)*(w'.length+1) = (d+2)*w'.length+(d+2) := by ring
    simp only [decLit, List.length_cons]
    cases hc : (decTerm d fuel w').1 with
    | none => simp only [hc, remLen] at hh ⊢; omega
    | some p =>
      obtain ⟨a,w''⟩ := p
      simp only [hc, remLen] at hh ⊢
      have hr := (dec_cost d fuel).1 w''
      cases hc' : (decTerm d fuel w'').1 with
      | none => simp only [hc', remLen] at hr ⊢; omega
      | some q =>
        obtain ⟨c,w'''⟩ := q
        simp only [hc', remLen] at hr ⊢
        omega

theorem decPremises_cost (d fuel : Nat) : ∀ (budget : Nat) (w : List Bool),
    (decPremises d fuel budget w).2+(d+2)*remLen (decPremises d fuel budget w).1
      ≤ (d+2)*w.length+3*budget+1 := by
  intro budget
  induction budget with
  | zero =>
    intro w
    match w with
    | [] => simp only [decPremises, remLen]; omega
    | _ :: _ => simp only [decPremises, remLen]; omega
  | succ b ih =>
    intro w
    match w with
    | [] => simp only [decPremises, remLen]; omega
    | false :: w' =>
      have hx : (d+2)*(w'.length+1) = (d+2)*w'.length+(d+2) := by ring
      simp only [decPremises, remLen, List.length_cons]
      omega
    | true :: w' =>
      have hl := decLit_cost d fuel w'
      have hx : (d+2)*(w'.length+1) = (d+2)*w'.length+(d+2) := by ring
      simp only [decPremises, List.length_cons]
      cases hc : (decLit d fuel w').1 with
      | none => simp only [hc, remLen] at hl ⊢; omega
      | some p =>
        obtain ⟨l,w''⟩ := p
        simp only [hc, remLen] at hl
        have hr := ih w''
        simp only [hc, remLen_map]
        omega

theorem decQuery_cost (d fuel : Nat) (w : List Bool) :
    (decQuery d fuel w).2 ≤ (d+2)*w.length+3*fuel+4 := by
  have hp := decPremises_cost d fuel fuel w
  simp only [decQuery]
  cases hc : (decPremises d fuel fuel w).1 with
  | none => simp only [hc, remLen] at hp ⊢; omega
  | some p =>
    obtain ⟨ls,w1⟩ := p
    simp only [hc, remLen] at hp ⊢
    have ha := (dec_cost d fuel).1 w1
    cases hc1 : (decTerm d fuel w1).1 with
    | none => simp only [hc1, remLen] at ha ⊢; omega
    | some q =>
      obtain ⟨l,w2⟩ := q
      simp only [hc1, remLen] at ha ⊢
      have hb := (dec_cost d fuel).1 w2
      cases hc2 : (decTerm d fuel w2).1 with
      | none => simp only [hc2, remLen] at hb ⊢; omega
      | some s =>
        obtain ⟨r,w3⟩ := s
        simp only [hc2, remLen] at hb ⊢
        omega

/-- Decoding a whole query is linear in the input length. -/
theorem decode_cost (d : Nat) (w : List Bool) :
    (decode d w).2 ≤ (d+5)*w.length+5 := by
  have h := decQuery_cost d w.length w
  have hx : (d+5)*w.length = (d+2)*w.length+3*w.length := by ring
  simp only [decode]
  cases hc : (decQuery d w.length w).1 with
  | none => simp only [hc]; omega
  | some p =>
    obtain ⟨Q,rest⟩ := p
    cases rest <;> simp only [hc] <;> omega

end NSSE.RawQueryCodec
