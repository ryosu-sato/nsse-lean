import NSSE.BinaryTokenCodec

/-! Binary decoder traversal counts, bounded on malformed inputs too.
Nat.bit, numeric recursion counters, allocation and meta-counter arithmetic
are not yet charged at their concrete representation cost. -/
namespace NSSE.CountedBinaryTokenDecode

def number : List Bool → Option (Nat × List Bool) × Nat
  | [] => (none,1)
  | false::rest => (some (0,rest),1)
  | [true] => (none,1)
  | true::b::rest =>
    let r := number rest
    (r.1.map (fun p => (Nat.bit b p.1,p.2)),1+r.2)

theorem number_value (bs : List Bool) : (number bs).1 = BinaryTokenCodec.readNumber bs := by
  induction bs using number.induct with
  | case1 => rfl
  | case2 rest => rfl
  | case3 => rfl
  | case4 b rest ih =>
    simp only [number, BinaryTokenCodec.readNumber, ih]
    cases BinaryTokenCodec.readNumber rest <;> rfl

theorem number_bound (bs : List Bool) : (number bs).2 ≤ bs.length+1 := by
  induction bs using number.induct with
  | case1 => rfl
  | case2 rest => simp [number]
  | case3 => simp [number]
  | case4 b rest ih => simp only [number, List.length_cons]; omega

theorem number_consumes (bs : List Bool) (v : Nat) (rest : List Bool)
    (h : (number bs).1 = some (v,rest)) :
    rest.length < bs.length ∧ (number bs).2+rest.length ≤ bs.length+1 := by
  induction bs using number.induct generalizing v rest with
  | case1 => simp [number] at h
  | case2 tail =>
    have he : (0,tail)=(v,rest) := by simpa [number] using h
    cases he
    simp only [number, List.length_cons]; omega
  | case3 => simp [number] at h
  | case4 b tail ih =>
    cases he : (number tail).1 with
    | none => simp [number, he] at h
    | some p =>
      obtain ⟨u,rs⟩ := p
      have hp : (Nat.bit b u,rs)=(v,rest) := by simpa [number, he] using h
      have hh := ih u rs he
      cases hp
      simp only [number, List.length_cons]
      omega

def many : Nat → List Bool → Option (List Nat × List Bool) × Nat
  | 0, bs => (some ([],bs),1)
  | k+1, bs =>
    let a := number bs
    match a.1 with
    | none => (none,1+a.2)
    | some (v,rest) =>
      let b := many k rest
      (b.1.map (fun p => (v::p.1,p.2)),1+a.2+b.2)

theorem many_value (k : Nat) (bs : List Bool) :
    (many k bs).1 = BinaryTokenCodec.readMany k bs := by
  induction k generalizing bs with
  | zero => rfl
  | succ k ih =>
    simp only [many, BinaryTokenCodec.readMany, number_value]
    cases BinaryTokenCodec.readNumber bs with
    | none => rfl
    | some p =>
      obtain ⟨v,rest⟩ := p
      simp only [ih, Option.some_bind]
      change (BinaryTokenCodec.readMany k rest).map (fun p => (v::p.1,p.2)) =
        (BinaryTokenCodec.readMany k rest).bind (fun p => some (v::p.1,p.2))
      cases BinaryTokenCodec.readMany k rest <;> rfl

/-- Independent of the declared count k, including huge malformed headers. -/
theorem many_bound (k : Nat) (bs : List Bool) : (many k bs).2 ≤ 3*bs.length+2 := by
  induction k generalizing bs with
  | zero => simp [many]
  | succ k ih =>
    have hn := number_bound bs
    cases he : (number bs).1 with
    | none => simp only [many, he]; omega
    | some p =>
      obtain ⟨v,rest⟩ := p
      have hc := number_consumes bs v rest he
      have hr := ih rest
      simp only [many, he]
      omega

def parse (bs : List Bool) : Option (List Nat × List Bool) × Nat :=
  let a := number bs
  match a.1 with
  | none => (none,1+a.2)
  | some (k,rest) => let b := many k rest; (b.1,1+a.2+b.2)

theorem parse_value (bs : List Bool) : (parse bs).1 = BinaryTokenCodec.parse bs := by
  simp only [parse, BinaryTokenCodec.parse, number_value]
  cases BinaryTokenCodec.readNumber bs with
  | none => rfl
  | some p => simpa using many_value p.1 p.2

theorem parse_bound (bs : List Bool) : (parse bs).2 ≤ 3*bs.length+2 := by
  have hn := number_bound bs
  cases he : (number bs).1 with
  | none => simp only [parse, he]; omega
  | some p =>
    obtain ⟨k,rest⟩ := p
    have hc := number_consumes bs k rest he
    have hm := many_bound k rest
    simp only [parse, he]; omega

def decode (bs : List Bool) : Option (List Nat) × Nat :=
  let p := parse bs
  (p.1.bind (fun r => if r.2.isEmpty then some r.1 else none),1+p.2)

theorem decode_value (bs : List Bool) : (decode bs).1 = BinaryTokenCodec.decode bs := by
  simp only [decode, parse_value, BinaryTokenCodec.decode]
  cases BinaryTokenCodec.parse bs <;> rfl

theorem decode_bound (bs : List Bool) : (decode bs).2 ≤ 3*bs.length+3 := by
  have h := parse_bound bs
  simp only [decode]; omega
end NSSE.CountedBinaryTokenDecode
