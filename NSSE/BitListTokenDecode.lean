import NSSE.BitListCountdown

/-! Token decoding with binary-list headers and binary-list values.
Termination uses strict input consumption; eval is specification-only.
Resource counters are still mathematical Nats, not machine integers. -/
namespace NSSE.BitListTokenDecode
open BitListTokenReader (eval)

def many (count bs : List Bool) : Option (List (List Bool) × List Bool) × Nat :=
  let c := BitListCountdown.decrement count
  match c.1 with
  | none => (some ([],bs),1+c.2)
  | some next =>
    let r := BitListTokenReader.read bs
    match hr : r.1 with
    | none => (none,2+c.2+r.2)
    | some (digits,rest) =>
      let t := many next rest
      (t.1.map (fun p => (digits::p.1,p.2)),2+c.2+r.2+t.2)
termination_by bs.length
decreasing_by
  have hs := BitListTokenReader.sizes bs digits rest hr
  omega

theorem value (count bs : List Bool) :
    (many count bs).1.map (fun p => (p.1.map eval,p.2)) =
      BinaryTokenCodec.readMany (eval count) bs := by
  induction count, bs using many.induct with
  | case1 count bs c hc =>
    dsimp only [c] at hc
    have hz := (BitListCountdown.none_iff count).mp hc
    rw [many]
    dsimp only
    simp only [ hc, hz, BinaryTokenCodec.readMany, Option.map_some', List.map_nil]
  | case2 count bs c next hc r hr =>
    dsimp only [c] at hc
    dsimp only [r] at hr
    have hs := BitListCountdown.some_value count next hc
    have hv := BitListTokenReader.value bs
    simp only [hr, Option.map_none'] at hv
    rw [many]
    dsimp only
    simp only [ hc, hr, Option.map_none', ← hs.1, BinaryTokenCodec.readMany, ← hv]
    split
    · rfl
    · rename_i ds rs hh
      rw [hr] at hh
      cases hh
  | case3 count bs c next hc r digits rest hr ih =>
    dsimp only [c] at hc
    dsimp only [r] at hr
    have hs := BitListCountdown.some_value count next hc
    have hv := BitListTokenReader.value bs
    simp only [hr, Option.map_some'] at hv
    rw [many]
    dsimp only
    simp only [hc, hr, Option.map_map, Function.comp_def, List.map_cons]
    split
    · rename_i hh; rw [hr] at hh; cases hh
    · rename_i ds rs hh
      have he : (digits,rest)=(ds,rs) := Option.some.inj (hr.symm.trans hh)
      cases he
      simp only [Option.map_map, Function.comp_def, List.map_cons]
      rw [← hs.1, BinaryTokenCodec.readMany, ← hv]
      change _ = (BinaryTokenCodec.readMany (eval next) rest).bind
        (fun p => some (eval digits::p.1,p.2))
      rw [← ih]
      cases (many next rest).1 <;> rfl

def budget (H B : Nat) := (B+1)*(2*H+B+6)

theorem bound (count bs : List Bool) :
    (many count bs).2 ≤ budget count.length bs.length := by
  induction count, bs using many.induct with
  | case1 count bs c hc =>
    dsimp only [c] at hc
    have h := BitListCountdown.bound count
    rw [many]
    dsimp only
    simp only [ hc, budget]
    nlinarith
  | case2 count bs c next hc r hr =>
    dsimp only [c] at hc
    dsimp only [r] at hr
    have h := BitListCountdown.bound count
    have hread := BitListTokenReader.bound bs
    rw [many]
    dsimp only
    simp only [ hc, hr, budget]
    split
    · nlinarith
    · rename_i ds rs hh; rw [hr] at hh; cases hh
  | case3 count bs c next hc r digits rest hr ih =>
    dsimp only [c] at hc
    dsimp only [r] at hr
    have h := BitListCountdown.bound count
    have hread := BitListTokenReader.bound bs
    have hn := (BitListCountdown.some_value count next hc).2
    have hs := BitListTokenReader.sizes bs digits rest hr
    have hrest : rest.length+1 ≤ bs.length := by omega
    have hi : (many next rest).2 ≤ bs.length*(2*count.length+bs.length+5) := by
      apply ih.trans
      dsimp only [budget]
      exact Nat.mul_le_mul hrest (by omega)
    rw [many]
    dsimp only
    simp only [ hc, hr, budget]
    split
    · rename_i hh; rw [hr] at hh; cases hh
    · rename_i ds rs hh
      have he : (digits,rest)=(ds,rs) := Option.some.inj (hr.symm.trans hh)
      cases he
      nlinarith

def parse (bs : List Bool) : Option (List (List Bool) × List Bool) × Nat :=
  let h := BitListTokenReader.read bs
  match h.1 with
  | none => (none,1+h.2)
  | some (count,rest) => let r := many count rest; (r.1,1+h.2+r.2)

theorem parse_value (bs : List Bool) :
    (parse bs).1.map (fun p => (p.1.map eval,p.2)) = BinaryTokenCodec.parse bs := by
  have hv := BitListTokenReader.value bs
  cases he : (BitListTokenReader.read bs).1 with
  | none =>
    simp only [he, Option.map_none'] at hv
    simp only [parse, he, Option.map_none', BinaryTokenCodec.parse, ← hv]
    rfl
  | some p =>
    obtain ⟨count,rest⟩ := p
    simp only [he, Option.map_some'] at hv
    simp only [parse, he, BinaryTokenCodec.parse, ← hv]
    exact value count rest

def decode (bs : List Bool) : Option (List (List Bool)) × Nat :=
  let r := parse bs
  (r.1.bind (fun p => if p.2.isEmpty then some p.1 else none),1+r.2)

theorem decode_value (bs : List Bool) :
    (decode bs).1.map (List.map eval) = BinaryTokenCodec.decode bs := by
  rw [BinaryTokenCodec.decode, ← parse_value]
  simp only [decode]
  cases (parse bs).1 with
  | none => rfl
  | some p =>
    obtain ⟨ns,rest⟩ := p
    by_cases h : rest.isEmpty <;> simp [h]
theorem parse_bound (bs : List Bool) :
    (parse bs).2 ≤ (bs.length+1)*(3*bs.length+8) := by
  have hr := BitListTokenReader.bound bs
  cases he : (BitListTokenReader.read bs).1 with
  | none => simp only [parse, he]; nlinarith
  | some p =>
    obtain ⟨count,rest⟩ := p
    have hs := BitListTokenReader.sizes bs count rest he
    have hm := bound count rest
    have hh : count.length ≤ bs.length := by omega
    have ht : rest.length ≤ bs.length := by omega
    have hm' : (many count rest).2 ≤ (bs.length+1)*(3*bs.length+6) := by
      apply hm.trans
      dsimp only [budget]
      exact Nat.mul_le_mul (by omega) (by omega)
    simp only [parse, he]
    nlinarith

theorem decode_bound (bs : List Bool) :
    (decode bs).2 ≤ (bs.length+1)*(3*bs.length+8)+1 := by
  have h := parse_bound bs
  simp only [decode]; omega
end NSSE.BitListTokenDecode
