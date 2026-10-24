import NSSE.ListFiniteSATSize

namespace NSSE.CountedBinaryFiniteSatisfiability
open BitListTokenReader (eval)
variable {limit arity : List Bool}

def decide (I : CheckedBitListInput.Input limit arity) : Bool × Nat :=
  let n := CountedBitListValue.convert limit
  let d := CountedBitListValue.convert arity
  let c := CountedBinaryInputConversion.convert I
  let ci : StoredSubtypeInput.Input n.1 d.1 :=
    cast (by rw [CountedBitListValue.value,CountedBitListValue.value]) c.1
  let q := ListFiniteSatisfiability.decide ci
  (q.1,1+n.2+d.2+c.2+q.2)

theorem decide_cast {n d m e : Nat} (hn : m=n) (hd : e=d) (I : StoredSubtypeInput.Input n d) :
    ListFiniteSatisfiability.decide (n := m) (d := e) (cast (by rw [hn,hd]) I) =
      ListFiniteSatisfiability.decide I := by
  subst m
  subst e
  rfl

theorem cost (I : CheckedBitListInput.Input limit arity) :
    (decide I).2 = 1+(CountedBitListValue.convert limit).2+(CountedBitListValue.convert arity).2+
      (CountedBinaryInputConversion.convert I).2+(ListFiniteSatisfiability.decide I.denote).2 := by
  have h := decide_cast (CountedBitListValue.value limit) (CountedBitListValue.value arity) I.denote
  simp only [decide,CountedBinaryInputConversion.value,h]

theorem value (I : CheckedBitListInput.Input limit arity) :
    (decide I).1 = FiniteSubtypeDecision.decideSatisfiable I.denote.denote := by
  have h := decide_cast (CountedBitListValue.value limit) (CountedBitListValue.value arity) I.denote
  simp only [decide,CountedBinaryInputConversion.value,h,ListFiniteSatisfiability.value]

def decode (limit arity bs : List Bool) : Option Bool × Nat :=
  let r := CheckedBinaryInput.decode limit arity bs
  match r.1 with
  | none => (none,1+r.2)
  | some I => let q := decide I; (some q.1,1+r.2+q.2)

theorem decode_value (limit arity bs : List Bool) :
    (decode limit arity bs).1 = (BinarySupportQuery.decode (eval limit) (eval arity) bs).map
      (fun I => FiniteSubtypeDecision.decideSatisfiable I.denote) := by
  have hv := CheckedBinaryInput.value limit arity bs
  cases hr : (CheckedBinaryInput.decode limit arity bs).1 with
  | none =>
    simp only [hr,Option.map_none'] at hv
    simp [decode,hr,← hv]
  | some I =>
    simp only [hr,Option.map_some'] at hv
    simp [decode,hr,← hv,value]

theorem encoded_correct (limit arity : List Bool)
    (I : StoredSubtypeInput.Input (eval limit) (eval arity)) :
    (decode limit arity (BinarySupportQuery.encode I)).1 = some true ↔
      SubtypeConstraints.Satisfiable (FiniteSubtypeTrees.constructor (eval arity)) I.denote := by
  rw [decode_value,BinarySupportQuery.decode_encode]
  simp only [Option.map_some',Option.some.injEq,FiniteSubtypeDecision.decideSatisfiable_correct]

end NSSE.CountedBinaryFiniteSatisfiability
