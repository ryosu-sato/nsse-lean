import NSSE.CountedBinaryInputConversion
import NSSE.CheckedBinaryInput
import NSSE.StoredSupportQuery

namespace NSSE.CountedBinarySupport
open BitListTokenReader (eval)
open CheckedBitListIndex (Index)
open CheckedBitListInput (Input)
variable {limit arity : List Bool}

def query (I : Input limit arity) (x y : Index limit) : Bool × Nat :=
  let n := CountedBitListValue.convert limit
  let d := CountedBitListValue.convert arity
  let c := CountedBinaryInputConversion.convert I
  let a := CountedBitListValue.index x
  let b := CountedBitListValue.index y
  let ci : StoredSubtypeInput.Input n.1 d.1 :=
    cast (by rw [CountedBitListValue.value,CountedBitListValue.value]) c.1
  let ax : Fin n.1 := cast (by rw [CountedBitListValue.value]) a.1
  let by_ : Fin n.1 := cast (by rw [CountedBitListValue.value]) b.1
  let q := StoredSupportQuery.query ci ax by_
  (q.1,1+n.2+d.2+c.2+a.2+b.2+q.2)

theorem query_cast {n d m e : Nat} (hn : m=n) (hd : e=d)
    (I : StoredSubtypeInput.Input n d) (x y : Fin n) :
    StoredSupportQuery.query (n := m) (d := e)
      (cast (by rw [hn,hd]) I) (cast (by rw [hn]) x) (cast (by rw [hn]) y) =
      StoredSupportQuery.query I x y := by
  subst m
  subst e
  rfl

theorem value (I : Input limit arity) (x y : Index limit) :
    (query I x y).1 = (StoredSupportQuery.query I.denote x.denote y.denote).1 := by
  simp only [query,CountedBinaryInputConversion.value,CountedBitListValue.index_value]
  exact congrArg Prod.fst (query_cast (CountedBitListValue.value limit)
    (CountedBitListValue.value arity) I.denote x.denote y.denote)

theorem correct (I : Input limit arity) (x y : Index limit) :
    (query I x y).1 = true ↔ SubtypeConstraints.Support I.denote.denote x.denote y.denote := by
  rw [value]
  exact StoredSupportQuery.correct I.denote x.denote y.denote

def budget (I : Input limit arity) (x y : Index limit) :=
  3+(2^limit.length+4*limit.length)+(2^arity.length+4*arity.length)+
    CountedBinaryInputConversion.budget I+2*eval limit+
    4*(x.digits.length+y.digits.length)+StoredSupportQuery.budget I.denote

theorem bound (I : Input limit arity) (x y : Index limit) :
    (query I x y).2 ≤ budget I x y := by
  have hn := CountedBitListValue.bit_bound limit
  have hd := CountedBitListValue.bit_bound arity
  have hc := CountedBinaryInputConversion.conversion_bound I
  have hx := CountedBitListValue.index_bound x
  have hy := CountedBitListValue.index_bound y
  have hq := StoredSupportQuery.bound I.denote x.denote y.denote
  have he := query_cast (CountedBitListValue.value limit)
    (CountedBitListValue.value arity) I.denote x.denote y.denote
  simp only [query,CountedBinaryInputConversion.value,CountedBitListValue.index_value,he,budget]
  omega

def decodeQuery (limit arity bs : List Bool) (x y : Index limit) : Option Bool × Nat :=
  let r := CheckedBinaryInput.decode limit arity bs
  match r.1 with
  | none => (none,1+r.2)
  | some I => let q := query I x y; (some q.1,1+r.2+q.2)

theorem decode_value (limit arity bs : List Bool) (x y : Index limit) :
    (decodeQuery limit arity bs x y).1 =
      (BinarySupportQuery.query (eval limit) (eval arity) bs x.denote y.denote).map Prod.fst := by
  have hv := CheckedBinaryInput.value limit arity bs
  cases hr : (CheckedBinaryInput.decode limit arity bs).1 with
  | none =>
    simp only [hr,Option.map_none'] at hv
    simp [decodeQuery,hr,BinarySupportQuery.query,← hv]
  | some I =>
    simp only [hr,Option.map_some'] at hv
    simp [decodeQuery,hr,BinarySupportQuery.query,← hv,value]

theorem rejected_bound (limit arity bs : List Bool) (x y : Index limit)
    (h : (CheckedBinaryInput.decode limit arity bs).1 = none) :
    (decodeQuery limit arity bs x y).2 ≤ 1+CheckedBinaryInput.budget limit.length arity.length bs.length := by
  simpa only [decodeQuery,h] using Nat.add_le_add_left (CheckedBinaryInput.bound limit arity bs) 1

theorem accepted_bound (limit arity bs : List Bool) (x y : Index limit) (I : Input limit arity)
    (h : (CheckedBinaryInput.decode limit arity bs).1 = some I) :
    (decodeQuery limit arity bs x y).2 ≤
      1+CheckedBinaryInput.budget limit.length arity.length bs.length+budget I x y := by
  have hd := CheckedBinaryInput.bound limit arity bs
  have hq := bound I x y
  simp only [decodeQuery,h]
  omega
end NSSE.CountedBinarySupport
