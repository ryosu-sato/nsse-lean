import NSSE.CheckedBitListInput
import NSSE.BitListTokenDecodeSize
import NSSE.BinarySupportQuery

namespace NSSE.CheckedBinaryInput
open BitListTokenReader (eval)

def decode (limit arity bs : List Bool) : Option (CheckedBitListInput.Input limit arity) × Nat :=
  let t := BitListTokenDecode.decode bs
  match t.1 with
  | none => (none,1+t.2)
  | some tokens => let r := CheckedBitListInput.decode limit arity tokens; (r.1,1+t.2+r.2)

theorem value (limit arity bs : List Bool) :
    (decode limit arity bs).1.map CheckedBitListInput.Input.denote =
      BinarySupportQuery.decode (eval limit) (eval arity) bs := by
  have hv := BitListTokenDecode.decode_value bs
  cases ht : (BitListTokenDecode.decode bs).1 with
  | none =>
    simp only [ht,Option.map_none'] at hv
    simp [decode,ht,BinarySupportQuery.decode,← hv]
  | some tokens =>
    simp only [ht,Option.map_some'] at hv
    simp only [decode,ht,BinarySupportQuery.decode,← hv,Option.some_bind]
    exact CheckedBitListInput.decode_value limit arity tokens

def boundBudget (V H L : Nat) := 5+3*(L+V)+(L+1)*(2*H+3*V+6)+3*L
def boundsBudget (V H L : Nat) := 1+(L+1)*(2*L+3+boundBudget V H L)
def indicesBudget (V L : Nat) := 1+(L+1)*(2*L+3*V+6)+3*L
def budget (V H L : Nat) := 7+(L+1)*(3*L+8)+2*boundsBudget V H L+2*indicesBudget V L

theorem bound (limit arity bs : List Bool) :
    (decode limit arity bs).2 ≤ budget limit.length arity.length bs.length := by
  have ht := BitListTokenDecode.decode_bound bs
  cases he : (BitListTokenDecode.decode bs).1 with
  | none => simp only [decode,he,budget]; omega
  | some tokens =>
    have hs := BitListTokenDecodeSize.decode bs tokens he
    have hb : CheckedBitListBound.budget limit arity tokens ≤
        boundBudget limit.length arity.length bs.length := by
      have hm := Nat.mul_le_mul_right (2*arity.length+3*limit.length+6)
        (show tokens.length+1 ≤ bs.length+1 by omega)
      dsimp only [CheckedBitListBound.budget,CheckedBitListChildren.budget,boundBudget]
      omega
    have hu : CheckedBitListBounds.readBudget limit arity tokens ≤
        boundsBudget limit.length arity.length bs.length := by
      dsimp only [CheckedBitListBounds.readBudget,boundsBudget]
      gcongr <;> omega
    have hi : CheckedBitListIndices.budget limit tokens ≤ indicesBudget limit.length bs.length := by
      dsimp only [CheckedBitListIndices.budget,indicesBudget]
      gcongr <;> omega
    have hr := CheckedBitListInput.decode_bound limit arity tokens
    simp only [CheckedBitListInput.budget] at hr
    simp only [decode,he,budget]
    omega

theorem roundtrip (limit arity : List Bool)
    (I : StoredSubtypeInput.Input (eval limit) (eval arity)) :
    (decode limit arity (BinarySupportQuery.encode I)).1.map CheckedBitListInput.Input.denote = some I := by
  rw [value,BinarySupportQuery.decode_encode]
end NSSE.CheckedBinaryInput
