import NSSE.StoredSubtypeInput

/-! Natural-number token serialization with checked indices and arity.
This fixes a token format, not yet a bit format or decoding-time bound. -/
namespace NSSE.StoredInputCodec
open StoredSubtypeInput
abbrev Parser (α : Type) := List Nat → Option (α × List Nat)

def index (n : Nat) : Parser (Fin n)
  | [] => none
  | x::xs => if h : x<n then some (⟨x,h⟩,xs) else none

theorem index_roundtrip {n : Nat} (x : Fin n) (rest : List Nat) :
    index n (x.val::rest) = some (x,rest) := by simp [index, x.isLt]

def many {α : Type} (p : Parser α) : Nat → Parser (List α)
  | 0, xs => some ([],xs)
  | k+1, xs => do
    let (a,ys) ← p xs
    let (as,zs) ← many p k ys
    pure (a::as,zs)

theorem many_roundtrip {α : Type} (p : Parser α) (write : α → List Nat)
    (h : ∀ a rest, p (write a++rest) = some (a,rest)) (as : List α) (rest : List Nat) :
    many p as.length (as.flatMap write++rest) = some (as,rest) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [many, List.flatMap_cons, List.append_assoc, h, ih]

def writeList {α : Type} (write : α → List Nat) (as : List α) : List Nat :=
  as.length::as.flatMap write

def readList {α : Type} (p : Parser α) : Parser (List α)
  | [] => none
  | k::xs => many p k xs

theorem list_roundtrip {α : Type} (p : Parser α) (write : α → List Nat)
    (h : ∀ a rest, p (write a++rest) = some (a,rest)) (as : List α) (rest : List Nat) :
    readList p (writeList write as++rest) = some (as,rest) := by
  simpa only [writeList, List.cons_append, readList] using many_roundtrip p write h as rest

variable {n d : Nat}
def writeIndex (x : Fin n) : List Nat := [x.val]
def writeBound (a : Bound n d) : List Nat := a.head.val::a.children.map Fin.val

def readBound (n d : Nat) : Parser (Bound n d) := fun xs => do
  let (head,ys) ← index n xs
  let (children,zs) ← many (index n) d ys
  if h : children.length=d then pure (⟨head,children,h⟩,zs) else none

theorem bound_roundtrip (a : Bound n d) (rest : List Nat) :
    readBound n d (writeBound a++rest) = some (a,rest) := by
  have hm := many_roundtrip (index n) writeIndex (fun x r => index_roundtrip x r) a.children rest
  simp only [writeIndex, List.flatMap_cons, List.flatMap_nil] at hm
  have hf : a.children.flatMap writeIndex = a.children.map Fin.val := by
    induction a.children with
    | nil => rfl
    | cons x xs ih => simp [writeIndex, ih]
  rw [hf, a.length_eq] at hm
  simp [readBound, writeBound, index_roundtrip, hm, a.length_eq]

def encode (I : Input n d) : List Nat :=
  writeList writeBound I.upper ++ writeList writeBound I.lower ++
    writeList writeIndex I.bot ++ writeList writeIndex I.top

def parse (n d : Nat) : Parser (Input n d) := fun xs => do
  let (upper,xs) ← readList (readBound n d) xs
  let (lower,xs) ← readList (readBound n d) xs
  let (bot,xs) ← readList (index n) xs
  let (top,xs) ← readList (index n) xs
  pure (⟨upper,lower,bot,top⟩,xs)

theorem parse_roundtrip (I : Input n d) (rest : List Nat) :
    parse n d (encode I++rest) = some (I,rest) := by
  have hb := list_roundtrip (readBound n d) writeBound bound_roundtrip
  have hi := list_roundtrip (index n) writeIndex (fun x r => index_roundtrip x r)
  simp [parse, encode, List.append_assoc, hb, hi]

def decode (n d : Nat) (xs : List Nat) : Option (Input n d) := do
  let (I,rest) ← parse n d xs
  if rest.isEmpty then pure I else none

theorem decode_encode (I : Input n d) : decode n d (encode I) = some I := by
  have h := parse_roundtrip I []
  simp only [List.append_nil] at h
  simp [decode, h]

theorem encode_injective : Function.Injective (encode (n := n) (d := d)) := by
  intro a b h
  have hh := congrArg (decode n d) h
  simpa only [decode_encode, Option.some.injEq] using hh
theorem writeList_length {α : Type} (write : α → List Nat) (as : List α) (k : Nat)
    (h : ∀ a, (write a).length = k) :
    (writeList write as).length = 1+as.length*k := by
  simp [writeList, List.length_flatMap, h, List.map_const', List.sum_replicate,
    smul_eq_mul, Nat.add_comm]

theorem encode_length (I : Input n d) :
    (encode I).length = 4+(I.upper.length+I.lower.length)*(d+1)+I.bot.length+I.top.length := by
  have hb (a : Bound n d) : (writeBound a).length = d+1 := by simp [writeBound, a.length_eq]
  have hi (x : Fin n) : (writeIndex x).length = 1 := rfl
  simp only [encode, List.length_append, writeList_length writeBound I.upper (d+1) hb,
    writeList_length writeBound I.lower (d+1) hb,
    writeList_length writeIndex I.bot 1 hi, writeList_length writeIndex I.top 1 hi]
  ring
end NSSE.StoredInputCodec
