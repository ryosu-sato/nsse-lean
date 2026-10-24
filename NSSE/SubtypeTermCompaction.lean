import NSSE.SubtypeTermRenaming
import NSSE.StoredQuerySize

/-! # Compaction of the declared variable universe

`StoredQuerySize.size` charges the DECLARED universe `n` and every variable
index in unary, so the seven-exponential bounds of the counted term deciders
are not yet bounds in a structural measure of the input: a query using three
variables but declaring `Fin (2^100)`, or naming its variables by huge indices,
inflates `size` without changing anything semantic.

This file removes that gap on the input side. `compactQuery` renames the
variables that actually occur to a dense universe `Fin k`, with `k` at most the
number of variable OCCURRENCES, and

* `rename_compactQuery` proves the compaction is exactly an injective renaming
  of the original query, hence (with `SubtypeTermRenaming.entails_rename`)
  entailment and satisfiability are unchanged for every constructor and every
  ordered semantics (`entails_compactQuery`, `satisfiable_compactQuery`);
* `size_compactQuery` bounds `StoredQuerySize.size` of the packed compacted
  query by `(unitSize Q+1)^2`, where `unitSize` counts symbols only: it charges
  `1` per variable occurrence and ignores both the declared universe and the
  variable names.

The remaining encoded-length question is the bit-level codec relating
`unitSize` to an actual input string; machine-time simulation is separate.
-/

namespace NSSE.SubtypeTermCompaction

open SubtypeTerms SubtypeTermRenaming

variable {n d k : Nat}

/-! ## Occurring variables -/

def termVars : Term n d → List (Fin n)
  | .var x => [x]
  | .bot => []
  | .top => []
  | .node c => (List.finRange d).flatMap (fun i => termVars (c i))

def literalVars : Literal n d → List (Fin n)
  | .le a b => termVars a ++ termVars b
  | .eq a b => termVars a ++ termVars b

def queryVars (Q : Query n d) : List (Fin n) :=
  (termVars Q.left ++ termVars Q.right ++ Q.premises.flatMap literalVars).dedup

theorem queryVars_nodup (Q : Query n d) : (queryVars Q).Nodup := List.nodup_dedup _

theorem mem_queryVars_left (Q : Query n d) {x : Fin n} (h : x ∈ termVars Q.left) :
    x ∈ queryVars Q := by
  simp only [queryVars, List.mem_dedup, List.mem_append]
  exact Or.inl (Or.inl h)

theorem mem_queryVars_right (Q : Query n d) {x : Fin n} (h : x ∈ termVars Q.right) :
    x ∈ queryVars Q := by
  simp only [queryVars, List.mem_dedup, List.mem_append]
  exact Or.inl (Or.inr h)

theorem mem_queryVars_premise (Q : Query n d) {l : Literal n d} (hl : l ∈ Q.premises)
    {x : Fin n} (h : x ∈ literalVars l) : x ∈ queryVars Q := by
  simp only [queryVars, List.mem_dedup, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨l, hl, h⟩

/-! ## The compaction -/

/-- Rename each variable to its position in `vs`. Variables outside `vs` are
sent to `bot`; every use below supplies the hypothesis that this never happens. -/
def compactTerm (vs : List (Fin n)) : Term n d → Term vs.length d
  | .var x => if h : vs.idxOf x < vs.length then .var ⟨vs.idxOf x, h⟩ else .bot
  | .bot => .bot
  | .top => .top
  | .node c => .node (fun i => compactTerm vs (c i))

def compactLiteral (vs : List (Fin n)) : Literal n d → Literal vs.length d
  | .le a b => .le (compactTerm vs a) (compactTerm vs b)
  | .eq a b => .eq (compactTerm vs a) (compactTerm vs b)

def compactQueryOn (vs : List (Fin n)) (Q : Query n d) : Query vs.length d :=
  ⟨Q.premises.map (compactLiteral vs), compactTerm vs Q.left, compactTerm vs Q.right⟩

/-- The dense universe supplied by the occurring variables. -/
def compactQuery (Q : Query n d) : Query (queryVars Q).length d :=
  compactQueryOn (queryVars Q) Q

/-- The injection back into the declared universe. -/
def place (vs : List (Fin n)) : Fin vs.length → Fin n := fun i => vs[i.val]

theorem place_injective {vs : List (Fin n)} (h : vs.Nodup) : Function.Injective (place vs) := by
  intro i j hij
  have hg : vs.get i = vs.get j := hij
  exact List.nodup_iff_injective_get.mp h hg

theorem place_idxOf {vs : List (Fin n)} {x : Fin n} (h : vs.idxOf x < vs.length) :
    place vs ⟨vs.idxOf x, h⟩ = x := List.getElem_idxOf h

/-! ## Compaction is an injective renaming -/

theorem rename_compactTerm (vs : List (Fin n)) (t : Term n d)
    (h : ∀ x ∈ termVars t, x ∈ vs) : renameTerm (place vs) (compactTerm vs t) = t := by
  induction t with
  | var x =>
    have hx : x ∈ vs := h x (by simp [termVars])
    have hlt : vs.idxOf x < vs.length := List.idxOf_lt_length_iff.mpr hx
    simp only [compactTerm, dif_pos hlt, renameTerm]
    exact congrArg _ (place_idxOf hlt)
  | bot => rfl
  | top => rfl
  | node c ih =>
    simp only [compactTerm, renameTerm]
    refine congrArg _ (funext fun i => ih i ?_)
    intro x hx
    exact h x (by simp only [termVars, List.mem_flatMap]; exact ⟨i, List.mem_finRange i, hx⟩)

theorem rename_compactLiteral (vs : List (Fin n)) (l : Literal n d)
    (h : ∀ x ∈ literalVars l, x ∈ vs) : renameLiteral (place vs) (compactLiteral vs l) = l := by
  cases l with
  | le a b =>
    simp only [compactLiteral, renameLiteral]
    rw [rename_compactTerm vs a (fun x hx => h x (by simp [literalVars, hx])),
      rename_compactTerm vs b (fun x hx => h x (by simp [literalVars, hx]))]
  | eq a b =>
    simp only [compactLiteral, renameLiteral]
    rw [rename_compactTerm vs a (fun x hx => h x (by simp [literalVars, hx])),
      rename_compactTerm vs b (fun x hx => h x (by simp [literalVars, hx]))]

/-- The compacted query, renamed back along the injection, is the original
query. Nothing is lost and nothing is invented. -/
theorem rename_compactQuery (Q : Query n d) :
    renameQuery (place (queryVars Q)) (compactQuery Q) = Q := by
  have hl := rename_compactTerm (queryVars Q) Q.left (fun x hx => mem_queryVars_left Q hx)
  have hr := rename_compactTerm (queryVars Q) Q.right (fun x hx => mem_queryVars_right Q hx)
  have hp : Q.premises.map (fun l => renameLiteral (place (queryVars Q)) (compactLiteral (queryVars Q) l))
      = Q.premises := by
    rw [List.map_congr_left (g := id) ?_, List.map_id]
    intro l hl'
    exact rename_compactLiteral _ l (fun x hx => mem_queryVars_premise Q hl' hx)
  simp only [renameQuery, compactQuery, compactQueryOn, List.map_map, Function.comp_def, hl, hr, hp]

section Semantics

open SubtypeConstraints (Constructor)

variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

/-- Compaction preserves entailment, for every constructor and every ordered
semantics: finite, regular and arbitrary trees alike. -/
theorem entails_compactQuery (F : Constructor T d) (Q : Query n d) :
    Entails F (compactQuery Q) ↔ Entails F Q := by
  conv_rhs => rw [← rename_compactQuery Q]
  exact (entails_rename F (place (queryVars Q)) (place_injective (queryVars_nodup Q))
    (compactQuery Q)).symm

theorem satisfiable_compactQuery (F : Constructor T d) (Q : Query n d) :
    Satisfiable F (compactQuery Q) ↔ Satisfiable F Q := by
  conv_rhs => rw [← rename_compactQuery Q]
  exact (satisfiable_rename F (place (queryVars Q)) (place_injective (queryVars_nodup Q))
    (compactQuery Q)).symm

end Semantics

/-! ## An identifier-free structural measure -/

/-- Symbol count: one per variable OCCURRENCE, one per constant, and the shape
of every node, charged exactly as `StoredSubtypeTerm.weight` charges it. It
never mentions the declared universe or a variable name. -/
def unitSizeTerm : Term n d → Nat
  | .var _ => 1
  | .bot => 1
  | .top => 1
  | .node c => 1+((List.finRange d).map (fun i => 1+unitSizeTerm (c i))).sum

def unitSizeLiteral : Literal n d → Nat
  | .le a b => 1+unitSizeTerm a+unitSizeTerm b
  | .eq a b => 1+unitSizeTerm a+unitSizeTerm b

def unitSize (Q : Query n d) : Nat :=
  1+unitSizeTerm Q.left+unitSizeTerm Q.right+(Q.premises.map unitSizeLiteral).sum

theorem unitSizeTerm_pos (t : Term n d) : 1 ≤ unitSizeTerm t := by
  cases t <;> simp [unitSizeTerm]

/-- Compaction only renames, so the structural measure is unchanged. -/
theorem unitSizeTerm_compact (vs : List (Fin n)) (t : Term n d) :
    unitSizeTerm (compactTerm vs t) = unitSizeTerm t := by
  induction t with
  | var x => by_cases h : vs.idxOf x < vs.length <;> simp [compactTerm, h, unitSizeTerm]
  | bot => rfl
  | top => rfl
  | node c ih =>
    simp only [compactTerm, unitSizeTerm]
    exact congrArg _ (congrArg _ (List.map_congr_left (fun i _ => by rw [ih i])))

theorem unitSizeLiteral_compact (vs : List (Fin n)) (l : Literal n d) :
    unitSizeLiteral (compactLiteral vs l) = unitSizeLiteral l := by
  cases l <;> simp only [compactLiteral, unitSizeLiteral, unitSizeTerm_compact]

theorem unitSize_compact (Q : Query n d) : unitSize (compactQuery Q) = unitSize Q := by
  simp only [unitSize, compactQuery, compactQueryOn, unitSizeTerm_compact, List.map_map,
    Function.comp_def, unitSizeLiteral_compact]

/-! ## The dense universe is bounded by the number of occurrences -/

theorem termVars_length (t : Term n d) : (termVars t).length ≤ unitSizeTerm t := by
  induction t with
  | var x => simp [termVars, unitSizeTerm]
  | bot => simp [termVars, unitSizeTerm]
  | top => simp [termVars, unitSizeTerm]
  | node c ih =>
    simp only [termVars, unitSizeTerm, List.length_flatMap]
    have h : ((List.finRange d).map (fun i => (termVars (c i)).length)).sum
        ≤ ((List.finRange d).map (fun i => 1+unitSizeTerm (c i))).sum := by
      apply List.sum_le_sum
      intro i _
      have := ih i
      omega
    omega

theorem literalVars_length (l : Literal n d) : (literalVars l).length ≤ unitSizeLiteral l := by
  cases l with
  | le a b =>
    have ha := termVars_length a
    have hb := termVars_length b
    simp only [literalVars, unitSizeLiteral, List.length_append]; omega
  | eq a b =>
    have ha := termVars_length a
    have hb := termVars_length b
    simp only [literalVars, unitSizeLiteral, List.length_append]; omega

theorem queryVars_length (Q : Query n d) : (queryVars Q).length ≤ unitSize Q := by
  have hd := (List.dedup_sublist (termVars Q.left ++ termVars Q.right ++
    Q.premises.flatMap literalVars)).length_le
  have hl := termVars_length Q.left
  have hr := termVars_length Q.right
  have hp : (Q.premises.flatMap literalVars).length ≤ (Q.premises.map unitSizeLiteral).sum := by
    simp only [List.length_flatMap]
    apply List.sum_le_sum
    intro l _
    exact literalVars_length l
  simp only [queryVars, List.length_append] at hd ⊢
  simp only [unitSize]
  omega

/-! ## The packed compacted query has identifier-free size -/

open StoredSubtypeTerm in
theorem weight_pack_le (t : Term k d) :
    StoredSubtypeTerm.weight (StoredSubtypeTerm.pack t) ≤ (k+1)*unitSizeTerm t := by
  induction t with
  | var x =>
    have hx := x.isLt
    simp only [StoredSubtypeTerm.pack, StoredSubtypeTerm.weight, unitSizeTerm, Nat.mul_one]
    omega
  | bot => simp [StoredSubtypeTerm.pack, StoredSubtypeTerm.weight, unitSizeTerm]
  | top => simp [StoredSubtypeTerm.pack, StoredSubtypeTerm.weight, unitSizeTerm]
  | node c ih =>
    simp only [StoredSubtypeTerm.pack, StoredSubtypeTerm.weight, unitSizeTerm, List.ofFn_eq_map,
      List.map_map, Function.comp_def]
    have hstep : ((List.finRange d).map (fun i => 1+StoredSubtypeTerm.weight
        (StoredSubtypeTerm.pack (c i)))).sum
          ≤ ((List.finRange d).map (fun i => (k+1)*(1+unitSizeTerm (c i)))).sum := by
      refine List.sum_le_sum (fun i _ => ?_)
      have h := ih i
      have hk : 1*1 ≤ (k+1)*1 := Nat.mul_le_mul_right 1 (by omega)
      calc 1+StoredSubtypeTerm.weight (StoredSubtypeTerm.pack (c i))
          ≤ (k+1)+(k+1)*unitSizeTerm (c i) := by omega
        _ = (k+1)*(1+unitSizeTerm (c i)) := by ring
    rw [List.sum_map_mul_left] at hstep
    calc 1+((List.finRange d).map (fun i => 1+StoredSubtypeTerm.weight
            (StoredSubtypeTerm.pack (c i)))).sum
        ≤ (k+1)+(k+1)*((List.finRange d).map (fun i => 1+unitSizeTerm (c i))).sum := by omega
      _ = (k+1)*(1+((List.finRange d).map (fun i => 1+unitSizeTerm (c i))).sum) := by ring

theorem literalWeight_pack_le (l : Literal k d) :
    StoredQuerySize.literalWeight (StoredTermQuery.packLiteral l) ≤ (k+1)*unitSizeLiteral l := by
  cases l with
  | le a b =>
    have ha := weight_pack_le a
    have hb := weight_pack_le b
    simp only [StoredTermQuery.packLiteral, StoredQuerySize.literalWeight, unitSizeLiteral]
    calc 1+StoredSubtypeTerm.weight (StoredSubtypeTerm.pack a)
            +StoredSubtypeTerm.weight (StoredSubtypeTerm.pack b)
        ≤ (k+1)+(k+1)*unitSizeTerm a+(k+1)*unitSizeTerm b := by omega
      _ = (k+1)*(1+unitSizeTerm a+unitSizeTerm b) := by ring
  | eq a b =>
    have ha := weight_pack_le a
    have hb := weight_pack_le b
    simp only [StoredTermQuery.packLiteral, StoredQuerySize.literalWeight, unitSizeLiteral]
    calc 1+StoredSubtypeTerm.weight (StoredSubtypeTerm.pack a)
            +StoredSubtypeTerm.weight (StoredSubtypeTerm.pack b)
        ≤ (k+1)+(k+1)*unitSizeTerm a+(k+1)*unitSizeTerm b := by omega
      _ = (k+1)*(1+unitSizeTerm a+unitSizeTerm b) := by ring

/-- For a query over a DENSE universe, the stored structural size is at most
the universe size times the symbol count. -/
theorem size_pack_le (Q : Query k d) :
    StoredQuerySize.size (StoredTermQuery.packQuery Q) ≤ (k+1)*unitSize Q := by
  have hl := weight_pack_le Q.left
  have hr := weight_pack_le Q.right
  have hp : (Q.premises.map (fun l => StoredQuerySize.literalWeight
      (StoredTermQuery.packLiteral l))).sum ≤ (k+1)*(Q.premises.map unitSizeLiteral).sum := by
    have h := List.sum_le_sum (l := Q.premises)
      (f := fun l => StoredQuerySize.literalWeight (StoredTermQuery.packLiteral l))
      (g := fun l => (k+1)*unitSizeLiteral l) (fun l _ => literalWeight_pack_le l)
    rwa [List.sum_map_mul_left] at h
  simp only [StoredQuerySize.size, StoredTermQuery.packQuery, List.map_map, Function.comp_def,
    unitSize]
  calc k+1+StoredSubtypeTerm.weight (StoredSubtypeTerm.pack Q.left)
          +StoredSubtypeTerm.weight (StoredSubtypeTerm.pack Q.right)
          +(Q.premises.map (fun l => StoredQuerySize.literalWeight
            (StoredTermQuery.packLiteral l))).sum
      ≤ (k+1)+(k+1)*unitSizeTerm Q.left+(k+1)*unitSizeTerm Q.right
          +(k+1)*(Q.premises.map unitSizeLiteral).sum := by omega
    _ = (k+1)*(1+unitSizeTerm Q.left+unitSizeTerm Q.right
          +(Q.premises.map unitSizeLiteral).sum) := by ring

/-- The whole point: after compaction the stored size is bounded by a
polynomial in the SYMBOL COUNT of the original query. Neither the declared
universe `n` nor the size of any variable name occurs on the right. -/
theorem size_compactQuery (Q : Query n d) :
    StoredQuerySize.size (StoredTermQuery.packQuery (compactQuery Q)) ≤ (unitSize Q+1)^2 := by
  have h := size_pack_le (compactQuery Q)
  rw [unitSize_compact] at h
  have hk := queryVars_length Q
  have hmul : ((queryVars Q).length+1)*unitSize Q ≤ (unitSize Q+1)*(unitSize Q+1) :=
    Nat.mul_le_mul (by omega) (by omega)
  calc StoredQuerySize.size (StoredTermQuery.packQuery (compactQuery Q))
      ≤ ((queryVars Q).length+1)*unitSize Q := h
    _ ≤ (unitSize Q+1)*(unitSize Q+1) := hmul
    _ = (unitSize Q+1)^2 := by ring

end NSSE.SubtypeTermCompaction
