import NSSE.RawCodecSoundness
import NSSE.SubtypeTermCompaction

/-! # From a decoded raw query to a typed query over a dense universe

A decoded query names its variables by arbitrary naturals. This file turns it
into a query of the development's own type `SubtypeTerms.Query k d`, where `k`
is the number of DISTINCT identifiers it mentions, and supplies the injection
back into any universe the identifiers fit in — at which point
`SubtypeTermRenaming.entails_rename` says the answer is unchanged.

The identifier-free size bound of v1621 then applies, so the stored size of the
converted query is quadratic in the number of symbols, hence quadratic in the
encoded input length.
-/

namespace NSSE.CodedQueryConversion

open RawTermCodec RawQueryCodec SubtypeTerms SubtypeTermRenaming SubtypeTermCompaction

variable {n d : Nat}

/-! ## Identifiers of a raw query -/

def termIds : Raw → List Nat
  | .var i => [i]
  | .bot => []
  | .top => []
  | .node cs => cs.flatMap termIds

def litIds : RawLit → List Nat
  | .le a b => termIds a ++ termIds b
  | .eq a b => termIds a ++ termIds b

def queryIds (Q : RawQuery) : List Nat :=
  (Q.premises.flatMap litIds ++ termIds Q.left ++ termIds Q.right).dedup

theorem queryIds_nodup (Q : RawQuery) : (queryIds Q).Nodup := List.nodup_dedup _

theorem mem_queryIds_left (Q : RawQuery) {i : Nat} (h : i ∈ termIds Q.left) :
    i ∈ queryIds Q := by
  simp only [queryIds, List.mem_dedup, List.mem_append]
  exact Or.inl (Or.inr h)

theorem mem_queryIds_right (Q : RawQuery) {i : Nat} (h : i ∈ termIds Q.right) :
    i ∈ queryIds Q := by
  simp only [queryIds, List.mem_dedup, List.mem_append]
  exact Or.inr h

theorem mem_queryIds_premise (Q : RawQuery) {l : RawLit} (hl : l ∈ Q.premises)
    {i : Nat} (h : i ∈ litIds l) : i ∈ queryIds Q := by
  simp only [queryIds, List.mem_dedup, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inl ⟨l,hl,h⟩)

/-! ## The conversion -/

def toTerm (d : Nat) (vs : List Nat) : Raw → Term vs.length d
  | .var i => if h : vs.idxOf i < vs.length then .var ⟨vs.idxOf i,h⟩ else .bot
  | .bot => .bot
  | .top => .top
  | .node cs =>
    let ts := cs.map (toTerm d vs)
    .node (fun i => ts[i.val]?.getD .bot)

def toLit (d : Nat) (vs : List Nat) : RawLit → Literal vs.length d
  | .le a b => .le (toTerm d vs a) (toTerm d vs b)
  | .eq a b => .eq (toTerm d vs a) (toTerm d vs b)

def toQueryOn (d : Nat) (vs : List Nat) (Q : RawQuery) : Query vs.length d :=
  ⟨Q.premises.map (toLit d vs),toTerm d vs Q.left,toTerm d vs Q.right⟩

def toQuery (d : Nat) (Q : RawQuery) : Query (queryIds Q).length d :=
  toQueryOn d (queryIds Q) Q

/-! ## The raw image of a typed query -/

def rawOfTerm : Term n d → Raw
  | .var x => .var x.val
  | .bot => .bot
  | .top => .top
  | .node c => .node (List.ofFn (fun i => rawOfTerm (c i)))

def rawOfLit : Literal n d → RawLit
  | .le a b => .le (rawOfTerm a) (rawOfTerm b)
  | .eq a b => .eq (rawOfTerm a) (rawOfTerm b)

def rawOfQuery (Q : Query n d) : RawQuery :=
  ⟨Q.premises.map rawOfLit,rawOfTerm Q.left,rawOfTerm Q.right⟩

@[simp] theorem rawOfQuery_premises (Q : Query n d) :
    (rawOfQuery Q).premises = Q.premises.map rawOfLit := rfl
@[simp] theorem rawOfQuery_left (Q : Query n d) : (rawOfQuery Q).left = rawOfTerm Q.left := rfl
@[simp] theorem rawOfQuery_right (Q : Query n d) : (rawOfQuery Q).right = rawOfTerm Q.right := rfl

theorem rawOfTerm_wf (t : Term n d) : WellFormed d (rawOfTerm t) := by
  induction t with
  | var x => simp [rawOfTerm, WellFormed]
  | bot => simp [rawOfTerm, WellFormed]
  | top => simp [rawOfTerm, WellFormed]
  | node c ih =>
    simp only [rawOfTerm, WellFormed, List.length_ofFn, true_and]
    intro t ht
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
    exact ih i

theorem rawOfLit_wf (l : Literal n d) : WellFormedLit d (rawOfLit l) := by
  cases l <;> exact ⟨rawOfTerm_wf _,rawOfTerm_wf _⟩

theorem rawOfQuery_wf (Q : Query n d) : WellFormedQuery d (rawOfQuery Q) := by
  refine ⟨?_,rawOfTerm_wf _,rawOfTerm_wf _⟩
  intro l hl
  simp only [rawOfQuery, List.mem_map] at hl
  obtain ⟨m,_,rfl⟩ := hl
  exact rawOfLit_wf m

theorem termIds_lt (t : Term n d) : ∀ i ∈ termIds (rawOfTerm t), i < n := by
  induction t with
  | var x =>
    intro i hi
    simp only [rawOfTerm, termIds, List.mem_singleton] at hi
    subst hi
    exact x.isLt
  | bot => intro i hi; simp [rawOfTerm, termIds] at hi
  | top => intro i hi; simp [rawOfTerm, termIds] at hi
  | node c ih =>
    intro i hi
    simp only [rawOfTerm, termIds, List.mem_flatMap] at hi
    obtain ⟨r,hr,hi⟩ := hi
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    exact ih j i hi

theorem litIds_lt (l : Literal n d) : ∀ i ∈ litIds (rawOfLit l), i < n := by
  cases l with
  | le a b =>
    intro i hi
    simp only [rawOfLit, litIds, List.mem_append] at hi
    rcases hi with hi | hi
    · exact termIds_lt a i hi
    · exact termIds_lt b i hi
  | eq a b =>
    intro i hi
    simp only [rawOfLit, litIds, List.mem_append] at hi
    rcases hi with hi | hi
    · exact termIds_lt a i hi
    · exact termIds_lt b i hi

theorem queryIds_lt (Q : Query n d) : ∀ i ∈ queryIds (rawOfQuery Q), i < n := by
  intro i hi
  simp only [queryIds, List.mem_dedup, List.mem_append, List.mem_flatMap] at hi
  rcases hi with (⟨l,hl,hi⟩ | hi) | hi
  · simp only [rawOfQuery, List.mem_map] at hl
    obtain ⟨m,_,rfl⟩ := hl
    exact litIds_lt m i hi
  · exact termIds_lt Q.left i hi
  · exact termIds_lt Q.right i hi

/-! ## The injection back -/

def place (n : Nat) (vs : List Nat) (h : ∀ i ∈ vs, i < n) : Fin vs.length → Fin n :=
  fun i => ⟨vs[i.val],h _ (List.getElem_mem i.isLt)⟩

theorem place_injective {vs : List Nat} (h : ∀ i ∈ vs, i < n) (hnd : vs.Nodup) :
    Function.Injective (place n vs h) := by
  intro i j hij
  have hg : vs.get i = vs.get j := congrArg Fin.val hij
  exact List.nodup_iff_injective_get.mp hnd hg

theorem place_idxOf {vs : List Nat} (h : ∀ i ∈ vs, i < n) {x : Nat}
    (hx : vs.idxOf x < vs.length) : (place n vs h ⟨vs.idxOf x,hx⟩).val = x :=
  List.getElem_idxOf hx

/-! ## The conversion is an injective renaming -/

theorem rename_toTerm (vs : List Nat) (h : ∀ i ∈ vs, i < n) (t : Term n d)
    (hsub : ∀ i ∈ termIds (rawOfTerm t), i ∈ vs) :
    renameTerm (place n vs h) (toTerm d vs (rawOfTerm t)) = t := by
  induction t with
  | var x =>
    have hx : x.val ∈ vs := hsub x.val (by simp [rawOfTerm, termIds])
    have hlt : vs.idxOf x.val < vs.length := List.idxOf_lt_length_iff.mpr hx
    simp only [rawOfTerm, toTerm, dif_pos hlt, renameTerm]
    exact congrArg _ (Fin.ext (place_idxOf h hlt))
  | bot => simp [rawOfTerm, toTerm, renameTerm]
  | top => simp [rawOfTerm, toTerm, renameTerm]
  | node c ih =>
    have hmap : (List.ofFn (fun j => rawOfTerm (c j))).map (toTerm d vs)
        = List.ofFn (fun j => toTerm d vs (rawOfTerm (c j))) := by
      simp [List.map_ofFn, Function.comp_def]
    simp only [rawOfTerm, toTerm, hmap, renameTerm]
    refine congrArg _ (funext fun i => ?_)
    have hget : (List.ofFn (fun j => toTerm d vs (rawOfTerm (c j))))[i.val]?
        = some (toTerm d vs (rawOfTerm (c i))) := by
      rw [List.getElem?_eq_getElem (by simp only [List.length_ofFn]; exact i.isLt)]
      simp
    rw [hget, Option.getD_some]
    refine ih i (fun x hx => hsub x ?_)
    simp only [rawOfTerm, termIds, List.mem_flatMap]
    exact ⟨rawOfTerm (c i),List.mem_ofFn.mpr ⟨i,rfl⟩,hx⟩

theorem rename_toLit (vs : List Nat) (h : ∀ i ∈ vs, i < n) (l : Literal n d)
    (hsub : ∀ i ∈ litIds (rawOfLit l), i ∈ vs) :
    renameLiteral (place n vs h) (toLit d vs (rawOfLit l)) = l := by
  cases l with
  | le a b =>
    simp only [rawOfLit, toLit, renameLiteral]
    rw [rename_toTerm vs h a (fun x hx => hsub x (by simp [litIds, rawOfLit, hx])),
      rename_toTerm vs h b (fun x hx => hsub x (by simp [litIds, rawOfLit, hx]))]
  | eq a b =>
    simp only [rawOfLit, toLit, renameLiteral]
    rw [rename_toTerm vs h a (fun x hx => hsub x (by simp [litIds, rawOfLit, hx])),
      rename_toTerm vs h b (fun x hx => hsub x (by simp [litIds, rawOfLit, hx]))]

/-- The decoded, converted query renamed back along the injection is the
original typed query. -/
theorem rename_toQuery (Q : Query n d) :
    renameQuery (place n (queryIds (rawOfQuery Q)) (queryIds_lt Q))
      (toQuery d (rawOfQuery Q)) = Q := by
  have hl := rename_toTerm (queryIds (rawOfQuery Q)) (queryIds_lt Q) Q.left
    (fun i hi => mem_queryIds_left (rawOfQuery Q) hi)
  have hr := rename_toTerm (queryIds (rawOfQuery Q)) (queryIds_lt Q) Q.right
    (fun i hi => mem_queryIds_right (rawOfQuery Q) hi)
  have hp : Q.premises.map (fun l => renameLiteral (place n (queryIds (rawOfQuery Q))
      (queryIds_lt Q)) (toLit d (queryIds (rawOfQuery Q)) (rawOfLit l))) = Q.premises := by
    rw [List.map_congr_left (g := id) ?_, List.map_id]
    intro l hl'
    refine rename_toLit _ _ l (fun i hi => mem_queryIds_premise (rawOfQuery Q) ?_ hi)
    simp only [rawOfQuery, List.mem_map]
    exact ⟨l,hl',rfl⟩
  simp only [renameQuery, toQuery, toQueryOn, rawOfQuery_premises, rawOfQuery_left,
    rawOfQuery_right, List.map_map, Function.comp_def, hl, hr, hp]

section Semantics

open SubtypeConstraints (Constructor)

variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

/-- Converting the raw image of a query changes neither entailment nor
satisfiability, in every ordered semantics. -/
theorem entails_toQuery (F : Constructor T d) (Q : Query n d) :
    Entails F (toQuery d (rawOfQuery Q)) ↔ Entails F Q := by
  conv_rhs => rw [← rename_toQuery Q]
  exact (entails_rename F (place n (queryIds (rawOfQuery Q)) (queryIds_lt Q))
    (place_injective (queryIds_lt Q) (queryIds_nodup (rawOfQuery Q))) _).symm

theorem satisfiable_toQuery (F : Constructor T d) (Q : Query n d) :
    Satisfiable F (toQuery d (rawOfQuery Q)) ↔ Satisfiable F Q := by
  conv_rhs => rw [← rename_toQuery Q]
  exact (satisfiable_rename F (place n (queryIds (rawOfQuery Q)) (queryIds_lt Q))
    (place_injective (queryIds_lt Q) (queryIds_nodup (rawOfQuery Q))) _).symm

end Semantics

end NSSE.CodedQueryConversion
