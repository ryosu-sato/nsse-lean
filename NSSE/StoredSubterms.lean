import NSSE.StoredTermClause

namespace NSSE.StoredSubterms
open StoredSubtypeTerm
variable {n : Nat}

mutual
  def subterms : Term n → List (Term n) × Nat
    | .var x => ([.var x],1)
    | .bot => ([.bot],1)
    | .top => ([.top],1)
    | .node cs => let r := forest cs; (.node cs::r.1,1+r.2)
  termination_by t => sizeOf t
  def forest : List (Term n) → List (Term n) × Nat
    | [] => ([],1)
    | t::ts =>
      let a := subterms t
      let b := forest ts
      let c := CountedListConstruction.append a.1 b.1
      (c.1,1+a.2+b.2+c.2)
  termination_by ts => sizeOf ts
end

def forestWeight (ts : List (Term n)) := (ts.map (fun t => 1+weight t)).sum

theorem bounds (t : Term n) :
    (subterms t).1.length ≤ weight t ∧ (subterms t).2 ≤ 4*(weight t)^2 := by
  apply subterms.induct
    (motive1 := fun t => (subterms t).1.length ≤ weight t ∧ (subterms t).2 ≤ 4*(weight t)^2)
    (motive2 := fun ts => (forest ts).1.length ≤ forestWeight ts ∧ (forest ts).2 ≤ 4*(forestWeight ts)^2+1)
  · intro x
    simp only [subterms,weight,List.length_singleton]
    constructor
    · omega
    · calc
        1 ≤ 4*1^2 := by norm_num
        _ ≤ 4*(x.val+1)^2 := by gcongr; omega
  · simp [subterms,weight]
  · simp [subterms,weight]
  · intro cs ih
    simp only [subterms,weight,List.length_cons]
    change (forest cs).1.length+1 ≤ 1+forestWeight cs ∧ 1+(forest cs).2 ≤ 4*(1+forestWeight cs)^2
    constructor <;> nlinarith [ih.1,ih.2]
  · simp [forest,forestWeight]
  · intro t ts ha hb
    simp only [forest,CountedListConstruction.append_value,CountedListConstruction.append_cost,
      List.length_append,forestWeight,List.map_cons,List.sum_cons]
    change (subterms t).1.length+(forest ts).1.length ≤ 1+weight t+forestWeight ts ∧
      1+(subterms t).2+(forest ts).2+((subterms t).1.length+1) ≤ 4*(1+weight t+forestWeight ts)^2+1
    constructor <;> nlinarith [ha.1,ha.2,hb.1,hb.2]

theorem length_bound (t : Term n) : (subterms t).1.length ≤ weight t := (bounds t).1

theorem bound (t : Term n) : (subterms t).2 ≤ 4*(weight t)^2 := (bounds t).2

theorem forest_value (ts : List (Term n)) :
    (forest ts).1 = ts.flatMap (fun t => (subterms t).1) := by
  induction ts with
  | nil => simp [forest]
  | cons t ts ih => simp only [forest,CountedListConstruction.append_value,List.flatMap_cons,ih]

theorem packed_value {d : Nat} (t : SubtypeTerms.Term n d) :
    (subterms (pack t)).1 = (SubtypeTerms.subterms t).map pack := by
  induction t with
  | var x => simp [pack,subterms,SubtypeTerms.subterms]
  | bot => simp [pack,subterms,SubtypeTerms.subterms]
  | top => simp [pack,subterms,SubtypeTerms.subterms]
  | node c ih =>
    simp only [pack,subterms,forest_value,SubtypeTerms.subterms,List.map_cons]
    congr 1
    simp only [List.ofFn_eq_map,List.flatMap_map,List.map_flatMap,Function.comp_def,ih]
theorem packed_wellFormed {d : Nat} (t : SubtypeTerms.Term n d) :
    ∀ u ∈ (subterms (pack t)).1, WellFormed d u := by
  rw [packed_value]
  intro u hu
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp hu
  exact pack_wellFormed v
end NSSE.StoredSubterms
