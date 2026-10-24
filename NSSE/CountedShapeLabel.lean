import NSSE.CountedRegularSatisfiability

/-! List-represented grammar states and counted label tests. Membership uses
unary equality, not an opaque set membership oracle. -/
namespace NSSE.CountedShapeLabel
open SubtypeConstraints SubtypeShapeGrammar FiniteTreeGrammar
open CountedRegularSatisfiability FiniteValuationLookup
variable {n d : Nat}

def member (x : Fin n) (xs : List (Fin n)) : Bool × Nat :=
  any (xs.map (fun y => equalNat x.val y.val))

theorem member_correct (x : Fin n) (xs : List (Fin n)) :
    (member x xs).1 = true ↔ x ∈ xs := by
  simp only [member, any, List.any_map, Function.comp_def, List.any_eq_true, equalNat_correct]
  constructor
  · rintro ⟨y,hy,he⟩
    have hxy : x=y := Fin.ext he
    simpa only [hxy] using hy
  · intro hx; exact ⟨x,hx,rfl⟩

theorem member_bound (x : Fin n) (xs : List (Fin n)) :
    (member x xs).2 ≤ 1+xs.length*(1+n) :=
  any_bound xs (fun y => equalNat x.val y.val) n (fun y _ => equalFin_bound x y)

def hits {α : Type*} (xs : List α) (key : α → Fin n) (ys : List (Fin n)) : Bool × Nat :=
  any (xs.map (fun x => member (key x) ys))

theorem hits_correct {α : Type*} (xs : List α) (key : α → Fin n) (ys : List (Fin n)) :
    (hits xs key ys).1 = true ↔ ∃ x ∈ xs, key x ∈ ys := by
  simp only [hits, any, List.any_map, Function.comp_def, List.any_eq_true, member_correct]

theorem hits_value {α : Type*} (xs : List α) (key : α → Fin n) (ys : List (Fin n)) :
    (hits xs key ys).1 = Decidable.decide (∃ x ∈ xs, key x ∈ ys) := by
  apply Bool.eq_iff_iff.mpr
  simp only [hits_correct, decide_eq_true_eq]

theorem hits_bound {α : Type*} (xs : List α) (key : α → Fin n) (ys : List (Fin n)) :
    (hits xs key ys).2 ≤ 1+xs.length*(2+ys.length*(1+n)) := by
  have h := any_bound xs (fun x => member (key x) ys) (1+ys.length*(1+n))
    (fun x _ => member_bound (key x) ys)
  simpa only [hits, ← Nat.add_assoc] using h

def label (φ : Constraints n d) (L U : List (Fin n)) : Label × Nat :=
  let l := hits φ.lower Prod.fst L
  let u := hits φ.upper Prod.fst U
  let b := hits φ.bot id U
  ((if l.1 then (if u.1 then .node else .top)
    else (if u.1 || b.1 then .bot else .top)),3+l.2+u.2+b.2)

theorem value (φ : Constraints n d) (L U : List (Fin n)) :
    (label φ L U).1 = (grammar φ).label (L.toFinset,U.toFinset) := by
  simp only [label, hits_value, grammar, LowF, HighF, HighBot, List.mem_toFinset,
    id_eq, Bool.or_eq_true, decide_eq_true_eq]

theorem bound (φ : Constraints n d) (L U : List (Fin n))
    (hL : L.length ≤ n) (hU : U.length ≤ n) :
    (label φ L U).2 ≤ 6+(φ.lower.length+φ.upper.length+φ.bot.length)*(2+n*(1+n)) := by
  have hl := hits_bound φ.lower Prod.fst L
  have hu := hits_bound φ.upper Prod.fst U
  have hb := hits_bound φ.bot id U
  have hmL := Nat.mul_le_mul_right (1+n) hL
  have hmU := Nat.mul_le_mul_right (1+n) hU
  have hl' := hl.trans (show 1+φ.lower.length*(2+L.length*(1+n)) ≤
    1+φ.lower.length*(2+n*(1+n)) by gcongr)
  have hu' := hu.trans (show 1+φ.upper.length*(2+U.length*(1+n)) ≤
    1+φ.upper.length*(2+n*(1+n)) by gcongr)
  have hb' := hb.trans (show 1+φ.bot.length*(2+U.length*(1+n)) ≤
    1+φ.bot.length*(2+n*(1+n)) by gcongr)
  simp only [label]
  nlinarith
end NSSE.CountedShapeLabel
