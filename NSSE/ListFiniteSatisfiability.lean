import NSSE.ListFiniteValuation

namespace NSSE.ListFiniteSatisfiability
open StoredSubtypeInput ListFiniteValuation StoredFiniteTree
open StoredFiniteSatisfiability (all all_value all_bound)
variable {n d : Nat}

theorem compare_value (a b : Tree) (ha : WellFormed d a) (hb : WellFormed d b) :
    (compare a b).1 = FiniteSubtypeDecision.leBool (denote d a) (denote d b) := by
  apply Bool.eq_iff_iff.mpr
  rw [StoredFiniteTree.correct a b ha hb,FiniteSubtypeDecision.leBool_correct]

def literal (v : Valuation n d) (reverse : Bool) (a : Bound n d) : Bool × Nat :=
  let h := v.get a.head
  let c := node v a
  let r := if reverse then compare c.1 h.1 else compare h.1 c.1
  (r.1,1+h.2+c.2+r.2)

def endpoint (v : Valuation n d) (top : Bool) (x : Fin n) : Bool × Nat :=
  let h := v.get x
  let r := if top then compare .top h.1 else compare h.1 .bot
  (r.1,1+h.2+r.2)

theorem literal_value (v : Valuation n d) (reverse : Bool) (a : Bound n d) :
    (literal v reverse a).1 = if reverse then
      FiniteSubtypeDecision.leBool (.node (fun i => v.denote (a.denote.2 i))) (v.denote a.head)
      else FiniteSubtypeDecision.leBool (v.denote a.head) (.node (fun i => v.denote (a.denote.2 i))) := by
  cases reverse <;> simp only [literal,get_value,Bool.false_eq_true,↓reduceIte]
  · rw [compare_value _ _ (raw_wellFormed v a.head) (node_wellFormed v a),node_denote]
    rfl
  · rw [compare_value _ _ (node_wellFormed v a) (raw_wellFormed v a.head),node_denote]
    rfl

theorem endpoint_value (v : Valuation n d) (top : Bool) (x : Fin n) :
    (endpoint v top x).1 = if top then FiniteSubtypeDecision.leBool .top (v.denote x)
      else FiniteSubtypeDecision.leBool (v.denote x) .bot := by
  cases top <;> simp only [endpoint,get_value,Bool.false_eq_true,↓reduceIte]
  · rw [compare_value _ _ (raw_wellFormed v x) (by simp [WellFormed])]
    simp only [denote]; rfl
  · rw [compare_value _ _ (by simp [WellFormed]) (raw_wellFormed v x)]
    simp only [denote]; rfl

def check (I : Input n d) (v : Valuation n d) : Bool × Nat :=
  let u := all (literal v false) I.upper
  let l := all (literal v true) I.lower
  let b := all (endpoint v false) I.bot
  let t := all (endpoint v true) I.top
  (u.1 && l.1 && b.1 && t.1,3+u.2+l.2+b.2+t.2)

theorem check_value (I : Input n d) (v : Valuation n d) :
    (check I v).1 = FiniteSubtypeDecision.checkSolution I.denote v.denote := by
  simp [check,all_value,literal_value,endpoint_value,FiniteSubtypeDecision.checkSolution,
    Input.denote,List.all_map,Function.comp_def,Bound.denote]

theorem node_weight (v : Valuation n d) (W : Nat) (hw : ∀ x, weight (v.raw x) ≤ W) (a : Bound n d) :
    weight (node v a).1 ≤ 1+d*(1+W) := by
  have h := CountedFiniteTreeComparison.sum_bound a.children (fun x => 1+weight (v.raw x)) (1+W)
    (fun x _ => Nat.add_le_add_left (hw x) 1)
  rw [a.length_eq] at h
  simpa only [node_value,weight,List.map_map,Function.comp_def] using Nat.add_le_add_left h 1

def literalBudget (n d W : Nat) := 3+n+d*(1+n)+2*(1+d*(1+W)+W)

theorem literal_bound (v : Valuation n d) (W : Nat) (hw : ∀ x, weight (v.raw x) ≤ W)
    (reverse : Bool) (a : Bound n d) : (literal v reverse a).2 ≤ literalBudget n d W := by
  have hh := get_bound v a.head
  have hc := node_bound v a
  have hwc := node_weight v W hw a
  have hwh := hw a.head
  have hq := StoredFiniteTree.bound (v.raw a.head) (node v a).1
  have hr := StoredFiniteTree.bound (node v a).1 (v.raw a.head)
  simp only [literal,get_value,literalBudget]
  cases reverse <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega

theorem endpoint_bound (v : Valuation n d) (W : Nat) (hw : ∀ x, weight (v.raw x) ≤ W)
    (top : Bool) (x : Fin n) : (endpoint v top x).2 ≤ literalBudget n d W := by
  have hh := get_bound v x
  have hwh := hw x
  have hb := StoredFiniteTree.bound (v.raw x) .bot
  have ht := StoredFiniteTree.bound .top (v.raw x)
  simp only [weight] at ht
  simp only [endpoint,get_value,literalBudget]
  cases top <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega

def checkBudget (I : Input n d) (W : Nat) :=
  7+(I.upper.length+I.lower.length+I.bot.length+I.top.length)*(1+literalBudget n d W)

theorem check_bound (I : Input n d) (v : Valuation n d) (W : Nat) (hw : ∀ x, weight (v.raw x) ≤ W) :
    (check I v).2 ≤ checkBudget I W := by
  have hu := all_bound (literal v false) I.upper (literalBudget n d W) (fun a _ => literal_bound v W hw false a)
  have hl := all_bound (literal v true) I.lower (literalBudget n d W) (fun a _ => literal_bound v W hw true a)
  have hb := all_bound (endpoint v false) I.bot (literalBudget n d W) (fun x _ => endpoint_bound v W hw false x)
  have ht := all_bound (endpoint v true) I.top (literalBudget n d W) (fun x _ => endpoint_bound v W hw true x)
  simp only [check,checkBudget]
  nlinarith

def decide (I : Input n d) : Bool × Nat :=
  let v := build I
  let r := check I v.1
  (r.1,1+v.2+r.2)

theorem value (I : Input n d) : (decide I).1 = FiniteSubtypeDecision.decideSatisfiable I.denote := by
  simp only [decide,check_value,build_denote]
  rfl

theorem correct (I : Input n d) :
    (decide I).1 = true ↔ SubtypeConstraints.Satisfiable (FiniteSubtypeTrees.constructor d) I.denote := by
  rw [value,FiniteSubtypeDecision.decideSatisfiable_correct]

theorem bound (I : Input n d) :
    (decide I).2 ≤ 1+ListFiniteValuation.budget I+checkBudget I (ListShapeSize.modelBudget n d) := by
  have hv := ListFiniteValuation.bound I
  have hw (x : Fin n) : weight ((build I).1.raw x) ≤ ListShapeSize.modelBudget n d := by
    rw [build_value]
    exact ListShapeSize.model_bound I x
  have hc := check_bound I (build I).1 _ hw
  simp only [decide]
  omega
end NSSE.ListFiniteSatisfiability
