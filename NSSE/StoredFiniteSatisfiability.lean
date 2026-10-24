import NSSE.StoredFiniteValuation

namespace NSSE.StoredFiniteSatisfiability
open StoredSubtypeInput StoredFiniteValuation FiniteSubtypeTrees
variable {n d : Nat}

def all {α : Type*} (f : α → Bool × Nat) : List α → Bool × Nat
  | [] => (true,1)
  | x::xs => let a := f x; let b := all f xs; (a.1 && b.1,1+a.2+b.2)

theorem all_value {α : Type*} (f : α → Bool × Nat) (xs : List α) :
    (all f xs).1 = xs.all (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change ((f x).1 && (all f xs).1) = _
    rw [ih]
    rfl

theorem all_bound {α : Type*} (f : α → Bool × Nat) (xs : List α) (B : Nat)
    (h : ∀ x ∈ xs, (f x).2 ≤ B) : (all f xs).2 ≤ 1+xs.length*(1+B) := by
  induction xs with
  | nil => simp [all]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [all,List.length_cons]
    nlinarith

def literal (v : Valuation n d) (reverse : Bool) (a : Bound n d) : Bool × Nat :=
  let h := v.get a.head
  let c := node v a
  let r := if reverse then CountedFiniteTreeComparison.compare c.1 h.1 else CountedFiniteTreeComparison.compare h.1 c.1
  (r.1,1+h.2+c.2+r.2)

def endpoint (v : Valuation n d) (top : Bool) (x : Fin n) : Bool × Nat :=
  let h := v.get x
  let r := if top then CountedFiniteTreeComparison.compare .top h.1 else CountedFiniteTreeComparison.compare h.1 .bot
  (r.1,1+h.2+r.2)

def check (I : Input n d) (v : Valuation n d) : Bool × Nat :=
  let u := all (literal v false) I.upper
  let l := all (literal v true) I.lower
  let b := all (endpoint v false) I.bot
  let t := all (endpoint v true) I.top
  (u.1 && l.1 && b.1 && t.1,3+u.2+l.2+b.2+t.2)

theorem check_value (I : Input n d) (v : Valuation n d) :
    (check I v).1 = FiniteSubtypeDecision.checkSolution I.denote v.denote := by
  simp [check,all_value,literal,endpoint,get_value,node_value,CountedFiniteTreeComparison.value,
    FiniteSubtypeDecision.checkSolution,Input.denote,List.all_map,Function.comp_def,Bound.denote]

def comparisonBudget (n d : Nat) := (2*d+3)^(2^n*2^n+1)
def literalBudget (n d : Nat) := 3+n+d*(1+n)+comparisonBudget n d

theorem literal_bound (I : Input n d) (v : Valuation n d)
    (hv : v.denote = FiniteSubtypeSmallModel.model I.denote) (reverse : Bool) (a : Bound n d) :
    (literal v reverse a).2 ≤ literalBudget n d := by
  have hh := get_bound v a.head
  have hc := node_bound v a
  have hq := CountedFiniteTreeComparison.model_bound I.denote a.head (node v a).1
  simp only [literal,get_value,hv,literalBudget,comparisonBudget]
  cases reverse <;> simp only [Bool.false_eq_true,↓reduceIte]
  · omega
  · rw [CountedFiniteTreeComparison.cost_symm]; omega

theorem endpoint_bound (I : Input n d) (v : Valuation n d)
    (hv : v.denote = FiniteSubtypeSmallModel.model I.denote) (top : Bool) (x : Fin n) :
    (endpoint v top x).2 ≤ literalBudget n d := by
  have hh := get_bound v x
  have hb := CountedFiniteTreeComparison.model_bound I.denote x (.bot : Tree d)
  have ht := CountedFiniteTreeComparison.model_bound I.denote x (.top : Tree d)
  simp only [endpoint,get_value,hv,literalBudget,comparisonBudget]
  cases top <;> simp only [Bool.false_eq_true,↓reduceIte]
  · omega
  · rw [CountedFiniteTreeComparison.cost_symm]; omega

def checkBudget (I : Input n d) :=
  7+(I.upper.length+I.lower.length+I.bot.length+I.top.length)*(1+literalBudget n d)

theorem check_bound (I : Input n d) (v : Valuation n d)
    (hv : v.denote = FiniteSubtypeSmallModel.model I.denote) : (check I v).2 ≤ checkBudget I := by
  have hu := all_bound (literal v false) I.upper (literalBudget n d) (fun a _ => literal_bound I v hv false a)
  have hl := all_bound (literal v true) I.lower (literalBudget n d) (fun a _ => literal_bound I v hv true a)
  have hb := all_bound (endpoint v false) I.bot (literalBudget n d) (fun x _ => endpoint_bound I v hv false x)
  have ht := all_bound (endpoint v true) I.top (literalBudget n d) (fun x _ => endpoint_bound I v hv true x)
  simp only [check,checkBudget]
  nlinarith

def decide (I : Input n d) : Bool × Nat :=
  let v := build I
  let r := check I v.1
  (r.1,1+v.2+r.2)

theorem value (I : Input n d) : (decide I).1 = FiniteSubtypeDecision.decideSatisfiable I.denote := by
  simp only [decide,check_value,build_value]
  rfl

theorem correct (I : Input n d) :
    (decide I).1 = true ↔ SubtypeConstraints.Satisfiable (constructor d) I.denote := by
  rw [value,FiniteSubtypeDecision.decideSatisfiable_correct]

theorem bound (I : Input n d) :
    (decide I).2 ≤ 1+StoredFiniteValuation.budget I+checkBudget I := by
  have hv := StoredFiniteValuation.bound I
  have hc := check_bound I (build I).1 (build_value I)
  simp only [decide]
  omega
end NSSE.StoredFiniteSatisfiability
