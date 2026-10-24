import NSSE.StoredShapeExpansion

namespace NSSE.StoredFiniteValuation
open FiniteSubtypeTrees StoredSubtypeInput
variable {n d : Nat}

structure Valuation (n d : Nat) where
  roots : List (Tree d)
  length_eq : roots.length = n

def Valuation.get (v : Valuation n d) (x : Fin n) : Tree d × Nat :=
  lookup v.roots ⟨x.val,by rw [v.length_eq]; exact x.isLt⟩

def Valuation.denote (v : Valuation n d) (x : Fin n) : Tree d :=
  v.roots[x.val]'(by rw [v.length_eq]; exact x.isLt)

theorem get_value (v : Valuation n d) (x : Fin n) : (v.get x).1 = v.denote x := lookup_value _ _
theorem get_bound (v : Valuation n d) (x : Fin n) : (v.get x).2 ≤ n := by
  rw [Valuation.get,lookup_cost]
  exact x.isLt

def build (I : Input n d) : Valuation n d × Nat :=
  let r := CountedFinEnumeration.tabulate n (StoredShapeExpansion.model I)
  (⟨r.1,by simp [r,CountedFinEnumeration.tabulate_value]⟩,1+r.2)

theorem build_value (I : Input n d) : (build I).1.denote = FiniteSubtypeSmallModel.model I.denote := by
  funext x
  simp [build,Valuation.denote,CountedFinEnumeration.tabulate_value,StoredShapeExpansion.model_value]

def modelBudget (I : Input n d) :=
  2+2*StoredShapeInitial.seedBudget I+(StoredShapeExpansion.localBudget I+d+1)^(2^n*2^n+1)
def budget (I : Input n d) := 3+(n+1)^2+n*(1+modelBudget I)

theorem bound (I : Input n d) : (build I).2 ≤ budget I := by
  have h := CountedFinEnumeration.tabulate_bound n (StoredShapeExpansion.model I) (modelBudget I)
    (fun x => StoredShapeExpansion.model_bound I x)
  simp only [build,budget]
  omega

def children (v : Valuation n d) (a : Bound n d) : List (Tree d) × Nat :=
  CountedListConstruction.map v.get a.children

theorem children_value (v : Valuation n d) (a : Bound n d) :
    (children v a).1 = a.children.map v.denote := by
  simp [children,CountedListConstruction.map_value,get_value]

theorem children_bound (v : Valuation n d) (a : Bound n d) :
    (children v a).2 ≤ 1+d*(1+n) := by
  simpa only [children,a.length_eq] using
    CountedListConstruction.map_bound v.get a.children n (fun x _ => get_bound v x)

def node (v : Valuation n d) (a : Bound n d) : Tree d × Nat :=
  let c := children v a
  (.node (fun i => c.1[i.val]'(by rw [children_value,List.length_map,a.length_eq]; exact i.isLt)),1+c.2)

theorem node_value (v : Valuation n d) (a : Bound n d) :
    (node v a).1 = .node (fun i => v.denote (a.denote.2 i)) := by
  simp only [node,children_value]
  congr 1
  funext i
  simp [Bound.denote]

theorem node_bound (v : Valuation n d) (a : Bound n d) : (node v a).2 ≤ 2+d*(1+n) := by
  have h := children_bound v a
  simp only [node]
  omega
end NSSE.StoredFiniteValuation
