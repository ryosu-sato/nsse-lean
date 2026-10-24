import NSSE.ListShapeSize

namespace NSSE.ListFiniteValuation
open StoredFiniteTree StoredSubtypeInput
variable {n d : Nat}

structure Valuation (n d : Nat) where
  roots : List (Tree)
  length_eq : roots.length = n
  wellFormed : ∀ t ∈ roots, WellFormed d t

def Valuation.get (v : Valuation n d) (x : Fin n) : Tree × Nat :=
  lookup v.roots ⟨x.val,by rw [v.length_eq]; exact x.isLt⟩

def Valuation.raw (v : Valuation n d) (x : Fin n) : Tree :=
  v.roots[x.val]'(by rw [v.length_eq]; exact x.isLt)

theorem get_value (v : Valuation n d) (x : Fin n) : (v.get x).1 = v.raw x := lookup_value _ _
theorem get_bound (v : Valuation n d) (x : Fin n) : (v.get x).2 ≤ n := by
  rw [Valuation.get,lookup_cost]
  exact x.isLt

def build (I : Input n d) : Valuation n d × Nat :=
  let r := CountedFinEnumeration.tabulate n (ListShapeExpansion.model I)
  (⟨r.1,by simp [r,CountedFinEnumeration.tabulate_value],by
    intro t ht
    simp only [r,CountedFinEnumeration.tabulate_value] at ht
    obtain ⟨x,rfl⟩ := List.mem_ofFn.mp ht
    exact ListShapeExpansion.model_wellFormed I x⟩,1+r.2)

theorem build_value (I : Input n d) : (build I).1.raw = fun x => (ListShapeExpansion.model I x).1 := by
  funext x
  simp [build,Valuation.raw,CountedFinEnumeration.tabulate_value]

def modelBudget (I : Input n d) :=
  3+2*StoredShapeInitial.seedBudget I+CountedModelDepth.budget n+(ListShapeExpansion.localBudget I+d+1)^(2^n*2^n+1)
def budget (I : Input n d) := 3+(n+1)^2+n*(1+modelBudget I)

theorem bound (I : Input n d) : (build I).2 ≤ budget I := by
  have h := CountedFinEnumeration.tabulate_bound n (ListShapeExpansion.model I) (modelBudget I)
    (fun x => ListShapeExpansion.model_bound I x)
  simp only [build,budget]
  omega

def children (v : Valuation n d) (a : Bound n d) : List (Tree) × Nat :=
  CountedListConstruction.map v.get a.children

theorem children_value (v : Valuation n d) (a : Bound n d) :
    (children v a).1 = a.children.map v.raw := by
  simp [children,CountedListConstruction.map_value,get_value]

theorem children_bound (v : Valuation n d) (a : Bound n d) :
    (children v a).2 ≤ 1+d*(1+n) := by
  simpa only [children,a.length_eq] using
    CountedListConstruction.map_bound v.get a.children n (fun x _ => get_bound v x)

def node (v : Valuation n d) (a : Bound n d) : Tree × Nat :=
  let c := children v a
  (.node c.1,1+c.2)

theorem node_value (v : Valuation n d) (a : Bound n d) :
    (node v a).1 = .node (a.children.map v.raw) := by simp [node,children_value]

theorem node_bound (v : Valuation n d) (a : Bound n d) : (node v a).2 ≤ 2+d*(1+n) := by
  have h := children_bound v a
  simp only [node]
  omega

def Valuation.denote (v : Valuation n d) (x : Fin n) : FiniteSubtypeTrees.Tree d := StoredFiniteTree.denote d (v.raw x)

theorem raw_wellFormed (v : Valuation n d) (x : Fin n) : WellFormed d (v.raw x) :=
  v.wellFormed _ (List.getElem_mem _)

theorem node_wellFormed (v : Valuation n d) (a : Bound n d) : WellFormed d (node v a).1 := by
  rw [node_value]
  simp only [WellFormed,List.length_map,a.length_eq]
  refine ⟨trivial,?_⟩
  intro t ht
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp ht
  exact raw_wellFormed v x

theorem node_denote (v : Valuation n d) (a : Bound n d) :
    denote d (node v a).1 = .node (fun i => v.denote (a.denote.2 i)) := by
  rw [node_value,denote]
  congr 1
  funext i
  have hi : i.val < a.children.length := by rw [a.length_eq]; exact i.isLt
  simp [List.getElem?_eq_getElem,hi,Valuation.denote,Bound.denote]

theorem build_denote (I : Input n d) : (build I).1.denote = FiniteSubtypeSmallModel.model I.denote := by
  funext x
  simp [Valuation.denote,build_value,ListShapeExpansion.model_value]
end NSSE.ListFiniteValuation
