import NSSE.StoredUniversalCoreGraph

namespace NSSE.StoredGraphHorn
open StoredProductivityGraph StoredForwardLookup CountedListConstruction

def range (n : Nat) : List Nat × Nat :=
  let e := CountedFinEnumeration.enumerate n
  let r := map (fun q => (q.val,1)) e.1
  (r.1,1+e.2+r.2)

theorem range_value (n : Nat) : (range n).1 = List.range n := by
  simp only [range,map_value,CountedFinEnumeration.value,List.map_coe_finRange]

theorem range_bound (n : Nat) : (range n).2 ≤ 2+(n+1)^2+2*n := by
  have he := CountedFinEnumeration.bound n
  have hr := map_bound (fun q : Fin n => (q.val,1)) (CountedFinEnumeration.enumerate n).1 1 (fun _ _ => le_rfl)
  rw [CountedFinEnumeration.value,List.length_finRange] at hr
  simp only [range,CountedFinEnumeration.value]; omega

def emit (G : Data) (q r : Nat) : List HornRule × Nat :=
  let e := two G.edge q r
  if e.1 then ([⟨q,[r]⟩],3+e.2) else ([],1+e.2)

def game (G : Data) : FiniteReachabilityGame :=
  ⟨G.count,fun q => (get false G.accepting q).1,fun _ => true,
    fun q r => (two G.edge q r).1⟩

def build (G : Data) : MaterializedHornProgram.Program × Nat :=
  let qs := range G.count
  let rs := flatMap (fun q => flatMap (emit G q) qs.1) qs.1
  let fs := CountedFinEnumeration.tabulate G.count (fun q => get false G.accepting q.val)
  (⟨G.count,fs.1,rs.1⟩,1+qs.2+rs.2+fs.2)

theorem emit_bound (G : Data) (q r : Nat) (hq : q<G.count) (hr : r<G.count) :
    (emit G q r).2 ≤ 2*G.count+4 := by
  have he := two_bound G.edge q r
  simp only [emit]; split <;> omega

theorem emit_length (G : Data) (q r : Nat) : (emit G q r).1.length ≤ 1 := by
  simp only [emit]; split <;> simp

def budget (n : Nat) := 1+(2+(n+1)^2+2*n)+
  (1+n*(2+(1+n*(2+(2*n+4)+1))+n))+StoredForwardTableBuild.tabBudget n n

theorem bound (G : Data) : (build G).2 ≤ budget G.count := by
  have hq := range_bound G.count
  have hi (q : Nat) (hq : q ∈ (range G.count).1) := flatMap_bound (emit G q) (range G.count).1
    (2*G.count+4) 1
    (fun r hr => emit_bound G q r (by simpa only [range_value,List.mem_range] using hq)
      (by simpa only [range_value,List.mem_range] using hr)) (fun r _ => emit_length G q r)
  have hl (q : Nat) : (flatMap (emit G q) (range G.count).1).1.length ≤ G.count := by
    rw [flatMap_value,List.length_flatMap]
    calc
      _ ≤ ((range G.count).1.map (fun _ => 1)).sum := List.sum_le_sum (by
        intro x hx; exact emit_length G q x)
      _ = G.count := by simp [range_value]
  have ho := flatMap_bound (fun q => flatMap (emit G q) (range G.count).1) (range G.count).1
    (1+G.count*(2+(2*G.count+4)+1)) G.count
    (fun q h => by simpa only [range_value,List.length_range] using hi q h) (fun q _ => hl q)
  have hf := CountedFinEnumeration.tabulate_bound G.count (fun q => get false G.accepting q.val) G.count
    (fun q => (get_bound false G.accepting q.val).trans q.isLt)
  rw [range_value,List.length_range] at ho
  simp only [build,budget,range_value]
  dsimp only [StoredForwardTableBuild.tabBudget] at *
  omega

theorem emit_rows (G : Data) (q : Nat) (rs : List Nat) :
    rs.flatMap (fun r => (emit G q r).1) =
      (rs.filter (fun r => (game G).edge q r)).map (fun r => (⟨q,[r]⟩ : HornRule)) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.flatMap_cons,ih]
    simp only [emit,game,List.filter_cons]
    split <;> simp_all only [List.singleton_append,List.nil_append,List.map_cons]

theorem value (G : Data) : (build G).1 = MaterializedHornProgram.materialize (game G).compiler := by
  simp only [build,flatMap_value,range_value,emit_rows,CountedFinEnumeration.tabulate_value,
    MaterializedHornProgram.materialize,FiniteReachabilityGame.compiler,FiniteReachabilityGame.rules,
    FiniteReachabilityGame.rulesFor,FiniteReachabilityGame.successors,game,↓reduceIte,
    ExplicitUnaryTableLanguage.tabulate]
  rfl
theorem terminals_length (G : Data) : (build G).1.terminals.length = G.count := by
  simp only [build,CountedFinEnumeration.tabulate_value,List.length_ofFn]

theorem rules_bound (G : Data) : (build G).1.rules.length ≤ G.count*G.count := by
  simp only [build,flatMap_value,range_value,emit_rows,List.length_flatMap,List.length_map]
  calc
    _ ≤ ((List.range G.count).map (fun _ => G.count)).sum := List.sum_le_sum (by
      intro q hq
      exact (List.length_filter_le _ _).trans_eq List.length_range)
    _ = G.count*G.count := by simp

theorem children_length (G : Data) (r : HornRule) (h : r ∈ (build G).1.rules) :
    r.children.length ≤ 1 := by
  simp only [build,flatMap_value,range_value,emit_rows,List.mem_flatMap,List.mem_map] at h
  obtain ⟨q,hq,t,ht,hr⟩ := h
  subst r
  exact le_rfl
end NSSE.StoredGraphHorn
