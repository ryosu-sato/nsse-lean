import NSSE.StoredEdgeClause
import NSSE.StoredTermDefinitions

/-! Counted edge emission from stored layout terms and inequality pairs.
The stored pair count p and its erased length certificate are inputs;
layout construction is a separate stage. -/
namespace NSSE.StoredEdgeEmission
open StoredSubtypeTerm
variable {n d p : Nat}

def atIndex (ts : List (Term n)) (ps : List (Term n × Term n)) (hp : ps.length=p)
    (i : Fin d) (j : Fin p) : StoredSubtypeInput.Input (n+(ts.length+(p+1))) d × Nat :=
  let a := StoredSubtypeInput.lookup ps ⟨j.val,by rw [hp]; exact j.isLt⟩
  let r := StoredEdgeClause.clause ts p i j a.1.1 a.1.2
  (r.1,1+a.2+r.2)

theorem atIndex_bound (ts : List (Term n)) (ps : List (Term n × Term n)) (hp : ps.length=p)
    (i : Fin d) (j : Fin p) (W : Nat) (hw : ∀ a ∈ ps, weight a.1 ≤ W ∧ weight a.2 ≤ W) :
    (atIndex ts ps hp i j).2 ≤ 1+p+StoredEdgeClause.budget n ts.length d W := by
  have hm := List.getElem_mem (by rw [hp]; exact j.isLt : j.val < ps.length)
  have h := hw _ hm
  have hc := StoredEdgeClause.bound ts p i j ps[j.val].1 ps[j.val].2 W h.1 h.2
  simp only [atIndex,StoredSubtypeInput.lookup_value,StoredSubtypeInput.lookup_cost]
  have hj := j.isLt
  omega

theorem atIndex_lengths (ts : List (Term n)) (ps : List (Term n × Term n)) (hp : ps.length=p)
    (i : Fin d) (j : Fin p) :
    let I := (atIndex ts ps hp i j).1
    I.upper.length+I.lower.length+I.bot.length+I.top.length = 2 := rfl

def collect (ts : List (Term n)) (ps : List (Term n × Term n)) (hp : ps.length=p)
    (i : Fin d) : List (Fin p) → StoredSubtypeInput.Input (n+(ts.length+(p+1))) d × Nat
  | [] => (⟨[],[],[],[]⟩,1)
  | j::js =>
    let a := atIndex ts ps hp i j
    let b := collect ts ps hp i js
    let c := StoredTermDefinitions.combine a.1 b.1
    (c.1,1+a.2+b.2+c.2)

theorem collect_bound (ts : List (Term n)) (ps : List (Term n × Term n)) (hp : ps.length=p)
    (i : Fin d) (js : List (Fin p)) (W : Nat) (hw : ∀ a ∈ ps, weight a.1 ≤ W ∧ weight a.2 ≤ W) :
    (collect ts ps hp i js).2 ≤ 1+js.length*(9+p+StoredEdgeClause.budget n ts.length d W) := by
  induction js with
  | nil => simp [collect]
  | cons j js ih =>
    have ha := atIndex_bound ts ps hp i j W hw
    have hl := atIndex_lengths ts ps hp i j
    simp only [collect,StoredTermDefinitions.combine_cost,List.length_cons]
    dsimp only at hl
    nlinarith

def edges (ts : List (Term n)) (ps : List (Term n × Term n)) (hp : ps.length=p)
    (i : Fin d) : StoredSubtypeInput.Input (n+(ts.length+(p+1))) d × Nat :=
  let js := CountedFinEnumeration.enumerate p
  let r := collect ts ps hp i js.1
  (r.1,1+js.2+r.2)

def budget (n m p d W : Nat) :=
  2+(p+1)^2+p*(9+p+StoredEdgeClause.budget n m d W)

theorem bound (ts : List (Term n)) (ps : List (Term n × Term n)) (hp : ps.length=p)
    (i : Fin d) (W : Nat) (hw : ∀ a ∈ ps, weight a.1 ≤ W ∧ weight a.2 ≤ W) :
    (edges ts ps hp i).2 ≤ budget n ts.length p d W := by
  have he := CountedFinEnumeration.bound p
  have hc := collect_bound ts ps hp i (CountedFinEnumeration.enumerate p).1 W hw
  rw [CountedFinEnumeration.value,List.length_finRange] at hc
  simp only [edges,budget,CountedFinEnumeration.value]; omega

theorem emitted (ts : List (Term n)) (ps : List (Term n × Term n)) (hp : ps.length=p)
    (i : Fin d) (js : List (Fin p)) :
    let I := (collect ts ps hp i js).1
    I.upper.length+I.lower.length+I.bot.length+I.top.length = 2*js.length := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    have ha := atIndex_lengths ts ps hp i j
    simp only [collect,StoredTermDefinitions.combine,CountedListConstruction.append_value,
      List.length_append,List.length_cons]
    dsimp only at ha ih
    omega

def packPairs (ps : List (SubtypeTerms.Term n d × SubtypeTerms.Term n d)) :=
  ps.map (fun a => (pack a.1,pack a.2))

theorem atIndex_value (L : SubtypeTermLayout.Layout n d) (i : Fin d) (j : Fin L.pairs.length) :
    StoredTermClause.transport (by simp [SubtypeTermLayout.Layout.count])
      (atIndex (L.terms.map pack) (packPairs L.pairs) (by simp [packPairs]) i j).1 =
      SubtypeTermFlattening.edgeClause L i j := by
  simp only [atIndex,StoredSubtypeInput.lookup_value,packPairs,List.getElem_map]
  exact StoredEdgeClause.packed_value L i j

theorem collect_value (L : SubtypeTermLayout.Layout n d) (i : Fin d) (js : List (Fin L.pairs.length)) :
    StoredTermClause.transport (by simp [SubtypeTermLayout.Layout.count])
      (collect (L.terms.map pack) (packPairs L.pairs) (by simp [packPairs]) i js).1 =
      SubtypeTermDefinitions.join (js.map (SubtypeTermFlattening.edgeClause L i)) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    simp only [collect,StoredTermDefinitions.combine_value,atIndex_value,List.map_cons,
      SubtypeTermDefinitions.join,List.foldr_cons]
    exact congrArg (SubtypeConstraintOperations.combine (SubtypeTermFlattening.edgeClause L i j)) ih

theorem value (L : SubtypeTermLayout.Layout n d) (i : Fin d) :
    StoredTermClause.transport (by simp [SubtypeTermLayout.Layout.count])
      (edges (p := L.pairs.length) (L.terms.map pack) (packPairs L.pairs) (by simp [packPairs]) i).1 =
      SubtypeTermFlattening.edges L i := by
  simp only [edges,CountedFinEnumeration.value,collect_value,SubtypeTermFlattening.edges]
end NSSE.StoredEdgeEmission
