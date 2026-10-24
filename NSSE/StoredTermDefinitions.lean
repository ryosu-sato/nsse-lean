import NSSE.StoredTermClause

namespace NSSE.StoredTermDefinitions
open StoredSubtypeTerm
variable {n d : Nat}

def combine {m : Nat} (I J : StoredSubtypeInput.Input m d) :
    StoredSubtypeInput.Input m d × Nat :=
  let u := CountedListConstruction.append I.upper J.upper
  let l := CountedListConstruction.append I.lower J.lower
  let b := CountedListConstruction.append I.bot J.bot
  let t := CountedListConstruction.append I.top J.top
  (⟨u.1,l.1,b.1,t.1⟩,1+u.2+l.2+b.2+t.2)

theorem combine_cost {m : Nat} (I J : StoredSubtypeInput.Input m d) :
    (combine I J).2 = 5+I.upper.length+I.lower.length+I.bot.length+I.top.length := by
  simp only [combine,CountedListConstruction.append_cost]; omega

theorem combine_value {a b : Nat} (h : a=b) (I J : StoredSubtypeInput.Input a d) :
    StoredTermClause.transport h (combine I J).1 =
      SubtypeConstraintOperations.combine (StoredTermClause.transport h I) (StoredTermClause.transport h J) := by
  simp only [combine,CountedListConstruction.append_value,StoredTermClause.transport,
    List.map_append,SubtypeConstraintOperations.combine]

theorem clause_lengths (ts : List (Term n)) (pairs : Nat) (t : Term n) (h : WellFormed d t) :
    let I := (StoredTermClause.clause ts pairs t h).1
    I.upper.length+I.lower.length+I.bot.length+I.top.length ≤ 2 := by
  cases t <;> simp [StoredTermClause.clause]

def collect (ts : List (Term n)) (pairs : Nat) :
    (xs : List (Term n)) → (∀ t ∈ xs, WellFormed d t) →
      StoredSubtypeInput.Input (n+(ts.length+(pairs+1))) d × Nat
  | [], _ => (⟨[],[],[],[]⟩,1)
  | t::xs,h =>
    let a := StoredTermClause.clause ts pairs t (h t (by simp))
    let b := collect ts pairs xs (fun u hu => h u (by simp [hu]))
    let c := combine a.1 b.1
    (c.1,1+a.2+b.2+c.2)

theorem bound (ts : List (Term n)) (pairs : Nat) (xs : List (Term n))
    (h : ∀ t ∈ xs, WellFormed d t) (W : Nat) (hw : ∀ t ∈ xs, weight t ≤ W) :
    (collect ts pairs xs h).2 ≤ 1+xs.length*(8+StoredTermClause.budget n ts.length d W) := by
  induction xs with
  | nil => simp [collect]
  | cons t xs ih =>
    have ha := StoredTermClause.bound ts pairs t (h t (by simp)) W (hw t (by simp))
    have hl := clause_lengths ts pairs t (h t (by simp))
    have hb := ih (fun u hu => h u (by simp [hu])) (fun u hu => hw u (by simp [hu]))
    simp only [collect,combine_cost,List.length_cons]
    dsimp only at hl
    nlinarith

theorem emitted_bound (ts : List (Term n)) (pairs : Nat) (xs : List (Term n))
    (h : ∀ t ∈ xs, WellFormed d t) :
    let I := (collect ts pairs xs h).1
    I.upper.length+I.lower.length+I.bot.length+I.top.length ≤ 2*xs.length := by
  induction xs with
  | nil => simp [collect]
  | cons t xs ih =>
    have ha := clause_lengths ts pairs t (h t (by simp))
    have hb := ih (fun u hu => h u (by simp [hu]))
    simp only [collect,combine,CountedListConstruction.append_value,List.length_append,List.length_cons]
    dsimp only at ha hb
    omega

theorem packed_value (L : SubtypeTermLayout.Layout n d) (xs : List (SubtypeTerms.Term n d)) :
    StoredTermClause.transport (by simp [SubtypeTermLayout.Layout.count])
      (collect (L.terms.map pack) L.pairs.length (xs.map pack)
        (by intro t ht; obtain ⟨u,_,rfl⟩ := List.mem_map.mp ht; exact pack_wellFormed u)).1 =
      SubtypeTermDefinitions.join (xs.map (SubtypeTermDefinitions.termClause L)) := by
  induction xs with
  | nil => rfl
  | cons t xs ih =>
    simp only [List.map_cons,collect,combine_value,StoredTermClause.packed_value,
      SubtypeTermDefinitions.join,List.foldr_cons]
    exact congrArg (SubtypeConstraintOperations.combine (SubtypeTermDefinitions.termClause L t)) ih

theorem definitions_value (L : SubtypeTermLayout.Layout n d) :
    StoredTermClause.transport (by simp [SubtypeTermLayout.Layout.count])
      (collect (L.terms.map pack) L.pairs.length (L.terms.map pack)
        (by intro t ht; obtain ⟨u,_,rfl⟩ := List.mem_map.mp ht; exact pack_wellFormed u)).1 =
      SubtypeTermDefinitions.definitions L := packed_value L L.terms
end NSSE.StoredTermDefinitions
