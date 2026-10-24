import NSSE.StoredShapeTransition

namespace NSSE.StoredShapeInitial
open StoredSubtypeInput CountedShapeInitial
variable {n d : Nat}

def seed (I : Input n d) (reverse : Bool) (x : Fin n) : List (Fin n) × Nat :=
  let ns := CountedFinEnumeration.enumerate n
  let r := select (fun z => StoredShapeTransition.relation I reverse z x) ns.1
  (r.1,1+ns.2+r.2)

theorem seed_value (I : Input n d) (reverse : Bool) (x : Fin n) :
    (seed I reverse x).1.toFinset =
      if reverse then SubtypeShapeGrammar.up I.denote x else SubtypeShapeGrammar.down I.denote x := by
  cases reverse <;>
    simp [seed,CountedFinEnumeration.value,select_value,StoredShapeTransition.relation,
      StoredSupportQuery.correct,SubtypeShapeGrammar.up,SubtypeShapeGrammar.down]

theorem seed_length (I : Input n d) (reverse : Bool) (x : Fin n) : (seed I reverse x).1.length ≤ n := by
  simpa only [seed,CountedFinEnumeration.value,List.length_finRange] using
    select_length (fun z => StoredShapeTransition.relation I reverse z x) (List.finRange n)

def seedBudget (I : Input n d) := 2+(n+1)^2+n*(2+StoredSupportQuery.budget I)

theorem seed_bound (I : Input n d) (reverse : Bool) (x : Fin n) :
    (seed I reverse x).2 ≤ seedBudget I := by
  have he := CountedFinEnumeration.bound n
  have hs := select_bound (fun z => StoredShapeTransition.relation I reverse z x) (List.finRange n)
    (StoredSupportQuery.budget I) (fun z _ => StoredShapeTransition.relation_bound I reverse z x)
  simp only [List.length_finRange] at hs
  simp only [seed,CountedFinEnumeration.value,seedBudget]
  omega

def initial (I : Input n d) (x : Fin n) :=
  let a := seed I false x
  let b := seed I true x
  ((a.1,b.1),1+a.2+b.2)

theorem value (I : Input n d) (x : Fin n) :
    ((initial I x).1.1.toFinset,(initial I x).1.2.toFinset) = SubtypeShapeGrammar.initial I.denote x := by
  simp [initial,seed_value,SubtypeShapeGrammar.initial]

theorem lengths (I : Input n d) (x : Fin n) :
    (initial I x).1.1.length ≤ n ∧ (initial I x).1.2.length ≤ n :=
  ⟨seed_length I false x,seed_length I true x⟩

theorem bound (I : Input n d) (x : Fin n) : (initial I x).2 ≤ 1+2*seedBudget I := by
  have ha := seed_bound I false x
  have hb := seed_bound I true x
  simp only [initial]
  omega
end NSSE.StoredShapeInitial
