import NSSE.StoredForwardStep

namespace NSSE.StoredForwardFinal
open ForwardTableAutomaton StoredForwardLookup
variable {n d : Nat}

def existsFin (n : Nat) (f : Fin n → Bool × Nat) : Bool × Nat :=
  let xs := CountedFinEnumeration.enumerate n
  let r := StoredRegularSatisfiability.any f xs.1
  (r.1,1+xs.2+r.2)

theorem existsFin_value (n : Nat) (f : Fin n → Bool × Nat) :
    (existsFin n f).1 = true ↔ ∃ i, (f i).1 = true := by
  simp only [existsFin,StoredRegularSatisfiability.any_value,CountedFinEnumeration.value,
    List.any_eq_true,List.mem_finRange,true_and]

theorem existsFin_bound (n B : Nat) (f : Fin n → Bool × Nat) (h : ∀ i, (f i).2 ≤ B) :
    (existsFin n f).2 ≤ StoredForwardTableBuild.tabBudget n B := by
  have he := CountedFinEnumeration.bound n
  have ha := StoredRegularSatisfiability.any_bound f (CountedFinEnumeration.enumerate n).1 B (fun i _ => h i)
  rw [CountedFinEnumeration.value,List.length_finRange] at ha
  simp only [existsFin,StoredForwardTableBuild.tabBudget,CountedFinEnumeration.value]; omega

def outgoing (D : StoredForwardTableBuild.Data n) (rev : Bool) (u : Token n) : Bool × Nat :=
  existsFin d (fun i => existsFin n (fun y => StoredForwardStep.move D rev u i (some y)))

theorem upper_value (D : StoredForwardTableBuild.Data n) (u : Token n) :
    (outgoing (d := d) D false u).1 = true ↔ ∃ i r, upperMove (denote (d := d) D) u i r := by
  simp only [outgoing,existsFin_value,StoredForwardStep.upper_value]
  constructor
  · rintro ⟨i,y,h⟩; exact ⟨i,some y,h⟩
  · rintro ⟨i,r,h⟩
    cases r with
    | none => cases u <;> simp [upperMove] at h
    | some y => exact ⟨i,y,h⟩

theorem lower_value (D : StoredForwardTableBuild.Data n) (u : Token n) :
    (outgoing (d := d) D true u).1 = true ↔ ∃ i r, lowerMove (denote (d := d) D) u i r := by
  simp only [outgoing,existsFin_value,StoredForwardStep.lower_value]
  constructor
  · rintro ⟨i,y,h⟩; exact ⟨i,some y,h⟩
  · rintro ⟨i,r,h⟩
    cases r with
    | none => cases u <;> simp [lowerMove] at h
    | some y => exact ⟨i,y,h⟩

def outgoingBudget (n d : Nat) :=
  StoredForwardTableBuild.tabBudget d (StoredForwardTableBuild.tabBudget n (2*n+d+3))

theorem outgoing_bound (D : StoredForwardTableBuild.Data n) (rev : Bool) (u : Token n) :
    (outgoing (d := d) D rev u).2 ≤ outgoingBudget n d :=
  existsFin_bound d _ _ (fun i => existsFin_bound n _ _
    (fun y => StoredForwardStep.move_bound D rev u (some y) i))

def final (D : StoredForwardTableBuild.Data n) (side : Side) : State n → Bool × Nat
  | none => (true,1)
  | some (u,v) =>
    let e := StoredForwardStep.escape D u v
    let r := match side with
      | .left => outgoing (d := d) D false u
      | .right => outgoing (d := d) D true v
    (e.1 || r.1,2+e.2+r.2)

theorem value (D : StoredForwardTableBuild.Data n) (side : Side) (q : State n) :
    (final (d := d) D side q).1 = true ↔ ForwardTableAutomaton.final (denote (d := d) D) side q := by
  cases q with
  | none => simp [final,ForwardTableAutomaton.final]
  | some q => rcases q with ⟨u,v⟩; cases side <;>
      simp only [final,ForwardTableAutomaton.final,Bool.or_eq_true,(StoredForwardStep.escape_value (d := d) D u v),
        upper_value,lower_value]

def budget (n d : Nat) := 6+4*n+outgoingBudget n d

theorem bound (D : StoredForwardTableBuild.Data n) (side : Side) (q : State n) :
    (final (d := d) D side q).2 ≤ budget n d := by
  cases q with
  | none => simp only [final,budget]; omega
  | some q =>
    rcases q with ⟨u,v⟩
    have he := StoredForwardStep.escape_bound D u v
    have hu := outgoing_bound (d := d) D false u
    have hv := outgoing_bound (d := d) D true v
    cases side <;> simp only [final,budget] <;> omega
end NSSE.StoredForwardFinal
