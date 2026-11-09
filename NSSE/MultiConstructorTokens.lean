import NSSE.MultiConstructorSupportDecision

/-! Actual one-sided support tokens, constructor pins and child moves.
Every finite computation uses the proved original support decision. -/
namespace NSSE.MultiConstructorTokens
open MultiConstructorConstraints MultiConstructorSupportDecision
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

abbrev Tokens (n : Nat) := Finset (Fin n)

def up (phi : Constraints arity n) (S : Tokens n) : Tokens n :=
  letI := supportDecision phi
  Finset.univ.filter (fun v => ∃ t ∈ S, Support phi t v)

def down (phi : Constraints arity n) (S : Tokens n) : Tokens n :=
  letI := supportDecision phi
  Finset.univ.filter (fun v => ∃ t ∈ S, Support phi v t)

theorem mem_up (phi : Constraints arity n) (S : Tokens n) (v : Fin n) :
    v ∈ up phi S ↔ ∃ t ∈ S, Support phi t v := by simp only [up,Finset.mem_filter,Finset.mem_univ,true_and]

theorem mem_down (phi : Constraints arity n) (S : Tokens n) (v : Fin n) :
    v ∈ down phi S ↔ ∃ t ∈ S, Support phi v t := by simp only [down,Finset.mem_filter,Finset.mem_univ,true_and]

def UpperClosed (phi : Constraints arity n) (S : Tokens n) : Prop :=
  ∀ u ∈ S, ∀ v, Support phi u v → v ∈ S

def LowerClosed (phi : Constraints arity n) (S : Tokens n) : Prop :=
  ∀ v ∈ S, ∀ u, Support phi u v → u ∈ S

theorem up_closed (phi : Constraints arity n) (S : Tokens n) : UpperClosed phi (up phi S) := by
  intro u hu v huv
  obtain ⟨t,ht,htu⟩ := (mem_up phi S u).mp hu
  exact (mem_up phi S v).mpr ⟨t,ht,htu.trans huv⟩

theorem down_closed (phi : Constraints arity n) (S : Tokens n) : LowerClosed phi (down phi S) := by
  intro v hv u huv
  obtain ⟨t,ht,hvt⟩ := (mem_down phi S v).mp hv
  exact (mem_down phi S u).mpr ⟨t,ht,huv.trans hvt⟩

def upperPins (phi : Constraints arity n) (S : Tokens n) : Finset H :=
  letI := supportDecision phi
  ((phi.upper.filter (fun a => ∃ t ∈ S, Support phi t a.parent)).map Bound.head).toFinset

def lowerPins (phi : Constraints arity n) (S : Tokens n) : Finset H :=
  letI := supportDecision phi
  ((phi.lower.filter (fun a => ∃ t ∈ S, Support phi a.parent t)).map Bound.head).toFinset

theorem mem_upperPins (phi : Constraints arity n) (S : Tokens n) (h : H) :
    h ∈ upperPins phi S ↔ ∃ a ∈ phi.upper, (∃ t ∈ S, Support phi t a.parent) ∧ a.head = h := by
  simp only [upperPins,List.mem_toFinset,List.mem_map,List.mem_filter,decide_eq_true_eq,and_assoc]

theorem mem_lowerPins (phi : Constraints arity n) (S : Tokens n) (h : H) :
    h ∈ lowerPins phi S ↔ ∃ a ∈ phi.lower, (∃ t ∈ S, Support phi a.parent t) ∧ a.head = h := by
  simp only [lowerPins,List.mem_toFinset,List.mem_map,List.mem_filter,decide_eq_true_eq,and_assoc]

def upperNext (phi : Constraints arity n) (S : Tokens n) (letter : Nat) : Tokens n :=
  letI := supportDecision phi
  Finset.univ.filter (fun v => ∃ a ∈ phi.upper, (∃ t ∈ S, Support phi t a.parent) ∧
    ∃ i : Fin (arity a.head), i.val = letter ∧ Support phi (a.children i) v)

def lowerNext (phi : Constraints arity n) (S : Tokens n) (letter : Nat) : Tokens n :=
  letI := supportDecision phi
  Finset.univ.filter (fun v => ∃ a ∈ phi.lower, (∃ t ∈ S, Support phi a.parent t) ∧
    ∃ i : Fin (arity a.head), i.val = letter ∧ Support phi v (a.children i))

theorem mem_upperNext (phi : Constraints arity n) (S : Tokens n) (letter : Nat) (v : Fin n) :
    v ∈ upperNext phi S letter ↔ ∃ a ∈ phi.upper, (∃ t ∈ S, Support phi t a.parent) ∧
      ∃ i : Fin (arity a.head), i.val = letter ∧ Support phi (a.children i) v := by
  simp only [upperNext,Finset.mem_filter,Finset.mem_univ,true_and]

theorem mem_lowerNext (phi : Constraints arity n) (S : Tokens n) (letter : Nat) (v : Fin n) :
    v ∈ lowerNext phi S letter ↔ ∃ a ∈ phi.lower, (∃ t ∈ S, Support phi a.parent t) ∧
      ∃ i : Fin (arity a.head), i.val = letter ∧ Support phi v (a.children i) := by
  simp only [lowerNext,Finset.mem_filter,Finset.mem_univ,true_and]

theorem upperNext_closed (phi : Constraints arity n) (S : Tokens n) (letter : Nat) :
    UpperClosed phi (upperNext phi S letter) := by
  intro u hu v huv
  obtain ⟨a,ha,ht,i,hi,hc⟩ := (mem_upperNext phi S letter u).mp hu
  exact (mem_upperNext phi S letter v).mpr ⟨a,ha,ht,i,hi,hc.trans huv⟩

theorem lowerNext_closed (phi : Constraints arity n) (S : Tokens n) (letter : Nat) :
    LowerClosed phi (lowerNext phi S letter) := by
  intro v hv u huv
  obtain ⟨a,ha,ht,i,hi,hc⟩ := (mem_lowerNext phi S letter v).mp hv
  exact (mem_lowerNext phi S letter u).mpr ⟨a,ha,ht,i,hi,huv.trans hc⟩

theorem upperPins_empty (phi : Constraints arity n) : upperPins phi ∅ = ∅ := by
  ext h
  simp [mem_upperPins]

theorem lowerPins_empty (phi : Constraints arity n) : lowerPins phi ∅ = ∅ := by
  ext h
  simp [mem_lowerPins]

theorem upperNext_of_unpinned (phi : Constraints arity n) (S : Tokens n) (letter : Nat)
    (hp : upperPins phi S = ∅) : upperNext phi S letter = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro v hv
  obtain ⟨a,ha,ht,_⟩ := (mem_upperNext phi S letter v).mp hv
  have h := (mem_upperPins phi S a.head).mpr ⟨a,ha,ht,rfl⟩
  rw [hp] at h
  exact Finset.not_mem_empty _ h

theorem lowerNext_of_unpinned (phi : Constraints arity n) (S : Tokens n) (letter : Nat)
    (hp : lowerPins phi S = ∅) : lowerNext phi S letter = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro v hv
  obtain ⟨a,ha,ht,_⟩ := (mem_lowerNext phi S letter v).mp hv
  have h := (mem_lowerPins phi S a.head).mpr ⟨a,ha,ht,rfl⟩
  rw [hp] at h
  exact Finset.not_mem_empty _ h

theorem upperNext_empty (phi : Constraints arity n) (letter : Nat) : upperNext phi ∅ letter = ∅ :=
  upperNext_of_unpinned phi ∅ letter (upperPins_empty phi)

theorem lowerNext_empty (phi : Constraints arity n) (letter : Nat) : lowerNext phi ∅ letter = ∅ :=
  lowerNext_of_unpinned phi ∅ letter (lowerPins_empty phi)

omit [DecidableEq H] in
theorem birth_iff_inter (phi : Constraints arity n) (U L : Tokens n) (hc : UpperClosed phi U) :
    (∃ u ∈ U, ∃ v ∈ L, Support phi u v) ↔ (U ∩ L).Nonempty := by
  constructor
  · rintro ⟨u,hu,v,hv,hs⟩
    exact ⟨v,Finset.mem_inter.mpr ⟨hc u hu v hs,hv⟩⟩
  · rintro ⟨v,hv⟩
    obtain ⟨hu,hl⟩ := Finset.mem_inter.mp hv
    exact ⟨v,hu,v,hl,.refl v⟩

end NSSE.MultiConstructorTokens
