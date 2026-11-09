import NSSE.MultiVarianceBranchFactors

/-! The finite parameter family for one fixed original query. Terminal
labels use a finite head-or-extremum code, independently of any witness
search. Coverage of arbitrary separating spines is a later theorem. -/
namespace NSSE.MultiVarianceBranchFamily
open MultiConstructorConstraints (Query)
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceBranch
variable {H : Type*} {arity : H → Nat} {n D : Nat}

abbrev Key (H : Type*) (n : Nat) := Frame n × H × (H ⊕ Bool) × (H ⊕ Bool)

def label : H ⊕ Bool → Label H
  | .inl h => .node h
  | .inr false => .bot
  | .inr true => .top

def code : Label H → H ⊕ Bool
  | .node h => .inl h
  | .bot => .inr false
  | .top => .inr true

theorem label_code (a : Label H) : label (code a)=a := by cases a <;> rfl
theorem code_label (a : H ⊕ Bool) : code (label a)=a := by
  cases a with
  | inl h => rfl
  | inr b => cases b <;> rfl

def parameters (Q : Query arity n) (k : Key H n) : Parameters arity n :=
  ⟨Q,k.1,k.2.1,label k.2.2.1,label k.2.2.2⟩

def key (C : Parameters arity n) : Key H n :=
  ⟨C.reset,C.fallback,code C.endX,code C.endY⟩

theorem parameters_key (C : Parameters arity n) : parameters C.query (key C)=C := by
  cases C
  simp only [parameters,key,label_code]

theorem key_parameters (Q : Query arity n) (k : Key H n) : key (parameters Q k)=k := by
  simp only [parameters,key,code_label]

theorem card_keys [Fintype H] (n : Nat) :
    Fintype.card (Key H n) = 2^(2*n+1)*Fintype.card H*(Fintype.card H+2)^2 := by
  have hp : 2*4^n=2^(2*n+1) := by
    simp only [pow_add,pow_mul,pow_one]
    norm_num
    ring
  simp only [Key,Fintype.card_prod,Fintype.card_sum,Fintype.card_bool,card_frames,hp]
  ring

variable [Fintype H] [DecidableEq H] (pol : Polarity arity)

def alphabetSize (arity : H → Nat) : Nat := Finset.univ.sup arity

omit [DecidableEq H] in
theorem arity_le_alphabet (h : H) : arity h ≤ alphabetSize arity :=
  Finset.le_sup (Finset.mem_univ h)

def familyDecision (Q : Query arity n) (w : List (Fin D)) :
    Decidable (∃ k : Key H n, P0DZBranch.Accepted (branch pol (parameters Q k) D) w) := by
  letI : DecidablePred (fun k : Key H n => P0DZBranch.Accepted (branch pol (parameters Q k) D) w) :=
    fun k => P0DZDecision.acceptedDecision (branch pol (parameters Q k) D) (birthDecision pol (parameters Q k) D) w
  infer_instance

def inspectAny (Q : Query arity n) (w : List (Fin D)) : Bool :=
  @decide (∃ k : Key H n, P0DZBranch.Accepted (branch pol (parameters Q k) D) w) (familyDecision pol Q w)

theorem inspectAny_correct (Q : Query arity n) (w : List (Fin D)) :
    inspectAny pol Q w=true ↔ ∃ k : Key H n, P0DZBranch.Accepted (branch pol (parameters Q k) D) w := by
  simp only [inspectAny,decide_eq_true_eq]

theorem inspectAny_parameters (Q : Query arity n) (w : List (Fin D)) :
    inspectAny pol Q w=true ↔ ∃ C : Parameters arity n, C.query=Q ∧ P0DZBranch.Accepted (branch pol C D) w := by
  rw [inspectAny_correct]
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨parameters Q k,rfl,hk⟩
  · rintro ⟨C,hq,hc⟩
    refine ⟨key C,?_⟩
    rw [← hq,parameters_key]
    exact hc

theorem epsilon_rejected (Q : Query arity n) : inspectAny pol Q ([] : List (Fin D))=false := by
  apply Bool.eq_false_iff.mpr
  intro hi
  obtain ⟨k,hk⟩ := (inspectAny_correct pol Q []).mp hi
  exact P0DZBranch.complete_nonempty _ _ hk.1 rfl

theorem empty_signature_rejected [IsEmpty H] (Q : Query arity n) (w : List (Fin D)) :
    inspectAny pol Q w=false := by
  apply Bool.eq_false_iff.mpr
  intro hi
  obtain ⟨k,_⟩ := (inspectAny_correct pol Q w).mp hi
  exact isEmptyElim k.2.1

end NSSE.MultiVarianceBranchFamily
