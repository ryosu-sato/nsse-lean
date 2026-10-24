import NSSE.StoredTermLiteral
import NSSE.SubtypeTermDefinitions

namespace NSSE.StoredTermClause
open StoredSubtypeTerm
variable {n d : Nat}

def clause (ts : List (Term n)) (pairs : Nat) (t : Term n) (h : WellFormed d t) :
    StoredSubtypeInput.Input (n+(ts.length+(pairs+1))) d × Nat :=
  match t with
  | .var _ => (⟨[],[],[],[]⟩,1)
  | .bot => let r := StoredTermReference.resolve ts pairs .bot; (⟨[],[],[r.1],[]⟩,2+r.2)
  | .top => let r := StoredTermReference.resolve ts pairs .top; (⟨[],[],[],[r.1]⟩,2+r.2)
  | .node cs =>
    let a := StoredTermLiteral.literal ts pairs (.node cs) cs (by simp only [WellFormed] at h; exact h.1)
    (⟨[a.1],[a.1],[],[]⟩,3+a.2)

theorem child_weight (cs : List (Term n)) (t : Term n) (ht : t ∈ cs) :
    weight t ≤ weight (.node cs) := by
  have h : weight t ≤ (cs.map (fun u => 1+weight u)).sum := by
    induction cs with
    | nil => simp at ht
    | cons u us ih =>
      simp only [List.mem_cons] at ht
      simp only [List.map_cons,List.sum_cons]
      rcases ht with rfl | ht
      · omega
      · have hh := ih ht; omega
  simp only [weight]; omega

def budget (n m d W : Nat) :=
  5+(n+2*m+8+m*(1+2*W))+d*(1+(n+2*m+8+m*(1+2*W)))

theorem bound (ts : List (Term n)) (pairs : Nat) (t : Term n) (h : WellFormed d t)
    (W : Nat) (hw : weight t ≤ W) :
    (clause ts pairs t h).2 ≤ budget n ts.length d W := by
  cases t with
  | var x => simp only [clause,budget]; omega
  | bot =>
    have hr := StoredTermReference.uniform_bound ts pairs .bot n ts.length W (by rfl) (by rfl) hw
    simp only [clause,budget]; omega
  | top =>
    have hr := StoredTermReference.uniform_bound ts pairs .top n ts.length W (by rfl) (by rfl) hw
    simp only [clause,budget]; omega
  | node cs =>
    have hr := StoredTermLiteral.literal_bound ts pairs (.node cs) cs (by simp only [WellFormed] at h; exact h.1) W hw
      (fun t ht => (child_weight cs t ht).trans hw)
    simp only [clause,budget]; omega

def transport {a b : Nat} (h : a=b) (I : StoredSubtypeInput.Input a d) :
    SubtypeConstraints.Constraints b d :=
  ⟨I.upper.map (StoredTermLiteral.transport h),I.lower.map (StoredTermLiteral.transport h),
    I.bot.map (Fin.cast h),I.top.map (Fin.cast h)⟩

theorem packed_value (L : SubtypeTermLayout.Layout n d) (t : SubtypeTerms.Term n d) :
    transport (by simp [SubtypeTermLayout.Layout.count])
      (clause (L.terms.map pack) L.pairs.length (pack t) (pack_wellFormed t)).1 =
      SubtypeTermDefinitions.termClause L t := by
  cases t with
  | var x => rfl
  | bot =>
    have hr : Fin.cast (by simp [SubtypeTermLayout.Layout.count])
        (StoredTermReference.resolve (L.terms.map pack) L.pairs.length (pack (.bot : SubtypeTerms.Term n d))).1 = L.ref .bot :=
      Fin.ext (StoredTermReference.packed_value L .bot)
    simpa only [pack,clause,transport,List.map_nil,List.map_cons,SubtypeTermDefinitions.termClause] using
      congrArg (fun x => (⟨[],[],[x],[]⟩ : SubtypeConstraints.Constraints L.count d)) hr
  | top =>
    have hr : Fin.cast (by simp [SubtypeTermLayout.Layout.count])
        (StoredTermReference.resolve (L.terms.map pack) L.pairs.length (pack (.top : SubtypeTerms.Term n d))).1 = L.ref .top :=
      Fin.ext (StoredTermReference.packed_value L .top)
    simpa only [pack,clause,transport,List.map_nil,List.map_cons,SubtypeTermDefinitions.termClause] using
      congrArg (fun x => (⟨[],[],[],[x]⟩ : SubtypeConstraints.Constraints L.count d)) hr
  | node c =>
    have hr := StoredTermLiteral.packed_literal_value L (.node c) c
    simpa only [pack,clause,transport,List.map_nil,List.map_cons,SubtypeTermDefinitions.termClause] using
      congrArg (fun x => (⟨[x],[x],[],[]⟩ : SubtypeConstraints.Constraints L.count d)) hr
end NSSE.StoredTermClause
