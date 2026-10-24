import NSSE.StoredPaddingDecode

namespace NSSE.StoredPaddedDFA
open StoredOrdinaryDFABuild
variable {d : Nat}

def rawStep (A : Data) : Option (Fin A.count) → Fin (d+2) → Option Nat × Nat
  | none,_ => (none,1)
  | some q,x =>
    let l := StoredPaddingDecode.classify d x.val
    match l.1 with
    | none => (none,1+l.2)
    | some i => let r := StoredDFAAccess.step A q i; (some r.1,2+l.2+r.2)

theorem rawStep_bound (A : Data) (q : Option (Fin A.count)) (x : Fin (d+2)) :
    (rawStep A q x).2 ≤ A.count+2*d+5 := by
  cases q with
  | none => simp only [rawStep]; omega
  | some q =>
    have hl := StoredPaddingDecode.classify_bound d x.val
    simp only [rawStep]
    split
    · omega
    · rename_i i hi
      have hr := StoredDFAAccess.step_bound A q i
      omega

theorem rawStep_value (D : FiniteSOARankDecision.InputDFA (Fin d)) (q : Option (Fin D.count)) (x : Fin (d+2)) :
    (rawStep (snapshot D) q x).1 = ((PaddedAlphabetDFA.raw D.automaton).step q x).map Fin.val := by
  cases q with
  | none => rfl
  | some q =>
    simp only [rawStep,StoredPaddingDecode.letter_value,PaddedAlphabetDFA.raw,Option.some_bind]
    cases hl : PaddedAlphabetDFA.letter x <;> simp [StoredDFAAccess.step_snapshot]

def step (A : Data) (q : Fin (A.count+1)) (x : Fin (d+2)) : Nat × Nat :=
  let s := StoredPaddingDecode.classify A.count q.val
  let r := rawStep A s.1 x
  (r.1.getD A.count,2+s.2+r.2)

def final (A : Data) (q : Fin (A.count+1)) : Bool × Nat :=
  let s := StoredPaddingDecode.classify A.count q.val
  match s.1 with
  | none => (false,1+s.2)
  | some q => let f := StoredDFAAccess.final A q; (f.1,1+s.2+f.2)

theorem step_bound (A : Data) (q : Fin (A.count+1)) (x : Fin (d+2)) :
    (step A q x).2 ≤ 2*A.count+2*d+9 := by
  have hs := StoredPaddingDecode.classify_bound A.count q.val
  have hr := rawStep_bound A (StoredPaddingDecode.classify A.count q.val).1 x
  simp only [step]; omega

theorem final_bound (A : Data) (q : Fin (A.count+1)) :
    (final A q).2 ≤ 2*A.count+3 := by
  have hs := StoredPaddingDecode.classify_bound A.count q.val
  simp only [final]; split
  · omega
  · rename_i r hr; have hf := StoredDFAAccess.final_bound A r; omega

theorem encode_value {n : Nat} (q : Option (Fin n)) :
    (q.map Fin.val).getD n = ((finSuccEquiv' (Fin.last n)).symm q).val := by
  cases q <;> simp [Fin.succAbove_last]

theorem step_value (D : FiniteSOARankDecision.InputDFA (Fin d)) (q : Fin (D.count+1)) (x : Fin (d+2)) :
    (step (snapshot D) q x).1 = ((PaddedAlphabetDFA.lift D).automaton.step q x).val := by
  unfold step
  dsimp only
  have hr := rawStep_value D (StoredPaddingDecode.classify D.count q.val).1 x
  have he := congrArg (fun r : Option Nat => r.getD D.count) hr
  dsimp only at he
  rw [encode_value] at he
  simpa only [StoredPaddingDecode.state_value,PaddedAlphabetDFA.lift,FiniteCapTerminal.reindex] using he

theorem final_value (D : FiniteSOARankDecision.InputDFA (Fin d)) (q : Fin (D.count+1)) :
    (final (snapshot D) q).1 = true ↔ (PaddedAlphabetDFA.lift D).automaton.accept q := by
  refine Fin.lastCases ?_ (fun i => ?_) q
  · simp [final,StoredPaddingDecode.classify_value,snapshot,PaddedAlphabetDFA.lift,
      FiniteCapTerminal.reindex,PaddedAlphabetDFA.raw]
    intro x hx
    have h := x.isLt
    have he := congrArg Fin.val hx
    simp only [Fin.val_last,Fin.coe_castSucc] at he
    omega
  · simp [final,StoredPaddingDecode.classify_value,snapshot,StoredDFAAccess.final,
      StoredForwardLookup.get_ofFn,i.isLt,PaddedAlphabetDFA.lift,FiniteCapTerminal.reindex,
      PaddedAlphabetDFA.raw,finSuccEquiv'_last_apply_castSucc]
end NSSE.StoredPaddedDFA
