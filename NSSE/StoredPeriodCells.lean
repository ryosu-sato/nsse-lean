import NSSE.StoredLiveInput

/-! Counted buffer, root-table and cyclic-offset operations for the existing
period monitor. State enumeration and indexing are separate construction steps. -/
namespace NSSE.StoredPeriodCells
variable {d p : Nat}

def advance (hp : 0<p) (q : Fin p) : Fin p × Nat :=
  let c := StoredPaddingDecode.less (q.val+1) p
  if h : c.1=true then (⟨q.val+1,(StoredPaddingDecode.less_value _ _).mp h⟩,1+c.2)
  else (⟨0,hp⟩,1+c.2)

theorem advance_value (hp : 0<p) (q : Fin p) :
    (advance hp q).1 = periodMonitorAdvanceOffset hp q := by
  apply Fin.ext
  simp only [advance,periodMonitorAdvanceOffset]
  split
  · rename_i h
    exact (Nat.mod_eq_of_lt ((StoredPaddingDecode.less_value _ _).mp h)).symm
  · rename_i h
    have he : q.val+1=p := by
      have hn : ¬q.val+1<p := fun hq => h ((StoredPaddingDecode.less_value _ _).mpr hq)
      omega
    simp [he]

theorem advance_bound (hp : 0<p) (q : Fin p) : (advance hp q).2 ≤ p+2 := by
  have h := StoredPaddingDecode.less_bound (q.val+1) p
  simp only [advance]; split <;> omega

def step (A : StoredOrdinaryDFABuild.Data) (hA : StoredDFAProductCells.Valid (d := d) A)
    (hp : 0<p) (s : PeriodMonitorState (Fin d) (Fin A.count) p) (i : Fin d) :
    PeriodMonitorState (Fin d) (Fin A.count) p × Nat :=
  let l := StoredTermReference.lengthCount s.buffer.word
  let c := StoredPaddingDecode.less l.1 p
  if h : c.1=true then
    have hf : s.buffer.word.length<p := by
      have := (StoredPaddingDecode.less_value l.1 p).mp h
      simpa only [l,StoredTermReference.length_value] using this
    let b := CountedListConstruction.append s.buffer.word [i]
    let t := StoredDFAAccess.step A s.rootState i
    (⟨⟨b.1,by rw [CountedListConstruction.append_value,List.length_append]; simp; omega⟩,
      ⟨t.1,hA.step s.rootState i⟩,s.offset,s.valid,s.pastRoot⟩,3+l.2+c.2+b.2+t.2)
  else
    have hf : s.buffer.word.length=p := by
      have hn : ¬l.1<p := fun hx => h ((StoredPaddingDecode.less_value _ _).mpr hx)
      have hb := s.buffer.length_le
      simp only [l,StoredTermReference.length_value] at hn
      omega
    let b := StoredSubtypeInput.lookup s.buffer.word ⟨s.offset.val,by rw [hf]; exact s.offset.isLt⟩
    let e := StoredForwardPedge.equal i b.1
    let a := advance hp s.offset
    (⟨s.buffer,s.rootState,a.1,s.valid && e.1,true⟩,4+l.2+c.2+b.2+e.2+a.2)

def stepBudget (n d p : Nat) := n+2*d+4*p+12

theorem step_bound (A : StoredOrdinaryDFABuild.Data)
    (hA : StoredDFAProductCells.Valid (d := d) A) (hp : 0<p)
    (s : PeriodMonitorState (Fin d) (Fin A.count) p) (i : Fin d) :
    (step A hA hp s i).2 ≤ stepBudget A.count d p := by
  have hl := s.buffer.length_le
  have hc := StoredPaddingDecode.less_bound (StoredTermReference.lengthCount s.buffer.word).1 p
  simp only [step,stepBudget]
  split
  · have ht := StoredDFAAccess.step_bound A s.rootState i
    simp only [StoredTermReference.length_cost,CountedListConstruction.append_cost]
    omega
  · rename_i h
    have hn : ¬s.buffer.word.length<p := by
      simpa only [StoredTermReference.length_value,StoredPaddingDecode.less_value] using h
    have hlen : s.buffer.word.length=p := by omega
    have ha := advance_bound hp s.offset
    have he := StoredForwardPedge.equal_bound i
      (StoredSubtypeInput.lookup s.buffer.word ⟨s.offset.val,by rw [hlen]; exact s.offset.isLt⟩).1
    simp only [StoredTermReference.length_cost,StoredSubtypeInput.lookup_cost]
    omega

theorem step_value (A : FiniteSOARankDecision.InputDFA (Fin d)) (hp : 0<p)
    (s : PeriodMonitorState (Fin d) (Fin A.count) p) (i : Fin d) :
    (step (StoredOrdinaryDFABuild.snapshot A) (StoredDFAProductCells.valid_snapshot A) hp s i).1 =
      periodMonitorStep A.automaton hp s i := by
  simp only [step,StoredTermReference.length_value,periodMonitorStep]
  split
  · rename_i h
    have hf := (StoredPaddingDecode.less_value _ _).mp h
    simp only [hf,↓reduceDIte,CountedListConstruction.append_value,StoredDFAAccess.step_snapshot]
    rfl
  · rename_i h
    have hn : ¬s.buffer.word.length<p := fun hf => h ((StoredPaddingDecode.less_value _ _).mpr hf)
    simp only [hn,↓reduceDIte,advance_value,StoredSubtypeInput.lookup_value]
    have he (x y : Fin d) : (StoredForwardPedge.equal x y).1 = decide (x=y) :=
      Bool.eq_iff_iff.mpr (by simp only [StoredForwardPedge.equal_value,decide_eq_true_eq])
    simp only [he]
    rfl

def final (A : StoredOrdinaryDFABuild.Data)
    (s : PeriodMonitorState (Fin d) (Fin A.count) p) : Bool × Nat :=
  let l := StoredTermReference.lengthCount s.buffer.word
  let e := FiniteValuationLookup.equalNat l.1 p
  let f := StoredDFAAccess.final A s.rootState
  (e.1 && s.pastRoot && s.valid && f.1,3+l.2+e.2+f.2)

theorem final_value (A : FiniteSOARankDecision.InputDFA (Fin d)) (hp : 0<p)
    (s : PeriodMonitorState (Fin d) (Fin A.count) p) :
    (final (StoredOrdinaryDFABuild.snapshot A) s).1 = true ↔
      (boundedPeriodDFA A.automaton p hp).accept s := by
  simp only [final,Bool.and_eq_true,FiniteValuationLookup.equalNat_correct,
    StoredTermReference.length_value,StoredDFAAccess.final_snapshot,boundedPeriodDFA]
  tauto

theorem final_bound (A : StoredOrdinaryDFABuild.Data)
    (s : PeriodMonitorState (Fin d) (Fin A.count) p) :
    (final A s).2 ≤ A.count+2*p+5 := by
  have hl := s.buffer.length_le
  have he := FiniteValuationLookup.equalNat_bound (StoredTermReference.lengthCount s.buffer.word).1 p
  have hf := StoredDFAAccess.final_bound A s.rootState
  simp only [StoredTermReference.length_value] at he
  simp only [final,StoredTermReference.length_cost,StoredTermReference.length_value]
  omega
end NSSE.StoredPeriodCells
