import NSSE.StoredDynamicRun
import NSSE.StoredPaddingDecode

/-! Actual counted array coordinates feeding the dynamic two-tape compiler. -/
namespace NSSE.StoredArrayColumns
open FirstOrder FirstOrder.Language StoredRelationalFormula FiniteWordCoordinates
variable {R : Nat → Type} {P : Type} {q T n : Nat}
abbrev Arguments (q : Nat) := StoredRelationTuple.Data (Fin q) 2

def finite (args : Arguments q) (t : Fin (T+1)) : StoredDynamicRun.Column (Params P q T) × Nat :=
  let fs := StoredRelationTuple.tabulate (fun i : Fin 2 =>
    let a := StoredRelationTuple.read args i
    let b := StoredArrayCoordinates.flag (P := P) t a.1
    (b.1,1+a.2+b.2))
  let ls := StoredRelationTuple.tabulate (fun i : Fin 2 =>
    let a := StoredRelationTuple.read args i
    let b := StoredArrayCoordinates.letter (P := P) t a.1
    (b.1,1+a.2+b.2))
  (⟨fs.1,ls.1⟩,1+fs.2+ls.2)
theorem finite_flag (zero : P) (args : Arguments q) (t : Fin (T+1)) (i : Fin 2) :
    (StoredRelationTuple.read (finite (P := P) args t).1.flags i).1 = flags zero q T t.val (StoredRelationTuple.read args i).1 := by
  simp only [finite,StoredRelationTuple.tabulate_read,StoredArrayCoordinates.flag_value zero]
theorem finite_letter (zero : P) (args : Arguments q) (t : Fin (T+1)) (i : Fin 2) :
    (StoredRelationTuple.read (finite (P := P) args t).1.letters i).1 = letters zero q T t.val (StoredRelationTuple.read args i).1 := by
  simp only [finite,StoredRelationTuple.tabulate_read,StoredArrayCoordinates.letter_value zero]
def finiteBudget (q T : Nat) := 3+StoredForwardTableBuild.tabBudget 2 (3+StoredArrayCoordinates.flagBudget q T)+
  StoredForwardTableBuild.tabBudget 2 (3+StoredArrayCoordinates.letterBudget q T)
theorem finite_bound (args : Arguments q) (t : Fin (T+1)) : (finite (P := P) args t).2 ≤ finiteBudget q T := by
  have hf := StoredRelationTuple.tabulate_bound (fun i : Fin 2 =>
    let a := StoredRelationTuple.read args i
    let b := StoredArrayCoordinates.flag (P := P) t a.1
    (b.1,1+a.2+b.2)) (3+StoredArrayCoordinates.flagBudget q T) (by
      intro i
      have ha := StoredRelationTuple.read_bound args i
      have hb := StoredArrayCoordinates.flag_bound (P := P) t (StoredRelationTuple.read args i).1
      dsimp only; omega)
  have hl := StoredRelationTuple.tabulate_bound (fun i : Fin 2 =>
    let a := StoredRelationTuple.read args i
    let b := StoredArrayCoordinates.letter (P := P) t a.1
    (b.1,1+a.2+b.2)) (3+StoredArrayCoordinates.letterBudget q T) (by
      intro i
      have ha := StoredRelationTuple.read_bound args i
      have hb := StoredArrayCoordinates.letter_bound (P := P) t (StoredRelationTuple.read args i).1
      dsimp only; omega)
  dsimp only at hf hl
  simp only [finite,finiteBudget]; omega

def fallback (zero : P) (q T : Nat) : StoredDynamicRun.Column (Params P q T) :=
  let v : StoredDynamicColumn.Coordinates (Params P q T) := ⟨[.inl zero,.inl zero],rfl⟩
  ⟨v,v⟩
def build (zero : P) (args : Arguments q) (T : Nat) : StoredDynamicRun.Columns (Params P q T) := fun t =>
  let a := StoredPaddingDecode.classify (T+1) t
  match a.1 with
  | some u => let b := finite args u; (b.1,1+a.2+b.2)
  | none => (fallback zero q T,10+a.2)
theorem flags_value (zero : P) (args : Arguments q) (t : Nat) (i : Fin 2) :
    StoredDynamicRun.flags (build zero args T) t i = flags zero q T t (StoredRelationTuple.read args i).1 := by
  by_cases ht : t<T+1
  · simp only [StoredDynamicRun.flags,build,StoredPaddingDecode.classify_value,ht,↓reduceDIte]
    exact finite_flag zero args ⟨t,ht⟩ i
  · simp only [StoredDynamicRun.flags,build,StoredPaddingDecode.classify_value,ht,↓reduceDIte,flags]
    fin_cases i <;> rfl
theorem letters_value (zero : P) (args : Arguments q) (t : Nat) (i : Fin 2) :
    StoredDynamicRun.letters (build zero args T) t i = letters zero q T t (StoredRelationTuple.read args i).1 := by
  by_cases ht : t<T+1
  · simp only [StoredDynamicRun.letters,build,StoredPaddingDecode.classify_value,ht,↓reduceDIte]
    exact finite_letter zero args ⟨t,ht⟩ i
  · simp only [StoredDynamicRun.letters,build,StoredPaddingDecode.classify_value,ht,↓reduceDIte,letters]
    fin_cases i <;> rfl

def budget (q T : Nat) := T+13+finiteBudget q T
theorem bound (zero : P) (args : Arguments q) (t : Nat) : (build zero args T t).2 ≤ budget q T := by
  have ha := StoredPaddingDecode.classify_bound (T+1) t
  dsimp only [build]
  split
  · rename_i u hu
    have hb := finite_bound (P := P) args u
    unfold budget; omega
  · unfold budget; omega

def closed (A : StoredDynamicColumn.Automaton R (Params P q T) n) (zero one : P)
    (args : Arguments q) (positive : Bool) : Data R (Params P q T) 0 × Nat :=
  StoredDynamicRun.closed A (build zero args T) (.inl one) T positive
theorem closed_value (A : StoredDynamicColumn.Automaton R (Params P q T) n) (zero one : P)
    (args : Arguments q) (positive : Bool) : denote (closed A zero one args positive).1 =
      DynamicColumnRunFormula.compile A.original
        (fun t i => flags zero q T t (StoredRelationTuple.read args i).1)
        (fun t i => letters zero q T t (StoredRelationTuple.read args i).1) (.inl one) T positive := by
  simp only [closed,StoredDynamicRun.closed_value]
  have hf : StoredDynamicRun.flags (build zero args T) = fun t i => flags zero q T t (StoredRelationTuple.read args i).1 := by
    funext t i; exact flags_value zero args t i
  have hl : StoredDynamicRun.letters (build zero args T) = fun t i => letters zero q T t (StoredRelationTuple.read args i).1 := by
    funext t i; exact letters_value zero args t i
  rw [hf,hl]
theorem closed_bound (A : StoredDynamicColumn.Automaton R (Params P q T) n) (zero one : P)
    (args : Arguments q) (positive : Bool) (c B K : Nat) (h : StoredDynamicColumn.Bounds A c B K) :
    (closed A zero one args positive).2 ≤ (1016*661^5)*(n+T+c+budget q T+B+K+1)^10 :=
  StoredDynamicRun.closed_polynomial A (build zero args T) (.inl one) positive c (budget q T) B K h
    (fun t _ => bound zero args t)
theorem budget_value (q T : Nat) : budget q T = 78+8*q*T+12*q+9*T := by
  unfold budget finiteBudget StoredForwardTableBuild.tabBudget StoredArrayCoordinates.flagBudget
    StoredArrayCoordinates.letterBudget
  ring
theorem radius_bound (n q T c B K : Nat) :
    n+T+c+budget q T+B+K+1 ≤ 113*(n+q+T+c+B+K+1)^2 := by
  let u := n+q+T+c+B+K+1
  have hn : n ≤ u := by dsimp [u]; omega
  have hq : q ≤ u := by dsimp [u]; omega
  have ht : T ≤ u := by dsimp [u]; omega
  have hc : c ≤ u := by dsimp [u]; omega
  have hb : B ≤ u := by dsimp [u]; omega
  have hk : K ≤ u := by dsimp [u]; omega
  have hu : 1 ≤ u := by dsimp [u]; omega
  rw [budget_value]
  have hm : n+T+c+(78+8*q*T+12*q+9*T)+B+K+1 ≤ u+u+u+(78+8*u*u+12*u+9*u)+u+u+1 := by gcongr
  change _ ≤ 113*u^2
  nlinarith
theorem closed_polynomial (A : StoredDynamicColumn.Automaton R (Params P q T) n) (zero one : P)
    (args : Arguments q) (positive : Bool) (c B K : Nat) (h : StoredDynamicColumn.Bounds A c B K) :
    (closed A zero one args positive).2 ≤ (1016*661^5*113^10)*(n+q+T+c+B+K+1)^20 := by
  have hb := closed_bound A zero one args positive c B K h
  have hp := Nat.mul_le_mul_left (1016*661^5) (Nat.pow_le_pow_left (radius_bound n q T c B K) 10)
  refine hb.trans (hp.trans_eq ?_)
  simp only [mul_pow,← pow_mul,Nat.mul_assoc]
end NSSE.StoredArrayColumns
