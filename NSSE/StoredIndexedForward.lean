import NSSE.StoredForwardDecode
import NSSE.StoredForwardFinal

namespace NSSE.StoredIndexedForward
open ForwardTableAutomaton
variable {n d : Nat}
abbrev Index (n : Nat) := Fin ((n+1)*(n+1)+1)

def step (D : StoredForwardTableBuild.Data n) (q : Index n) (i : Fin d) (r : Index n) : Bool × Nat :=
  let a := StoredForwardDecode.decode q
  let b := StoredForwardDecode.decode r
  let s := StoredForwardStep.step D a.1 i b.1
  (s.1,2+a.2+b.2+s.2)

def final (D : StoredForwardTableBuild.Data n) (side : Side) (q : Index n) : Bool × Nat :=
  let a := StoredForwardDecode.decode q
  let f := StoredForwardFinal.final (d := d) D side a.1
  (f.1,1+a.2+f.2)

def pedge (side : Side) (q r : Index n) : Bool × Nat :=
  let a := StoredForwardDecode.decode q
  let b := StoredForwardDecode.decode r
  let e := StoredForwardPedge.pedge side a.1 b.1
  (e.1,2+a.2+b.2+e.2)

def start (D : StoredForwardTableBuild.Data n) : Index n × Nat :=
  let r := StoredForwardStateIndex.encode (some (some D.queryLeft,some D.queryRight))
  (⟨r.1,StoredForwardStateIndex.range _⟩,1+r.2)

theorem step_value (D : StoredForwardTableBuild.Data n) (side : Side) (q r : Index n) (i : Fin d) :
    (step D q i r).1 = true ↔
      (ForwardTableAutomaton.compile (StoredForwardLookup.denote D) side).step q i r := by
  simp only [step,StoredForwardStep.step_value,StoredForwardDecode.value,ForwardTableAutomaton.compile]

theorem final_value (D : StoredForwardTableBuild.Data n) (side : Side) (q : Index n) :
    (final (d := d) D side q).1 = true ↔
      (ForwardTableAutomaton.compile (StoredForwardLookup.denote (d := d) D) side).final q := by
  simp only [final,StoredForwardFinal.value,StoredForwardDecode.value,ForwardTableAutomaton.compile]

theorem pedge_value (D : StoredForwardTableBuild.Data n) (side : Side) (q r : Index n) :
    (pedge side q r).1 = true ↔
      (ForwardTableAutomaton.compile (StoredForwardLookup.denote (d := d) D) side).pedge q r := by
  simp only [pedge,StoredForwardPedge.value,StoredForwardDecode.value,ForwardTableAutomaton.compile]

theorem start_value (D : StoredForwardTableBuild.Data n) (side : Side) :
    (start D).1 = (ForwardTableAutomaton.compile (StoredForwardLookup.denote (d := d) D) side).start := by
  apply Fin.ext
  simp only [start,StoredForwardStateIndex.value,ForwardTableAutomaton.compile,StoredForwardLookup.denote]

def stepBudget (n d : Nat) := 2+2*StoredForwardDecode.budget n+(4*n+2*d+11)
def finalBudget (n d : Nat) := 1+StoredForwardDecode.budget n+StoredForwardFinal.budget n d
def pedgeBudget (n : Nat) := 3+2*StoredForwardDecode.budget n+n

theorem step_bound (D : StoredForwardTableBuild.Data n) (q r : Index n) (i : Fin d) :
    (step D q i r).2 ≤ stepBudget n d := by
  have ha := StoredForwardDecode.bound q
  have hb := StoredForwardDecode.bound r
  have hs := StoredForwardStep.step_bound D (StoredForwardDecode.decode q).1 (StoredForwardDecode.decode r).1 i
  simp only [step,stepBudget]; omega

theorem final_bound (D : StoredForwardTableBuild.Data n) (side : Side) (q : Index n) :
    (final (d := d) D side q).2 ≤ finalBudget n d := by
  have ha := StoredForwardDecode.bound q
  have hf := StoredForwardFinal.bound (d := d) D side (StoredForwardDecode.decode q).1
  simp only [final,finalBudget]; omega

theorem pedge_bound (side : Side) (q r : Index n) : (pedge side q r).2 ≤ pedgeBudget n := by
  have ha := StoredForwardDecode.bound q
  have hb := StoredForwardDecode.bound r
  have he := StoredForwardPedge.bound side (StoredForwardDecode.decode q).1 (StoredForwardDecode.decode r).1
  simp only [pedge,pedgeBudget]; omega

theorem start_bound (D : StoredForwardTableBuild.Data n) : (start D).2 ≤ n*(n+3)+n+9 := by
  have h := StoredForwardStateIndex.bound (some (some D.queryLeft,some D.queryRight))
  simp only [start]; omega
end NSSE.StoredIndexedForward
