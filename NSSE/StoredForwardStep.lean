import NSSE.StoredForwardLookup

namespace NSSE.StoredForwardStep
open ForwardTableAutomaton StoredForwardLookup
variable {n d : Nat}

def move (D : StoredForwardTableBuild.Data n) (rev : Bool) : Token n → Fin d → Token n → Bool × Nat
  | some x,i,some y => let r := three (if rev then D.lower else D.upper) x.val i.val y.val; (r.1,1+r.2)
  | _,_,_ => (false,1)

def escape (D : StoredForwardTableBuild.Data n) : Token n → Token n → Bool × Nat
  | none,none => (false,1)
  | some x,none => let r := get false D.bot x.val; (r.1,1+r.2)
  | none,some y => let r := get false D.top y.val; (r.1,1+r.2)
  | some x,some y =>
    let b := get false D.bot x.val
    let t := get false D.top y.val
    let r := two D.le x.val y.val
    (b.1 || t.1 || r.1,3+b.2+t.2+r.2)

theorem upper_value (D : StoredForwardTableBuild.Data n) (u v : Token n) (i : Fin d) :
    (move D false u i v).1 = true ↔ upperMove (denote D) u i v := by
  cases u <;> cases v <;> simp [move,upperMove,denote]
theorem lower_value (D : StoredForwardTableBuild.Data n) (u v : Token n) (i : Fin d) :
    (move D true u i v).1 = true ↔ lowerMove (denote D) u i v := by
  cases u <;> cases v <;> simp [move,lowerMove,denote]
theorem escape_value (D : StoredForwardTableBuild.Data n) (u v : Token n) :
    (escape D u v).1 = true ↔ ForwardTableAutomaton.escape (denote (d := d) D) u v := by
  cases u <;> cases v <;> simp [escape,ForwardTableAutomaton.escape,denote,or_assoc]

theorem move_bound (D : StoredForwardTableBuild.Data n) (rev : Bool) (u v : Token n) (i : Fin d) :
    (move D rev u i v).2 ≤ 2*n+d+3 := by
  cases u with
  | none => simp [move]
  | some x => cases v with
    | none => simp [move]
    | some y =>
      have h := StoredForwardLookup.move_bound (if rev then D.lower else D.upper) x i y
      simp only [move]; omega

theorem escape_bound (D : StoredForwardTableBuild.Data n) (u v : Token n) :
    (escape D u v).2 ≤ 4*n+4 := by
  cases u with
  | none => cases v with
    | none => simp [escape]
    | some y => have h := get_bound false D.top y.val; have hy := y.isLt; simp only [escape]; omega
  | some x => cases v with
    | none => have h := get_bound false D.bot x.val; have hx := x.isLt; simp only [escape]; omega
    | some y =>
      have hb := get_bound false D.bot x.val
      have ht := get_bound false D.top y.val
      have hr := relation_bound D x y
      have hx := x.isLt; have hy := y.isLt
      simp only [escape]; omega

def step (D : StoredForwardTableBuild.Data n) : State n → Fin d → State n → Bool × Nat
  | none,_,none => (true,1)
  | none,_,some _ => (false,1)
  | some (u,v),_,none => let r := escape D u v; (r.1,1+r.2)
  | some (u,v),i,some (u',v') =>
    let a := move D false u i u'
    let b := move D true v i v'
    ((a.1 && v'.isNone) || (u'.isNone && b.1) || (a.1 && b.1),5+a.2+b.2)

theorem step_value (D : StoredForwardTableBuild.Data n) (q r : State n) (i : Fin d) :
    (step D q i r).1 = true ↔ ForwardTableAutomaton.step (denote D) q i r := by
  cases q with
  | none => cases r <;> simp [step,ForwardTableAutomaton.step]
  | some q => rcases q with ⟨u,v⟩; cases r with
    | none => exact escape_value D u v
    | some r =>
      rcases r with ⟨u',v'⟩
      simp only [step,ForwardTableAutomaton.step,Bool.or_eq_true,Bool.and_eq_true,upper_value,lower_value]
      cases u' <;> cases v' <;> simp [or_assoc]

theorem step_bound (D : StoredForwardTableBuild.Data n) (q r : State n) (i : Fin d) :
    (step D q i r).2 ≤ 4*n+2*d+11 := by
  cases q with
  | none => cases r <;> simp [step]
  | some q => rcases q with ⟨u,v⟩; cases r with
    | none => have h := escape_bound D u v; simp only [step]; omega
    | some r =>
      rcases r with ⟨u',v'⟩
      have ha := move_bound D false u u' i
      have hb := move_bound D true v v' i
      simp only [step]; omega
end NSSE.StoredForwardStep
