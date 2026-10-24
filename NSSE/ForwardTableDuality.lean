import NSSE.SubtypeDuality

/-! # Literal automaton duality, including FINAL-target capped certificates

The state involution is conjugated through the ACTUAL stateEquiv encoding.
No epsilon edges, reversed words, missing-target P-edges, or SAT premise.
-/

namespace NSSE.ForwardTableDuality

open ForwardTableAutomaton ForwardCapAutomaton SubtypeDuality

variable {n d : Nat}

def dual (D : Tables n d) : Tables n d where
  queryLeft := D.queryRight
  queryRight := D.queryLeft
  upper := D.lower
  lower := D.upper
  bot := D.top
  top := D.bot
  le := fun a b => D.le b a

@[simp] theorem dual_twice (D : Tables n d) : dual (dual D) = D := by cases D; rfl

def swap : State n → State n | none => none | some (u,v) => some (v,u)

@[simp] theorem swap_twice (q : State n) : swap (swap q) = q := by
  cases q with | none => rfl | some q => cases q; rfl

@[simp] theorem upper_dual (D : Tables n d) (u v : Token n) (i : Fin d) :
    upperMove (dual D) u i v ↔ lowerMove D u i v := by
  cases u <;> cases v <;> rfl

@[simp] theorem lower_dual (D : Tables n d) (u v : Token n) (i : Fin d) :
    lowerMove (dual D) u i v ↔ upperMove D u i v := by
  cases u <;> cases v <;> rfl

@[simp] theorem escape_dual (D : Tables n d) (u v : Token n) :
    escape (dual D) v u ↔ escape D u v := by
  cases u <;> cases v <;> simp [escape, dual, or_comm, or_left_comm, or_assoc]

@[simp] theorem step_swap (D : Tables n d) (q r : State n) (i : Fin d) :
    step (dual D) (swap q) i (swap r) ↔ step D q i r := by
  cases q with
  | none => cases r <;> rfl
  | some q =>
      rcases q with ⟨u,v⟩
      cases r with
      | none => exact escape_dual D u v
      | some r =>
          rcases r with ⟨u',v'⟩
          simp only [swap, step, upper_dual, lower_dual]
          tauto

@[simp] theorem final_swap (D : Tables n d) (s : Side) (q : State n) :
    final (dual D) (opposite s) (swap q) ↔ final D s q := by
  cases q with
  | none => rfl
  | some q =>
      rcases q with ⟨u,v⟩
      cases s <;> simp only [swap, final, opposite, escape_dual, upper_dual, lower_dual]

@[simp] theorem pedge_swap (s : Side) (q r : State n) :
    pedge (opposite s) (swap q) (swap r) ↔ pedge s q r := by
  cases q with
  | none => cases s <;> cases r <;> rfl
  | some q =>
      rcases q with ⟨u,v⟩
      cases r with
      | none => cases s <;> cases u <;> cases v <;> rfl
      | some r =>
          rcases r with ⟨u',v'⟩
          cases s <;> cases u <;> cases v <;> cases u' <;> cases v' <;> rfl

def encoded (q : Fin ((n+1)*(n+1)+1)) : Fin ((n+1)*(n+1)+1) :=
  stateEquiv n (swap ((stateEquiv n).symm q))

@[simp] theorem encoded_twice (q : Fin ((n+1)*(n+1)+1)) : encoded (encoded q) = q := by
  simp [encoded]

@[simp] theorem encoded_start (D : Tables n d) (s : Side) :
    encoded (compile D s).start = (compile (dual D) (opposite s)).start := by
  simp [encoded, compile, swap, dual]

@[simp] theorem encoded_step (D : Tables n d) (s : Side) (q r) (i : Fin d) :
    (compile (dual D) (opposite s)).step (encoded q) i (encoded r) ↔ (compile D s).step q i r := by
  simp only [compile, encoded, Equiv.symm_apply_apply, step_swap]

@[simp] theorem encoded_final (D : Tables n d) (s : Side) (q) :
    (compile (dual D) (opposite s)).final (encoded q) ↔ (compile D s).final q := by
  simp only [compile, encoded, Equiv.symm_apply_apply, final_swap]

@[simp] theorem encoded_pedge (D : Tables n d) (s : Side) (q r) :
    (compile (dual D) (opposite s)).pedge (encoded q) (encoded r) ↔ (compile D s).pedge q r := by
  simp only [compile, encoded, Equiv.symm_apply_apply, pedge_swap]

theorem run_dual (D : Tables n d) (s : Side) {q r} {w : List (Fin d)}
    (h : (ordinary (compile D s)).Runs q w r) :
    (ordinary (compile (dual D) (opposite s))).Runs (encoded q) w (encoded r) := by
  induction h with
  | nil q => exact .nil _
  | cons hs _ ih => exact .cons ((encoded_step D s _ _ _).mpr hs) ih

theorem ordinary_dual (D : Tables n d) (s : Side) (w : List (Fin d))
    (h : (ordinary (compile D s)).Accepts w) :
    (ordinary (compile (dual D) (opposite s))).Accepts w := by
  obtain ⟨q,hr,hf⟩ := (ordinary_accepts _ w).mp h
  apply (ordinary_accepts _ w).mpr
  refine ⟨encoded q, ?_, (encoded_final D s q).mpr hf⟩
  simpa only [encoded_start] using run_dual D s hr

theorem capped_dual (D : Tables n d) (s : Side) (w : List (Fin d))
    (h : Capped (compile D s) w) : Capped (compile (dual D) (opposite s)) w := by
  obtain ⟨anchor,tail,q,source,root,k,he,ha,hq,hr,hp,hpref⟩ := h
  refine ⟨anchor,tail,encoded q,encoded source,root,k,he,?_,
    (encoded_final D s q).mpr hq,run_dual D s hr,(encoded_pedge D s source q).mpr hp,hpref⟩
  simpa only [encoded_start] using run_dual D s ha

theorem accepts_to_dual (D : Tables n d) (s : Side) (w : List (Fin d))
    (h : Accepts (compile D s) w) : Accepts (compile (dual D) (opposite s)) w :=
  h.elim (fun h => Or.inl (ordinary_dual D s w h)) (fun h => Or.inr (capped_dual D s w h))

@[simp] theorem accepts_dual (D : Tables n d) (s : Side) (w : List (Fin d)) :
    Accepts (compile (dual D) (opposite s)) w ↔ Accepts (compile D s) w := by
  constructor
  · intro h; simpa only [dual_twice, opposite_opposite] using accepts_to_dual (dual D) (opposite s) w h
  · exact accepts_to_dual D s w

@[simp] theorem universal_dual (D : Tables n d) (s : Side) :
    Universal (compile (dual D) (opposite s)) ↔ Universal (compile D s) := by
  simp only [Universal, accepts_dual]

theorem decideUniversal_dual (D : Tables n d) (s : Side) :
    ForwardTableAutomaton.decideUniversal (dual D) (opposite s) =
      ForwardTableAutomaton.decideUniversal D s := by
  have h := (ForwardTableAutomaton.decideUniversal_correct (dual D) (opposite s)).trans
    ((universal_dual D s).trans (ForwardTableAutomaton.decideUniversal_correct D s).symm)
  cases h₁ : ForwardTableAutomaton.decideUniversal (dual D) (opposite s) <;>
    cases h₂ : ForwardTableAutomaton.decideUniversal D s <;> simp_all

end NSSE.ForwardTableDuality
