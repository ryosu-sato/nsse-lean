import NSSE.PaddedAlphabetDFA

/-! Concrete cap input alphabet padding, including empty and singleton sources. -/

namespace NSSE.PaddedCapInput

open FiniteSOARankDecision FiniteCapFrontEnd PaddedAlphabetDFA

variable {d : Nat}

def foreignRaw : DFA (Fin (d+2)) Bool where
  start := false
  step b x := b || (letter x).isNone
  accept b := b = true

instance foreignAccept : DecidablePred (foreignRaw (d := d)).accept :=
  fun b => inferInstanceAs (Decidable (b = true))

theorem foreign_run (b : Bool) (ys : List (Fin (d+2))) :
    foreignRaw.runFrom b ys = (b || (PaddedAlphabetDFA.decode ys).isNone) := by
  induction ys generalizing b with
  | nil => cases b <;> rfl
  | cons y ys ih =>
    rw [DFA.runFrom_cons, ih]
    change ((b || (letter y).isNone) || (PaddedAlphabetDFA.decode ys).isNone) = _
    cases hl : letter y <;> cases hd : PaddedAlphabetDFA.decode ys <;> cases b <;> simp [PaddedAlphabetDFA.decode, hl, hd]

def foreignDFA : InputDFA (Fin (d+2)) := FiniteCapTerminal.reindex foreignRaw finTwoEquiv.symm

theorem foreign_count : (foreignDFA (d := d)).count = 2 := rfl

theorem foreign_accepts (ys : List (Fin (d+2))) :
    foreignDFA.automaton.Accepts ys ↔ CapAlphabetPadding.foreign embed ys := by
  rw [foreignDFA, FiniteCapTerminal.reindex_accepts]
  change foreignRaw.runFrom false ys = true ↔ _
  rw [foreign_run]
  simp only [Bool.false_or, CapAlphabetPadding.foreign, ← decode_eq_some]
  cases PaddedAlphabetDFA.decode ys <;> simp

def liftComponent (c : Component (Fin d)) : Component (Fin (d+2)) := ⟨lift c.left,lift c.right⟩

def pad (E : Input (Fin d)) : Input (Fin (d+2)) where
  rows := E.rows.map liftComponent
  routes := foreignDFA :: E.routes.map lift

theorem lift_language (A : InputDFA (Fin d)) :
    (lift A).automaton.language = CapAlphabetImage.image embed A.automaton.language :=
  funext (fun w => propext (lift_accepts A w))

theorem foreign_language : (foreignDFA (d := d)).automaton.language = CapAlphabetPadding.foreign embed :=
  funext (fun w => propext (foreign_accepts w))

theorem pad_denote (E : Input (Fin d)) :
    (pad E).denote = CapAlphabetPadding.pad embed E.denote := by
  simp only [Input.denote, pad, List.map_cons, List.map_map, Function.comp_def,
    Component.denote, CapComponent.ofDFA, liftComponent, lift_language, foreign_language,
    CapAlphabetPadding.pad, CapAlphabetImage.component]

theorem uncovered_iff (E : Input (Fin d)) (ys : List (Fin (d+2))) :
    (pad E).denote.Uncovered ys ↔
      ∃ xs : List (Fin d), xs.map embed = ys ∧ E.denote.Uncovered xs := by
  rw [pad_denote]
  exact CapAlphabetPadding.uncovered_iff embed embed_injective E.denote ys

theorem exists_uncovered_iff (E : Input (Fin d)) :
    (∃ ys, (pad E).denote.Uncovered ys) ↔ ∃ xs, E.denote.Uncovered xs := by
  rw [pad_denote]
  exact CapAlphabetPadding.exists_uncovered_iff embed embed_injective E.denote

/-- All finite alphabets are now semantically accepted by the counted cap entrypoint. -/
def decide (E : Input (Fin d)) : Bool × Nat := CountedCapEvaluation.decide (pad E)

theorem decide_correct (E : Input (Fin d)) :
    (decide E).1 = true ↔ ∃ xs, E.denote.Uncovered xs := by
  haveI : Nontrivial (Fin (d+2)) := ⟨⟨0,1,by intro h; have h' := congrArg (fun x : Fin (d+2) => x.val) h; change 0 = 1 at h'; omega⟩⟩
  exact (CountedCapEvaluation.decide_correct (pad E)).trans (exists_uncovered_iff E)

theorem route_sum (routes : List (InputDFA (Fin d))) :
    ((routes.map lift).map (fun A => A.count+1)).sum =
      (routes.map (fun A => A.count+1)).sum+routes.length := by
  induction routes with
  | nil => rfl
  | cons A routes ih => simp only [List.map_cons, List.sum_cons, lift_count, List.length_cons, ih]; omega

theorem row_sum (rows : List (Component (Fin d))) :
    ((rows.map liftComponent).map (fun c => 2*c.left.count+c.right.count)).sum =
      (rows.map (fun c => 2*c.left.count+c.right.count)).sum+3*rows.length := by
  induction rows with
  | nil => rfl
  | cons c rows ih =>
    simp only [List.map_cons, List.sum_cons, liftComponent, lift_count, List.length_cons, ih]
    omega

theorem size_eq (E : Input (Fin d)) :
    ExplicitCapTerminalTower.size (pad E) =
      ExplicitCapTerminalTower.size E+E.routes.length+3*E.rows.length+3 := by
  simp only [ExplicitCapTerminalTower.size, pad, List.map_cons, List.sum_cons,
    foreign_count, route_sum, row_sum, List.length_map]
  omega

theorem route_length_le (routes : List (InputDFA (Fin d))) :
    routes.length ≤ (routes.map (fun A => A.count+1)).sum := by
  induction routes with
  | nil => simp
  | cons A routes ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega

theorem size_bound (E : Input (Fin d)) :
    ExplicitCapTerminalTower.size (pad E) ≤ 5*ExplicitCapTerminalTower.size E+3 := by
  rw [size_eq]
  have hr := route_length_le E.routes
  unfold ExplicitCapTerminalTower.size
  omega

theorem decide_bound (E : Input (Fin d)) :
    (decide E).2 ≤ DirectRankStateTower.tower 5 (51215*ExplicitCapTerminalTower.size E+3418*d+47829) := by
  have h := CountedCapEvaluation.decide_explicit_bound (pad E)
  have hs := size_bound E
  apply h.trans
  apply DirectRankFormulaTower.tower_mono 5
  omega

end NSSE.PaddedCapInput
