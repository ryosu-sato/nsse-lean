import NSSE.ExactGuardedRunSize

/-! # Identity transitions erase empty padding columns exactly -/

namespace NSSE.SkipEmptyColumns

open FirstOrder FirstOrder.Language SymbolicAutomata ConvolutionShapes GuardedBlockRelation

universe u v w

def skip {α Q : Type*} (A : NSSE.NFA α Q) (keep : α → Bool) : NSSE.NFA α Q where
  start := A.start
  accept := A.accept
  step q a r := if keep a then A.step q a r else q = r

theorem runs_cons_iff {α Q : Type*} (A : NSSE.NFA α Q) (q r : Q) (a : α) (w : List α) :
    A.Runs q (a::w) r ↔ ∃ s, A.step q a s ∧ A.Runs s w r := by
  constructor
  · intro h
    cases h with
    | cons hs hr => exact ⟨_, hs, hr⟩
  · rintro ⟨s, hs, hr⟩
    exact .cons hs hr

theorem skip_runs {α Q : Type*} (A : NSSE.NFA α Q) (keep : α → Bool)
    (w : List α) (q r : Q) : (skip A keep).Runs q w r ↔ A.Runs q (w.filter keep) r := by
  induction w generalizing q with
  | nil => simp [runs_nil_iff]
  | cons a w ih =>
    simp only [runs_cons_iff, ih]
    cases hk : keep a
    · simp [skip, hk, ih]
    · simp [skip, hk, ih, runs_cons_iff]

theorem skip_accepts {α Q : Type*} (A : NSSE.NFA α Q) (keep : α → Bool) (w : List α) :
    (skip A keep).Accepts w ↔ A.Accepts (w.filter keep) := by
  simp only [NSSE.NFA.Accepts, skip_runs]
  rfl

variable {L : FirstOrder.Language.{u,v}} {P : Type w} {n k : Nat}

def automaton (A : WordAutomaton L P n k) : WordAutomaton L P n k where
  initial := A.initial
  final := A.final
  silent := A.silent
  step s q r := if maskPresent (mask s) then A.step s q r else if q = r then ⊤ else ⊥

theorem dataInterpret_eq (A : WordAutomaton L P n k) {D : Type*} [L.Structure D] (p : P → D) :
    (automaton A).dataInterpret p = skip (A.dataInterpret p) (fun c => maskPresent (mask c.1)) := by
  unfold Automaton.dataInterpret automaton skip
  congr 1
  funext q c r
  cases h : maskPresent (mask c.1)
  · by_cases hqr : q = r <;> simp [h, hqr]
  · simp [h]

theorem data_accepts (A : WordAutomaton L P n k) {D : Type*} [L.Structure D] (p : P → D)
    (w : List (Sparse D k)) :
    ((automaton A).dataInterpret p).Accepts w ↔
      (A.dataInterpret p).Accepts (w.filter (fun c => maskPresent (mask c.1))) := by
  rw [dataInterpret_eq, skip_accepts]

theorem step_qf (A : WordAutomaton L P n k) (hs : ∀ s q r, (A.step s q r).IsQF)
    (s : Shape k) (q r : Fin n) : ((automaton A).step s q r).IsQF := by
  change (if maskPresent (mask s) then A.step s q r else if q = r then ⊤ else ⊥).IsQF
  split
  · exact hs s q r
  · split
    · exact BoundedFormula.IsQF.top
    · exact BoundedFormula.isQF_bot

theorem step_nodes_le {G : Nat} (A : WordAutomaton L P n k)
    (hs : ∀ s q r, ExactReachabilitySize.nodes (A.step s q r) ≤ G) (hG : 3 ≤ G)
    (s : Shape k) (q r : Fin n) : ExactReachabilitySize.nodes ((automaton A).step s q r) ≤ G := by
  change ExactReachabilitySize.nodes (if maskPresent (mask s) then A.step s q r else if q = r then ⊤ else ⊥) ≤ G
  split
  · exact hs s q r
  · split
    · exact hG
    · exact Nat.le_trans (by decide : 1 ≤ 3) hG

theorem filter_dense {D : Type*} (w : List (Sparse D k)) :
    (w.filter (fun c => maskPresent (mask c.1))).map toDense =
      (w.map toDense).filter CanonicalConvolution.present := by
  induction w with
  | nil => rfl
  | cons c w ih => cases h : maskPresent (mask c.1) <;> simp [h, ih]

theorem dense_filter_project {D : Type*} (w : List (CanonicalConvolution.Column D k)) :
    w.filter CanonicalConvolution.present = CanonicalConvolution.project id w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    unfold CanonicalConvolution.project at ih
    cases h : CanonicalConvolution.present c <;>
      simp [CanonicalConvolution.project, CanonicalConvolution.projectColumn, h, ih, Function.comp_def]

theorem decode_filter {D : Type*} (w : List (CanonicalConvolution.Column D k)) :
    CanonicalConvolution.decode (w.filter CanonicalConvolution.present) = CanonicalConvolution.decode w := by
  rw [dense_filter_project, CanonicalConvolution.decode_project]
  rfl

end NSSE.SkipEmptyColumns
