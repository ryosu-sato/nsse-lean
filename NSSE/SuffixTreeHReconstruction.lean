import NSSE.SymbolicGuardedBlocks

/-! # Exact H reconstruction at a maximal shared reversed prefix

The v1451 reconstruction, using the existing raw H automaton. No bound
on words, finiteness assumption, or supplied semantic equivalence is used.
-/

namespace NSSE.SuffixTreeHReconstruction

open CanonicalConvolution GuardedBlockRelation

universe u v
variable {D : Type u} {Q : Type v}

def NoCommonHead (x y : List D) : Prop :=
  ∀ a, x.head? = some a → y.head? ≠ some a

def boundary (G : Data D Q) (q : PairState Q) (x y : List D) : Prop :=
  G.guard (x.head?.getD G.leftDefault) (y.head?.getD G.rightDefault) ∧
    ∃ i j, G.T.Runs G.leftStart x.reverse i ∧ G.left i q.1 ∧
      G.T.Runs G.rightStart y.reverse j ∧ G.right j q.2

theorem core_boundary (G : Data D Q) (q : PairState Q) (x y : List D)
    (h : NoCommonHead x y) : G.core q x y ↔ boundary G q x y := by
  constructor
  · rintro ⟨shared, px, py, hx, hy, hg, hl, hr⟩
    cases shared with
    | nil =>
      simp only [List.nil_append] at hx hy
      subst x
      subst y
      obtain ⟨i, hi, hleft⟩ := (G.marked_nil _ _ _ _).mp hl
      obtain ⟨j, hj, hright⟩ := (G.marked_nil _ _ _ _).mp hr
      exact ⟨hg, i, j, hi, hleft, hj, hright⟩
    | cons a rest =>
      exact False.elim (h a (by rw [hx]; rfl) (by rw [hy]; rfl))
  · rintro ⟨hg, i, j, hi, hl, hj, hr⟩
    exact ⟨[], x, y, rfl, rfl, hg,
      (G.marked_nil _ _ _ _).mpr ⟨i, hi, hl⟩,
      (G.marked_nil _ _ _ _).mpr ⟨j, hj, hr⟩⟩

def diagonal (z : List D) : List (Column D 2) :=
  z.map (fun a _ => some a)

theorem diagonal_canonical_append (z : List D) (w : List (Column D 2))
    (hw : Canonical w) : Canonical (diagonal z ++ w) := by
  induction z with
  | nil => exact hw
  | cons a z ih =>
    change present (fun _ : Fin 2 => some a) = true ∧ _
    refine ⟨(present_iff _).mpr ⟨0, rfl⟩, ?_, ?_⟩
    · intro i _; rfl
    · exact ih

theorem decode_diagonal_append (z : List D) (w : List (Column D 2)) (i : Fin 2) :
    CanonicalConvolution.decode (diagonal z ++ w) i = z ++ CanonicalConvolution.decode w i := by
  induction z with
  | nil => rfl
  | cons a z ih =>
    change a :: CanonicalConvolution.decode (diagonal z ++ w) i = a :: (z ++ CanonicalConvolution.decode w i)
    rw [ih]

theorem acceptFrom_append {A : Type*} (T : NSSE.NFA A Q) (q : Q) (x y : List A) :
    AcceptFrom T q (x ++ y) ↔ ∃ r, T.Runs q x r ∧ AcceptFrom T r y := by
  constructor
  · rintro ⟨s, hs, hf⟩
    obtain ⟨r, hx, hy⟩ := (runs_append_iff T q s x y).mp hs
    exact ⟨r, hx, s, hy, hf⟩
  · rintro ⟨r, hx, s, hy, hf⟩
    exact ⟨s, hx.append T hy, hf⟩

def residual (G : Data D Q) (q : State Q) (x y : List D) : Prop :=
  if q.1 then G.prefixMeaning q.2 x y else boundary G q.2 x y

theorem core_reconstruction (G : Data D Q) (q : PairState Q)
    (z x y : List D) (h : NoCommonHead x y) :
    G.core q (z ++ x) (z ++ y) ↔
      ∃ r, G.automaton.Runs (false, q) (diagonal z) r ∧ residual G r x y := by
  let w := encode ![x, y]
  have hw : Canonical w := canonical_encode _
  have hx : CanonicalConvolution.decode w 0 = x := by simp [w, decode_encode]
  have hy : CanonicalConvolution.decode w 1 = y := by simp [w, decode_encode]
  have hc := G.acceptFrom_correct (diagonal z ++ w)
    (diagonal_canonical_append z w hw) (false, q)
  have he : AcceptFrom G.automaton (false, q) (diagonal z ++ w) ↔
      G.core q (z ++ x) (z ++ y) := by
    simpa only [Data.meaning, Bool.false_eq_true, ↓reduceIte,
      decode_diagonal_append, hx, hy] using hc
  rw [← he, acceptFrom_append]
  apply exists_congr
  intro r
  apply and_congr_right
  intro _
  rw [G.acceptFrom_correct w hw r]
  rcases r with ⟨phase, pair⟩
  cases phase
  · simpa only [Data.meaning, residual, Bool.false_eq_true, ↓reduceIte, hx, hy]
      using core_boundary G pair x y h
  · simp only [Data.meaning, residual, ↓reduceIte, hx, hy]

/-- The entries of the diagonal transfer matrix compose on edge labels. -/
theorem diagonal_runs_append (G : Data D Q) (q r : State Q) (x y : List D) :
    G.automaton.Runs q (diagonal (x ++ y)) r ↔
      ∃ s, G.automaton.Runs q (diagonal x) s ∧
        G.automaton.Runs s (diagonal y) r := by
  simpa only [diagonal, List.map_append] using
    runs_append_iff G.automaton q r (diagonal x) (diagonal y)

/-- Exact pointwise preservation; the transfer equalities quantify over
all states, and the two boundary letters retain their actual identities. -/
theorem core_summary_congr (G : Data D Q) (q : PairState Q)
    (z x y z' x' y' : List D)
    (h : NoCommonHead x y) (h' : NoCommonHead x' y')
    (hz : ∀ a b, G.automaton.Runs a (diagonal z) b ↔
      G.automaton.Runs a (diagonal z') b)
    (hx : ∀ a b, G.T.Runs a x.reverse b ↔ G.T.Runs a x'.reverse b)
    (hy : ∀ a b, G.T.Runs a y.reverse b ↔ G.T.Runs a y'.reverse b)
    (hheadx : x.head? = x'.head?) (hheady : y.head? = y'.head?) :
    G.core q (z ++ x) (z ++ y) ↔ G.core q (z' ++ x') (z' ++ y') := by
  rw [core_reconstruction G q z x y h, core_reconstruction G q z' x' y' h']
  apply exists_congr
  intro r
  apply and_congr (hz _ _)
  simp only [residual, Data.prefixMeaning, boundary, hx, hy, hheadx, hheady]

/-- The reconstruction applies to the actual row relation, including its
final separator and its predecessor defaults; it is not a new interface. -/
theorem literalH_reconstruction
    {L : FirstOrder.Language} {P : Type*} {n : Nat}
    (R : SymbolicGuardedBlocks.Row L P n) (e : SymbolicGuardedBlocks.Ends n)
    (seed last : P) (first : Bool) [L.Structure D] (p : P → D)
    (z x y : List D) (h : NoCommonHead x y) :
    R.LiteralH e seed last first p (z ++ x).reverse (z ++ y).reverse ↔
      ∃ q r, (R.semantics e seed last first p).finish q ∧
        (R.semantics e seed last first p).automaton.Runs (false, q) (diagonal z) r ∧
        residual (R.semantics e seed last first p) r x y := by
  rw [← R.H_iff_literal, R.H_iff_core]
  simp only [List.reverse_reverse]
  simp_rw [core_reconstruction _ _ z x y h]
  constructor
  · rintro ⟨q, hf, r, hr, hb⟩
    exact ⟨q, r, hf, hr, hb⟩
  · rintro ⟨q, r, hf, hr, hb⟩
    exact ⟨q, hf, r, hr, hb⟩

end NSSE.SuffixTreeHReconstruction
