import NSSE.CommonCutWordReplacement

/-! # Common cuts preserve all pairwise H decompositions -/

namespace NSSE.CommonCutPairPreservation

open GuardedBlockRelation SuffixTreeHReconstruction CommonCutRefinement CommonCutWordReplacement
universe u v
variable {D : Type u} {Q : Type v} [DecidableEq D]

def commonLength : List D → List D → Nat
  | a :: x, b :: y => if a = b then commonLength x y + 1 else 0
  | _, _ => 0

theorem common_spec (x y : List D) :
    commonLength x y ≤ x.length ∧ commonLength x y ≤ y.length ∧
      x.take (commonLength x y) = y.take (commonLength x y) ∧
      NoCommonHead (x.drop (commonLength x y)) (y.drop (commonLength x y)) := by
  induction x generalizing y with
  | nil => simp [commonLength, NoCommonHead]
  | cons a x ih =>
    cases y with
    | nil => simp [commonLength, NoCommonHead]
    | cons b y =>
      by_cases h : a = b
      · subst b
        obtain ⟨hx, hy, ht, hh⟩ := ih y
        simp only [commonLength, ↓reduceIte, List.length_cons, List.take_succ_cons,
          List.drop_succ_cons]
        exact ⟨by omega, by omega, congrArg (List.cons a) ht, hh⟩
      · simp [commonLength, h, NoCommonHead, eq_comm]

theorem core_replace (G : Data D Q) (F : List D → List D)
    (hhead : ∀ w, (F w).head? = w.head?)
    (hdata : ∀ w q r, G.T.Runs q (F w).reverse r ↔ G.T.Runs q w.reverse r)
    (hdiag : ∀ w q r, G.automaton.Runs q (diagonal (F w)) r ↔
      G.automaton.Runs q (diagonal w) r)
    (gs : List Nat) (x y : List D) (hc : Cut gs (commonLength x y)) (q : PairState Q) :
    G.core q (replace F gs x) (replace F gs y) ↔ G.core q x y := by
  obtain ⟨hlx, _, heq, hno⟩ := common_spec x y
  obtain ⟨before, after, hgs, hsum⟩ := cut_split gs (commonLength x y) hc
  let z := x.take (commonLength x y)
  let a := x.drop (commonLength x y)
  let b := y.drop (commonLength x y)
  have hz : z.length = before.sum := by
    simp only [z, List.length_take, Nat.min_eq_left hlx, hsum]
  have hx : z ++ a = x := List.take_append_drop _ _
  have hy : z ++ b = y := by
    change x.take (commonLength x y) ++ b = y
    rw [heq]
    exact List.take_append_drop _ _
  have hF0 : F [] = [] := List.head?_eq_none_iff.mp (hhead [])
  have hrx : replace F gs x = replace F before z ++ replace F after a := by
    rw [hgs, ← hx]
    exact replace_split F hF0 before after z a hz
  have hry : replace F gs y = replace F before z ++ replace F after b := by
    rw [hgs, ← hy]
    exact replace_split F hF0 before after z b hz
  have ha := replace_head F hhead after a
  have hb := replace_head F hhead after b
  have hn : NoCommonHead (replace F after a) (replace F after b) := by
    intro d hd he
    exact hno d (ha.symm.trans hd) (hb.symm.trans he)
  rw [hrx, hry, ← hx, ← hy]
  exact core_summary_congr G q (replace F before z) (replace F after a) (replace F after b)
    z a b hn hno (replace_diagonal_runs G F hdiag before z)
    (replace_reverse_runs G.T F hdata after a) (replace_reverse_runs G.T F hdata after b) ha hb

def requests {q : Nat} (w : Fin q → List D) : List Nat :=
  (List.finRange q).flatMap fun i => (List.finRange q).map fun j => commonLength (w i) (w j)

theorem requests_length {q : Nat} (w : Fin q → List D) : (requests w).length = q*q := by
  simp [requests, List.length_flatMap]

theorem pair_cut {q : Nat} (w : Fin q → List D) (i j : Fin q) :
    Cut (build (requests w)) (commonLength (w i) (w j)) := by
  apply mem_cut_build
  apply List.mem_flatMap.mpr
  exact ⟨i, List.mem_finRange i, List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩⟩

theorem equality_replace (F : List D → List D)
    (hhead : ∀ w, (F w).head? = w.head?) (gs : List Nat) (x y : List D)
    (hc : Cut gs (commonLength x y)) : replace F gs x = replace F gs y ↔ x = y := by
  constructor
  · intro he
    obtain ⟨hlx, _, ht, hn⟩ := common_spec x y
    obtain ⟨before, after, hgs, hsum⟩ := cut_split gs (commonLength x y) hc
    let z := x.take (commonLength x y)
    let a := x.drop (commonLength x y)
    let b := y.drop (commonLength x y)
    have hz : z.length = before.sum := by
      simp only [z, List.length_take, Nat.min_eq_left hlx, hsum]
    have hx : z ++ a = x := List.take_append_drop _ _
    have hy : z ++ b = y := by
      change x.take (commonLength x y) ++ b = y
      rw [ht]
      exact List.take_append_drop _ _
    have hF0 : F [] = [] := List.head?_eq_none_iff.mp (hhead [])
    have hrx : replace F gs x = replace F before z ++ replace F after a := by
      rw [hgs, ← hx]
      exact replace_split F hF0 before after z a hz
    have hry : replace F gs y = replace F before z ++ replace F after b := by
      rw [hgs, ← hy]
      exact replace_split F hF0 before after z b hz
    rw [hrx, hry] at he
    have hr := congrArg List.head? (List.append_cancel_left he)
    rw [replace_head F hhead, replace_head F hhead] at hr
    have ha : a = [] := by
      cases ha : a with
      | nil => rfl
      | cons d ds =>
        exact False.elim (hn d (by change a.head? = some d; rw [ha]; rfl)
          (by change b.head? = some d; rw [← hr, ha]; rfl))
    have hb : b = [] := List.head?_eq_none_iff.mp (hr.symm.trans (by rw [ha]; rfl))
    simp only [ha, hb, List.append_nil] at hx hy
    exact hx.symm.trans hy
  · intro h; rw [h]

end NSSE.CommonCutPairPreservation
