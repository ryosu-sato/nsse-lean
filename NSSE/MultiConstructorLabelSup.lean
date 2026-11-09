import NSSE.MultiConstructorTrees
import Mathlib.Data.Finset.Lattice.Fold

/-! Finite joins in the actual flat constructor-label order. Distinct
heads join to Top; no default constructor or inhabited signature is needed. -/
namespace NSSE.MultiConstructorTrees.Label
variable {H : Type*} [DecidableEq H]

def join : Label H → Label H → Label H
  | .bot, b => b
  | .top, _ => .top
  | .node h, .bot => .node h
  | .node _, .top => .top
  | .node h, .node k => if h = k then .node h else .top

instance : SemilatticeSup (Label H) where
  sup := join
  le_sup_left a b := by
    change Below a (join a b)
    cases a <;> cases b <;> simp_all [join,Below]
    split_ifs <;> simp_all
  le_sup_right a b := by
    change Below b (join a b)
    cases a <;> cases b <;> simp_all [join,Below]
    split_ifs <;> simp_all
  sup_le a b c := by
    change Below a c → Below b c → Below (join a b) c
    cases a <;> cases b <;> cases c <;> simp_all [join,Below]

theorem node_le_join_heads (S : Finset H) (h : H) (hh : h ∈ S) :
    (node h : Label H) ≤ S.sup node := Finset.le_sup hh

theorem join_heads_le (S : Finset H) (h : H) (hs : ∀ g ∈ S, g = h) :
    S.sup node ≤ (node h : Label H) := by
  apply Finset.sup_le
  intro g hg
  rw [hs g hg]

theorem join_heads_mono (S T : Finset H) (hst : S ⊆ T) :
    S.sup node ≤ T.sup (node : H → Label H) := by
  apply Finset.sup_le
  intro h hh
  exact Finset.le_sup (hst hh)

end NSSE.MultiConstructorTrees.Label
