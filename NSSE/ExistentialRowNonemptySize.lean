import NSSE.DirectExistentialRankCompiler

/-! # Primitive sizes of the actual seed and nonempty existential packages -/

namespace NSSE.ExistentialRowNonemptySize

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks ExistentialFormulaPackage
open ArrayAtomExistentialPackages ExistentialRowNonempty ExactReachabilitySize DirectRowBooleanSize

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {n B : Nat}

theorem any_le (m : Nat) (f : Fin m → Package L P) (h : ∀ i, nodes (f i).toFormula ≤ B) :
    nodes (anyPackage m f).toFormula ≤ 1+m*(3+B) := by
  have hl (as : List (Package L P)) (ha : ∀ A ∈ as, nodes A.toFormula ≤ B) :
      nodes (as.foldr Package.disj (Package.atom ⊥ BoundedFormula.isQF_bot)).toFormula ≤ 1+as.length*(3+B) := by
    induction as with
    | nil => simp [Package.nodes_atom, nodes]
    | cons A as ih =>
      have ht := ih (fun C hc => ha C (by simp [hc]))
      have hh := ha A (by simp)
      simp only [List.foldr_cons, Package.nodes_disj, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  have hh := hl ((List.finRange m).map f) (by
    intro A ha; obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha; exact h i)
  simpa only [anyPackage, List.length_map, List.length_finRange] using hh

theorem eliminate_le (W : Fin n → Fin n → Package L P) (h : ∀ a b, nodes (W a b).toFormula ≤ B)
    (ts : List (Fin n)) (a b : Fin n) :
    nodes (ExistentialRowNonempty.eliminate W ts a b).toFormula+4 ≤ (B+4)*3^ts.length := by
  induction ts generalizing a b with
  | nil => simpa only [ExistentialRowNonempty.eliminate, List.length_nil, pow_zero, Nat.mul_one] using Nat.add_le_add_right (h a b) 4
  | cons t ts ih =>
    have h₁ := ih a b; have h₂ := ih a t; have h₃ := ih t b
    simp only [ExistentialRowNonempty.eliminate, Package.nodes_disj, Package.nodes_conj, List.length_cons, Nat.pow_succ]
    nlinarith

theorem reach_le (W : Fin n → Fin n → Package L P) (h : ∀ a b, nodes (W a b).toFormula ≤ B)
    (a b : Fin n) : nodes (reachPackage W a b).toFormula ≤ (B+10)*3^n := by
  have hh := eliminate_le (B := B+6)
    (fun a b => Package.disj (Package.atom (if a=b then ⊤ else ⊥)
      (by split; exact BoundedFormula.IsQF.top; exact BoundedFormula.isQF_bot)) (W a b)) (by
        intro a b
        rw [Package.nodes_disj, Package.nodes_atom]
        have hw := h a b
        split <;> simp only [nodes, BoundedFormula.not] <;> omega)
    (List.finRange n) a b
  simp only [List.length_finRange] at hh
  change nodes (reachPackage W a b).toFormula+4 ≤ _ at hh
  rw [show B+6+4 = B+10 by omega] at hh
  omega

theorem data_le (R : Row L P n) (hq : RowQF R) (h : Fields R B) (q r : Fin n) :
    nodes (dataPackage R hq q r).toFormula ≤ B+5 := by
  simp only [dataPackage, Package.nodes_bind, Package.nodes_atom]
  have := h.data q r
  omega

theorem edge_le (R : Row L P n) (hq : RowQF R) (h : Fields R B) (q r : Fin n) :
    nodes (edgePackage R hq q r).toFormula ≤ B+13 := by
  have hh := any_le 1 (fun _ => dataPackage R hq q r) (fun _ => data_le R hq h q r)
  simp only [edgePackage, Package.nodes_disj, Package.nodes_atom, nodes]
  omega

def seedBound (n B : Nat) := 1+n*(4+n*(18+3*B))
def nonemptyBound (n B : Nat) := 1+n*(4+n*(13+2*B+(B+23)*3^n))

theorem seed_le (R : Row L P n) (hq : RowQF R) (h : Fields R B) :
    nodes (seedOnly R hq).toFormula ≤ seedBound n B := by
  have hc (q r : Fin n) : nodes (Package.conj (Package.atom (R.initial q) (hq.initial q))
      (Package.conj (dataPackage R hq q r) (Package.atom (R.final r) (hq.final r)))).toFormula ≤ 15+3*B := by
    simp only [Package.nodes_conj, Package.nodes_atom]
    have := h.initial q; have := h.final r; have := data_le R hq h q r; omega
  have hh := any_le n _ (fun q => any_le n _ (hc q))
  simpa only [seedOnly, seedBound, show 3+(15+3*B) = 18+3*B by omega,
    show 3+(1+n*(18+3*B)) = 4+n*(18+3*B) by omega] using hh

theorem nonempty_le (R : Row L P n) (hq : RowQF R) (h : Fields R B) :
    nodes (nonempty R hq).toFormula ≤ nonemptyBound n B := by
  have hc (q r : Fin n) : nodes (Package.conj (Package.atom (R.initial q) (hq.initial q))
      (Package.conj (reachPackage (edgePackage R hq) q r) (Package.atom (R.final r) (hq.final r)))).toFormula ≤
      10+2*B+(B+23)*3^n := by
    simp only [Package.nodes_conj, Package.nodes_atom]
    have := h.initial q; have := h.final r
    have hh := reach_le (edgePackage R hq) (edge_le R hq h) q r
    have he : B+13+10 = B+23 := by omega
    rw [he] at hh
    omega
  have hh := any_le n _ (fun q => any_le n _ (hc q))
  convert hh using 1
  unfold nonemptyBound
  ring

end NSSE.ExistentialRowNonemptySize
