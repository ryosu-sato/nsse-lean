import NSSE.SubtypeConstraints
import NSSE.HornCompiler

/-! # Executable exact support closure from the original finite constraints

The finite Horn kernel is used only for its unconditional saturation theorem.
Its n*n states are actual variable pairs; its rules are exactly reflexivity,
transitivity, and decomposition against the original lower/upper literal lists.
-/

namespace NSSE.FiniteSubtypeSupport

open SubtypeConstraints

variable {n d : Nat}

def pairId (x y : Fin n) : Nat := (finProdFinEquiv (x,y)).val

theorem pairId_lt (x y : Fin n) : pairId x y < n * n := (finProdFinEquiv (x,y)).isLt

theorem pairId_injective {x y u v : Fin n} (h : pairId x y = pairId u v) : x = u ∧ y = v := by
  have he : finProdFinEquiv (x,y) = finProdFinEquiv (u,v) := Fin.ext h
  exact Prod.mk.inj (finProdFinEquiv.injective he)

def terminal (n : Nat) (s : Nat) : Bool :=
  if hs : s < n * n then
    let p : Fin n × Fin n := finProdFinEquiv.symm ⟨s,hs⟩
    decide (p.1 = p.2)
  else false

theorem terminal_pair (x y : Fin n) : terminal n (pairId x y) = true ↔ x = y := by
  rw [terminal, dif_pos (pairId_lt x y)]
  change decide ((finProdFinEquiv.symm (finProdFinEquiv (x,y))).1 =
    (finProdFinEquiv.symm (finProdFinEquiv (x,y))).2) = true ↔ x = y
  simp only [Equiv.symm_apply_apply, decide_eq_true_eq]

def transRule (x y z : Fin n) : HornRule := ⟨pairId x z, [pairId x y, pairId y z]⟩
def decompRule (a b : BoundLiteral n d) (i : Fin d) : HornRule :=
  ⟨pairId (a.2 i) (b.2 i), [pairId a.1 b.1]⟩

def transRules (n : Nat) : List HornRule :=
  (List.finRange n).flatMap fun x => (List.finRange n).flatMap fun y =>
    (List.finRange n).map fun z => transRule x y z

def decompRules (φ : Constraints n d) : List HornRule :=
  φ.lower.flatMap fun a => φ.upper.flatMap fun b => (List.finRange d).map (decompRule a b)

theorem mem_transRules (r : HornRule) : r ∈ transRules n ↔ ∃ x y z : Fin n, transRule x y z = r := by
  simp [transRules]

theorem mem_decompRules (φ : Constraints n d) (r : HornRule) :
    r ∈ decompRules φ ↔ ∃ a ∈ φ.lower, ∃ b ∈ φ.upper, ∃ i, decompRule a b i = r := by
  simp [decompRules]

def compiler (φ : Constraints n d) : FiniteHornCompiler where
  stateCount := n * n
  terminal := terminal n
  rules := transRules n ++ decompRules φ

theorem support_derives (φ : Constraints n d) {x y : Fin n} (h : Support φ x y) :
    HornDerives (compiler φ) (pairId x y) := by
  induction h with
  | refl x => exact .terminal (pairId_lt x x) ((terminal_pair x x).mpr rfl)
  | @trans x y z hxy hyz ihxy ihyz =>
      apply HornDerives.rule (rule := transRule x y z)
      · exact List.mem_append.mpr (Or.inl ((mem_transRules _).mpr ⟨x,y,z,rfl⟩))
      · exact pairId_lt x z
      · intro s hs
        simp only [transRule, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact ihxy
        · exact ihyz
  | @decomp a b ha hb h i ih =>
      apply HornDerives.rule (rule := decompRule a b i)
      · exact List.mem_append.mpr (Or.inr ((mem_decompRules φ _).mpr ⟨a,ha,b,hb,i,rfl⟩))
      · exact pairId_lt (a.2 i) (b.2 i)
      · intro s hs
        have he : s = pairId a.1 b.1 := List.mem_singleton.mp hs
        subst s
        exact ih

def Meaning (φ : Constraints n d) (s : Nat) : Prop := ∃ x y, pairId x y = s ∧ Support φ x y

theorem meaning_pair (φ : Constraints n d) (x y : Fin n) : Meaning φ (pairId x y) ↔ Support φ x y := by
  constructor
  · rintro ⟨u,v,he,h⟩
    obtain ⟨rfl,rfl⟩ := pairId_injective he
    exact h
  · intro h; exact ⟨x,y,rfl,h⟩

theorem derives_meaning (φ : Constraints n d) {s : Nat} (h : HornDerives (compiler φ) s) : Meaning φ s := by
  induction h with
  | @terminal s hs ht =>
      let p : Fin n × Fin n := finProdFinEquiv.symm ⟨s,hs⟩
      have he : pairId p.1 p.2 = s := congrArg Fin.val (finProdFinEquiv.apply_symm_apply ⟨s,hs⟩)
      have hp : p.1 = p.2 := (terminal_pair p.1 p.2).mp (by rwa [he])
      refine ⟨p.1,p.2,he,?_⟩
      rw [← hp]
      exact .refl _
  | @rule r hr hlt children ih =>
      rcases List.mem_append.mp hr with ht | hd
      · obtain ⟨x,y,z,rfl⟩ := (mem_transRules _).mp ht
        exact ⟨x,z,rfl,.trans
          ((meaning_pair φ x y).mp (ih (pairId x y) (by simp [transRule])))
          ((meaning_pair φ y z).mp (ih (pairId y z) (by simp [transRule])))⟩
      · obtain ⟨a,ha,b,hb,i,rfl⟩ := (mem_decompRules φ _).mp hd
        exact ⟨a.2 i,b.2 i,rfl,.decomp ha hb
          ((meaning_pair φ a.1 b.1).mp (ih (pairId a.1 b.1) (by simp [decompRule]))) i⟩

theorem derives_iff (φ : Constraints n d) (x y : Fin n) :
    HornDerives (compiler φ) (pairId x y) ↔ Support φ x y :=
  ⟨fun h => (meaning_pair φ x y).mp (derives_meaning φ h), support_derives φ⟩

/-- The Boolean matrix is obtained after the kernel's proved n*n-round
saturation, not from a decidability assumption about syntactic support. -/
def table (φ : Constraints n d) : Fin n → Fin n → Bool :=
  let mask := hornSemantic (compiler φ)
  fun x y => maskBit mask (pairId x y)

theorem table_correct (φ : Constraints n d) (x y : Fin n) : table φ x y = true ↔ Support φ x y :=
  (hornSemantic_bit_iff_derives (compiler φ) (pairId x y) (pairId_lt x y)).trans (derives_iff φ x y)

def supportDecision (φ : Constraints n d) (x y : Fin n) : Decidable (Support φ x y) :=
  decidable_of_iff (table φ x y = true) (table_correct φ x y)

end NSSE.FiniteSubtypeSupport
