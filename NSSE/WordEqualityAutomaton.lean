import NSSE.ConvolutionShapes

/-! # Literal word equality, not an assumed automatic relation -/

namespace NSSE.WordEqualityAutomaton

open FirstOrder FirstOrder.Language SymbolicAutomata ConvolutionShapes

universe u v w
variable {L : FirstOrder.Language.{u, v}} {P : Type w} {k : Nat}

def localColumns (g : (s : Shape k) → L.Formula (P ⊕ Fin (arity k s))) :
    WordAutomaton L P 1 k where
  initial _ := ⊤
  final _ := ⊤
  silent _ _ := ⊥
  step s _ _ := g s

theorem localColumns_correct (g : (s : Shape k) → L.Formula (P ⊕ Fin (arity k s)))
    {D : Type*} [L.Structure D] (p : P → D) (w : List (Sparse D k)) :
    (localColumns g).Accepts p w ↔ ∀ c ∈ w, (g c.1).Realize (Sum.elim p c.2) := by
  rw [(localColumns g).accepts_iff_data_of_noSilent p (by intro q r; simp [localColumns]) w]
  constructor
  · rintro ⟨q, r, hq, hrun, hr⟩
    clear hq hr
    induction hrun with
    | nil => simp
    | @cons q r s c w hstep _ ih =>
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hstep
        · exact ih x hx
  · intro hw
    have hrun : ((localColumns g).dataInterpret p).Runs 0 w 0 := by
      induction w with
      | nil => exact .nil 0
      | cons c w ih =>
          exact .cons (hw c (List.mem_cons_self)) (ih (fun x hx => hw x (List.mem_cons_of_mem _ hx)))
    exact ⟨0, 0, by simp [localColumns, Automaton.dataInterpret], hrun,
      by simp [localColumns, Automaton.dataInterpret]⟩

def equalityGuard (i j : Fin k) (s : Shape k) : L.Formula (P ⊕ Fin (arity k s)) :=
  if hi : mask s i = true then
    if hj : mask s j = true then
      Term.equal (Term.var (Sum.inr (slot (mask s) i hi)))
        (Term.var (Sum.inr (slot (mask s) j hj)))
    else ⊥
  else if mask s j = true then ⊥ else ⊤

theorem realize_equalityGuard {D : Type*} [L.Structure D] (p : P → D)
    (i j : Fin k) (c : Sparse D k) :
    (equalityGuard (L := L) (P := P) i j c.1).Realize (Sum.elim p c.2) ↔
      toDense c i = toDense c j := by
  by_cases hi : mask c.1 i = true <;> by_cases hj : mask c.1 j = true <;>
    simp [equalityGuard, hi, hj, toDense, expand]

theorem column_eq_of_decode_eq {D : Type*} {a : Fin k → Bool}
    {w : List (CanonicalConvolution.Column D k)} (hw : CanonicalConvolution.ValidFrom a w)
    (i j : Fin k) (he : CanonicalConvolution.decode w i = CanonicalConvolution.decode w j) :
    ∀ c ∈ w, c i = c j := by
  induction w generalizing a with
  | nil => simp
  | cons c w ih =>
      have hh : c i = c j := (CanonicalConvolution.head_decode hw i).symm.trans
        ((congrArg List.head? he).trans (CanonicalConvolution.head_decode hw j))
      have ht : CanonicalConvolution.decode w i = CanonicalConvolution.decode w j :=
        (CanonicalConvolution.tail_decode hw i).symm.trans
          ((congrArg List.tail he).trans (CanonicalConvolution.tail_decode hw j))
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hh
      · exact ih hw.2.2 ht d hd

theorem decode_eq_of_column_eq {D : Type*} (w : List (CanonicalConvolution.Column D k))
    (i j : Fin k) (he : ∀ c ∈ w, c i = c j) :
    CanonicalConvolution.decode w i = CanonicalConvolution.decode w j := by
  induction w with
  | nil => rfl
  | cons c w ih =>
      have hc := he c List.mem_cons_self
      have ht := ih (fun d hd => he d (List.mem_cons_of_mem _ hd))
      unfold CanonicalConvolution.decode at ht ⊢
      simp only [List.filterMap_cons, hc, ht]

def equalityWords (L : FirstOrder.Language.{u, v}) (P : Type w) (i j : Fin k) :=
  enforcePadding (localColumns (equalityGuard (L := L) (P := P) i j))

theorem equalityWords_correct {D : Type*} [L.Structure D] (p : P → D)
    (i j : Fin k) (t : CanonicalConvolution.Tuple D k) :
    tupleAccepts (equalityWords L P i j) p t ↔ t i = t j := by
  rw [equalityWords, enforcePadding_tuple]
  unfold tupleAccepts denseAccepts
  rw [localColumns_correct]
  simp only [List.forall_mem_map, realize_equalityGuard, toDense_fromDense]
  constructor
  · intro h
    simpa only [CanonicalConvolution.decode_encode] using
      decode_eq_of_column_eq (CanonicalConvolution.encode t) i j h
  · intro h
    exact column_eq_of_decode_eq (CanonicalConvolution.canonical_encode t) i j
      (by simpa only [CanonicalConvolution.decode_encode] using h)

def falseWords (L : FirstOrder.Language.{u, v}) (P : Type w) (k : Nat) : WordAutomaton L P 1 k where
  initial _ := ⊥
  final _ := ⊥
  silent _ _ := ⊥
  step _ _ _ := ⊥

theorem falseWords_correct {D : Type*} [L.Structure D] (p : P → D)
    (t : CanonicalConvolution.Tuple D k) : ¬ tupleAccepts (falseWords L P k) p t := by
  rintro ⟨trace, _, q, r, hq, _, _⟩
  exact hq

end NSSE.WordEqualityAutomaton
