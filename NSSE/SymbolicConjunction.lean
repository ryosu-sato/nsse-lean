import NSSE.ConvolutionShapes

/-! # Exact symbolic NFA conjunction with shared parameters -/

namespace NSSE.SymbolicConjunction

open FirstOrder FirstOrder.Language SymbolicAutomata ConvolutionShapes

universe u v w
variable {L : FirstOrder.Language.{u, v}} {P : Type w}

section Product

variable {α Q R : Type*}

def product (A : NSSE.NFA α Q) (B : NSSE.NFA α R) : NSSE.NFA α (Q × R) where
  start s := A.start s.1 ∧ B.start s.2
  accept s := A.accept s.1 ∧ B.accept s.2
  step s a t := A.step s.1 a t.1 ∧ B.step s.2 a t.2

theorem product_run (A : NSSE.NFA α Q) (B : NSSE.NFA α R)
    {q r : Q} {w : List α} (ha : A.Runs q w r) :
    ∀ {s t : R}, B.Runs s w t → (product A B).Runs (q, s) w (r, t) := by
  induction ha with
  | nil q =>
      intro s t hb
      cases hb
      exact .nil _
  | cons hstep _ ih =>
      intro s t hb
      cases hb with
      | cons hb hrest => exact .cons ⟨hstep, hb⟩ (ih hrest)

theorem of_product_run (A : NSSE.NFA α Q) (B : NSSE.NFA α R)
    {s t : Q × R} {w : List α} (h : (product A B).Runs s w t) :
    A.Runs s.1 w t.1 ∧ B.Runs s.2 w t.2 := by
  induction h with
  | nil s => exact ⟨.nil _, .nil _⟩
  | cons hstep _ ih => exact ⟨.cons hstep.1 ih.1, .cons hstep.2 ih.2⟩

theorem product_accepts (A : NSSE.NFA α Q) (B : NSSE.NFA α R) (w : List α) :
    (product A B).Accepts w ↔ A.Accepts w ∧ B.Accepts w := by
  constructor
  · rintro ⟨s, t, ⟨hsA, hsB⟩, hrun, ⟨htA, htB⟩⟩
    obtain ⟨ha, hb⟩ := of_product_run A B hrun
    exact ⟨⟨s.1, t.1, hsA, ha, htA⟩, ⟨s.2, t.2, hsB, hb, htB⟩⟩
  · rintro ⟨⟨q, r, hq, ha, hr⟩, ⟨s, t, hs, hb, ht⟩⟩
    exact ⟨(q, s), (r, t), ⟨hq, hs⟩, product_run A B ha hb, hr, ht⟩

end Product

def pairs (n r : Nat) : List (Fin n × Fin r) :=
  (List.finRange n).flatMap (fun q => (List.finRange r).map (fun s => (q, s)))

def decode (n r : Nat) (i : Fin (pairs n r).length) : Fin n × Fin r := (pairs n r).get i

theorem decode_surjective (n r : Nat) : Function.Surjective (decode n r) := by
  intro s
  apply List.mem_iff_get.mp
  exact List.mem_flatMap.mpr ⟨s.1, List.mem_finRange _,
    List.mem_map.mpr ⟨s.2, List.mem_finRange _, Prod.mk.eta⟩⟩

theorem length_pairs (n r : Nat) : (pairs n r).length = n * r := by
  simp [pairs, List.length_flatMap]

variable {n r m : Nat} {arity : Fin m → Nat}

def compile (A : Automaton L P n m arity) (B : Automaton L P r m arity) :
    Automaton L P (pairs n r).length m arity where
  initial i := A.epsilonFree.initial (decode n r i).1 ⊓ B.epsilonFree.initial (decode n r i).2
  final i := A.epsilonFree.final (decode n r i).1 ⊓ B.epsilonFree.final (decode n r i).2
  silent _ _ := ⊥
  step s i j := A.epsilonFree.step s (decode n r i).1 (decode n r j).1 ⊓
    B.epsilonFree.step s (decode n r i).2 (decode n r j).2

theorem compile_dataInterpret (A : Automaton L P n m arity) (B : Automaton L P r m arity)
    {D : Type*} [L.Structure D] (p : P → D) :
    (compile A B).dataInterpret p = SymbolicComplement.pullback
      (product (A.epsilonFree.dataInterpret p) (B.epsilonFree.dataInterpret p)) (decode n r) := by
  unfold compile Automaton.dataInterpret SymbolicComplement.pullback product
  congr 1
  · funext q; exact propext Formula.realize_inf
  · funext q c s; exact propext Formula.realize_inf
  · funext q; exact propext Formula.realize_inf

theorem compile_correct (A : Automaton L P n m arity) (B : Automaton L P r m arity)
    {D : Type*} [L.Structure D] (p : P → D) (w : List (Column D arity)) :
    (compile A B).Accepts p w ↔ A.Accepts p w ∧ B.Accepts p w := by
  rw [(compile A B).accepts_iff_data_of_noSilent p (by intro q r; simp [compile]) w,
    compile_dataInterpret, SymbolicComplement.pullback_accepts _ _ (decode_surjective n r),
    product_accepts, A.epsilonFree_correct p w, B.epsilonFree_correct p w]

variable {k : Nat}

def andWords (A : WordAutomaton L P n k) (B : WordAutomaton L P r k) :=
  enforcePadding (compile A B)

theorem andWords_correct (A : WordAutomaton L P n k) (B : WordAutomaton L P r k)
    {D : Type*} [L.Structure D] (p : P → D) (t : CanonicalConvolution.Tuple D k) :
    tupleAccepts (andWords A B) p t ↔ tupleAccepts A p t ∧ tupleAccepts B p t := by
  rw [andWords, enforcePadding_tuple]
  exact compile_correct A B p _

def impWords (A : WordAutomaton L P n k) (B : WordAutomaton L P r k) :=
  complementWords (andWords A (complementWords B))

theorem impWords_correct (A : WordAutomaton L P n k) (B : WordAutomaton L P r k)
    {D : Type*} [L.Structure D] (p : P → D) (t : CanonicalConvolution.Tuple D k) :
    tupleAccepts (impWords A B) p t ↔ (tupleAccepts A p t → tupleAccepts B p t) := by
  simp [impWords, complementWords_correct, andWords_correct]

end NSSE.SymbolicConjunction
