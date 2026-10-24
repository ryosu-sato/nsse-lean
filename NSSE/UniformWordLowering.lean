import NSSE.SymbolicConjunction
import NSSE.WordEqualityAutomaton

/-!
# Uniform first-order lowering of automatically presented word structures

The compiler recurses on Mathlib's actual first-order formula syntax in a
relational language. Every relation is supplied by finite symbolic automaton
syntax over the base language. A domain presentation equivalence is allowed;
in particular the same lowering works for reversed-word presentations.
-/

namespace NSSE.UniformWordLowering

open FirstOrder FirstOrder.Language SymbolicAutomata ConvolutionShapes

universe u v w r
variable {L : FirstOrder.Language.{u, v}} {P : Type w} {R : Nat → Type r}

def wordLanguage (R : Nat → Type r) : FirstOrder.Language.{0, r} where
  Functions _ := Empty
  Relations := R

structure Presentation (L : FirstOrder.Language.{u, v}) (P : Type w) (R : Nat → Type r) where
  states : {a : Nat} → R a → Nat
  automaton : {a : Nat} → (s : R a) → WordAutomaton L P (states s) a

def model (F : Presentation L P R) {D : Type*} [L.Structure D]
    (p : P → D) (e : List D ≃ List D) : (wordLanguage R).Structure (List D) where
  funMap f := nomatch f
  RelMap s xs := tupleAccepts (F.automaton s) p (e ∘ xs)

def termIndex {k n : Nat} : (wordLanguage R).Term (Fin k ⊕ Fin n) → Fin (k + n)
  | .var (.inl i) => Fin.castAdd n i
  | .var (.inr i) => Fin.natAdd k i
  | .func f _ => nomatch f

theorem termIndex_eval {X Y : Type*} [(wordLanguage R).Structure X]
    {k n : Nat} (g : X → Y) (v : Fin k → X) (xs : Fin n → X)
    (t : (wordLanguage R).Term (Fin k ⊕ Fin n)) :
    Fin.append (g ∘ v) (g ∘ xs) (termIndex t) = g (t.realize (Sum.elim v xs)) := by
  cases t with
  | var i =>
      cases i with
      | inl i => exact Fin.append_left _ _ i
      | inr i => exact Fin.append_right _ _ i
  | func f _ => cases f

def existsLastWord {n k : Nat} (A : WordAutomaton L P n (k + 1)) :=
  projectWords Fin.castSucc A

theorem existsLastWord_correct {D : Type*} [L.Structure D] {n k : Nat}
    (A : WordAutomaton L P n (k + 1)) (p : P → D) (t : CanonicalConvolution.Tuple D k) :
    tupleAccepts (existsLastWord A) p t ↔ ∃ x : List D, tupleAccepts A p (Fin.snoc t x) := by
  rw [existsLastWord, projectWords_correct]
  constructor
  · rintro ⟨s, hs, he⟩
    refine ⟨s (Fin.last k), ?_⟩
    have hrec : Fin.snoc t (s (Fin.last k)) = s := by
      rw [← he]
      exact Fin.snoc_init_self s
    rwa [hrec]
  · rintro ⟨x, hx⟩
    exact ⟨Fin.snoc t x, hx, by funext i; simp⟩

def forallLastWord {n k : Nat} (A : WordAutomaton L P n (k + 1)) :=
  complementWords (existsLastWord (complementWords A))

theorem forallLastWord_correct {D : Type*} [L.Structure D] {n k : Nat}
    (A : WordAutomaton L P n (k + 1)) (p : P → D) (t : CanonicalConvolution.Tuple D k) :
    tupleAccepts (forallLastWord A) p t ↔ ∀ x : List D, tupleAccepts A p (Fin.snoc t x) := by
  simp [forallLastWord, complementWords_correct, existsLastWord_correct]

/-- A finite automaton AND its computed state count; no acceptance oracle. -/
abbrev Compiled (L : FirstOrder.Language.{u, v}) (P : Type w) (k : Nat) :=
  (n : Nat) × WordAutomaton L P n k

/-- Structural recursion on the actual relational FO syntax, including its
free and bound variables. Both classes of word variables stay on tapes. -/
def compile (F : Presentation L P R) {k : Nat} :
    {n : Nat} → (wordLanguage R).BoundedFormula (Fin k) n → Compiled L P (k + n)
  | _, .falsum => ⟨1, WordEqualityAutomaton.falseWords L P _⟩
  | _, .equal t₁ t₂ => ⟨_, WordEqualityAutomaton.equalityWords L P (termIndex t₁) (termIndex t₂)⟩
  | _, .rel s ts => ⟨_, pullbackWords (fun i => termIndex (ts i)) (F.automaton s)⟩
  | _, .imp φ ψ =>
      let A := compile F φ
      let B := compile F ψ
      ⟨_, SymbolicConjunction.impWords A.2 B.2⟩
  | _, .all φ =>
      let A := compile F φ
      ⟨_, forallLastWord A.2⟩

/-- Every free-variable valuation is preserved, not only sentence truth.
The equivalence e specifies the presentation of the entire word domain. -/
theorem compile_correct (F : Presentation L P R) {D : Type*} [L.Structure D]
    (p : P → D) (e : List D ≃ List D) {k n : Nat}
    (φ : (wordLanguage R).BoundedFormula (Fin k) n)
    (v : Fin k → List D) (xs : Fin n → List D) :
    letI := model F p e
    tupleAccepts (compile F φ).2 p (Fin.append (e ∘ v) (e ∘ xs)) ↔ φ.Realize v xs := by
  letI := model F p e
  induction φ generalizing v with
  | falsum => exact iff_false_intro (WordEqualityAutomaton.falseWords_correct p _)
  | equal t₁ t₂ =>
      change tupleAccepts (WordEqualityAutomaton.equalityWords L P (termIndex t₁) (termIndex t₂))
        p _ ↔ t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
      rw [WordEqualityAutomaton.equalityWords_correct, termIndex_eval, termIndex_eval]
      exact e.injective.eq_iff
  | rel s ts =>
      change tupleAccepts (pullbackWords (fun i => termIndex (ts i)) (F.automaton s)) p _ ↔
        tupleAccepts (F.automaton s) p (e ∘ (fun i => (ts i).realize (Sum.elim v xs)))
      rw [pullbackWords_correct]
      have ht : Fin.append (e ∘ v) (e ∘ xs) ∘ (fun i => termIndex (ts i)) =
          e ∘ (fun i => (ts i).realize (Sum.elim v xs)) := by
        funext i
        exact termIndex_eval e v xs (ts i)
      rw [ht]
  | imp φ ψ ihφ ihψ =>
      dsimp only [compile, BoundedFormula.Realize]
      rw [SymbolicConjunction.impWords_correct]
      constructor
      · intro h hφ
        exact (ihψ v xs).mp (h ((ihφ v xs).mpr hφ))
      · intro h hφ
        exact (ihψ v xs).mpr (h ((ihφ v xs).mp hφ))
  | all φ ih =>
      dsimp only [compile, BoundedFormula.Realize]
      rw [forallLastWord_correct]
      constructor
      · intro h x
        apply (ih v (Fin.snoc xs x)).mp
        simpa only [Fin.comp_snoc, Fin.append_snoc] using h (e x)
      · intro h y
        have hy := (ih v (Fin.snoc xs (e.symm y))).mpr (h (e.symm y))
        simpa only [Fin.comp_snoc, Fin.append_snoc, Equiv.apply_symm_apply] using hy

theorem encode_zero {D : Type*} (t : CanonicalConvolution.Tuple D 0) :
    CanonicalConvolution.encode t = [] := by
  simp [CanonicalConvolution.encode, CanonicalConvolution.height, CanonicalConvolution.encodeAux]

/-- On zero word tapes, canonical nonemptiness is precisely empty-input
acceptance. The padding intersection is constructed, not a hypothesis. -/
theorem zero_nonempty {D : Type*} [L.Structure D] {n : Nat}
    (A : WordAutomaton L P n 0) (p : P → D) :
    (enforcePadding A).nonemptyFormula.Realize p ↔
      tupleAccepts A p (Fin.elim0 : Fin 0 → List D) := by
  rw [Automaton.realize_nonemptyFormula]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨ha, hc⟩ := (enforcePadding_correct A p w).mp hw
    have hd : w.map toDense = [] := CanonicalConvolution.eq_nil_of_decode_nil hc (fun i => i.elim0)
    have hn : w = [] := by simpa using hd
    subst w
    simpa [tupleAccepts, denseAccepts, encode_zero] using ha
  · intro ha
    refine ⟨[], (enforcePadding_correct A p []).mpr ⟨?_, trivial⟩⟩
    simpa [tupleAccepts, denseAccepts, encode_zero] using ha

def normalizeSentence (φ : (wordLanguage R).Sentence) : (wordLanguage R).Formula (Fin 0) :=
  Formula.relabel (fun x : Empty => (x.elim : Fin 0)) φ

/-- The input-computable base-language formula. The caller supplies NO model,
parameter valuation, or decision oracle to this definition. -/
def lower (F : Presentation L P R) (φ : (wordLanguage R).Sentence) : L.Formula P :=
  (enforcePadding (compile F (normalizeSentence φ)).2).nonemptyFormula

theorem lower_correct (F : Presentation L P R) {D : Type*} [L.Structure D]
    (p : P → D) (e : List D ≃ List D) (φ : (wordLanguage R).Sentence) :
    letI := model F p e
    (lower F φ).Realize p ↔ φ.Realize (List D) := by
  letI := model F p e
  unfold lower
  rw [zero_nonempty]
  have hc := compile_correct F p e (normalizeSentence φ)
    (Fin.elim0 : Fin 0 → List D) (Fin.elim0 : Fin 0 → List D)
  have ht : Fin.append (e ∘ (Fin.elim0 : Fin 0 → List D))
      (e ∘ (Fin.elim0 : Fin 0 → List D)) = (Fin.elim0 : Fin 0 → List D) := by
    funext i
    exact i.elim0
  rw [ht] at hc
  refine hc.trans ?_
  rw [Formula.boundedFormula_realize_eq_realize, normalizeSentence, Formula.realize_relabel]
  rw [Sentence.Realize]
  exact iff_of_eq (congrArg (Formula.Realize φ) (Subsingleton.elim _ _))

/-- The usual forward-word presentation is an instance of the same compiler. -/
theorem lower_identity_correct (F : Presentation L P R) {D : Type*} [L.Structure D]
    (p : P → D) (φ : (wordLanguage R).Sentence) :
    letI := model F p (Equiv.refl (List D))
    (lower F φ).Realize p ↔ φ.Realize (List D) :=
  lower_correct F p (Equiv.refl (List D)) φ

def reverseEquiv (D : Type*) : List D ≃ List D where
  toFun := List.reverse
  invFun := List.reverse
  left_inv := List.reverse_reverse
  right_inv := List.reverse_reverse

/-- The same computed formula works for the reversed-word presentation
used by the endpoint lift. No separate reversal closure algorithm is assumed. -/
theorem lower_reverse_correct (F : Presentation L P R) {D : Type*} [L.Structure D]
    (p : P → D) (φ : (wordLanguage R).Sentence) :
    letI := model F p (reverseEquiv D)
    (lower F φ).Realize p ↔ φ.Realize (List D) :=
  lower_correct F p (reverseEquiv D) φ

end NSSE.UniformWordLowering
