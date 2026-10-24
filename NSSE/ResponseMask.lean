import NSSE.GlobalTerminalBridge
import NSSE.FiniteFixpoint

/-!
# Least-fixed-point mask for classified response derivations

Each global response derivation belongs to one of four bounded guard
classes or the PWE class.  A concrete monotone inflationary update marks
the corresponding bit, and its exact least fixed point is proved here.
-/

namespace NSSE

def markAt : Nat → List Bool → List Bool
  | _, [] => []
  | 0, _ :: rest => true :: rest
  | n + 1, bit :: rest => bit :: markAt n rest

theorem maskLe_markAt (index : Nat) (mask : List Bool) :
    MaskLe mask (markAt index mask) := by
  induction index generalizing mask with
  | zero =>
      cases mask with
      | nil => exact .nil
      | cons bit rest =>
          exact .cons (fun _ => rfl) (MaskLe.refl rest)
  | succ index ih =>
      cases mask with
      | nil => exact .nil
      | cons bit rest =>
          exact .cons (fun h => h) (ih rest)

theorem markAt_monotone (index : Nat) :
    MaskMonotone (markAt index) := by
  intro x y hxy
  induction index generalizing x y with
  | zero =>
      cases hxy with
      | nil => exact .nil
      | cons head tail =>
          exact .cons (fun _ => rfl) tail
  | succ index ih =>
      cases hxy with
      | nil => exact .nil
      | cons head tail =>
          exact .cons head (ih tail)

theorem markAt_idempotent (index : Nat) (mask : List Bool) :
    markAt index (markAt index mask) = markAt index mask := by
  induction index generalizing mask with
  | zero =>
      cases mask <;> rfl
  | succ index ih =>
      cases mask with
      | nil => rfl
      | cons bit rest =>
          simp [markAt, ih]

theorem maskBit_markAt_self
    (index : Nat) (mask : List Bool)
    (hindex : index < mask.length) :
    maskBit (markAt index mask) index = true := by
  induction index generalizing mask with
  | zero =>
      cases mask with
      | nil => simp at hindex
      | cons bit rest => rfl
  | succ index ih =>
      cases mask with
      | nil => simp at hindex
      | cons bit rest =>
          simp only [markAt, maskBit, List.getElem?_cons_succ]
          exact ih rest (by simpa using hindex)

theorem markAt_leastFixedPointSpec
    (index : Nat) (initial : List Bool) :
    LeastFixedPointSpec (markAt index) initial
      (markAt index initial) where
  initial_le := maskLe_markAt index initial
  fixed := markAt_idempotent index initial
  least := by
    intro other hbelow hfixed
    have hmarked :=
      markAt_monotone index hbelow
    rw [hfixed] at hmarked
    exact hmarked

inductive ResponseClass
  | candidateLoop
  | beforeLeftLoop
  | betweenRight
  | afterSlot
  | pwe
deriving DecidableEq

def responseClassIndex : ResponseClass → Nat
  | .candidateLoop => 0
  | .beforeLeftLoop => 1
  | .betweenRight => 2
  | .afterSlot => 3
  | .pwe => 4

def responseInitialMask : List Bool :=
  [false, false, false, false, false]

theorem responseClassIndex_lt (responseClass : ResponseClass) :
    responseClassIndex responseClass < responseInitialMask.length := by
  cases responseClass <;> decide

def finiteGuardResponseClass :
    FirstEventFiniteGuardQuery I left right event w j t → ResponseClass
  | .candidateLoop => .candidateLoop
  | .beforeLeftLoop => .beforeLeftLoop
  | .betweenRight => .betweenRight
  | .afterSlot => .afterSlot

inductive DispositionHasClass
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    FirstEventGlobalDisposition I left right event w j t →
      ResponseClass → Prop where
  | bounded
      (query : FirstEventFiniteGuardQuery I left right event w j t) :
      DispositionHasClass I left right event w j t
        (.inl (boundedResponseTag query))
        (finiteGuardResponseClass query)
  | pwe (terminal : ResponsePWETerminal α) :
      DispositionHasClass I left right event w j t
        (.inr terminal) .pwe

theorem globalDispositionDerives_hasClass
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (disposition :
      FirstEventGlobalDisposition I left right event w j t)
    (hderive :
      GlobalDispositionDerives I left right rightFinal
        event w j t disposition) :
    ∃ responseClass, DispositionHasClass I left right event w j t
      disposition responseClass := by
  cases disposition with
  | inr terminal =>
      exact ⟨.pwe, .pwe terminal⟩
  | inl tag =>
      have hterminal :=
        (boundedResponse_derives_iff_terminal
          I left right rightFinal event w j t tag).1 hderive
      cases tag with
      | bounded control cut query =>
          exact ⟨finiteGuardResponseClass query, .bounded query⟩
      | nonstrong control cut lca macroData wire =>
          exact False.elim hterminal
      | strong control cut macroData wire quotient =>
          exact False.elim hterminal
      | hub control cut macroData wire =>
          exact False.elim hterminal
      | copy control cut orientation macroData wire =>
          exact False.elim hterminal
      | side control cut lca =>
          exact False.elim hterminal

theorem globalDerivation_has_responseLeastFixedPoint
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (disposition :
      FirstEventGlobalDisposition I left right event w j t)
    (hderive :
      GlobalDispositionDerives I left right rightFinal
        event w j t disposition) :
    ∃ responseClass,
      DispositionHasClass I left right event w j t
        disposition responseClass ∧
      LeastFixedPointSpec
        (markAt (responseClassIndex responseClass))
        responseInitialMask
        (markAt (responseClassIndex responseClass)
          responseInitialMask) ∧
      maskBit
        (markAt (responseClassIndex responseClass)
          responseInitialMask)
        (responseClassIndex responseClass) = true := by
  obtain ⟨responseClass, hclass⟩ :=
    globalDispositionDerives_hasClass
      I left right rightFinal event w j t disposition hderive
  exact ⟨responseClass, hclass,
    markAt_leastFixedPointSpec
      (responseClassIndex responseClass) responseInitialMask,
    maskBit_markAt_self
      (responseClassIndex responseClass) responseInitialMask
      (responseClassIndex_lt responseClass)⟩

theorem decideResponseClassFixedPoint (responseClass : ResponseClass) :
    decideLeastFixedPoint
        (markAt (responseClassIndex responseClass))
        responseInitialMask
        (responseClassIndex responseClass) = true := by
  rw [decideLeastFixedPoint_correct
    (markAt (responseClassIndex responseClass))
    (maskLe_markAt (responseClassIndex responseClass))
    (markAt_monotone (responseClassIndex responseClass))
    responseInitialMask
    (markAt (responseClassIndex responseClass) responseInitialMask)
    (markAt_leastFixedPointSpec
      (responseClassIndex responseClass) responseInitialMask)
    (responseClassIndex responseClass)]
  exact maskBit_markAt_self
    (responseClassIndex responseClass) responseInitialMask
    (responseClassIndex_lt responseClass)

theorem globalDerivation_has_true_fixedPointDecision
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (disposition :
      FirstEventGlobalDisposition I left right event w j t)
    (hderive :
      GlobalDispositionDerives I left right rightFinal
        event w j t disposition) :
    ∃ responseClass,
      DispositionHasClass I left right event w j t
        disposition responseClass ∧
      decideLeastFixedPoint
        (markAt (responseClassIndex responseClass))
        responseInitialMask
        (responseClassIndex responseClass) = true := by
  obtain ⟨responseClass, hclass⟩ :=
    globalDispositionDerives_hasClass
      I left right rightFinal event w j t disposition hderive
  exact ⟨responseClass, hclass,
    decideResponseClassFixedPoint responseClass⟩

def embeddedResponseInitial
    (prefixMask suffixMask : List Bool) : List Bool :=
  prefixMask ++ responseInitialMask ++ suffixMask

def embeddedResponseIndex
    (prefixMask : List Bool) (responseClass : ResponseClass) : Nat :=
  prefixMask.length + responseClassIndex responseClass

theorem embeddedResponseIndex_lt
    (prefixMask suffixMask : List Bool)
    (responseClass : ResponseClass) :
    embeddedResponseIndex prefixMask responseClass <
      (embeddedResponseInitial prefixMask suffixMask).length := by
  unfold embeddedResponseIndex embeddedResponseInitial
  simp only [List.length_append]
  have hclass := responseClassIndex_lt responseClass
  omega

theorem embeddedResponse_leastFixedPoint
    (prefixMask suffixMask : List Bool)
    (responseClass : ResponseClass) :
    LeastFixedPointSpec
      (markAt (embeddedResponseIndex prefixMask responseClass))
      (embeddedResponseInitial prefixMask suffixMask)
      (markAt (embeddedResponseIndex prefixMask responseClass)
        (embeddedResponseInitial prefixMask suffixMask)) :=
  markAt_leastFixedPointSpec
    (embeddedResponseIndex prefixMask responseClass)
    (embeddedResponseInitial prefixMask suffixMask)

theorem decideEmbeddedResponseFixedPoint
    (prefixMask suffixMask : List Bool)
    (responseClass : ResponseClass) :
    decideLeastFixedPoint
      (markAt (embeddedResponseIndex prefixMask responseClass))
      (embeddedResponseInitial prefixMask suffixMask)
      (embeddedResponseIndex prefixMask responseClass) = true := by
  rw [decideLeastFixedPoint_correct
    (markAt (embeddedResponseIndex prefixMask responseClass))
    (maskLe_markAt (embeddedResponseIndex prefixMask responseClass))
    (markAt_monotone (embeddedResponseIndex prefixMask responseClass))
    (embeddedResponseInitial prefixMask suffixMask)
    (markAt (embeddedResponseIndex prefixMask responseClass)
      (embeddedResponseInitial prefixMask suffixMask))
    (embeddedResponse_leastFixedPoint
      prefixMask suffixMask responseClass)
    (embeddedResponseIndex prefixMask responseClass)]
  exact maskBit_markAt_self
    (embeddedResponseIndex prefixMask responseClass)
    (embeddedResponseInitial prefixMask suffixMask)
    (embeddedResponseIndex_lt prefixMask suffixMask responseClass)

theorem globalDerivation_has_embeddedFixedPoint
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (disposition :
      FirstEventGlobalDisposition I left right event w j t)
    (hderive :
      GlobalDispositionDerives I left right rightFinal
        event w j t disposition)
    (prefixMask suffixMask : List Bool) :
    ∃ responseClass,
      DispositionHasClass I left right event w j t
        disposition responseClass ∧
      LeastFixedPointSpec
        (markAt (embeddedResponseIndex prefixMask responseClass))
        (embeddedResponseInitial prefixMask suffixMask)
        (markAt (embeddedResponseIndex prefixMask responseClass)
          (embeddedResponseInitial prefixMask suffixMask)) ∧
      decideLeastFixedPoint
        (markAt (embeddedResponseIndex prefixMask responseClass))
        (embeddedResponseInitial prefixMask suffixMask)
        (embeddedResponseIndex prefixMask responseClass) = true := by
  obtain ⟨responseClass, hclass⟩ :=
    globalDispositionDerives_hasClass
      I left right rightFinal event w j t disposition hderive
  exact ⟨responseClass, hclass,
    embeddedResponse_leastFixedPoint
      prefixMask suffixMask responseClass,
    decideEmbeddedResponseFixedPoint
      prefixMask suffixMask responseClass⟩

end NSSE
