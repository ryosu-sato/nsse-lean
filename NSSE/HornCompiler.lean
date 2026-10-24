import NSSE.FiniteFixpoint

/-!
# Executable finite Horn-rule saturation

This is the common fixed-point kernel for finite compiler states.
Terminal bits and finite child-to-parent rules generate an inflationary,
monotone Boolean-mask update.
-/

namespace NSSE

structure HornRule where
  parent : Nat
  children : List Nat
deriving DecidableEq

structure FiniteHornCompiler where
  stateCount : Nat
  terminal : Nat → Bool
  rules : List HornRule

def allMaskBits (mask : List Bool) (indices : List Nat) : Bool :=
  indices.all (fun index => maskBit mask index)

def hornFires
    (rules : List HornRule) (parent : Nat) (mask : List Bool) : Bool :=
  rules.any fun rule =>
    decide (rule.parent = parent) && allMaskBits mask rule.children

def hornNewBit
    (compiler : FiniteHornCompiler)
    (mask : List Bool) (index : Nat) (old : Bool) : Bool :=
  old || compiler.terminal index ||
    hornFires compiler.rules index mask

def hornBuild
    (compiler : FiniteHornCompiler) (original : List Bool) :
    Nat → List Bool → List Bool
  | _, [] => []
  | index, old :: rest =>
      hornNewBit compiler original index old ::
        hornBuild compiler original (index + 1) rest

def hornUpdate
    (compiler : FiniteHornCompiler) (mask : List Bool) : List Bool :=
  hornBuild compiler mask 0 mask

theorem MaskLe.maskBit_true
    {x y : List Bool} (hxy : MaskLe x y) (index : Nat) :
    maskBit x index = true → maskBit y index = true := by
  induction hxy generalizing index with
  | nil =>
      simp [maskBit]
  | @cons xHead yHead xTail yTail hhead htail ih =>
      cases index with
      | zero =>
          simp only [maskBit, List.getElem?_cons_zero, Option.getD_some]
          exact hhead
      | succ index =>
          simpa [maskBit] using ih index

theorem allMaskBits_monotone
    {x y : List Bool} (hxy : MaskLe x y) (indices : List Nat) :
    allMaskBits x indices = true →
      allMaskBits y indices = true := by
  induction indices with
  | nil =>
      simp [allMaskBits]
  | cons index indices ih =>
      simp only [allMaskBits, List.all_cons, Bool.and_eq_true]
      rintro ⟨hindex, hrest⟩
      exact ⟨hxy.maskBit_true index hindex, ih hrest⟩

theorem hornFires_monotone
    (rules : List HornRule) (parent : Nat)
    {x y : List Bool} (hxy : MaskLe x y) :
    hornFires rules parent x = true →
      hornFires rules parent y = true := by
  induction rules with
  | nil =>
      simp [hornFires]
  | cons rule rules ih =>
      simp only [hornFires, List.any_cons, Bool.or_eq_true,
        Bool.and_eq_true]
      intro hfire
      rcases hfire with hhead | htail
      · exact Or.inl
          ⟨hhead.1,
            allMaskBits_monotone hxy rule.children hhead.2⟩
      · exact Or.inr (ih htail)

theorem hornNewBit_monotone
    (compiler : FiniteHornCompiler)
    {x y : List Bool} (hxy : MaskLe x y)
    {oldX oldY : Bool}
    (hold : oldX = true → oldY = true)
    (index : Nat) :
    hornNewBit compiler x index oldX = true →
      hornNewBit compiler y index oldY = true := by
  simp only [hornNewBit, Bool.or_eq_true]
  rintro ((holdBit | hterminal) | hfire)
  · exact Or.inl (Or.inl (hold holdBit))
  · exact Or.inl (Or.inr hterminal)
  · exact Or.inr
      (hornFires_monotone compiler.rules index hxy hfire)

theorem maskLe_hornBuild
    (compiler : FiniteHornCompiler)
    (original remaining : List Bool) (index : Nat) :
    MaskLe remaining
      (hornBuild compiler original index remaining) := by
  induction remaining generalizing index with
  | nil => exact .nil
  | cons old rest ih =>
      exact .cons
        (fun hold => by
          simp [hornBuild, hornNewBit, hold])
        (ih (index + 1))

theorem hornUpdate_inflationary
    (compiler : FiniteHornCompiler) :
    ∀ mask, MaskLe mask (hornUpdate compiler mask) := by
  intro mask
  exact maskLe_hornBuild compiler mask mask 0

theorem hornBuild_monotone
    (compiler : FiniteHornCompiler)
    {originalX originalY : List Bool}
    (horiginal : MaskLe originalX originalY) :
    ∀ {remainingX remainingY : List Bool},
      MaskLe remainingX remainingY →
      ∀ index,
        MaskLe
          (hornBuild compiler originalX index remainingX)
          (hornBuild compiler originalY index remainingY) := by
  intro remainingX remainingY hremaining
  induction hremaining with
  | nil =>
      intro index
      exact .nil
  | @cons xHead yHead xTail yTail hhead htail ih =>
      intro index
      exact .cons
        (hornNewBit_monotone compiler horiginal hhead index)
        (ih (index + 1))

theorem hornUpdate_monotone
    (compiler : FiniteHornCompiler) :
    MaskMonotone (hornUpdate compiler) := by
  intro x y hxy
  exact hornBuild_monotone compiler hxy hxy 0

theorem hornUpdate_length
    (compiler : FiniteHornCompiler) (mask : List Bool) :
    (hornUpdate compiler mask).length = mask.length :=
  (hornUpdate_inflationary compiler mask).length_eq.symm

theorem maskBit_hornBuild
    (compiler : FiniteHornCompiler)
    (original remaining : List Bool) (start index : Nat)
    (hindex : index < remaining.length) :
    maskBit (hornBuild compiler original start remaining) index =
      hornNewBit compiler original (start + index)
        (maskBit remaining index) := by
  induction remaining generalizing start index with
  | nil =>
      simp at hindex
  | cons old rest ih =>
      cases index with
      | zero =>
          simp [hornBuild, maskBit]
      | succ index =>
          change
            maskBit
                (hornBuild compiler original (start + 1) rest)
                index =
              hornNewBit compiler original (start + (index + 1))
                (maskBit rest index)
          rw [ih (start + 1) index (by simpa using hindex)]
          rw [show start + 1 + index = start + (index + 1) by omega]

theorem hornFires_iff
    (rules : List HornRule) (parent : Nat) (mask : List Bool) :
    hornFires rules parent mask = true ↔
      ∃ rule ∈ rules,
        rule.parent = parent ∧
        allMaskBits mask rule.children = true := by
  simp [hornFires]

theorem hornUpdate_bit_iff
    (compiler : FiniteHornCompiler) (mask : List Bool) (index : Nat)
    (hindex : index < mask.length) :
    maskBit (hornUpdate compiler mask) index = true ↔
      maskBit mask index = true ∨
      compiler.terminal index = true ∨
      ∃ rule ∈ compiler.rules,
        rule.parent = index ∧
        allMaskBits mask rule.children = true := by
  rw [hornUpdate, maskBit_hornBuild
    compiler mask mask 0 index hindex]
  simp only [Nat.zero_add, hornNewBit, Bool.or_eq_true]
  rw [hornFires_iff]
  constructor
  · rintro ((hold | hterminal) | hfire)
    · exact Or.inl hold
    · exact Or.inr (Or.inl hterminal)
    · exact Or.inr (Or.inr hfire)
  · rintro (hold | hterminal | hfire)
    · exact Or.inl (Or.inl hold)
    · exact Or.inl (Or.inr hterminal)
    · exact Or.inr hfire

theorem allMaskBits_iff
    (mask : List Bool) (indices : List Nat) :
    allMaskBits mask indices = true ↔
      ∀ index ∈ indices, maskBit mask index = true := by
  induction indices with
  | nil =>
      simp [allMaskBits]
  | cons index indices ih =>
      simp [allMaskBits, ih]

inductive HornDerives (compiler : FiniteHornCompiler) : Nat → Prop where
  | terminal {state : Nat}
      (state_lt : state < compiler.stateCount)
      (terminal_true : compiler.terminal state = true) :
      HornDerives compiler state
  | rule {rule : HornRule}
      (rule_mem : rule ∈ compiler.rules)
      (parent_lt : rule.parent < compiler.stateCount)
      (children :
        ∀ child ∈ rule.children, HornDerives compiler child) :
      HornDerives compiler rule.parent

theorem HornDerives.state_lt
    {compiler : FiniteHornCompiler} {state : Nat}
    (hderive : HornDerives compiler state) :
    state < compiler.stateCount := by
  cases hderive with
  | terminal state_lt _ => exact state_lt
  | rule _ parent_lt _ => exact parent_lt

def hornInitial (compiler : FiniteHornCompiler) : List Bool :=
  List.replicate compiler.stateCount false

def hornSemantic (compiler : FiniteHornCompiler) : List Bool :=
  iterateMask (hornUpdate compiler)
    (hornInitial compiler).length (hornInitial compiler)

@[simp] theorem hornInitial_length (compiler : FiniteHornCompiler) :
    (hornInitial compiler).length = compiler.stateCount := by
  simp [hornInitial]

theorem maskBit_replicate_false (count index : Nat) :
    maskBit (List.replicate count false) index = false := by
  induction count generalizing index with
  | zero =>
      simp [maskBit]
  | succ count ih =>
      cases index with
      | zero => simp [maskBit, List.replicate_succ]
      | succ index =>
          simpa [maskBit, List.replicate_succ] using ih index

theorem maskBit_true_lt
    (mask : List Bool) (index : Nat)
    (htrue : maskBit mask index = true) :
    index < mask.length := by
  induction mask generalizing index with
  | nil =>
      simp [maskBit] at htrue
  | cons bit rest ih =>
      cases index with
      | zero => simp
      | succ index =>
          simp only [maskBit, List.getElem?_cons_succ] at htrue
          have := ih index htrue
          simp
          omega

theorem HornDerives.in_fixed
    {compiler : FiniteHornCompiler} {state : Nat}
    (hderive : HornDerives compiler state)
    (mask : List Bool)
    (hlength : mask.length = compiler.stateCount)
    (hfixed : hornUpdate compiler mask = mask) :
    maskBit mask state = true := by
  induction hderive with
  | @terminal terminalState state_lt terminal_true =>
      have hindex : terminalState < mask.length := by omega
      have hupdated :
          maskBit (hornUpdate compiler mask) terminalState = true :=
        (hornUpdate_bit_iff compiler mask terminalState hindex).2
          (Or.inr (Or.inl terminal_true))
      rw [hfixed] at hupdated
      exact hupdated
  | @rule rule rule_mem parent_lt children ih =>
      have hindex : rule.parent < mask.length := by omega
      have hall :
          allMaskBits mask rule.children = true :=
        (allMaskBits_iff mask rule.children).2
          (fun child hmem => ih child hmem)
      have hupdated :
          maskBit (hornUpdate compiler mask) rule.parent = true :=
        (hornUpdate_bit_iff compiler mask rule.parent hindex).2
          (Or.inr (Or.inr
            ⟨rule, rule_mem, rfl, hall⟩))
      rw [hfixed] at hupdated
      exact hupdated

theorem hornSemantic_fixed (compiler : FiniteHornCompiler) :
    hornUpdate compiler (hornSemantic compiler) =
      hornSemantic compiler := by
  exact iterateMask_length_is_fixed
    (hornUpdate compiler) (hornUpdate_inflationary compiler)
    (hornInitial compiler)

theorem hornSemantic_length (compiler : FiniteHornCompiler) :
    (hornSemantic compiler).length = compiler.stateCount := by
  unfold hornSemantic
  rw [iterateMask_length
    (hornUpdate compiler) (hornUpdate_inflationary compiler)]
  exact hornInitial_length compiler

theorem HornDerives.in_semantic
    {compiler : FiniteHornCompiler} {state : Nat}
    (hderive : HornDerives compiler state) :
    maskBit (hornSemantic compiler) state = true :=
  hderive.in_fixed (hornSemantic compiler)
    (hornSemantic_length compiler) (hornSemantic_fixed compiler)

theorem iterate_hornUpdate_bit_derives
    (compiler : FiniteHornCompiler) :
    ∀ (round state : Nat),
      state < compiler.stateCount →
      maskBit
          (iterateMask (hornUpdate compiler) round
            (hornInitial compiler))
          state = true →
        HornDerives compiler state
  | 0, state, hstate, htrue => by
      change maskBit (hornInitial compiler) state = true at htrue
      rw [hornInitial, maskBit_replicate_false] at htrue
      contradiction
  | round + 1, state, hstate, htrue => by
      let previous :=
        iterateMask (hornUpdate compiler) round
          (hornInitial compiler)
      have hpreviousLength :
          previous.length = compiler.stateCount := by
        dsimp [previous]
        rw [iterateMask_length
          (hornUpdate compiler) (hornUpdate_inflationary compiler)]
        exact hornInitial_length compiler
      have hstatePrevious : state < previous.length := by omega
      have hstep :
          maskBit previous state = true ∨
          compiler.terminal state = true ∨
          ∃ rule ∈ compiler.rules,
            rule.parent = state ∧
            allMaskBits previous rule.children = true := by
        apply (hornUpdate_bit_iff
          compiler previous state hstatePrevious).1
        simpa [previous] using htrue
      rcases hstep with hold | hterminal | hrule
      · exact iterate_hornUpdate_bit_derives
          compiler round state hstate hold
      · exact .terminal hstate hterminal
      · obtain ⟨rule, hmem, hparent, hall⟩ := hrule
        subst state
        apply HornDerives.rule hmem hstate
        intro child hchild
        have hchildBit :
            maskBit previous child = true :=
          (allMaskBits_iff previous rule.children).1 hall
            child hchild
        have hchildBound : child < compiler.stateCount := by
          have := maskBit_true_lt previous child hchildBit
          omega
        exact iterate_hornUpdate_bit_derives
          compiler round child hchildBound hchildBit

theorem hornSemantic_bit_iff_derives
    (compiler : FiniteHornCompiler) (state : Nat)
    (hstate : state < compiler.stateCount) :
    maskBit (hornSemantic compiler) state = true ↔
      HornDerives compiler state := by
  constructor
  · exact iterate_hornUpdate_bit_derives
      compiler (hornInitial compiler).length state hstate
  · exact HornDerives.in_semantic

theorem hornSemantic_lfp (compiler : FiniteHornCompiler) :
    LeastFixedPointSpec (hornUpdate compiler)
      (hornInitial compiler) (hornSemantic compiler) where
  initial_le :=
    initial_le_iterateMask
      (hornUpdate compiler) (hornUpdate_inflationary compiler)
      (hornInitial compiler) (hornInitial compiler).length
  fixed := hornSemantic_fixed compiler
  least := by
    intro other hbelow hfixed
    exact iterateMask_length_least
      (hornUpdate compiler) (hornUpdate_monotone compiler)
      (hornInitial compiler) other hbelow hfixed

def decideHornState
    (compiler : FiniteHornCompiler) (state : Nat) : Bool :=
  decideLeastFixedPoint (hornUpdate compiler)
    (hornInitial compiler) state

theorem decideHornState_correct
    (compiler : FiniteHornCompiler) (state : Nat)
    (hstate : state < compiler.stateCount) :
    decideHornState compiler state = true ↔
      HornDerives compiler state := by
  rw [decideHornState,
    decideLeastFixedPoint_correct
      (hornUpdate compiler)
      (hornUpdate_inflationary compiler)
      (hornUpdate_monotone compiler)
      (hornInitial compiler) (hornSemantic compiler)
      (hornSemantic_lfp compiler) state]
  exact hornSemantic_bit_iff_derives compiler state hstate

end NSSE
