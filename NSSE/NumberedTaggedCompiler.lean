import NSSE.HornRuleEnumeration
import NSSE.HornSOACompiler
import NSSE.TaggedCompiler

/-!
# Numbering finite tagged states

An explicit `Enumeration State` is converted to the natural-number
indices required by `FiniteHornCompiler`.  Parent and child vectors are
decoded safely; out-of-range indices never enable a terminal or rule.
-/

namespace NSSE

universe u

namespace Enumeration

def stateCount (states : Enumeration State) : Nat :=
  states.values.length

def decode (states : Enumeration State) (index : Nat) : Option State :=
  states.values[index]?

theorem decode_some_lt
    (states : Enumeration State) {index : Nat} {state : State}
    (hdecode : states.decode index = some state) :
    index < states.stateCount := by
  unfold decode stateCount at *
  exact (List.getElem?_eq_some_iff.mp hdecode).choose

theorem decode_of_lt
    (states : Enumeration State) {index : Nat}
    (hindex : index < states.stateCount) :
    ∃ state, states.decode index = some state := by
  refine ⟨states.values[index], ?_⟩
  exact List.getElem?_eq_getElem hindex

theorem exists_index_decode
    (states : Enumeration State) (state : State) :
    ∃ index,
      index < states.stateCount ∧
      states.decode index = some state := by
  obtain ⟨index, hindex, hget⟩ :=
    List.mem_iff_getElem.mp (states.complete state)
  refine ⟨index, hindex, ?_⟩
  rw [decode, List.getElem?_eq_getElem hindex, hget]

end Enumeration

def decodeStateVector
    (states : Enumeration State) : List Nat → Option (List State)
  | [] => some []
  | index :: indices => do
      let state ← states.decode index
      let rest ← decodeStateVector states indices
      pure (state :: rest)

theorem decodeStateVector_length
    (states : Enumeration State)
    {indices : List Nat} {decoded : List State}
    (hdecode : decodeStateVector states indices = some decoded) :
    decoded.length = indices.length := by
  induction indices generalizing decoded with
  | nil =>
      simp [decodeStateVector] at hdecode
      subst decoded
      rfl
  | cons index indices ih =>
      simp only [decodeStateVector] at hdecode
      cases hstate : states.decode index with
      | none => simp [hstate] at hdecode
      | some state =>
          cases hrest : decodeStateVector states indices with
          | none => simp [hstate, hrest] at hdecode
          | some rest =>
              simp [hstate, hrest] at hdecode
              subst decoded
              simp [ih hrest]

theorem decodeStateVector_exists_of_bounded
    (states : Enumeration State) (indices : List Nat)
    (hbounded :
      ∀ index ∈ indices, index < states.stateCount) :
    ∃ decoded,
      decodeStateVector states indices = some decoded := by
  induction indices with
  | nil =>
      exact ⟨[], rfl⟩
  | cons index indices ih =>
      obtain ⟨state, hstate⟩ :=
        states.decode_of_lt
          (hbounded index (by simp))
      obtain ⟨rest, hrest⟩ :=
        ih (fun child hchild =>
          hbounded child (by simp [hchild]))
      exact ⟨state :: rest, by
        simp [decodeStateVector, hstate, hrest]⟩

structure NumberedRuleSystem (State : Type u) where
  states : Enumeration State
  arities : List Nat
  terminal : State → Bool
  enabled : State → List State → Bool

namespace NumberedRuleSystem

def numberedTerminal
    (system : NumberedRuleSystem State) (index : Nat) : Bool :=
  match system.states.decode index with
  | some state => system.terminal state
  | none => false

def numberedEnabled
    (system : NumberedRuleSystem State) (rule : HornRule) : Bool :=
  match system.states.decode rule.parent,
      decodeStateVector system.states rule.children with
  | some parent, some children => system.enabled parent children
  | _, _ => false

def compiler (system : NumberedRuleSystem State) :
    FiniteHornCompiler :=
  enumeratedHornCompiler system.states.stateCount system.arities
    system.numberedTerminal system.numberedEnabled

theorem numberedTerminal_eq
    (system : NumberedRuleSystem State)
    {index : Nat} {state : State}
    (hdecode : system.states.decode index = some state) :
    system.numberedTerminal index = system.terminal state := by
  simp [numberedTerminal, hdecode]

theorem numberedEnabled_eq
    (system : NumberedRuleSystem State)
    (rule : HornRule) {parent : State} {children : List State}
    (hparent : system.states.decode rule.parent = some parent)
    (hchildren :
      decodeStateVector system.states rule.children = some children) :
    system.numberedEnabled rule =
      system.enabled parent children := by
  simp [numberedEnabled, hparent, hchildren]

theorem enabled_rule_decodes
    (system : NumberedRuleSystem State) {rule : HornRule}
    (hwell : rule.WellFormed
      system.states.stateCount system.arities)
    (henabled : system.numberedEnabled rule = true) :
    ∃ parent children,
      system.states.decode rule.parent = some parent ∧
      decodeStateVector system.states rule.children = some children ∧
      children.length ∈ system.arities ∧
      system.enabled parent children = true := by
  obtain ⟨parent, hparent⟩ :=
    system.states.decode_of_lt hwell.1
  obtain ⟨children, hchildren⟩ :=
    decodeStateVector_exists_of_bounded
      system.states rule.children hwell.2.2
  refine ⟨parent, children, hparent, hchildren, ?_, ?_⟩
  · rw [decodeStateVector_length system.states hchildren]
    exact hwell.2.1
  · simpa [system.numberedEnabled_eq rule hparent hchildren]
      using henabled

inductive TaggedDerives
    (system : NumberedRuleSystem State) : State → Prop where
  | terminal {state : State}
      (terminal_true : system.terminal state = true) :
      TaggedDerives system state
  | rule {parent : State} {children : List State}
      (arity : children.length ∈ system.arities)
      (enabled_true : system.enabled parent children = true)
      (child_derives :
        ∀ child ∈ children, TaggedDerives system child) :
      TaggedDerives system parent

namespace TaggedDerives

theorem sound
    {system : NumberedRuleSystem State}
    (meaning : State → Prop)
    (terminal_sound :
      ∀ state,
        system.terminal state = true →
        meaning state)
    (rule_sound :
      ∀ parent children,
        system.enabled parent children = true →
        (∀ child ∈ children, meaning child) →
        meaning parent)
    {state : State}
    (derive : system.TaggedDerives state) :
    meaning state := by
  induction derive with
  | terminal hterminal =>
      exact terminal_sound _ hterminal
  | rule harity henabled hchildren ih =>
      exact rule_sound _ _ henabled
        (fun child hchild => ih child hchild)

theorem sound_exists
    {system : NumberedRuleSystem State}
    (meaning : State → Prop)
    (terminal_sound :
      ∀ state,
        system.terminal state = true →
        meaning state)
    (rule_sound :
      ∀ parent children,
        system.enabled parent children = true →
        (∀ child ∈ children, meaning child) →
        meaning parent)
    {states : List State}
    (derive :
      ∃ state ∈ states, system.TaggedDerives state) :
    ∃ state ∈ states, meaning state := by
  obtain ⟨state, hstate, hderive⟩ := derive
  exact ⟨state, hstate,
    hderive.sound meaning terminal_sound rule_sound⟩

end TaggedDerives

theorem chooseDecodedIndices
    (system : NumberedRuleSystem State)
    (states : List State) (P : Nat → Prop)
    (hchoose :
      ∀ state ∈ states,
        ∃ index,
          system.states.decode index = some state ∧ P index) :
    ∃ indices,
      decodeStateVector system.states indices = some states ∧
      ∀ index ∈ indices, P index := by
  induction states with
  | nil =>
      exact ⟨[], rfl, by simp⟩
  | cons state states ih =>
      obtain ⟨index, hdecode, hP⟩ :=
        hchoose state (by simp)
      obtain ⟨indices, hindices, hPs⟩ :=
        ih (fun child hchild =>
          hchoose child (by simp [hchild]))
      exact ⟨index :: indices, by
        simp [decodeStateVector, hdecode, hindices], by
          intro candidate hcandidate
          simp only [List.mem_cons] at hcandidate
          rcases hcandidate with rfl | hcandidate
          · exact hP
          · exact hPs candidate hcandidate⟩

theorem transferDecodedVector
    (system : NumberedRuleSystem State)
    {indices : List Nat} {states : List State}
    (hdecode :
      decodeStateVector system.states indices = some states)
    (P : State → Prop)
    (hindex :
      ∀ index ∈ indices,
        ∃ state,
          system.states.decode index = some state ∧ P state) :
    ∀ state ∈ states, P state := by
  induction indices generalizing states with
  | nil =>
      simp [decodeStateVector] at hdecode
      subst states
      simp
  | cons index indices ih =>
      simp only [decodeStateVector] at hdecode
      cases hhead : system.states.decode index with
      | none => simp [hhead] at hdecode
      | some head =>
          cases htail :
              decodeStateVector system.states indices with
          | none => simp [hhead, htail] at hdecode
          | some tail =>
              simp [hhead, htail] at hdecode
              subst states
              have hPhead : P head := by
                obtain ⟨decoded, hdecoded, hP⟩ :=
                  hindex index (by simp)
                rw [hhead] at hdecoded
                simp at hdecoded
                subst decoded
                exact hP
              have hPtail : ∀ state ∈ tail, P state :=
                ih htail (fun child hchild =>
                  hindex child (by simp [hchild]))
              intro state hstate
              simp only [List.mem_cons] at hstate
              rcases hstate with rfl | hstate
              · exact hPhead
              · exact hPtail state hstate

theorem taggedDerives_iff_numberedHorn
    (system : NumberedRuleSystem State) (state : State) :
    TaggedDerives system state ↔
      ∃ index,
        system.states.decode index = some state ∧
        HornDerives system.compiler index := by
  constructor
  · intro hderive
    induction hderive with
    | @terminal state terminal_true =>
        obtain ⟨index, hindex, hdecode⟩ :=
          system.states.exists_index_decode state
        refine ⟨index, hdecode, .terminal hindex ?_⟩
        simpa [compiler, enumeratedHornCompiler,
          numberedTerminal, hdecode] using terminal_true
    | @rule parent children arity enabled_true child_derives ih =>
        obtain ⟨parentIndex, hparentIndex, hparentDecode⟩ :=
          system.states.exists_index_decode parent
        obtain ⟨childIndices, hchildrenDecode, hchildDerives⟩ :=
          chooseDecodedIndices system children
            (fun index => HornDerives system.compiler index)
            (fun child hchild => ih child hchild)
        let rule : HornRule := ⟨parentIndex, childIndices⟩
        have hchildrenLength :
            childIndices.length = children.length := by
          symm
          exact decodeStateVector_length
            system.states hchildrenDecode
        have hchildrenBounded :
            ∀ child ∈ childIndices,
              child < system.states.stateCount := by
          intro child hchild
          obtain ⟨decoded, hdecoded⟩ :=
            system.states.decode_of_lt
              (by
                have hderived := hchildDerives child hchild
                exact HornDerives.state_lt hderived)
          exact system.states.decode_some_lt hdecoded
        have hwell :
            rule.WellFormed
              system.states.stateCount system.arities :=
          ⟨hparentIndex, by
            dsimp [rule]
            rw [hchildrenLength]
            exact arity, hchildrenBounded⟩
        have henabled :
            system.numberedEnabled rule = true := by
          simpa [rule, system.numberedEnabled_eq rule
            hparentDecode hchildrenDecode] using enabled_true
        refine ⟨parentIndex, hparentDecode, ?_⟩
        apply HornDerives.rule
          ((enumeratedHornCompiler_rule_mem_iff
            system.states.stateCount system.arities
            system.numberedTerminal system.numberedEnabled rule).2
              ⟨hwell, henabled⟩)
          hparentIndex
        exact hchildDerives
  · rintro ⟨index, hdecode, hderive⟩
    induction hderive generalizing state with
    | @terminal terminalIndex state_lt terminal_true =>
        change system.numberedTerminal terminalIndex = true
          at terminal_true
        apply TaggedDerives.terminal
        rw [system.numberedTerminal_eq hdecode] at terminal_true
        exact terminal_true
    | @rule rule rule_mem parent_lt children ih =>
        have hmem :=
          (enumeratedHornCompiler_rule_mem_iff
            system.states.stateCount system.arities
            system.numberedTerminal system.numberedEnabled rule).1
            rule_mem
        obtain ⟨parent, decodedChildren, hparent,
            hdecodedChildren, harity, henabled⟩ :=
          system.enabled_rule_decodes hmem.1 hmem.2
        rw [hdecode] at hparent
        simp at hparent
        subst parent
        apply TaggedDerives.rule harity henabled
        apply transferDecodedVector system hdecodedChildren
          (TaggedDerives system)
        intro child hchild
        obtain ⟨decoded, hdecoded⟩ :=
          system.states.decode_of_lt
            (HornDerives.state_lt (children child hchild))
        exact ⟨decoded, hdecoded,
          ih child hchild decoded hdecoded⟩

theorem TaggedDerives.toHornAt
    (system : NumberedRuleSystem State)
    {state : State} (hderive : TaggedDerives system state)
    {index : Nat}
    (hdecode : system.states.decode index = some state) :
    HornDerives system.compiler index := by
  induction hderive generalizing index with
  | @terminal state terminal_true =>
      exact .terminal
        (system.states.decode_some_lt hdecode)
        (by
          change system.numberedTerminal index = true
          rw [system.numberedTerminal_eq hdecode]
          exact terminal_true)
  | @rule parent children arity enabled_true child_derives ih =>
      have hchoose :
          ∀ child ∈ children,
            ∃ childIndex,
              system.states.decode childIndex = some child ∧
              HornDerives system.compiler childIndex := by
        intro child hchild
        obtain ⟨childIndex, _, hchildDecode⟩ :=
          system.states.exists_index_decode child
        exact ⟨childIndex, hchildDecode,
          ih child hchild hchildDecode⟩
      obtain ⟨childIndices, hchildrenDecode, hchildDerives⟩ :=
        chooseDecodedIndices system children
          (fun childIndex =>
            HornDerives system.compiler childIndex)
          hchoose
      let rule : HornRule := ⟨index, childIndices⟩
      have hchildrenLength :
          childIndices.length = children.length := by
        symm
        exact decodeStateVector_length
          system.states hchildrenDecode
      have hchildrenBounded :
          ∀ child ∈ childIndices,
            child < system.states.stateCount := by
        intro child hchild
        exact (hchildDerives child hchild).state_lt
      have hwell :
          rule.WellFormed
            system.states.stateCount system.arities :=
        ⟨system.states.decode_some_lt hdecode, by
          dsimp [rule]
          rw [hchildrenLength]
          exact arity, hchildrenBounded⟩
      have henabled :
          system.numberedEnabled rule = true := by
        simpa [rule, system.numberedEnabled_eq rule
          hdecode hchildrenDecode] using enabled_true
      apply HornDerives.rule
        ((enumeratedHornCompiler_rule_mem_iff
          system.states.stateCount system.arities
          system.numberedTerminal system.numberedEnabled rule).2
            ⟨hwell, henabled⟩)
        hwell.1
      exact hchildDerives

theorem decideState_correct
    (system : NumberedRuleSystem State)
    (index : Nat) (hindex : index < system.states.stateCount) :
    decideHornState system.compiler index = true ↔
      ∃ state,
        system.states.decode index = some state ∧
        TaggedDerives system state := by
  rw [decideHornState_correct system.compiler index hindex]
  constructor
  · intro hderive
    obtain ⟨state, hdecode⟩ :=
      system.states.decode_of_lt hindex
    exact ⟨state, hdecode,
      (system.taggedDerives_iff_numberedHorn state).2
        ⟨index, hdecode, hderive⟩⟩
  · rintro ⟨state, hdecode, hderive⟩
    exact hderive.toHornAt system hdecode

end NumberedRuleSystem

structure NumberedTaggedSOACertificate
    {α : Type u} (I : SOAInstance α) (State : Type u) where
  system : NumberedRuleSystem State
  rootState : State
  rootIndex : Nat
  root_decode :
    system.states.decode rootIndex = some rootState
  root_correct :
    system.TaggedDerives rootState ↔
      ∃ word, I.Avoider word

namespace NumberedTaggedSOACertificate

def toHornRootCertificate
    {I : SOAInstance α}
    (certificate : NumberedTaggedSOACertificate I State) :
    HornSOARootCertificate I where
  compiler := certificate.system.compiler
  root := certificate.rootIndex
  root_lt :=
    certificate.system.states.decode_some_lt certificate.root_decode
  root_correct := by
    constructor
    · intro hhorn
      apply certificate.root_correct.1
      exact
        (certificate.system.taggedDerives_iff_numberedHorn
          certificate.rootState).2
          ⟨certificate.rootIndex, certificate.root_decode, hhorn⟩
    · intro havoider
      exact
        (certificate.root_correct.2 havoider).toHornAt
          certificate.system certificate.root_decode

def toCertifiedSOACompiler
    {I : SOAInstance α}
    (certificate : NumberedTaggedSOACertificate I State) :
    CertifiedSOACompiler I :=
  certificate.toHornRootCertificate.toCertifiedSOACompiler

theorem decideAvoider_correct
    {I : SOAInstance α}
    (certificate : NumberedTaggedSOACertificate I State) :
    certificate.toCertifiedSOACompiler.decideAvoider = true ↔
      ∃ word, I.Avoider word :=
  certificate.toCertifiedSOACompiler.decideAvoider_correct

end NumberedTaggedSOACertificate

end NSSE
