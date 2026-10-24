import NSSE.AddressedSuffixPresburger

/-!
# Complete Presburger split-route search over addressed cuts
-/

namespace NSSE

universe u v₁ v₂

inductive AddressedCutCase (arity : Nat)
  | initial (offset : Nat)
  | pump (index : Fin arity) (offset : Nat)
  | separator (index : Fin arity) (offset : Nat)
  | terminal
deriving DecidableEq

namespace LinearWordFamily

def addressedCutPosition
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) :
    AddressedCutCase arity → Nat → Nat
  | .initial offset, _ => offset
  | .pump index offset, copy =>
      family.addressPosition parameters index copy offset
  | .separator index offset, _ =>
      family.separatorAddressPosition parameters index offset
  | .terminal, _ => (family.word parameters).length

def AddressedCutWitness
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) :
    AddressedCutCase arity → Nat → Prop
  | .initial offset, _ =>
      family.ValidInitialAddress offset
  | .pump index offset, copy =>
      family.ValidPumpAddress parameters index copy offset
  | .separator index offset, _ =>
      family.ValidSeparatorAddress index offset
  | .terminal, _ => True

def addressedCutPrefix
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) :
    AddressedCutCase arity → Nat → Word α
  | .initial offset, _ =>
      family.initialAddressPrefix offset
  | .pump index offset, copy =>
      family.addressPrefix parameters index copy offset
  | .separator index offset, _ =>
      family.separatorAddressPrefix parameters index offset
  | .terminal, _ => family.word parameters

theorem take_word_eq_addressedCutPrefix
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (cut : AddressedCutCase arity)
    (copy : Nat)
    (hvalid : family.AddressedCutWitness parameters cut copy) :
    (family.word parameters).take
        (family.addressedCutPosition parameters cut copy) =
      family.addressedCutPrefix parameters cut copy := by
  cases cut with
  | initial offset =>
      have hword :=
        family.word_eq_initialAddress_decomposition parameters offset
      have hlength :
          (family.initialAddressPrefix offset).length = offset := by
        simp [initialAddressPrefix, ValidInitialAddress,
          Nat.min_eq_left hvalid]
      change
        (family.word parameters).take offset =
          family.initialAddressPrefix offset
      rw [hword]
      simp only [List.append_assoc]
      exact List.take_left' hlength
  | pump index offset =>
      obtain ⟨rest, hword⟩ :=
        family.word_eq_addressPrefix_decomposition parameters
          index copy offset hvalid
      have hlength :=
        family.addressPrefix_length parameters index copy offset
          hvalid.2
      change
        (family.word parameters).take
            (family.addressPosition parameters index copy offset) =
          family.addressPrefix parameters index copy offset
      rw [hword]
      exact List.take_left' hlength
  | separator index offset =>
      have hword :=
        family.word_eq_separatorAddress_decomposition
          parameters index offset
      have hlength :=
        family.separatorAddressPrefix_length parameters index
          offset hvalid
      change
        (family.word parameters).take
            (family.separatorAddressPosition parameters index offset) =
          family.separatorAddressPrefix parameters index offset
      rw [hword]
      simp only [List.append_assoc]
      exact List.take_left' hlength
  | terminal =>
      simp [addressedCutPosition, addressedCutPrefix]

noncomputable def addressedCutPrefixStatePredicateFormula
    [Fintype Q₁]
    (automaton : DFA α Q₁)
    (family : LinearWordFamily α arity)
    (predicate : Q₁ → Prop) :
    AddressedCutCase arity → NatPresburger arity
  | .initial offset =>
      family.validInitialAddressStatePredicateFormula automaton
        offset predicate
  | .pump index offset =>
      family.existsValidAddressedStatePredicateFormula automaton
        index offset predicate
  | .separator index offset =>
      family.validSeparatorAddressStatePredicateFormula automaton
        index offset predicate
  | .terminal =>
      NatPresburger.poweredStatePredicateFormula
        (family.dfaStages automaton)
        (automaton.run family.initial) predicate

noncomputable def addressedCutSuffixStatePredicateFormula
    [Fintype Q₂]
    (automaton : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (predicate : Q₂ → Prop) :
    AddressedCutCase arity → NatPresburger arity
  | .initial offset =>
      family.validInitialSuffixStatePredicateFormula automaton
        offset predicate
  | .pump index offset =>
      family.existsPumpSuffixStatePredicateFormula automaton
        index offset predicate
  | .separator index offset =>
      family.validSeparatorSuffixStatePredicateFormula automaton
        index offset predicate
  | .terminal => by
      classical
      exact
        if predicate (automaton.run [])
          then NatPresburger.truth
          else .falsum

def AddressedCutPrefixStateWitness
    (automaton : DFA α Q₁)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (predicate : Q₁ → Prop)
    (cut : AddressedCutCase arity) : Prop :=
  ∃ copy,
    family.AddressedCutWitness parameters cut copy ∧
      predicate
        (automaton.run
          (family.addressedCutPrefix parameters cut copy))

def AddressedCutSuffixStateWitness
    (automaton : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (predicate : Q₂ → Prop)
    (cut : AddressedCutCase arity) : Prop :=
  ∃ copy,
    family.AddressedCutWitness parameters cut copy ∧
      predicate
        (automaton.run
          ((family.word parameters).drop
            (family.addressedCutPosition parameters cut copy)))

theorem eval_addressedCutPrefixStatePredicateFormula_iff
    [Fintype Q₁]
    (automaton : DFA α Q₁)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (predicate : Q₁ → Prop)
    (cut : AddressedCutCase arity) :
    (family.addressedCutPrefixStatePredicateFormula automaton
      predicate cut).Eval parameters ↔
      family.AddressedCutPrefixStateWitness automaton parameters
        predicate cut := by
  cases cut with
  | initial offset =>
      rw [addressedCutPrefixStatePredicateFormula,
        family.eval_validInitialAddressStatePredicateFormula_iff]
      constructor
      · intro h
        exact ⟨0, h⟩
      · rintro ⟨copy, h⟩
        exact h
  | pump index offset =>
      rw [addressedCutPrefixStatePredicateFormula,
        family.eval_existsValidAddressedStatePredicateFormula_iff]
      simp only [AddressedCutPrefixStateWitness,
        AddressedCutWitness, addressedCutPrefix]
      constructor
      · rintro ⟨copy, hvalid, hpredicate⟩
        refine ⟨copy, hvalid, ?_⟩
        rw [DFA.run_addressPrefix]
        exact hpredicate
      · rintro ⟨copy, hvalid, hpredicate⟩
        refine ⟨copy, hvalid, ?_⟩
        rw [← DFA.run_addressPrefix]
        exact hpredicate
  | separator index offset =>
      rw [addressedCutPrefixStatePredicateFormula,
        family.eval_validSeparatorAddressStatePredicateFormula_iff]
      constructor
      · intro h
        exact ⟨0, h⟩
      · rintro ⟨copy, h⟩
        exact h
  | terminal =>
      rw [addressedCutPrefixStatePredicateFormula,
        NatPresburger.poweredStatePredicateFormula_correct,
        family.evaluate_dfaStages]
      constructor
      · intro h
        exact ⟨0, trivial, h⟩
      · rintro ⟨copy, hvalid, hpredicate⟩
        exact hpredicate

theorem eval_addressedCutSuffixStatePredicateFormula_iff
    [Fintype Q₂]
    (automaton : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (predicate : Q₂ → Prop)
    (cut : AddressedCutCase arity) :
    (family.addressedCutSuffixStatePredicateFormula automaton
      predicate cut).Eval parameters ↔
      family.AddressedCutSuffixStateWitness automaton parameters
        predicate cut := by
  cases cut with
  | initial offset =>
      rw [addressedCutSuffixStatePredicateFormula,
        family.eval_validInitialSuffixStatePredicateFormula_iff]
      constructor
      · rintro ⟨hvalid, hpredicate⟩
        refine ⟨0, hvalid, ?_⟩
        change predicate
          (automaton.run ((family.word parameters).drop offset))
        rw [family.drop_word_eq_initialSuffixWord
          parameters offset hvalid]
        exact hpredicate
      · rintro ⟨copy, hvalid, hpredicate⟩
        refine ⟨hvalid, ?_⟩
        change predicate
          (automaton.run ((family.word parameters).drop offset))
          at hpredicate
        rw [family.drop_word_eq_initialSuffixWord
          parameters offset hvalid] at hpredicate
        exact hpredicate
  | pump index offset =>
      exact family.eval_existsPumpSuffixStatePredicateFormula_iff
        automaton parameters index offset predicate
  | separator index offset =>
      rw [addressedCutSuffixStatePredicateFormula,
        family.eval_validSeparatorSuffixStatePredicateFormula_iff]
      constructor
      · rintro ⟨hvalid, hpredicate⟩
        refine ⟨0, hvalid, ?_⟩
        change predicate
          (automaton.run
            ((family.word parameters).drop
              (family.separatorAddressPosition parameters
                index offset)))
        rw [family.drop_word_eq_separatorSuffixWord
          parameters index offset hvalid]
        exact hpredicate
      · rintro ⟨copy, hvalid, hpredicate⟩
        refine ⟨hvalid, ?_⟩
        change predicate
          (automaton.run
            ((family.word parameters).drop
              (family.separatorAddressPosition parameters
                index offset))) at hpredicate
        rw [family.drop_word_eq_separatorSuffixWord
          parameters index offset hvalid] at hpredicate
        exact hpredicate
  | terminal =>
      classical
      by_cases hpredicate : predicate (automaton.run [])
      · simp [addressedCutSuffixStatePredicateFormula,
          hpredicate, NatPresburger.truth, NatPresburger.Eval,
          AddressedCutSuffixStateWitness,
          AddressedCutWitness, addressedCutPosition]
      · simp [addressedCutSuffixStatePredicateFormula,
          hpredicate, NatPresburger.Eval,
          AddressedCutSuffixStateWitness,
          AddressedCutWitness, addressedCutPosition]

def pumpSplitPrefixFinalStage
    (automaton : DFA α Q₁)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (offset : Nat) :
    PoweredStateStage (arity + 2) Q₁ where
  coordinate := (Fin.last arity).castSucc
  powerStep := fun state =>
    automaton.runFrom state (family.pump index)
  separatorStep := fun state =>
    automaton.runFrom state ((family.pump index).take offset)

def pumpSplitPrefixStages
    (automaton : DFA α Q₁)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (offset : Nat) :
    List (PoweredStateStage (arity + 2) Q₁) :=
  ((List.finRange arity).filter
      (fun earlier => earlier < index)).map
        (family.pumpSuffixLaterStage automaton) ++
    [family.pumpSplitPrefixFinalStage automaton index offset]

theorem evaluate_pumpSplitPrefixStages
    (automaton : DFA α Q₁)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (startCopy remaining offset : Nat) :
    PoweredStateStage.evaluate
        (family.pumpSplitPrefixStages automaton index offset)
        (pumpRemainingValuation parameters startCopy remaining)
        (automaton.run family.initial) =
      automaton.run
        (family.addressPrefix parameters index startCopy offset) := by
  unfold pumpSplitPrefixStages
  rw [PoweredStateStage.evaluate_append]
  rw [family.evaluate_pumpSuffixLaterStages]
  simp only [PoweredStateStage.evaluate,
    pumpSplitPrefixFinalStage, pumpRemainingValuation,
    NatPresburger.extendValuation_castSucc,
    NatPresburger.extendValuation_last]
  unfold addressPrefix
  have hstage :
      family.stageBlock parameters =
        (fun earlier =>
          Word.power (family.pump earlier)
              (parameters earlier) ++
            family.separator earlier) := rfl
  rw [hstage]
  simp only [automaton.run_append,
    automaton.runFrom_append,
    automaton.runFrom_word_power_eq_iterate,
    List.append_assoc]

noncomputable def pumpSplitPrefixStatePredicateFormula
    [Fintype Q₁]
    (automaton : DFA α Q₁)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (offset : Nat)
    (predicate : Q₁ → Prop) :
    NatPresburger (arity + 2) :=
  NatPresburger.poweredStatePredicateFormula
    (family.pumpSplitPrefixStages automaton index offset)
    (automaton.run family.initial) predicate

noncomputable def existsPumpSplitStatePredicatesFormula
    [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (offset : Nat)
    (leftPredicate : Q₁ → Prop)
    (rightPredicate : Q₂ → Prop) :
    NatPresburger arity :=
  .existsQ <| .existsQ <| .conj
    (family.pumpSplitPrefixStatePredicateFormula left
      index offset leftPredicate)
    (family.validPumpSuffixStatePredicateFormula right
      index offset rightPredicate)

theorem eval_existsPumpSplitStatePredicatesFormula_iff
    [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : DFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (offset : Nat)
    (leftPredicate : Q₁ → Prop)
    (rightPredicate : Q₂ → Prop) :
    (family.existsPumpSplitStatePredicatesFormula left right
      index offset leftPredicate rightPredicate).Eval parameters ↔
      ∃ startCopy remaining,
        family.ValidPumpSuffixAddress parameters index
            startCopy remaining offset ∧
          leftPredicate
            (left.run
              (family.addressPrefix parameters index
                startCopy offset)) ∧
          rightPredicate
            (right.run
              (family.pumpSuffixWord parameters index
                remaining offset)) := by
  simp only [existsPumpSplitStatePredicatesFormula,
    NatPresburger.Eval]
  constructor
  · rintro ⟨startCopy, remaining, hleft, hright⟩
    have hleft' :=
      (NatPresburger.poweredStatePredicateFormula_correct
        (family.pumpSplitPrefixStages left index offset)
        (left.run family.initial) leftPredicate
        (pumpRemainingValuation parameters startCopy remaining)).1
          hleft
    rw [family.evaluate_pumpSplitPrefixStages] at hleft'
    have hright' :=
      (family.eval_validPumpSuffixStatePredicateFormula_iff
        right parameters index startCopy remaining offset
        rightPredicate).1 hright
    exact ⟨startCopy, remaining, hright'.1, hleft', hright'.2⟩
  · rintro ⟨startCopy, remaining, hvalid, hleft, hright⟩
    refine ⟨startCopy, remaining, ?_, ?_⟩
    · apply
        (NatPresburger.poweredStatePredicateFormula_correct
          (family.pumpSplitPrefixStages left index offset)
          (left.run family.initial) leftPredicate
          (pumpRemainingValuation parameters startCopy remaining)).2
      rw [family.evaluate_pumpSplitPrefixStages]
      exact hleft
    · exact
        (family.eval_validPumpSuffixStatePredicateFormula_iff
          right parameters index startCopy remaining offset
          rightPredicate).2 ⟨hvalid, hright⟩

noncomputable def addressedSplitRouteCaseFormula
    [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (cut : AddressedCutCase arity) :
    NatPresburger arity :=
  match cut with
  | .pump index offset =>
      family.existsPumpSplitStatePredicatesFormula
        left right.automaton index offset left.accept
        (fun state => right.productive state = true)
  | _ =>
      .conj
        (family.addressedCutPrefixStatePredicateFormula left
          left.accept cut)
        (family.addressedCutSuffixStatePredicateFormula right.automaton
          (fun state => right.productive state = true) cut)

def AddressedSplitRouteCaseWitness
    (left : DFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (cut : AddressedCutCase arity) : Prop :=
  ∃ copy,
    family.AddressedCutWitness parameters cut copy ∧
      left.Accepts
        ((family.word parameters).take
          (family.addressedCutPosition parameters cut copy)) ∧
      Language.prefixClosure right.language
        ((family.word parameters).drop
          (family.addressedCutPosition parameters cut copy))

theorem eval_addressedSplitRouteCaseFormula_iff
    [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (cut : AddressedCutCase arity) :
    (family.addressedSplitRouteCaseFormula left right cut).Eval
        parameters ↔
      family.AddressedSplitRouteCaseWitness left right parameters
        cut := by
  cases cut with
  | initial offset =>
      simp only [addressedSplitRouteCaseFormula,
        NatPresburger.Eval]
      rw [family.eval_addressedCutPrefixStatePredicateFormula_iff,
        family.eval_addressedCutSuffixStatePredicateFormula_iff]
      constructor
      · rintro ⟨⟨prefixCopy, hvalid, hleft⟩,
          ⟨suffixCopy, hsuffixValid, hright⟩⟩
        refine ⟨0, hvalid, ?_, ?_⟩
        · unfold DFA.Accepts
          rw [family.take_word_eq_addressedCutPrefix
            parameters (.initial offset) 0 hvalid]
          exact hleft
        · exact (right.prefixClosure_iff _).2 hright
      · rintro ⟨copy, hvalid, hleft, hright⟩
        constructor
        · refine ⟨0, hvalid, ?_⟩
          unfold DFA.Accepts at hleft
          rw [family.take_word_eq_addressedCutPrefix
            parameters (.initial offset) copy hvalid] at hleft
          exact hleft
        · exact ⟨0, hvalid,
            (right.prefixClosure_iff _).1 hright⟩
  | separator index offset =>
      simp only [addressedSplitRouteCaseFormula,
        NatPresburger.Eval]
      rw [family.eval_addressedCutPrefixStatePredicateFormula_iff,
        family.eval_addressedCutSuffixStatePredicateFormula_iff]
      constructor
      · rintro ⟨⟨prefixCopy, hvalid, hleft⟩,
          ⟨suffixCopy, hsuffixValid, hright⟩⟩
        refine ⟨0, hvalid, ?_, ?_⟩
        · unfold DFA.Accepts
          rw [family.take_word_eq_addressedCutPrefix
            parameters (.separator index offset) 0 hvalid]
          exact hleft
        · exact (right.prefixClosure_iff _).2 hright
      · rintro ⟨copy, hvalid, hleft, hright⟩
        constructor
        · refine ⟨0, hvalid, ?_⟩
          unfold DFA.Accepts at hleft
          rw [family.take_word_eq_addressedCutPrefix
            parameters (.separator index offset) copy hvalid] at hleft
          exact hleft
        · exact ⟨0, hvalid,
            (right.prefixClosure_iff _).1 hright⟩
  | terminal =>
      simp only [addressedSplitRouteCaseFormula,
        NatPresburger.Eval]
      rw [family.eval_addressedCutPrefixStatePredicateFormula_iff,
        family.eval_addressedCutSuffixStatePredicateFormula_iff]
      constructor
      · rintro ⟨⟨prefixCopy, hvalid, hleft⟩,
          ⟨suffixCopy, hsuffixValid, hright⟩⟩
        refine ⟨0, trivial, ?_,
          (right.prefixClosure_iff _).2 hright⟩
        unfold DFA.Accepts
        rw [family.take_word_eq_addressedCutPrefix
          parameters .terminal 0 trivial]
        exact hleft
      · rintro ⟨copy, hvalid, hleft, hright⟩
        constructor
        · refine ⟨0, trivial, ?_⟩
          unfold DFA.Accepts at hleft
          rw [family.take_word_eq_addressedCutPrefix
            parameters .terminal copy trivial] at hleft
          exact hleft
        · exact
            ⟨0, trivial, (right.prefixClosure_iff _).1 hright⟩
  | pump index offset =>
      rw [addressedSplitRouteCaseFormula,
        family.eval_existsPumpSplitStatePredicatesFormula_iff]
      constructor
      · rintro ⟨copy, remaining, hvalid, hleft, hright⟩
        have hpump :
            family.ValidPumpAddress parameters index copy offset :=
          ⟨by rw [hvalid.1]; omega, hvalid.2⟩
        refine ⟨copy, hpump, ?_, ?_⟩
        · unfold DFA.Accepts
          rw [family.take_word_eq_addressedCutPrefix
            parameters (.pump index offset) copy hpump]
          exact hleft
        · rw [right.prefixClosure_iff]
          change
            right.productive
              (right.automaton.run
                ((family.word parameters).drop
                  (family.addressPosition parameters index
                    copy offset))) = true
          rw [family.drop_word_eq_pumpSuffixWord parameters index
            copy remaining offset hvalid]
          exact hright
      · rintro ⟨copy, hpump, hleft, hright⟩
        let remaining := parameters index - (copy + 1)
        have hvalid :
            family.ValidPumpSuffixAddress parameters index
              copy remaining offset := by
          exact ⟨by
            dsimp [remaining]
            have hcopy := hpump.1
            omega, hpump.2⟩
        refine ⟨copy, remaining, hvalid, ?_, ?_⟩
        · unfold DFA.Accepts at hleft
          rw [family.take_word_eq_addressedCutPrefix
            parameters (.pump index offset) copy hpump] at hleft
          exact hleft
        · have hproductive := (right.prefixClosure_iff _).1 hright
          change
            right.productive
              (right.automaton.run
                ((family.word parameters).drop
                  (family.addressPosition parameters index
                    copy offset))) = true at hproductive
          rw [family.drop_word_eq_pumpSuffixWord parameters index
            copy remaining offset hvalid] at hproductive
          exact hproductive

def allAddressedCutCases
    (family : LinearWordFamily α arity) :
    List (AddressedCutCase arity) :=
  (List.range (family.initial.length + 1)).map .initial ++
  (List.finRange arity).flatMap (fun index =>
    (List.range ((family.pump index).length + 1)).map
      (.pump index)) ++
  (List.finRange arity).flatMap (fun index =>
    (List.range ((family.separator index).length + 1)).map
      (.separator index)) ++
  [.terminal]

theorem addressedCutPosition_le_word_length
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (cut : AddressedCutCase arity)
    (copy : Nat)
    (hvalid : family.AddressedCutWitness parameters cut copy) :
    family.addressedCutPosition parameters cut copy ≤
      (family.word parameters).length := by
  cases cut with
  | initial offset =>
      have hword :=
        family.word_eq_initialAddress_decomposition parameters offset
      have hlength :
          (family.initialAddressPrefix offset).length = offset := by
        simp [initialAddressPrefix, ValidInitialAddress,
          Nat.min_eq_left hvalid]
      have := congrArg List.length hword
      simp only [List.length_append] at this
      change offset ≤ (family.word parameters).length
      omega
  | pump index offset =>
      obtain ⟨rest, hword⟩ :=
        family.word_eq_addressPrefix_decomposition parameters
          index copy offset hvalid
      have hlength :=
        family.addressPrefix_length parameters index copy offset
          hvalid.2
      have := congrArg List.length hword
      simp only [List.length_append] at this
      change
        family.addressPosition parameters index copy offset ≤
          (family.word parameters).length
      omega
  | separator index offset =>
      have hword :=
        family.word_eq_separatorAddress_decomposition
          parameters index offset
      have hlength :=
        family.separatorAddressPrefix_length parameters index
          offset hvalid
      have := congrArg List.length hword
      simp only [List.length_append] at this
      change
        family.separatorAddressPosition parameters index offset ≤
          (family.word parameters).length
      omega
  | terminal => simp [addressedCutPosition]

theorem exists_addressedCut_at_position
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (position : Nat)
    (hposition : position ≤ (family.word parameters).length) :
    ∃ cut ∈ family.allAddressedCutCases, ∃ copy,
      family.AddressedCutWitness parameters cut copy ∧
      family.addressedCutPosition parameters cut copy = position := by
  by_cases hterminal :
      position = (family.word parameters).length
  · refine ⟨.terminal, ?_, 0, trivial, ?_⟩
    · simp [allAddressedCutCases]
    · simp [addressedCutPosition, hterminal]
  · have hstrict :
        position < (family.word parameters).length := by omega
    obtain ⟨zone, hstart, hend⟩ :=
      family.exists_zone_containing_position
        parameters position hstrict
    cases zone with
    | initial =>
        refine ⟨.initial position, ?_, 0, ?_, rfl⟩
        · simp [allAddressedCutCases]
          change position < family.initial.length at hend
          omega
        · change family.ValidInitialAddress position
          change position < family.initial.length at hend
          exact Nat.le_of_lt hend
    | separator index =>
        let offset :=
          position - family.pumpEndPosition parameters index
        have hoffset :
            offset < (family.separator index).length := by
          change
            family.pumpEndPosition parameters index ≤ position
              at hstart
          change
            position <
              family.separatorEndPosition parameters index at hend
          unfold separatorEndPosition at hend
          dsimp [offset]
          omega
        refine ⟨.separator index offset, ?_, 0, ?_, ?_⟩
        · simp [allAddressedCutCases]
          omega
        · exact Nat.le_of_lt hoffset
        · change
            family.separatorAddressPosition parameters index offset =
              position
          unfold separatorAddressPosition
          dsimp [offset]
          change
            family.pumpEndPosition parameters index ≤ position at hstart
          omega
    | pump index =>
        let blockLength := (family.pump index).length
        have hblockLength : 0 < blockLength := by
          exact family.pump_length_positive hnonempty index
        let relative :=
          position - family.stageStartPosition parameters index
        let copy := relative / blockLength
        let offset := relative % blockLength
        have hrelative :
            relative <
              parameters index * blockLength := by
          change
            position <
              family.pumpEndPosition parameters index at hend
          unfold pumpEndPosition at hend
          dsimp [relative, blockLength]
          change
            family.stageStartPosition parameters index ≤ position
              at hstart
          omega
        have hcopy : copy < parameters index := by
          dsimp [copy]
          rw [Nat.div_lt_iff_lt_mul hblockLength]
          simpa [Nat.mul_comm] using hrelative
        have hoffset : offset < blockLength := by
          exact Nat.mod_lt _ hblockLength
        refine ⟨.pump index offset, ?_, copy, ?_, ?_⟩
        · simp [allAddressedCutCases]
          dsimp [blockLength] at hoffset
          omega
        · exact ⟨hcopy, Nat.le_of_lt hoffset⟩
        · change
            family.addressPosition parameters index copy offset =
              position
          change
            family.stageStartPosition parameters index +
                  copy * (family.pump index).length +
                offset =
              position
          dsimp [copy, offset, relative, blockLength]
          have hdivision :
              ((position -
                    family.stageStartPosition parameters index) /
                  (family.pump index).length) *
                    (family.pump index).length +
                (position -
                    family.stageStartPosition parameters index) %
                  (family.pump index).length =
                position -
                  family.stageStartPosition parameters index := by
            simpa [Nat.mul_comm] using
              Nat.div_add_mod
                (position -
                  family.stageStartPosition parameters index)
                (family.pump index).length
          change
            family.stageStartPosition parameters index ≤ position
              at hstart
          omega

noncomputable def allAddressedSplitRoutesFormula
    [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity) :
    NatPresburger arity :=
  NatPresburger.disjoin <|
    family.allAddressedCutCases.map
      (family.addressedSplitRouteCaseFormula left right)

theorem eval_allAddressedSplitRoutesFormula_iff
    [Fintype Q₁] [Fintype Q₂]
    (left : DFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) :
    (family.allAddressedSplitRoutesFormula left right).Eval
        parameters ↔
      ∃ cut ∈ family.allAddressedCutCases,
        family.AddressedSplitRouteCaseWitness left right parameters
          cut := by
  rw [allAddressedSplitRoutesFormula,
    NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_map] at hformula
    obtain ⟨cut, hcut, rfl⟩ := hformula
    exact ⟨cut, hcut,
      (family.eval_addressedSplitRouteCaseFormula_iff
        left right parameters cut).1 heval⟩
  · rintro ⟨cut, hcut, hwitness⟩
    exact
      ⟨family.addressedSplitRouteCaseFormula left right cut,
        List.mem_map.mpr ⟨cut, hcut, rfl⟩,
        (family.eval_addressedSplitRouteCaseFormula_iff
          left right parameters cut).2 hwitness⟩

theorem eval_allAddressedSplitRoutesFormula_iff_splitRoute
    [Fintype Q₁] [Fintype Q₂]
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat) :
    (family.allAddressedSplitRoutesFormula
      left.automaton right).Eval parameters ↔
      SplitRoute (automataCapComponent left right)
        (family.word parameters) := by
  rw [family.eval_allAddressedSplitRoutesFormula_iff]
  constructor
  · rintro ⟨cut, hcut, copy, hvalid, hleft, hright⟩
    let position :=
      family.addressedCutPosition parameters cut copy
    refine ⟨position,
      family.addressedCutPosition_le_word_length
        parameters cut copy hvalid, ?_, hright⟩
    exact hleft
  · rintro ⟨position, hposition, hleft, hright⟩
    obtain ⟨cut, hcut, copy, hvalid, hpositionEq⟩ :=
      family.exists_addressedCut_at_position
        hnonempty parameters position hposition
    refine ⟨cut, hcut, copy, hvalid, ?_, ?_⟩
    · simpa [hpositionEq] using hleft
    · simpa [hpositionEq] using hright

end LinearWordFamily

end NSSE
