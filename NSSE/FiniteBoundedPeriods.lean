import NSSE.FiniteDFAOperations
import NSSE.BoundedPeriodAutomaton
import NSSE.RegularSkeleton

/-! # Existing period monitors become actual Fin-indexed input DFAs

The monitor stores a bounded root buffer and a cyclic comparison offset.
Its general soundness/completeness theorems are reused; only the executable
state enumeration and finite union are assembled here.
-/

deriving instance DecidableEq for NSSE.PeriodMonitorState

namespace NSSE.FiniteBoundedPeriods

open FiniteSOARankDecision FiniteDFAOperations

variable {α : Type} [DecidableEq α]

instance monitorAcceptDecision (A : InputDFA α) (p : Nat) (hp : 0 < p) :
    DecidablePred (boundedPeriodDFA A.automaton p hp).accept := by
  intro q
  dsimp [boundedPeriodDFA]
  infer_instance

def fixed (alphabet : Enumeration α) (A : InputDFA α) (p : Nat) (hp : 0 < p) : InputDFA α :=
  let states := periodMonitorStateEnumeration alphabet (finEnumeration A.count) p
  ofEnumerated (boundedPeriodDFA A.automaton p hp) states.values states.complete

theorem fixed_accepts (alphabet : Enumeration α) (A : InputDFA α) (p : Nat) (hp : 0 < p) (xs : List α) :
    (fixed alphabet A p hp).automaton.Accepts xs ↔
      Word.HasPeriod xs p ∧ A.automaton.Accepts (xs.take p) := by
  rw [fixed, ofEnumerated_accepts]
  exact ⟨fun h => ⟨boundedPeriodDFA_accepts_hasPeriod A.automaton p hp xs h,
    (boundedPeriodDFA_accepts_root A.automaton p hp xs h).2⟩,
    fun h => boundedPeriodDFA_complete A.automaton p hp xs h.1 h.2⟩

def bounded (alphabet : Enumeration α) (A : InputDFA α) (bound : Nat) : InputDFA α :=
  unions ((List.finRange bound).map (fun i => fixed alphabet A (i.val + 1) (Nat.zero_lt_succ _)))

theorem bounded_accepts (alphabet : Enumeration α) (A : InputDFA α) (bound : Nat) (xs : List α) :
    (bounded alphabet A bound).automaton.Accepts xs ↔ BoundedPeriodLanguage A.automaton.language bound xs := by
  rw [bounded, unions_accepts]
  constructor
  · rintro ⟨M, hM, hx⟩
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hM
    obtain ⟨hp, hr⟩ := (fixed_accepts alphabet A (i.val + 1) (Nat.zero_lt_succ _) xs).mp hx
    exact ⟨i.val + 1, Nat.zero_lt_succ _, i.isLt, hp, hr⟩
  · rintro ⟨p, hp, hpb, hper, hr⟩
    let i : Fin bound := ⟨p - 1, by omega⟩
    have he : i.val + 1 = p := by dsimp [i]; omega
    refine ⟨fixed alphabet A (i.val + 1) (Nat.zero_lt_succ _),
      List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩, ?_⟩
    apply (fixed_accepts alphabet A (i.val + 1) (Nat.zero_lt_succ _) xs).mpr
    simpa only [he] using And.intro hper hr

end NSSE.FiniteBoundedPeriods
