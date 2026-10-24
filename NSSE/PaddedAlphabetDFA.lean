import NSSE.CapAlphabetPadding

/-! Executable finite-DFA transport into an alphabet with two extra letters. -/

namespace NSSE.PaddedAlphabetDFA

open FiniteSOARankDecision

variable {d : Nat}

def embed (a : Fin d) : Fin (d+2) := Fin.castAdd 2 a

theorem embed_injective : Function.Injective (embed (d := d)) := by
  intro a b h
  exact Fin.ext (congrArg (fun x : Fin (d+2) => x.val) h)

def letter (x : Fin (d+2)) : Option (Fin d) :=
  if h : x.val < d then some ⟨x.val,h⟩ else none

theorem letter_eq_some (x : Fin (d+2)) (a : Fin d) : letter x = some a ↔ embed a = x := by
  by_cases h : x.val < d
  · simp [letter, h, embed, Fin.ext_iff, eq_comm]
  · have hne : embed a ≠ x := by
      intro he
      have hv := congrArg (fun x : Fin (d+2) => x.val) he
      change a.val = x.val at hv
      have ha := a.isLt
      omega
    simp [letter, h, hne]

def decode : List (Fin (d+2)) → Option (List (Fin d))
  | [] => some []
  | x::xs => (letter x).bind (fun a => (decode xs).map (a::·))

theorem decode_eq_some (ys : List (Fin (d+2))) (xs : List (Fin d)) :
    decode ys = some xs ↔ xs.map embed = ys := by
  induction ys generalizing xs with
  | nil => cases xs <;> simp [decode]
  | cons y ys ih =>
    cases xs with
    | nil => simp [decode, Option.bind_eq_some_iff]
    | cons x xs =>
      simp [decode, Option.bind_eq_some_iff, Option.map_eq_some_iff, List.map_cons, ih, letter_eq_some]

def raw {Q : Type} (A : DFA (Fin d) Q) : DFA (Fin (d+2)) (Option Q) where
  start := some A.start
  step q x := q.bind (fun q => (letter x).map (A.step q))
  accept q := ∃ r, q = some r ∧ A.accept r

instance raw_accept {Q : Type} [DecidableEq Q] (A : DFA (Fin d) Q) [DecidablePred A.accept] :
    DecidablePred (raw A).accept := by
  intro q
  cases q with
  | none => exact isFalse (by rintro ⟨r,h,_⟩; cases h)
  | some q => exact decidable_of_iff (A.accept q) (by simp [raw])

theorem raw_run_none {Q : Type} (A : DFA (Fin d) Q) (ys : List (Fin (d+2))) :
    (raw A).runFrom none ys = none := by
  induction ys with
  | nil => rfl
  | cons y ys ih => exact ih

theorem raw_run {Q : Type} (A : DFA (Fin d) Q) (q : Q) (ys : List (Fin (d+2))) :
    (raw A).runFrom (some q) ys = (decode ys).map (A.runFrom q) := by
  induction ys generalizing q with
  | nil => rfl
  | cons y ys ih =>
    rw [DFA.runFrom_cons]
    change (raw A).runFrom ((letter y).map (A.step q)) ys = _
    cases hl : letter y with
    | none => simp only [Option.map_none', raw_run_none, decode, hl, Option.none_bind]
    | some a =>
      simp only [Option.map_some', ih, decode, hl, Option.some_bind, Option.map_map]
      rfl

theorem raw_accepts {Q : Type} (A : DFA (Fin d) Q) (ys : List (Fin (d+2))) :
    (raw A).Accepts ys ↔ CapAlphabetImage.image embed A.language ys := by
  change (∃ r, (raw A).runFrom (some A.start) ys = some r ∧ A.accept r) ↔ _
  rw [raw_run]
  simp only [Option.map_eq_some_iff]
  constructor
  · rintro ⟨r,⟨xs,hx,he⟩,hr⟩
    exact ⟨xs,by simpa only [DFA.language, DFA.Accepts, DFA.run, he] using hr,(decode_eq_some ys xs).mp hx⟩
  · rintro ⟨xs,hx,he⟩
    exact ⟨A.runFrom A.start xs,⟨xs,(decode_eq_some ys xs).mpr he,rfl⟩,hx⟩

def lift (A : InputDFA (Fin d)) : InputDFA (Fin (d+2)) :=
  FiniteCapTerminal.reindex (raw A.automaton) (finSuccEquiv' (Fin.last A.count)).symm

theorem lift_count (A : InputDFA (Fin d)) : (lift A).count = A.count+1 := rfl

theorem lift_accepts (A : InputDFA (Fin d)) (ys : List (Fin (d+2))) :
    (lift A).automaton.Accepts ys ↔ CapAlphabetImage.image embed A.automaton.language ys := by
  rw [lift, FiniteCapTerminal.reindex_accepts, raw_accepts]

end NSSE.PaddedAlphabetDFA
