import NSSE.Automata
import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Basic

/-!
# Canonical padded convolutions and exact tape selection

Columns are tuples of optional letters. Nonempty columns and monotonically
ending tapes define canonical convolutions. Every finite tuple of words has
one such representation, and deleting tapes erases only empty columns.
-/

namespace NSSE.CanonicalConvolution

universe u
variable {D : Type u} {k l : Nat}

abbrev Column (D : Type u) (k : Nat) := Fin k → Option D
abbrev Tuple (D : Type u) (k : Nat) := Fin k → List D

def active (c : Column D k) (i : Fin k) : Bool := (c i).isSome

def present (c : Column D k) : Bool :=
  (List.finRange k).any (active c)

theorem present_iff (c : Column D k) : present c = true ↔ ∃ i, active c i = true := by
  simp [present, List.any_eq_true]

def ValidFrom (a : Fin k → Bool) : List (Column D k) → Prop
  | [] => True
  | c :: w => present c = true ∧
      (∀ i, active c i = true → a i = true) ∧ ValidFrom (active c) w

def Canonical (w : List (Column D k)) : Prop := ValidFrom (fun _ => true) w

def decode (w : List (Column D k)) (i : Fin k) : List D :=
  w.filterMap (fun c => c i)

theorem validFrom_mono {a b : Fin k → Bool} {w : List (Column D k)}
    (h : ValidFrom a w) (hab : ∀ i, a i = true → b i = true) : ValidFrom b w := by
  cases w with
  | nil => trivial
  | cons c w => exact ⟨h.1, fun i hi => hab i (h.2.1 i hi), h.2.2⟩

theorem inactive_decode {a : Fin k → Bool} {w : List (Column D k)}
    (hw : ValidFrom a w) (i : Fin k) (hi : a i = false) : decode w i = [] := by
  induction w generalizing a with
  | nil => rfl
  | cons c w ih =>
      cases hc : c i with
      | none =>
          have ht := ih hw.2.2 (by simp [active, hc])
          simpa [decode, hc] using ht
      | some x =>
          have h := hw.2.1 i (by simp [active, hc])
          rw [hi] at h
          cases h

theorem head_decode {a : Fin k → Bool} {c : Column D k} {w : List (Column D k)}
    (hw : ValidFrom a (c :: w)) (i : Fin k) : (decode (c :: w) i).head? = c i := by
  cases hc : c i with
  | none =>
      have ht := inactive_decode hw.2.2 i (by simp [active, hc])
      simp only [decode, List.filterMap_cons, hc]
      change (decode w i).head? = none
      rw [ht]
      rfl
  | some x => simp [decode, hc]

theorem tail_decode {a : Fin k → Bool} {c : Column D k} {w : List (Column D k)}
    (hw : ValidFrom a (c :: w)) (i : Fin k) : (decode (c :: w) i).tail = decode w i := by
  cases hc : c i with
  | none =>
      have ht := inactive_decode hw.2.2 i (by simp [active, hc])
      simp only [decode, List.filterMap_cons, hc]
      change (decode w i).tail = decode w i
      rw [ht]
      rfl
  | some x => simp [decode, hc]

theorem eq_nil_of_decode_nil {a : Fin k → Bool} {w : List (Column D k)}
    (hw : ValidFrom a w) (hd : ∀ i, decode w i = []) : w = [] := by
  cases w with
  | nil => rfl
  | cons c w =>
      obtain ⟨i, hi⟩ := (present_iff c).mp hw.1
      have hc : c i = none := (head_decode hw i).symm.trans (congrArg List.head? (hd i))
      simp [active, hc] at hi

/-- The same decoded tuple cannot have two different valid padded representations. -/
theorem decode_injective {a b : Fin k → Bool} {v w : List (Column D k)}
    (hv : ValidFrom a v) (hw : ValidFrom b w) (he : decode v = decode w) : v = w := by
  induction v generalizing a b w with
  | nil =>
      have hn : w = [] := eq_nil_of_decode_nil hw (fun i => (congrFun he i).symm)
      exact hn.symm
  | cons c v ih =>
      cases w with
      | nil => exact eq_nil_of_decode_nil hv (fun i => congrFun he i)
      | cons d w =>
          have hcd : c = d := by
            funext i
            exact (head_decode hv i).symm.trans
              ((congrArg (fun t => (t i).head?) he).trans (head_decode hw i))
          have htail : decode v = decode w := by
            funext i
            exact (tail_decode hv i).symm.trans
              ((congrArg (fun t => (t i).tail) he).trans (tail_decode hw i))
          exact congrArg₂ List.cons hcd (ih hv.2.2 hw.2.2 htail)

def projectColumn (f : Fin l → Fin k) (c : Column D k) : Option (Column D l) :=
  if present (c ∘ f) then some (c ∘ f) else none

def project (f : Fin l → Fin k) (w : List (Column D k)) : List (Column D l) :=
  w.filterMap (projectColumn f)

theorem project_cons_keep (f : Fin l → Fin k) (c : Column D k) (w : List (Column D k))
    (hc : present (c ∘ f) = true) :
    project f (c :: w) = (c ∘ f) :: project f w := by
  simp only [project, List.filterMap_cons, projectColumn, if_pos hc]

theorem project_cons_erase (f : Fin l → Fin k) (c : Column D k) (w : List (Column D k))
    (hc : ¬ present (c ∘ f) = true) : project f (c :: w) = project f w := by
  simp only [project, List.filterMap_cons, projectColumn, if_neg hc]

/-- Selecting tapes preserves their words even before any padding assumption. -/
theorem decode_project (f : Fin l → Fin k) (w : List (Column D k)) :
    decode (project f w) = decode w ∘ f := by
  funext i
  induction w with
  | nil => rfl
  | cons c w ih =>
      by_cases hc : present (c ∘ f) = true
      · rw [project_cons_keep f c w hc]
        cases hi : c (f i) with
        | none => simpa only [decode, List.filterMap_cons, Function.comp_apply, hi] using ih
        | some x => simpa only [decode, List.filterMap_cons, Function.comp_apply, hi] using
            congrArg (List.cons x) ih
      · have hn : c (f i) = none := by
          cases h : c (f i) with
          | none => rfl
          | some x =>
              exact (hc ((present_iff _).mpr ⟨i, by simp [active, Function.comp_def, h]⟩)).elim
        rw [project_cons_erase f c w hc]
        simpa only [decode, List.filterMap_cons, Function.comp_apply, hn] using ih

theorem validFrom_project (f : Fin l → Fin k) {a : Fin k → Bool}
    {w : List (Column D k)} (hw : ValidFrom a w) :
    ValidFrom (a ∘ f) (project f w) := by
  induction w generalizing a with
  | nil => trivial
  | cons c w ih =>
      by_cases hc : present (c ∘ f) = true
      · rw [project_cons_keep f c w hc]
        exact ⟨hc, fun i hi => hw.2.1 (f i) hi, ih hw.2.2⟩
      · have htail := ih hw.2.2
        have hmono : ∀ i, (active c ∘ f) i = true → (a ∘ f) i = true :=
          fun i hi => hw.2.1 (f i) hi
        rw [project_cons_erase f c w hc]
        exact validFrom_mono htail hmono

theorem canonical_project (f : Fin l → Fin k) {w : List (Column D k)}
    (hw : Canonical w) : Canonical (project f w) := validFrom_project f hw

def heads (t : Tuple D k) (i : Fin k) : Option D := (t i).head?
def tails (t : Tuple D k) (i : Fin k) : List D := (t i).tail

def encodeAux : Nat → Tuple D k → List (Column D k)
  | 0, _ => []
  | n + 1, t => if present (heads t) then heads t :: encodeAux n (tails t) else []

theorem validFrom_encodeAux (n : Nat) (t : Tuple D k) (a : Fin k → Bool)
    (ha : ∀ i, t i ≠ [] → a i = true) : ValidFrom a (encodeAux n t) := by
  induction n generalizing t a with
  | zero => trivial
  | succ n ih =>
      by_cases hp : present (heads t) = true
      · simp only [encodeAux, hp, ↓reduceIte]
        refine ⟨hp, ?_, ih (tails t) (active (heads t)) ?_⟩
        · intro i hi
          apply ha i
          intro he
          simp [active, heads, he] at hi
        · intro i hi
          cases ht : t i with
          | nil => exact (hi (by simp [tails, ht])).elim
          | cons x xs => simp [active, heads, ht]
      · simp [encodeAux, hp, ValidFrom]

theorem decode_encodeAux (n : Nat) (t : Tuple D k)
    (ht : ∀ i, (t i).length ≤ n) : decode (encodeAux n t) = t := by
  induction n generalizing t with
  | zero =>
      funext i
      exact (List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (ht i))).symm
  | succ n ih =>
      have htail : ∀ i, ((tails t) i).length ≤ n := by
        intro i
        simp only [tails, List.length_tail]
        have := ht i
        omega
      by_cases hp : present (heads t) = true
      · have he := ih (tails t) htail
        funext i
        have hi := congrFun he i
        cases hti : t i with
        | nil => simpa [encodeAux, hp, decode, heads, tails, hti] using hi
        | cons x xs =>
            simpa [encodeAux, hp, decode, heads, tails, hti] using congrArg (List.cons x) hi
      · funext i
        have hn : t i = [] := by
          cases hti : t i with
          | nil => rfl
          | cons x xs =>
              exact (hp ((present_iff _).mpr ⟨i, by simp [active, heads, hti]⟩)).elim
        simp [encodeAux, hp, decode, hn]

/-- An explicit list maximum avoids any choice of a finite enumeration. -/
def height (t : Tuple D k) : Nat :=
  ((List.finRange k).map (fun i => (t i).length)).foldr max 0

theorem le_fold_max (ns : List Nat) (n : Nat) (hn : n ∈ ns) : n ≤ ns.foldr max 0 := by
  induction ns with
  | nil => simp at hn
  | cons a ns ih =>
      rcases List.mem_cons.mp hn with rfl | hn
      · exact Nat.le_max_left _ _
      · exact (ih hn).trans (Nat.le_max_right _ _)

theorem le_height (t : Tuple D k) (i : Fin k) : (t i).length ≤ height t :=
  le_fold_max _ _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)

def encode (t : Tuple D k) : List (Column D k) := encodeAux (height t) t

theorem decode_encode (t : Tuple D k) : decode (encode t) = t := by
  apply decode_encodeAux
  intro i
  exact le_height t i

theorem canonical_encode (t : Tuple D k) : Canonical (encode t) :=
  validFrom_encodeAux _ t _ (fun _ _ => rfl)

theorem encode_decode {w : List (Column D k)} (hw : Canonical w) :
    encode (decode w) = w :=
  decode_injective (canonical_encode _) hw (decode_encode _)

/-- Dropping tapes from a canonical tuple representation gives exactly the
canonical representation of the selected tuple, even for zero visible tapes. -/
theorem project_encode (f : Fin l → Fin k) (t : Tuple D k) :
    project f (encode t) = encode (t ∘ f) := by
  apply decode_injective (canonical_project f (canonical_encode t)) (canonical_encode _)
  rw [decode_project, decode_encode, decode_encode]

def stepAllowed (a : Fin k → Bool) (c : Column D k) : Bool :=
  present c && decide (∀ i, active c i = true → a i = true)

theorem stepAllowed_iff (a : Fin k → Bool) (c : Column D k) :
    stepAllowed a c = true ↔
      present c = true ∧ (∀ i, active c i = true → a i = true) := by
  simp [stepAllowed]

/-- The finite DFA that enforces canonical padding, not an assumed regularity witness. -/
def monitor (D : Type u) (k : Nat) : NSSE.DFA (Column D k) (Option (Fin k → Bool)) where
  start := some (fun _ => true)
  step S c := match S with
    | none => none
    | some a => if stepAllowed a c then some (active c) else none
  accept S := S.isSome = true

theorem monitor_dead (w : List (Column D k)) :
    (monitor D k).runFrom none w = none := by
  induction w with
  | nil => rfl
  | cons c w ih => exact ih

theorem monitor_valid (a : Fin k → Bool) (w : List (Column D k)) :
    ((monitor D k).runFrom (some a) w).isSome = true ↔ ValidFrom a w := by
  induction w generalizing a with
  | nil => simp [ValidFrom]
  | cons c w ih =>
      rw [NSSE.DFA.runFrom_cons]
      change ((monitor D k).runFrom
        (if stepAllowed a c then some (active c) else none) w).isSome = true ↔ _
      by_cases ha : stepAllowed a c = true
      · rw [if_pos ha, ih]
        have hh := (stepAllowed_iff a c).mp ha
        exact ⟨fun hw => ⟨hh.1, hh.2, hw⟩, fun hw => hw.2.2⟩
      · rw [if_neg ha, monitor_dead]
        constructor
        · intro h
          cases h
        · intro hw
          exact (ha ((stepAllowed_iff a c).mpr ⟨hw.1, hw.2.1⟩)).elim

theorem monitor_correct (w : List (Column D k)) :
    (monitor D k).Accepts w ↔ Canonical w := monitor_valid _ w

theorem monitor_state_count (k : Nat) :
    Fintype.card (Option (Fin k → Bool)) = 2 ^ k + 1 := by
  simp

/-- After canonical padding is enforced, existential image of columns is
exactly existential selection of WORDS. The omitted words have no length bound. -/
theorem tuple_image_iff (R : List (Column D k) → Prop) (f : Fin l → Fin k)
    (t : Tuple D l) :
    (∃ w, (monitor D k).Accepts w ∧ R w ∧ project f w = encode t) ↔
      ∃ s : Tuple D k, R (encode s) ∧ s ∘ f = t := by
  constructor
  · rintro ⟨w, hc, hr, hp⟩
    have hc' := (monitor_correct w).mp hc
    refine ⟨decode w, ?_, ?_⟩
    · rwa [encode_decode hc']
    · have he := congrArg decode hp
      rwa [decode_project, decode_encode] at he
  · rintro ⟨s, hr, rfl⟩
    exact ⟨encode s, (monitor_correct _).mpr (canonical_encode s), hr, project_encode f s⟩

theorem project_zero (w : List (Column D k)) :
    project (Fin.elim0 : Fin 0 → Fin k) w = [] := by
  simp [project, projectColumn, present]

end NSSE.CanonicalConvolution
