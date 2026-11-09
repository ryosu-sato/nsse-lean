import NSSE.MultiConstructorTrees
import NSSE.P0ProperWords

/-! Full normalized D/Z branches. Continuation and final transitions can
coexist on the same letter. Final state IDs are retained for births, while
the ordered pair of terminal labels is fixed by the branch. -/
namespace NSSE.P0DZBranch
open MultiConstructorTrees P0ProperWords
variable {Q Z A H : Type*}

structure Branch (Q Z A H : Type*) where
  initial : Q
  next : Q → A → Option Q
  final : Q → A → Option Z
  head : Q → H
  endX : Label H
  endY : Label H
  birth : Q ⊕ Z → Bool → Q ⊕ Z → Bool → Prop

def advance (J : Branch Q Z A H) : Option Q → A → Option Q
  | some q, a => J.next q a
  | none, _ => none

def properFrom (J : Branch Q Z A H) (q : Q) (w : List A) : Option Q :=
  w.foldl (advance J) (some q)

def finishFrom (J : Branch Q Z A H) (q : Q) : List A → Option Z
  | [] => none
  | [a] => J.final q a
  | a::b::v => (J.next q a).bind (fun r => finishFrom J r (b::v))

def terminal (J : Branch Q Z A H) (w : List A) : Option Z := finishFrom J J.initial w
def Complete (J : Branch Q Z A H) (w : List A) : Prop := (terminal J w).isSome = true

def stateAt (J : Branch Q Z A H) (w : List A) (k : Nat) : Option (Q ⊕ Z) :=
  if k < w.length then (properFrom J J.initial (w.take k)).map Sum.inl
  else (terminal J w).map Sum.inr

def endpoint (J : Branch Q Z A H) (s : Bool) : Label H := if s then J.endY else J.endX

def labelAt (J : Branch Q Z A H) (w : List A) (s : Bool) (k : Nat) : Label H :=
  match stateAt J w k with
  | some (.inl q) => .node (J.head q)
  | some (.inr _) => endpoint J s
  | none => .bot

/-- Extreme labels never count as a common proper constructor. -/
def Agree : Label H → Label H → Prop
  | .node h, .node k => h = k
  | _, _ => False

instance [DecidableEq H] : DecidableRel (@Agree H) := by
  intro a b
  cases a <;> cases b <;> unfold Agree <;> infer_instance

def Compatible (J : Branch Q Z A H) (w : List A) (a : Nat) (s : Bool) (b : Nat) (t : Bool) : Prop :=
  ∀ l, l ≤ w.length → a+l ≤ w.length → b+l ≤ w.length → WordMatch w a b l →
    Agree (labelAt J w s (a+l)) (labelAt J w t (b+l))

def bornAt (J : Branch Q Z A H) (w : List A) (a : Nat) (s : Bool) (b : Nat) (t : Bool) : Prop :=
  ∃ q r, stateAt J w a = some q ∧ stateAt J w b = some r ∧ J.birth q s r t

def Safe (J : Branch Q Z A H) (w : List A) : Prop :=
  ∀ a, a ≤ w.length → ∀ b, b ≤ w.length → ∀ s t, a ≠ b ∨ s ≠ t →
    bornAt J w a s b t → Compatible J w a s b t

def Accepted (J : Branch Q Z A H) (w : List A) : Prop := Complete J w ∧ Safe J w

theorem fold_failure (J : Branch Q Z A H) (w : List A) : w.foldl (advance J) none = none := by
  induction w with
  | nil => rfl
  | cons a w ih => exact ih

theorem proper_cons (J : Branch Q Z A H) (q : Q) (a : A) (w : List A) :
    properFrom J q (a::w) = (J.next q a).bind (fun r => properFrom J r w) := by
  simp only [properFrom,List.foldl_cons,advance]
  cases he : J.next q a
  · exact fold_failure J w
  · rfl

theorem finish_cons_append (J : Branch Q Z A H) (q : Q) (a b : A) (w : List A) :
    finishFrom J q (a::(w++[b])) = (J.next q a).bind (fun r => finishFrom J r (w++[b])) := by
  cases w <;> rfl

theorem finish_append (J : Branch Q Z A H) (q : Q) (w : List A) (a : A) :
    finishFrom J q (w++[a]) = (properFrom J q w).bind (fun r => J.final r a) := by
  induction w generalizing q with
  | nil => rfl
  | cons b w ih =>
    rw [List.cons_append,finish_cons_append,proper_cons]
    simp only [ih,Option.bind_assoc]

theorem complete_nonempty (J : Branch Q Z A H) (w : List A) (hc : Complete J w) : w ≠ [] := by
  intro he
  subst w
  cases hc

theorem terminal_state (J : Branch Q Z A H) (w : List A) :
    stateAt J w w.length = (terminal J w).map Sum.inr := by simp only [stateAt,lt_self_iff_false,if_false]

theorem proper_state (J : Branch Q Z A H) (w : List A) (k : Nat) (hk : k < w.length) :
    stateAt J w k = (properFrom J J.initial (w.take k)).map Sum.inl := by rw [stateAt,if_pos hk]

end NSSE.P0DZBranch
