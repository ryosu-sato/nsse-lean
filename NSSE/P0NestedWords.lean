import NSSE.P0NestedSelection

/-! Actual finite words supply the bounded nested repetition. Padding
uses an existing first letter and is used only outside the source word. -/
namespace NSSE.P0NestedWords
open P0ProperWords P0NestedRepeats P0NestedSelection
variable {A : Type*}

def pad (w : List A) (hw : 0 < w.length) (k : Nat) : A :=
  w[k]?.getD w[0]

theorem pad_spells (w : List A) (hw : 0 < w.length) : Spells (pad w hw) w := by
  intro k hk
  simp only [pad,List.getElem?_eq_getElem hk,Option.getD_some]

theorem pad_letters (w : List A) (hw : 0 < w.length) (alphabet : Finset A)
    (ha : ∀ x ∈ w, x ∈ alphabet) (k : Nat) : pad w hw k ∈ alphabet := by
  unfold pad
  cases he : w[k]? with
  | none => exact ha w[0] (List.getElem_mem ..)
  | some x => exact ha x (List.mem_of_getElem? he)

variable [DecidableEq A]

theorem word_nested (alphabet : Finset A) (w : List A)
    (ha : ∀ x ∈ w, x ∈ alphabet) (k s : Nat)
    (hlen : s+bound alphabet k ≤ w.length) :
    ∃ z : Nat → A, Spells z w ∧ ∃ a L,
      s ≤ a ∧ a+L ≤ s+bound alphabet k ∧ a+L ≤ w.length ∧ Nest z a L k := by
  have hw : 0 < w.length := by have := bound_positive alphabet k; omega
  obtain ⟨a,L,hs,he,hn⟩ := exists_nested alphabet (pad w hw) (pad_letters w hw alphabet ha) k s
  exact ⟨pad w hw,pad_spells w hw,a,L,hs,he,he.trans hlen,hn⟩

end NSSE.P0NestedWords
