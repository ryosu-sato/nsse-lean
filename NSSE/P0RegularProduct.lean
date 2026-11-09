import NSSE.P0ProperWordLemmas
import Mathlib.Computability.DFA

/-! Actual synchronous product with a supplied finite automaton. Births
and heads come from the original control; erasure is on OLD states before
forming the product, not on pairs of product states. -/
namespace NSSE.P0RegularProduct
open P0ProperMachine P0ProperWords
variable {Q S A H : Type*}

def product (M : Machine Q A H) (F : DFA A S) : Machine (Q × S) A H where
  initial := (M.initial,F.start)
  step q a := (M.step q.1 a,F.step q.2 a)
  valid q := M.valid q.1
  head q := M.head q.1
  birth q t := M.birth q.1 t.1

theorem fold_product (M : Machine Q A H) (F : DFA A S) (w : List A) (q : Q) (s : S) :
    w.foldl (product M F).step (q,s) = (w.foldl M.step q,w.foldl F.step s) := by
  induction w generalizing q s with
  | nil => rfl
  | cons a w ih => exact ih (M.step q a) (F.step s a)

theorem state_product (M : Machine Q A H) (F : DFA A S) (w : List A) (k : Nat) :
    state (product M F) w k = (state M w k,F.eval (w.take k)) :=
  fold_product M F (w.take k) M.initial F.start

theorem goodWord_product (M : Machine Q A H) (F : DFA A S) (w : List A) :
    GoodWord (product M F) w ↔ GoodWord M w := by
  simp only [GoodWord,state_product]
  rfl

def erasedProduct (M : Machine Q A H) (F : DFA A S) : Machine (Q × S) A H :=
  product (eraseEqual M) F

theorem goodWord_erasedProduct (M : Machine Q A H) (F : DFA A S) (w : List A) :
    GoodWord (erasedProduct M F) w ↔ GoodWord M w :=
  (goodWord_product (eraseEqual M) F w).trans (P0ProperWordLemmas.goodWord_eraseEqual M w)

theorem final_filter (M : Machine Q A H) (F : DFA A S) (w : List A) :
    (state (erasedProduct M F) w w.length).2 ∈ F.accept ↔ w ∈ F.accepts := by
  simp only [erasedProduct,state_product,List.take_length]
  rfl

theorem accepts_intersection (M : Machine Q A H) (F : DFA A S) (w : List A) :
    (GoodWord (erasedProduct M F) w ∧ (state (erasedProduct M F) w w.length).2 ∈ F.accept) ↔
      GoodWord M w ∧ w ∈ F.accepts := by
  rw [goodWord_erasedProduct,final_filter]

end NSSE.P0RegularProduct
