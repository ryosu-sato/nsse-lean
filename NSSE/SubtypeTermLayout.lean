import NSSE.SubtypeTerms

/-! # Computable finite variable layout for term flattening

Old variables, term slots, inequality slots, then one shared padding
variable. Duplicate subterms are allowed; references use their first index.
No finite-type equivalence or fresh-name choice is supplied by the caller.
-/

namespace NSSE.SubtypeTermLayout

open SubtypeTerms
open SubtypeConstraints (Constructor)

structure Layout (n d : Nat) where
  terms : List (Term n d)
  pairs : List (Term n d × Term n d)

variable {n d : Nat}

def layout (Q : Query n d) : Layout n d := ⟨SubtypeTerms.terms Q, expanded Q⟩

def Layout.count (L : Layout n d) : Nat := n + (L.terms.length + (L.pairs.length + 1))

def Layout.old (L : Layout n d) (x : Fin n) : Fin L.count := Fin.castAdd _ x

def Layout.termSlot (L : Layout n d) (j : Fin L.terms.length) : Fin L.count :=
  Fin.natAdd n (Fin.castAdd _ j)

def Layout.edgeSlot (L : Layout n d) (j : Fin L.pairs.length) : Fin L.count :=
  Fin.natAdd n (Fin.natAdd L.terms.length (Fin.castAdd 1 j))

def Layout.padding (L : Layout n d) : Fin L.count :=
  Fin.natAdd n (Fin.natAdd L.terms.length (Fin.natAdd L.pairs.length (0 : Fin 1)))

def Layout.ref (L : Layout n d) (t : Term n d) : Fin L.count :=
  match t with
  | .var x => L.old x
  | t => if h : t ∈ L.terms then L.termSlot ⟨L.terms.idxOf t,List.idxOf_lt_length_iff.mpr h⟩
    else L.padding

def padded {α : Type*} (i : Fin d) (a e : α) (j : Fin d) : α := if j = i then a else e

section Semantics

variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

def Layout.restrict (L : Layout n d) (σ : Fin L.count → T) (x : Fin n) : T := σ (L.old x)

def Layout.extend (L : Layout n d) (i : Fin d) (F : Constructor T d) (ρ : Fin n → T) :
    Fin L.count → T :=
  Fin.addCases ρ (Fin.addCases (fun j => eval F ρ L.terms[j.val])
    (Fin.addCases (fun j => F.node (padded i (eval F ρ L.pairs[j.val].1) ⊥)) (fun _ => ⊥)))

@[simp] theorem extend_old (L : Layout n d) (i : Fin d) (F : Constructor T d)
    (ρ : Fin n → T) (x : Fin n) : L.extend i F ρ (L.old x) = ρ x := by
  simp [Layout.extend, Layout.old]

@[simp] theorem restrict_extend (L : Layout n d) (i : Fin d) (F : Constructor T d)
    (ρ : Fin n → T) : L.restrict (L.extend i F ρ) = ρ := by
  funext x
  exact extend_old L i F ρ x

@[simp] theorem extend_termSlot (L : Layout n d) (i : Fin d) (F : Constructor T d)
    (ρ : Fin n → T) (j : Fin L.terms.length) :
    L.extend i F ρ (L.termSlot j) = eval F ρ L.terms[j.val] := by
  simp [Layout.extend, Layout.termSlot, Fin.addCases_right]

@[simp] theorem extend_edgeSlot (L : Layout n d) (i : Fin d) (F : Constructor T d)
    (ρ : Fin n → T) (j : Fin L.pairs.length) :
    L.extend i F ρ (L.edgeSlot j) = F.node (padded i (eval F ρ L.pairs[j.val].1) ⊥) := by
  simp [Layout.extend, Layout.edgeSlot, Fin.addCases_right]

@[simp] theorem extend_padding (L : Layout n d) (i : Fin d) (F : Constructor T d)
    (ρ : Fin n → T) : L.extend i F ρ L.padding = ⊥ := by
  simp [Layout.extend, Layout.padding, Fin.addCases_right]

theorem extend_ref (L : Layout n d) (i : Fin d) (F : Constructor T d)
    (ρ : Fin n → T) (t : Term n d) (h : t ∈ L.terms) :
    L.extend i F ρ (L.ref t) = eval F ρ t := by
  cases t with
  | var x => exact extend_old L i F ρ x
  | bot => simp only [Layout.ref, dif_pos h, extend_termSlot, List.getElem_idxOf]
  | top => simp only [Layout.ref, dif_pos h, extend_termSlot, List.getElem_idxOf]
  | node c => simp only [Layout.ref, dif_pos h, extend_termSlot, List.getElem_idxOf]

omit [OrderBot T] [OrderTop T] in
theorem padded_order (F : Constructor T d) (i : Fin d) (a b e : T) :
    F.node (padded i a e) ≤ F.node (padded i b e) ↔ a ≤ b := by
  rw [F.le_iff]
  constructor
  · intro h; simpa only [padded, if_pos rfl] using h i
  · intro h j
    by_cases hj : j = i
    · simpa only [padded, if_pos hj] using h
    · simp only [padded, if_neg hj]; exact le_rfl

theorem extend_closed (L : Layout n d) (i : Fin d) (F : Constructor T d) (P : T → Prop)
    (hb : P ⊥) (ht : P ⊤) (hn : ∀ c, (∀ j, P (c j)) → P (F.node c))
    (ρ : Fin n → T) (hρ : ∀ x, P (ρ x)) : ∀ x, P (L.extend i F ρ x) := by
  apply Fin.addCases
  · intro x
    simp only [Layout.extend, Fin.addCases_left]
    exact hρ x
  · apply Fin.addCases
    · intro j
      simp only [Layout.extend, Fin.addCases_right, Fin.addCases_left]
      exact eval_closed F P hb ht hn ρ hρ L.terms[j.val]
    · apply Fin.addCases
      · intro k
        simp only [Layout.extend, Fin.addCases_right, Fin.addCases_left]
        apply hn
        intro j
        by_cases hj : j = i
        · simpa only [padded, if_pos hj] using eval_closed F P hb ht hn ρ hρ L.pairs[k.val].1
        · simpa only [padded, if_neg hj] using hb
      · intro k
        simp only [Layout.extend, Fin.addCases_right]
        exact hb

end Semantics

end NSSE.SubtypeTermLayout
