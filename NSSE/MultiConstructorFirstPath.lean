import NSSE.MultiConstructorTrees
import Mathlib.Data.Finset.Lattice.Fold

/-! Every actual failed tree comparison has a finite path with common
proper heads and legal original child indices, ending in its first failure. -/
namespace NSSE.MultiConstructorFirstPath
open MultiConstructorTrees
variable {H : Type*} {arity : H → Nat} {D : Nat}

inductive Path (D : Nat) : Tree arity → Tree arity → List (Fin D) → Prop
  | stop {a b : Tree arity} (bad : ¬a.label [] ≤ b.label []) : Path D a b []
  | step {a b : Tree arity} (h : H) (ha : a.label [] = .node h) (hb : b.label [] = .node h)
      (i : Fin D) (hi : i.val < arity h) {w : List (Fin D)}
      (tail : Path D (MultiConstructorTrees.Tree.project a [i.val])
        (MultiConstructorTrees.Tree.project b [i.val]) w) : Path D a b (i::w)

theorem of_bad_word (hD : ∀ h, arity h ≤ D) (a b : Tree arity) (p : List Nat)
    (hp : ¬a.label p ≤ b.label p) : ∃ w, Path D a b w := by
  induction p generalizing a b with
  | nil => exact ⟨[],.stop hp⟩
  | cons i p ih =>
    by_cases hh : a.label [] ≤ b.label []
    · rcases MultiConstructorTrees.Tree.root_cases a with rfl | rfl | ⟨h,ca,rfl⟩
      · exact False.elim (hp bot_le)
      · have hb : b.label [] = .top := le_antisymm le_top hh
        have he := MultiConstructorTrees.Tree.eq_top_of_root b hb
        subst b
        exact False.elim (hp le_rfl)
      · rcases MultiConstructorTrees.Tree.root_cases b with rfl | rfl | ⟨k,cb,rfl⟩
        · exact False.elim (Label.node_not_le_bot h hh)
        · exact False.elim (hp le_top)
        · have he : h = k := (Label.node_le_node h k).mp hh
          subst k
          by_cases hi : i < arity h
          · have hc : ¬(ca ⟨i,hi⟩).label p ≤ (cb ⟨i,hi⟩).label p := by
              simpa only [MultiConstructorTrees.Tree.node,hi,dif_pos] using hp
            obtain ⟨w,hw⟩ := ih (ca ⟨i,hi⟩) (cb ⟨i,hi⟩) hc
            refine ⟨⟨i,hi.trans_le (hD h)⟩::w,.step h rfl rfl _ hi ?_⟩
            simpa only [MultiConstructorTrees.Tree.project_node h ca ⟨i,hi⟩,
              MultiConstructorTrees.Tree.project_node h cb ⟨i,hi⟩] using hw
          · exact False.elim (hp (by simp [MultiConstructorTrees.Tree.node,hi]))
    · exact ⟨[],.stop hh⟩

theorem of_not_le (hD : ∀ h, arity h ≤ D) (a b : Tree arity) (hab : ¬a ≤ b) :
    ∃ w, Path D a b w := by
  obtain ⟨p,hp⟩ := (MultiConstructorTrees.Tree.not_le_iff a b).mp hab
  exact of_bad_word hD a b p hp

theorem terminal_bad {a b : Tree arity} {w : List (Fin D)} (hp : Path D a b w) :
    ¬a.label (w.map Fin.val) ≤ b.label (w.map Fin.val) := by
  induction hp with
  | stop hb => exact hb
  | step h ha hb i hi ht ih => exact ih

theorem prefix_heads {a b : Tree arity} {w : List (Fin D)} (hp : Path D a b w)
    (k : Nat) (hk : k < w.length) :
    ∃ h, a.label ((w.take k).map Fin.val) = .node h ∧
      b.label ((w.take k).map Fin.val) = .node h ∧ w[k].val < arity h := by
  induction hp generalizing k with
  | stop hb => simp at hk
  | @step a b h ha hb i hi w ht ih =>
    cases k with
    | zero => exact ⟨h,ha,hb,hi⟩
    | succ k =>
      have hkw : k < w.length := by simpa using hk
      simpa only [List.take_succ_cons,List.map_cons,MultiConstructorTrees.Tree.project_label,
        List.singleton_append,List.getElem_cons_succ] using ih k hkw

theorem proper_heads {a b : Tree arity} {w : List (Fin D)} (hp : Path D a b w) :
    ∃ heads : Fin w.length → H, ∀ k,
      a.label ((w.take k.val).map Fin.val) = .node (heads k) ∧
      b.label ((w.take k.val).map Fin.val) = .node (heads k) ∧ w[k.val].val < arity (heads k) := by
  choose heads hh using fun k : Fin w.length => prefix_heads hp k.val k.isLt
  exact ⟨heads,hh⟩

theorem terminal_constraints {a b : Tree arity} {w : List (Fin D)} (hp : Path D a b w) :
    a.label (w.map Fin.val) ≠ .bot ∧ b.label (w.map Fin.val) ≠ .top ∧
      a.label (w.map Fin.val) ≠ b.label (w.map Fin.val) := by
  have hb := terminal_bad hp
  change ¬Label.Below _ _ at hb
  simpa only [Label.Below,not_or] using hb

def alphabetSize [Fintype H] (arity : H → Nat) : Nat := Finset.univ.sup arity

theorem arity_le_alphabet [Fintype H] (h : H) : arity h ≤ alphabetSize arity :=
  Finset.le_sup (Finset.mem_univ h)

theorem finite_signature_path [Fintype H] (a b : Tree arity) (hab : ¬a ≤ b) :
    ∃ w, Path (alphabetSize arity) a b w := of_not_le arity_le_alphabet a b hab

end NSSE.MultiConstructorFirstPath
