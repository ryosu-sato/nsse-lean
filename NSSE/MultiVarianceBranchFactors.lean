import NSSE.MultiVarianceBranchLetters

/-! Raw-index and CURRENT-head-decorated factors give the same universal
ray safety. The reverse implication grows a matching decorated prefix by
using agreement at the preceding offset. No next-head tags are used. -/
namespace NSSE.MultiVarianceBranchFactors
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceBranch
open MultiVarianceBranchLocal MultiVarianceBranchLetters MultiVarianceBranchAssignment
open P0DZBranch P0ProperWords
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}
variable (pol : Polarity arity)

theorem option_fin_ext {a b : Option (Fin D)}
    (he : a.map Fin.val=b.map Fin.val) : a=b := by
  cases a with
  | none => cases b <;> simp_all
  | some a =>
    cases b with
    | none => simp at he
    | some b => exact congrArg some (Fin.ext (Option.some.inj he))

omit [DecidableEq H] in
theorem letter_ext {a b : Letter arity} (hh : a.1=b.1) (hi : a.2.val=b.2.val) : a=b := by
  rcases a with ⟨h,i⟩
  rcases b with ⟨k,j⟩
  cases hh
  have he : i=j := Fin.ext hi
  cases he
  rfl

omit [DecidableEq H] in
theorem option_letter_ext {a b : Option (Letter arity)}
    (hh : a.map Sigma.fst=b.map Sigma.fst)
    (hi : a.map (fun z => z.2.val)=b.map (fun z => z.2.val)) : a=b := by
  cases a with
  | none => cases b <;> simp_all
  | some a =>
    cases b with
    | none => simp at hh
    | some b => exact congrArg some (letter_ext (Option.some.inj hh) (Option.some.inj hi))

theorem letters_raw_match (C : Parameters arity n) (s : State n) (w : List (Fin D))
    (ha : ArityRun pol C s w) (a b l : Nat)
    (hm : WordMatch (letters pol C s w) a b l) : WordMatch w a b l := by
  intro k hk
  apply option_fin_ext
  have he := congrArg (Option.map (fun z : Letter arity => z.2.val)) (hm k hk)
  simpa only [← List.getElem?_map,letters_indices pol C s w ha] using he

theorem letters_at_eq (C : Parameters arity n) (s : State n) (w : List (Fin D))
    (hr : ArityRun pol C s w) (a b : Nat) (ha : a<w.length) (hb : b<w.length)
    (hh : output C (walk pol C s (w.take a))=output C (walk pol C s (w.take b)))
    (hi : w[a]?=w[b]?) : (letters pol C s w)[a]?=(letters pol C s w)[b]? := by
  apply option_letter_ext
  · rw [letters_current_head pol C s w hr a ha,letters_current_head pol C s w hr b hb,hh]
  · have he := congrArg (Option.map Fin.val) hi
    simpa only [← List.getElem?_map,letters_indices pol C s w hr] using he

def DecoratedRays (C : Parameters arity n) (w : List (Fin D)) : Prop :=
  ∀ a, a ≤ w.length → ∀ b, b ≤ w.length → ∀ s t,
    RawBirth (walk pol C (branch pol C D).initial (w.take a)).1 s
      (walk pol C (branch pol C D).initial (w.take b)).1 t →
    ∀ l, l ≤ w.length → a+l ≤ w.length → b+l ≤ w.length →
      WordMatch (letters pol C (branch pol C D).initial w) a b l →
      Agree (value pol C w s (a+l)) (value pol C w t (b+l))

theorem rays_iff_decorated (C : Parameters arity n) (w : List (Fin D))
    (hr : ArityRun pol C (branch pol C D).initial w) : Rays pol C w ↔ DecoratedRays pol C w := by
  constructor
  · intro hh a ha b hb s t hborn l hl hal hbl hm
    exact hh a ha b hb s t hborn l hl hal hbl
      (letters_raw_match pol C _ w hr a b l hm)
  · intro hh a ha b hb s t hborn l hl hal hbl hm
    have hprefix : ∀ j, j ≤ l → WordMatch (letters pol C (branch pol C D).initial w) a b j := by
      intro j
      induction j with
      | zero => intro _ k hk; omega
      | succ j ih =>
        intro hj
        have hp := ih (by omega)
        intro k hk
        by_cases hk' : k<j
        · exact hp k hk'
        · have he : k=j := by omega
          subst k
          have hak : a+j<w.length := by omega
          have hbk : b+j<w.length := by omega
          have ha' := hh a ha b hb s t hborn j (by omega) (by omega) (by omega) hp
          have hh' : output C (walk pol C (branch pol C D).initial (w.take (a+j))) =
              output C (walk pol C (branch pol C D).initial (w.take (b+j))) := by
            simpa only [value,if_pos hak,if_pos hbk,Agree] using ha'
          exact letters_at_eq pol C _ w hr (a+j) (b+j) hak hbk hh' (hm j (by omega))
    exact hh a ha b hb s t hborn l hl hal hbl (hprefix l le_rfl)

theorem accepted_iff_decorated (C : Parameters arity n) (w : List (Fin D)) :
    Accepted (branch pol C D) w ↔
      LocalRun pol C (branch pol C D).initial w ∧ DecoratedRays pol C w := by
  rw [accepted_iff]
  constructor
  · rintro ⟨hl,hr⟩
    exact ⟨hl,(rays_iff_decorated pol C w (local_arities pol C _ w hl)).mp hr⟩
  · rintro ⟨hl,hr⟩
    exact ⟨hl,(rays_iff_decorated pol C w (local_arities pol C _ w hl)).mpr hr⟩

end NSSE.MultiVarianceBranchFactors
