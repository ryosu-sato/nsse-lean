import NSSE.P0ProfileSelection
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases

/-! Finite-type form of the already proved ordered four-object selection.
Encodings are used inside the proof; the numerical bound is explicit. -/
namespace NSSE.P0TypedSelection
variable {P E : Type*} [Fintype P] [Fintype E]

theorem four (profile : Nat → P) (edge : Nat → Nat → E) (S : Finset Nat)
    (hc : 0 < Fintype.card E)
    (hsize : Fintype.card P * (P0FiniteSelection.bound (Fintype.card E)-1) < S.card) :
    ∃ pick : Fin 4 → Nat,
      (∀ r, pick r ∈ S) ∧ StrictMono pick ∧
      (∀ r s, profile (pick r) = profile (pick s)) ∧
      ∀ r s, r < s → edge (pick r) (pick s) = edge (pick 0) (pick 1) := by
  classical
  let fp := Fintype.equivFin P
  let fe := Fintype.equivFin E
  obtain ⟨a,b,d,e,t,v,ha,hb,hd,he,hab,hbd,hde,hpa,hpb,hpd,hpe,
    habv,hadv,haev,hbdv,hbev,hdev⟩ :=
    P0ProfileSelection.configuration_of_many _ _ hc (fun a => fp (profile a))
      (fun a b => fe (edge a b)) S hsize
  let pick : Fin 4 → Nat := fun r => match r.val with
    | 0 => a
    | 1 => b
    | 2 => d
    | _ => e
  have hhprofile (r : Fin 4) : fp (profile (pick r)) = t := by
    fin_cases r <;> simp only [pick] <;> assumption
  refine ⟨pick,?_,?_,?_,?_⟩
  · intro r
    fin_cases r <;> simp only [pick] <;> assumption
  · intro r s hrs
    fin_cases r <;> fin_cases s <;> simp_all [pick] <;> omega
  · intro r s
    exact fp.injective ((hhprofile r).trans (hhprofile s).symm)
  · intro r s hrs
    apply fe.injective
    have hf : fe (edge (pick r) (pick s)) = v := by
      fin_cases r <;> fin_cases s <;> simp_all [pick]
    exact hf.trans habv.symm

end NSSE.P0TypedSelection
