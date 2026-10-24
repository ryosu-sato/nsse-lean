import NSSE.DFAPadding
import NSSE.ComponentCoveragePresburger

/-!
# Heterogeneous finite DFA routes

Each route may have its own finite state count.  The list is padded to its
maximum state count before use by the homogeneous Presburger compiler.
-/

namespace NSSE

universe u

structure FiniteDFA (α : Type u) where
  stateCount : Nat
  automaton : DFA α (Fin stateCount)

namespace FiniteDFA

def pad (route : FiniteDFA α)
    (hsize : route.stateCount ≤ stateBound) :
    DFA α (Fin stateBound) :=
  route.automaton.finPad hsize

@[simp] theorem pad_accepts
    (route : FiniteDFA α)
    (hsize : route.stateCount ≤ stateBound)
    (word : Word α) :
    (route.pad hsize).Accepts word ↔
      route.automaton.Accepts word :=
  route.automaton.finPad_accepts hsize word

end FiniteDFA

def HeterogeneousDFARouteFamilyCovers
    (routes : List (FiniteDFA α))
    (word : Word α) : Prop :=
  match routes with
  | [] => False
  | route :: routes =>
      (∃ position ≤ word.length,
        route.automaton.Accepts (word.take position)) ∨
      HeterogeneousDFARouteFamilyCovers routes word

def heterogeneousRouteStateBound :
    List (FiniteDFA α) → Nat
  | [] => 0
  | route :: routes =>
      max route.stateCount
        (heterogeneousRouteStateBound routes)

theorem stateCount_le_heterogeneousRouteStateBound_of_mem
    (route : FiniteDFA α)
    (routes : List (FiniteDFA α))
    (hmem : route ∈ routes) :
    route.stateCount ≤ heterogeneousRouteStateBound routes := by
  induction routes with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      rw [heterogeneousRouteStateBound]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

def padHeterogeneousDFARoutesTo
    (stateBound : Nat)
    (routes : List (FiniteDFA α))
    (hbound :
      ∀ route ∈ routes, route.stateCount ≤ stateBound) :
    List (DFA α (Fin stateBound)) :=
  match routes with
  | [] => []
  | route :: routes =>
      route.pad (hbound route (by simp)) ::
        padHeterogeneousDFARoutesTo stateBound routes
          (fun tailRoute hmem =>
            hbound tailRoute (by simp [hmem]))

theorem dfaRouteFamilyCovers_padHeterogeneousDFARoutesTo_iff
    (stateBound : Nat)
    (routes : List (FiniteDFA α))
    (hbound :
      ∀ route ∈ routes, route.stateCount ≤ stateBound)
    (word : Word α) :
    LinearWordFamily.DFARouteFamilyCovers
        (padHeterogeneousDFARoutesTo
          stateBound routes hbound) word ↔
      HeterogeneousDFARouteFamilyCovers routes word := by
  induction routes with
  | nil =>
      simp [padHeterogeneousDFARoutesTo.eq_def,
        LinearWordFamily.DFARouteFamilyCovers,
        HeterogeneousDFARouteFamilyCovers]
  | cons route routes ih =>
      have ihTail :=
        ih (fun tailRoute hmem =>
          hbound tailRoute (by simp [hmem]))
      rw [padHeterogeneousDFARoutesTo.eq_def,
        LinearWordFamily.DFARouteFamilyCovers,
        HeterogeneousDFARouteFamilyCovers]
      simp only [List.mem_cons]
      constructor
      · rintro ⟨candidate, hcandidate, hcovered⟩
        rcases hcandidate with rfl | hcandidate
        · left
          obtain ⟨position, hposition, haccepts⟩ := hcovered
          exact ⟨position, hposition,
            (route.pad_accepts
              (hbound route (by simp))
              (word.take position)).1 haccepts⟩
        · right
          apply ihTail.mp
          exact ⟨candidate, hcandidate, hcovered⟩
      · rintro (hroute | hroutes)
        · obtain ⟨position, hposition, haccepts⟩ := hroute
          exact ⟨route.pad (hbound route (by simp)),
            Or.inl rfl, position, hposition,
            (route.pad_accepts
              (hbound route (by simp))
              (word.take position)).2 haccepts⟩
        · obtain ⟨candidate, hcandidate, hcovered⟩ :=
            ihTail.mpr hroutes
          exact ⟨candidate, Or.inr hcandidate, hcovered⟩

noncomputable def normalizeHeterogeneousDFARoutes
    (routes : List (FiniteDFA α)) :
    List (DFA α (Fin (heterogeneousRouteStateBound routes))) :=
  padHeterogeneousDFARoutesTo
    (heterogeneousRouteStateBound routes) routes
    (fun route hmem =>
      stateCount_le_heterogeneousRouteStateBound_of_mem
        route routes hmem)

theorem dfaRouteFamilyCovers_normalizeHeterogeneous_iff
    (routes : List (FiniteDFA α))
    (word : Word α) :
    LinearWordFamily.DFARouteFamilyCovers
        (normalizeHeterogeneousDFARoutes routes) word ↔
      HeterogeneousDFARouteFamilyCovers routes word := by
  unfold normalizeHeterogeneousDFARoutes
  exact dfaRouteFamilyCovers_padHeterogeneousDFARoutesTo_iff
    (heterogeneousRouteStateBound routes) routes _ word

end NSSE
