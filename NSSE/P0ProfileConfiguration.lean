import NSSE.P0PositionProfiles

/-! Too many equally sized sets of actual word positions force the
precise homogeneous equal-profile configuration used by the cut theorem. -/
namespace NSSE.P0ProfileConfiguration
open P0PositionProfiles P0HomogeneousOrder P0FourGroupEntry P0LayoutReader
open P0DDeadReader P0DDeadColor
variable {Q A H : Type*}

def selectedGrid (s : Nat) (sets : Nat → Finset Nat) (I : Finset Nat)
    (hcard : ∀ i ∈ I, (sets i).card = s)
    (hdis : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (sets i) (sets j))
    (pick : Fin 4 → Nat) (hmem : ∀ r, pick r ∈ I) (hmono : StrictMono pick)
    (hshuffle : ∀ r t, r < t → shuffle s (sets (pick r)) (sets (pick t)) =
      shuffle s (sets (pick 0)) (sets (pick 1))) : Grid s where
  pos r i := position (sets (pick r)) i
  row := by
    intro r i j hij hj
    exact position_increasing _ i j hij (by rw [hcard _ (hmem r)]; exact hj)
  apart := by
    intro r t hne i j hi hj he
    have hp := position_mem (sets (pick r)) i (by rw [hcard _ (hmem r)]; exact hi)
    have hq := position_mem (sets (pick t)) j (by rw [hcard _ (hmem t)]; exact hj)
    exact Finset.disjoint_left.mp (hdis _ (hmem r) _ (hmem t)
      (fun hh => hne (hmono.injective hh))) hp (he ▸ hq)
  homogeneous := by
    intro r t hrt i j hi hj
    exact shuffle_order s _ _ _ _ (hshuffle r t hrt) ⟨i,hi⟩ ⟨j,hj⟩

theorem configuration (J : Reader Q A H) (w : List A) (U : Finset Nat)
    (k s : Nat) (code : Nat → Fin k)
    (hcode : ∀ a ∈ U, ∀ b ∈ U, code a = code b → color J w a = color J w b)
    (sets : Nat → Finset Nat) (I : Finset Nat)
    (hin : ∀ i ∈ I, sets i ⊆ U) (hcard : ∀ i ∈ I, (sets i).card = s)
    (hdis : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (sets i) (sets j))
    (hsize : k^s * 2^(s*s) * (P0FiniteSelection.bound (2^(s*s))-1) < I.card) :
    ∃ (pick : Fin 4 → Nat) (G : Grid s),
      (∀ r, pick r ∈ I) ∧ StrictMono pick ∧
      (∀ r p, p ∈ sets (pick r) ↔ InRow G r p) ∧
      UniformStates J w G ∧ EqualMatrices J w G := by
  classical
  have hsize' : Fintype.card (Profile k s) *
      (P0FiniteSelection.bound (Fintype.card (Bits s))-1) < I.card := by
    simpa only [profile_card,bits_card] using hsize
  obtain ⟨pick,hmem,hmono,hprofile,hshuffle⟩ := P0TypedSelection.four
    (fun i => profile J w k s code (sets i)) (fun i j => shuffle s (sets i) (sets j)) I
    (by rw [bits_card]; exact Nat.pow_pos (by decide)) hsize'
  let G := selectedGrid s sets I hcard hdis pick hmem hmono hshuffle
  have hpos (r : Fin 4) (i : Nat) (hi : i < s) : position (sets (pick r)) i ∈ sets (pick r) :=
    position_mem _ i (by rw [hcard _ (hmem r)]; exact hi)
  refine ⟨pick,G,hmem,hmono,?_,?_,?_⟩
  · intro r p
    constructor
    · intro hp
      obtain ⟨i,hi,he⟩ := position_surjective _ p hp
      rw [hcard _ (hmem r)] at hi
      exact ⟨i,hi,he.symm⟩
    · rintro ⟨i,hi,he⟩
      rw [he]
      exact hpos r i hi
  · intro r t i hi
    apply hcode _ (hin _ (hmem r) (hpos r i hi)) _ (hin _ (hmem t) (hpos t i hi))
    exact profile_states J w k s code _ _ (hprofile r t) ⟨i,hi⟩
  · intro r t i j hi hj _
    exact profile_matrix J w k s code _ _ (hprofile r t) ⟨i,hi⟩ ⟨j,hj⟩

end NSSE.P0ProfileConfiguration
