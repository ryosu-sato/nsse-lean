import NSSE.P0DZPositionProfiles
import NSSE.P0ProfileConfiguration

/-! Too many equally sized actual position sets force four equal
refined-color/full-rail profiles with homogeneous position shuffles. -/
namespace NSSE.P0DZProfileConfiguration
open P0PositionProfiles (position position_mem position_surjective shuffle)
open P0DZPositionProfiles P0HomogeneousOrder P0DZFourGroupEntry P0DZLayout
open P0DZBranch P0DZRankColor
open P0FourGroupEntry (InRow)
variable {Q Z A H : Type*} [DecidableEq Q] [DecidableEq A]

theorem configuration (J : Branch Q Z A H) (w : List A) (U : Finset Nat)
    (k s : Nat) (code : Nat → Fin k)
    (hcode : ∀ a ∈ U, ∀ b ∈ U, code a = code b → color J w a = color J w b)
    (sets : Nat → Finset Nat) (I : Finset Nat)
    (hin : ∀ i ∈ I, sets i ⊆ U) (hcard : ∀ i ∈ I, (sets i).card = s)
    (hdis : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (sets i) (sets j))
    (hsize : k^s * 2^(4*s*s) * (P0FiniteSelection.bound (2^(s*s))-1) < I.card) :
    ∃ (pick : Fin 4 → Nat) (G : Grid s),
      (∀ r, pick r ∈ I) ∧ StrictMono pick ∧
      (∀ r p, p ∈ sets (pick r) ↔ InRow G r p) ∧
      UniformColors J w G ∧ EqualMatrices J w G := by
  classical
  have hsize' : Fintype.card (Profile k s) *
      (P0FiniteSelection.bound (Fintype.card (P0PositionProfiles.Bits s))-1) < I.card := by
    simpa only [profile_card,P0PositionProfiles.bits_card] using hsize
  obtain ⟨pick,hmem,hmono,hprofile,hshuffle⟩ := P0TypedSelection.four
    (fun i => profile J w k s code (sets i)) (fun i j => shuffle s (sets i) (sets j)) I
    (by rw [P0PositionProfiles.bits_card]; exact Nat.pow_pos (by decide)) hsize'
  let G := P0ProfileConfiguration.selectedGrid s sets I hcard hdis pick hmem hmono hshuffle
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
    exact profile_colors J w k s code _ _ (hprofile r t) ⟨i,hi⟩
  · intro r t i j hi hj _ x y
    exact profile_matrix J w k s code _ _ (hprofile r t) ⟨i,hi⟩ ⟨j,hj⟩ x y

end NSSE.P0DZProfileConfiguration
