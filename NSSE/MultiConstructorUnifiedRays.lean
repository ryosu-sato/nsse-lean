import NSSE.MultiConstructorUnifiedPrefix
import NSSE.P0PeriodicIsolation

/-! The finite unified word uses exactly the existing all-origin copy grid.
Optional letters preserve literal matching without a padding alphabet or
constructor assumption. The annotation head is irrelevant to propagation. -/
namespace NSSE.MultiConstructorUnifiedRays
open MultiConstructorConstraints MultiConstructorTokens MultiConstructorUnifiedWords
open MultiConstructorUnifiedPrefix PeriodicCopyHeadNormalization
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

def annotation (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D)) (k : Nat) :
    Annotation (Fin n) Unit (Option (Fin D)) :=
  ⟨(row phi x y w k).1,(row phi x y w k).2,(),w[k]?⟩

theorem born_exact (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D)) (a b : Nat) :
    GeneralCopyGrid.Born (annotation phi x y w) a b ↔ Born phi x y w a b := by
  rw [Born,birth_iff_inter phi _ _ (row_closed phi x y w a).1]
  simp only [GeneralCopyGrid.Born,annotation,Finset.mem_coe,Finset.Nonempty,Finset.mem_inter]

theorem ray_exact (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D)) (a b l : Nat) :
    Ray (annotation phi x y w) a b l ↔ Born phi x y w a b ∧ P0ProperWords.WordMatch w a b l := by
  change (GeneralCopyGrid.Born (annotation phi x y w) a b ∧ _) ↔ _
  rw [born_exact]
  rfl

def IncidentY (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D)) (k : Nat) : Prop :=
  P0PeriodicIsolation.Incident (annotation phi x y w) k

def IncidentX (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D)) (k : Nat) : Prop :=
  ∃ j, j ≤ k ∧ GeneralCopyGrid.Active (annotation phi x y w) k j k

theorem ray_incidentY (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (m a b l : Nat) (ha : a+l ≤ m) (hb : b+l = m)
    (hborn : Born phi x y w a b) (hm : P0ProperWords.WordMatch w a b l) :
    IncidentY phi x y w m :=
  ⟨a+l,(GeneralCopyGrid.active_iff_ray _ m m (a+l)).mpr
    ⟨ha,a,b,l,rfl,hb,(ray_exact phi x y w a b l).mpr ⟨hborn,hm⟩⟩⟩

theorem active_agree (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (ex ey : MultiConstructorTrees.Label H)
    (ha : Assignment phi x y w heads ex ey) (N k j : Nat)
    (hk : k ≤ w.length) (hj : j ≤ w.length)
    (hact : GeneralCopyGrid.Active (annotation phi x y w) N k j) :
    P0DZBranch.Agree (value w heads ex ey false j) (value w heads ex ey true k) := by
  obtain ⟨_,a,b,l,haj,hbk,hr⟩ := (GeneralCopyGrid.active_iff_ray _ N k j).mp hact
  obtain ⟨hb,hm⟩ := (ray_exact phi x y w a b l).mp hr
  have h := ha.2.2 ⟨a,by omega⟩ ⟨b,by omega⟩ ⟨l,by omega⟩ hb
    (by change a+l ≤ w.length; omega) (by change b+l ≤ w.length; omega) hm
  simpa only [haj,hbk] using h

theorem no_active_diagonal (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (ex ey : MultiConstructorTrees.Label H)
    (ha : Assignment phi x y w heads ex ey) (N k : Nat) (hk : k ≤ w.length) :
    ¬GeneralCopyGrid.Active (annotation phi x y w) N k k := by
  intro hact
  obtain ⟨_,a,hak,hb⟩ := (GeneralCopyGrid.diagonal_iff _ N k).mp hact
  exact MultiConstructorUnifiedBranch.no_diagonal phi x y w heads ex ey ha a (by omega)
    ((born_exact phi x y w a a).mp hb)

end NSSE.MultiConstructorUnifiedRays
