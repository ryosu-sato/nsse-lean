import NSSE.MultiConstructorExtremeWitness
import NSSE.MultiConstructorOrientedMachine

/-! Actual stream annotations retain original Fin D letters. Their token
rows agree exactly with every spelled finite prefix, without padding. -/
namespace NSSE.MultiConstructorStreamTrace
open MultiConstructorConstraints MultiConstructorTokens MultiConstructorRawTrace
open P0ProperWords PeriodicCopyHeadNormalization
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

def rawRow (phi : Constraints arity n) (x y : Fin n) (z : Nat → Fin D) (k : Nat) : Row n :=
  trace phi (initial phi x y) (fun j => (z j).val) k

def annotation (phi : Constraints arity n) (x y : Fin n) (z : Nat → Fin D) (k : Nat) :
    Annotation (Fin n) Unit (Fin D) :=
  ⟨(rawRow phi x y z k).1,(rawRow phi x y z k).2,(),z k⟩

theorem row_spells (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (z : Nat → Fin D) (hz : Spells z w) (k : Nat) (hk : k ≤ w.length) :
    MultiConstructorUnifiedWords.row phi x y w k = rawRow phi x y z k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkn : k < w.length := by omega
    have hletter : w[k] = z k := by
      simpa only [List.getElem?_eq_getElem hkn,Option.some.injEq] using hz k hkn
    rw [MultiConstructorUnifiedPrefix.row_succ phi x y w k hkn,ih (by omega),hletter]
    rfl

theorem prefix_row (phi : Constraints arity n) (x y : Fin n) (z : Nat → Fin D)
    (m k : Nat) (hk : k ≤ m) :
    MultiConstructorUnifiedWords.row phi x y (prefixWord z m) k = rawRow phi x y z k :=
  row_spells phi x y _ z (spells_prefix z m) k (by simpa only [prefix_length] using hk)

theorem born_exact (phi : Constraints arity n) (x y : Fin n) (z : Nat → Fin D) (a b : Nat) :
    GeneralCopyGrid.Born (annotation phi x y z) a b ↔
      ∃ u ∈ (rawRow phi x y z a).1, ∃ v ∈ (rawRow phi x y z b).2, Support phi u v := by
  have hc : UpperClosed phi (rawRow phi x y z a).1 :=
    (trace_closed phi x y (fun j => (z j).val) a).1
  rw [birth_iff_inter phi (rawRow phi x y z a).1 (rawRow phi x y z b).2 hc]
  simp only [GeneralCopyGrid.Born,annotation,Finset.mem_coe,Finset.Nonempty,Finset.mem_inter]

theorem born_spells (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (z : Nat → Fin D) (hz : Spells z w) (a b : Nat) (ha : a ≤ w.length) (hb : b ≤ w.length) :
    GeneralCopyGrid.Born (annotation phi x y z) a b ↔ MultiConstructorUnifiedWords.Born phi x y w a b := by
  rw [born_exact,MultiConstructorUnifiedWords.Born,row_spells phi x y w z hz a ha,row_spells phi x y w z hz b hb]

theorem ray_spells (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (z : Nat → Fin D) (hz : Spells z w) (a b l : Nat) (ha : a+l ≤ w.length) (hb : b+l ≤ w.length) :
    Ray (annotation phi x y z) a b l ↔
      Ray (MultiConstructorUnifiedRays.annotation phi x y w) a b l := by
  rw [MultiConstructorUnifiedRays.ray_exact]
  change (GeneralCopyGrid.Born (annotation phi x y z) a b ∧ P0ProperMachine.Match z a b l) ↔ _
  rw [born_spells phi x y w z hz a b (by omega) (by omega),← match_iff w z hz a b l ha hb]

end NSSE.MultiConstructorStreamTrace
