import NSSE.StoredWitnessExponent

/-! Actual production of the original scalar lowering witness length. -/
namespace NSSE.StoredWitnessLength
variable {R : Nat → Type} {P : Type} {k : Nat} {ns : Fin k → Nat}

def build (A : StoredRelationArrayPackage.Family R P ns) (c q : Nat) : Nat × Nat :=
  let e := StoredWitnessExponent.build A c
  let p := CountedNaturalPower.build 2 e.1
  let s := CountedSupportRule.mul q q
  let a := CountedSupportRule.add s.1 1
  let m := CountedSupportRule.mul a.1 p.1
  (m.1,5+e.2+p.2+s.2+a.2+m.2)
def length (ns : Fin k → Nat) (c q : Nat) := (q*q+1)*2^UnifiedBlockWitnessBound.exponent ns c
theorem value (A : StoredRelationArrayPackage.Family R P ns) (c q : Nat) :
    (build A c q).1 = length ns c q := by
  simp only [build,StoredWitnessExponent.value,CountedNaturalPower.value,CountedSupportRule.mul_value,
    CountedSupportRule.add_value,length]
def budget (ns : Fin k → Nat) (c q N : Nat) :=
  8+StoredWitnessExponent.budget k N+CountedNaturalPower.budget 2 (UnifiedBlockWitnessBound.exponent ns c)+
  q*(q+2)+q*q+2^UnifiedBlockWitnessBound.exponent ns c*(q*q+3)
theorem bound (A : StoredRelationArrayPackage.Family R P ns) (c q N : Nat) (hc : c ≤ N) (hn : ∀ i, ns i ≤ N) :
    (build A c q).2 ≤ budget ns c q N := by
  have he := StoredWitnessExponent.bound A c N hc hn
  have hp := CountedNaturalPower.bound 2 (StoredWitnessExponent.build A c).1
  simp only [StoredWitnessExponent.value] at hp
  simp only [build,StoredWitnessExponent.value,CountedNaturalPower.value,CountedSupportRule.mul_cost,
    CountedSupportRule.add_cost,CountedSupportRule.mul_value,CountedSupportRule.add_value,budget]
  ring_nf at *
  omega
end NSSE.StoredWitnessLength
