import NSSE.CodedTermEntailment

/-! # From counted steps to machine time: what is still assumed, exactly

`CodedTermEntailment.finite_bound` bounds the COUNTED step number of the
decision, decoding included, by `tower 7` of a polynomial in the encoded input
length. A complexity claim needs machine time, and the counter is not machine
time: it counts steps of the counted Lean implementation.

This file isolates the remaining premise and shows that it is the only thing
missing — any POLYNOMIAL per-step overhead is absorbed by the tower.

`PolynomiallyFaithful c a T S` says: a run whose counted step number is `S`
takes at most `c * S^(a+1)` machine steps. It is a statement about the
implementation (how a counted step is realised on a machine), not about the
mathematics; it is exactly what a verified compiler, or a re-implementation in
a machine model, would have to supply. Everything else is proved:

    counted ≤ tower 7 A  and  PolynomiallyFaithful c a T counted
      ⟹ T ≤ tower 7 (A+a+c+2).

So the tower height does not move, whatever polynomial overhead a machine
realisation costs; only the argument grows by an additive constant.
-/

namespace NSSE.MachineTimeBound

open DirectRankStateTower DirectRankFormulaTower CodedTermEntailment
open RawTermCodec RawQueryCodec CodedQueryConversion SubtypeTerms

/-! ## The tower absorbs constants and powers -/

theorem const_step (k c x : Nat) : c*tower (k+1) x ≤ tower (k+1) (x+c) := by
  induction c with
  | zero => simp
  | succ c ih =>
    show (c+1)*tower (k+1) x ≤ tower (k+1) (x+c+1)
    have hmono : tower (k+1) x ≤ tower (k+1) (x+c) := tower_mono (k+1) (by omega)
    have hstep : 2*tower (k+1) (x+c) ≤ tower (k+1) (x+c+1) :=
      TowerExpression.double_step k (x+c)
    have : (c+1)*tower (k+1) x = c*tower (k+1) x+tower (k+1) x := by ring
    omega

theorem poly_absorb (c a x : Nat) : c*(tower 7 x)^a ≤ tower 7 (x+a+c) := by
  have hp : (tower 7 x)^a ≤ tower 7 (x+a) := TowerExpression.power_step 7 x a (by decide)
  have hc : c*tower 7 (x+a) ≤ tower 7 (x+a+c) := const_step 6 c (x+a)
  exact (Nat.mul_le_mul_left c hp).trans hc

/-! ## The premise -/

/-- `T` machine steps realise a run of `S` counted steps with polynomial
overhead `c * S^(a+1)`. This is the only thing still assumed on this line. -/
def PolynomiallyFaithful (c a T S : Nat) : Prop := T ≤ c*S^(a+1)

theorem machine_time_of_counted {c a T S x : Nat} (hf : PolynomiallyFaithful c a T S)
    (hs : S ≤ tower 7 x) : T ≤ tower 7 (x+(a+1)+c) := by
  have hpow : S^(a+1) ≤ (tower 7 x)^(a+1) := Nat.pow_le_pow_left hs (a+1)
  have habs := poly_absorb c (a+1) x
  exact hf.trans ((Nat.mul_le_mul_left c hpow).trans habs)

/-! ## The decision, under that premise -/

theorem machine_time_finite (d : Nat) (w : List Bool) (hd : 0 < d) {c a T : Nat}
    (hf : PolynomiallyFaithful c a T (decideFinite d w hd).2) :
    T ≤ tower 7 (argument w.length d+1+(a+1)+c) :=
  machine_time_of_counted hf (finite_bound d w hd)

theorem machine_time_all (d : Nat) (w : List Bool) (hd : 0 < d) {c a T : Nat}
    (hf : PolynomiallyFaithful c a T (decideAll d w hd).2) :
    T ≤ tower 7 (argument w.length d+1+(a+1)+c) :=
  machine_time_of_counted hf (all_bound d w hd)

/-- The shape of the conclusion, spelled out: seven exponentials of a
polynomial in the input length, for a fixed signature and a fixed realisation.
`argument L d + a + c + 2` is a polynomial in `L` of degree eight. -/
theorem machine_time_polynomial (d : Nat) (L a c : Nat) :
    argument L d+1+(a+1)+c
      = 16*((d+1)*(L+1)^2)^4+40*((d+1)*(L+1)^2)^3+53*((d+1)*(L+1)^2)^2
        +34*((d+1)*(L+1)^2)+d+74426+a+c+2 := by
  unfold argument
  omega

/-! ## What is NOT proved here

`PolynomiallyFaithful` is a hypothesis. Discharging it requires exhibiting a
machine model and a realisation of the counted implementation in it — a
verified compiler, or a re-implementation of the decision procedure as a
machine program — together with the fact that every counted step touches data
of size polynomial in the step count. Nothing in this file, and nothing else in
the repository, proves that; until it is proved, 7-EXPTIME is not established.
-/

end NSSE.MachineTimeBound
