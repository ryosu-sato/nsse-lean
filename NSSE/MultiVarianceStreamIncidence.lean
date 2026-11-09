import NSSE.MultiVarianceStreamTrace

/-! Signed physical incidence at a frontier. The other endpoint must
also lie in the prefix. Once the selected side has no new birth origins,
every later incident ray restricts to the old frontier, including lag zero. -/
namespace NSSE.MultiVarianceStreamIncidence
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceTokenExact
open MultiVarianceBranch MultiVarianceProperTrace MultiVarianceSideTokens MultiVarianceStreamTrace
open P0ProperMachine P0ProperWords
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}
variable (pol : Polarity arity)

def Incident (C : Parameters arity n) (z : Nat → Fin D) (side : Bool) (m : Nat) : Prop :=
  ∃ a b l other, a+l≤m ∧ b+l=m ∧
    SymBirth (rawFrame pol C z a) other (rawFrame pol C z b) side ∧ Match z a b l

theorem incident_spells (C : Parameters arity n) (w : List (Fin D)) (z : Nat → Fin D)
    (hz : Spells z w) (side : Bool) (m : Nat) (hm : m≤w.length) :
    MultiVarianceTerminalIsolation.Incident pol C w side m ↔ Incident pol C z side m := by
  constructor
  · rintro ⟨a,b,l,s,ha,hb,hborn,hmatch⟩
    refine ⟨a,b,l,s,ha,hb,?_,(match_iff w z hz a b l (by omega) (by omega)).mp hmatch⟩
    rwa [raw_spells pol C w z hz a (by omega),raw_spells pol C w z hz b (by omega)] at hborn
  · rintro ⟨a,b,l,s,ha,hb,hborn,hmatch⟩
    refine ⟨a,b,l,s,ha,hb,?_,(match_iff w z hz a b l (by omega) (by omega)).mpr hmatch⟩
    rwa [raw_spells pol C w z hz a (by omega),raw_spells pol C w z hz b (by omega)]

theorem incident_before (C : Parameters arity n) (z : Nat → Fin D) (side : Bool)
    (m t : Nat) (hmt : m≤t) (he : ∀ k, m<k → tokensOf (rawFrame pol C z k) side=∅)
    (hi : Incident pol C z side t) : Incident pol C z side m := by
  obtain ⟨a,b,l,s,ha,hb,hborn,hmatch⟩ := hi
  have hbm : b≤m := by
    by_contra hn
    exact empty_no_symBirth _ s _ side (he b (by omega)) hborn
  refine ⟨a,b,m-b,s,by omega,by omega,hborn,?_⟩
  exact match_mono z a b l (m-b) (by omega) hmatch

theorem isolation_after (C : Parameters arity n) (z : Nat → Fin D) (side : Bool)
    (m t : Nat) (hmt : m≤t) (he : ∀ k, m<k → tokensOf (rawFrame pol C z k) side=∅)
    (hi : ¬Incident pol C z side m) : ¬Incident pol C z side t :=
  fun ht => hi (incident_before pol C z side m t hmt he ht)

theorem accepted_isolation (C : Parameters arity n) (w : List (Fin D))
    (ha : P0DZBranch.Accepted (branch pol C D) w) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch pol C D)) z) (hz : Spells z w) :
    ∃ side, (∀ t, w.length<t → tokensOf (rawFrame pol C z t) side=∅) ∧
      ∀ t, w.length≤t → ¬Incident pol C z side t := by
  have hw := (goodWord_iff_stream _ w z hz).mpr (hg w.length)
  obtain ⟨side,hp,hi⟩ := MultiVarianceTerminalIsolation.changed_side pol C w ha hw
  have hpin : pins C.query.constraints (roleOf (rawFrame pol C z w.length).sign side)
      (tokensOf (rawFrame pol C z w.length) side)=∅ := by
    rwa [raw_spells pol C w z hz w.length le_rfl] at hp
  have hem := fun t ht => loss_after pol C z hg side w.length t ht hpin
  have hni : ¬Incident pol C z side w.length := fun h => hi ((incident_spells pol C w z hz side w.length le_rfl).mpr h)
  exact ⟨side,hem,fun t ht => isolation_after pol C z side w.length t ht hem hni⟩

end NSSE.MultiVarianceStreamIncidence
