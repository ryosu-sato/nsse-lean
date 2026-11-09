import NSSE.P0FiniteSelection

/-! The finite per-profile count used by the cotree argument. This is
pure finite selection: excluding the configuration in an actual shortest
word still requires the four-child literal shortening theorem. -/
namespace NSSE.P0ProfileSelection
open P0FiniteSelection

def Configuration {p c : Nat} (profile : Nat → Fin p) (edge : Nat → Nat → Fin c)
    (S : Finset Nat) : Prop :=
  ∃ a b d e t v, a ∈ S ∧ b ∈ S ∧ d ∈ S ∧ e ∈ S ∧ a < b ∧ b < d ∧ d < e ∧
    profile a = t ∧ profile b = t ∧ profile d = t ∧ profile e = t ∧
    edge a b = v ∧ edge a d = v ∧ edge a e = v ∧
    edge b d = v ∧ edge b e = v ∧ edge d e = v

theorem configuration_of_many (p c : Nat) (hc : 0 < c)
    (profile : Nat → Fin p) (edge : Nat → Nat → Fin c) (S : Finset Nat)
    (hsize : p * (bound c-1) < S.card) : Configuration profile edge S := by
  classical
  obtain ⟨t,_,ht⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := S) (t := Finset.univ) (f := profile) (n := bound c-1)
    (fun _ _ => Finset.mem_univ _) (by simpa using hsize)
  have hb : bound c ≤ (S.filter (fun a => profile a = t)).card := by
    have hpos := threshold_pos c (3*c)
    change 0 < bound c at hpos
    omega
  obtain ⟨a,b,d,e,v,ha,hb,hd,he,hab,hbd,hde,habv,hadv,haev,hbdv,hbev,hdev⟩ :=
    four c hc edge (S.filter (fun a => profile a = t)) hb
  have hpa := Finset.mem_filter.mp ha
  have hpb := Finset.mem_filter.mp hb
  have hpd := Finset.mem_filter.mp hd
  have hpe := Finset.mem_filter.mp he
  exact ⟨a,b,d,e,t,v,hpa.1,hpb.1,hpd.1,hpe.1,hab,hbd,hde,hpa.2,hpb.2,hpd.2,hpe.2,
    habv,hadv,haev,hbdv,hbev,hdev⟩

theorem count (p c : Nat) (hc : 0 < c) (profile : Nat → Fin p)
    (edge : Nat → Nat → Fin c) (S : Finset Nat) (hn : ¬ Configuration profile edge S) :
    S.card ≤ p * (bound c-1) := by
  by_contra h
  exact hn (configuration_of_many p c hc profile edge S (by omega))

end NSSE.P0ProfileSelection
