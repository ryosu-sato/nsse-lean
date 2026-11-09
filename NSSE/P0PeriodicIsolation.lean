import NSSE.GeneralCopyGrid

/-! The eventual-isolation lemma of x749, on the actual equal-letter ray
definition. Only letters are assumed periodic; annotation states and token
sets need not be periodic. All offsets, diagonal births and physical origin
orders are retained. No decidability theorem is assumed.
-/
namespace NSSE.P0PeriodicIsolation
open PeriodicCopyHeadNormalization GeneralCopyGrid
variable {V H I : Type*}

def LettersPeriodic (q : Nat → Annotation V H I) (n r : Nat) : Prop :=
  PhasePeriodic (fun k => (q k).index) n r

def MatchForever (q : Nat → Annotation V H I) (a b : Nat) : Prop :=
  ∀ k, (q (a+k)).index = (q (b+k)).index

/-- A full transient and one period suffice for literal future equality.
The bound depends on the EARLIER origin a, not on the whole old history. -/
theorem match_forever_of_long (q : Nat → Annotation V H I) (n r a b l : Nat)
    (hr : 0 < r) (hp : LettersPeriodic q n r) (hab : a ≤ b)
    (hl : n-a+r ≤ l)
    (hm : ∀ k, k < l → (q (a+k)).index = (q (b+k)).index) :
    MatchForever q a b := by
  intro k
  by_cases hk : k < n-a+r
  · exact hm k (by omega)
  · obtain ⟨e,he,her,hem⟩ := residue_in_interval (n-a) k r hr
    have ha := hp (a+e) (a+k) (by omega) (by omega) (hem.add_left a)
    have hb := hp (b+e) (b+k) (by omega) (by omega) (hem.add_left b)
    dsimp only at ha hb
    rw [← ha, ← hb]
    exact hm e (by omega)

/-- Every birth with its Y arm at a later physical origin, including a=b. -/
def Permanent (q : Nat → Annotation V H I) (n : Nat) : Prop :=
  ∃ a b, a ≤ b ∧ b ≤ n ∧ Born q a b ∧ MatchForever q a b

/-- The Y vertex at the current end has an incident actual ray. -/
def Incident (q : Nat → Annotation V H I) (t : Nat) : Prop :=
  ∃ j, Active q t t j

/-- A side has no new birth origins once its support is empty. -/
def LowerEmptyAfter (q : Nat → Annotation V H I) (n : Nat) : Prop :=
  ∀ b, n < b → (q b).lower = ∅

theorem permanent_incident (q : Nat → Annotation V H I) (n t : Nat)
    (hnt : n ≤ t) (hp : Permanent q n) : Incident q t := by
  obtain ⟨a,b,hab,hbn,hborn,hmatch⟩ := hp
  refine ⟨a+(t-b),(active_iff_ray q t t _).mpr ?_⟩
  refine ⟨by omega,a,b,t-b,rfl,by omega,hborn,?_⟩
  intro k _
  exact hmatch k

theorem incident_permanent (q : Nat → Annotation V H I) (n r t : Nat)
    (hr : 0 < r) (hp : LettersPeriodic q n r)
    (he : LowerEmptyAfter q n) (ht : 2*n+r ≤ t)
    (hi : Incident q t) : Permanent q n := by
  obtain ⟨j,hj⟩ := hi
  obtain ⟨hjt,a,b,l,haj,hbt,hborn,hmatch⟩ := (active_iff_ray q t t j).mp hj
  have hab : a ≤ b := by omega
  have hbn : b ≤ n := by
    by_contra h
    obtain ⟨v,_,hv⟩ := hborn
    rw [he b (by omega)] at hv
    exact hv
  exact ⟨a,b,hab,hbn,hborn,
    match_forever_of_long q n r a b l hr hp hab (by omega) hmatch⟩

/-- Exact x749 endpoint bound. It is also valid at every later frontier. -/
theorem incident_iff_permanent (q : Nat → Annotation V H I) (n r t : Nat)
    (hr : 0 < r) (hp : LettersPeriodic q n r)
    (he : LowerEmptyAfter q n) (ht : 2*n+r ≤ t) :
    Incident q t ↔ Permanent q n :=
  ⟨incident_permanent q n r t hr hp he ht,
   permanent_incident q n t (by omega)⟩

theorem isolated_at_bound_iff (q : Nat → Annotation V H I) (n r : Nat)
    (hr : 0 < r) (hp : LettersPeriodic q n r) (he : LowerEmptyAfter q n) :
    ¬ Incident q (2*n+r) ↔ ¬ Permanent q n :=
  not_congr (incident_iff_permanent q n r (2*n+r) hr hp he (by omega))

theorem eventually_isolated_iff (q : Nat → Annotation V H I) (n r : Nat)
    (hr : 0 < r) (hp : LettersPeriodic q n r) (he : LowerEmptyAfter q n) :
    (∃ t, n ≤ t ∧ ¬ Incident q t) ↔ ¬ Permanent q n := by
  constructor
  · rintro ⟨t,hnt,hi⟩ hperm
    exact hi (permanent_incident q n t hnt hperm)
  · intro hn
    exact ⟨2*n+r,by omega,(isolated_at_bound_iff q n r hr hp he).mpr hn⟩

/-- Rail exchange keeps literal comparisons and reverses semantic births.
Applying the proved theorem to this annotation gives the X-side result. -/
def exchange (q : Nat → Annotation V H I) (k : Nat) : Annotation V H I :=
  ⟨(q k).lower,(q k).upper,(q k).head,(q k).index⟩

theorem born_exchange (q : Nat → Annotation V H I) (a b : Nat) :
    Born (exchange q) a b ↔ Born q b a := by
  simp only [Born, exchange]
  exact exists_congr (fun _ => and_comm)

theorem ray_exchange (q : Nat → Annotation V H I) (a b l : Nat) :
    Ray (exchange q) a b l ↔ Ray q b a l := by
  change (Born (exchange q) a b ∧ _) ↔ (Born q b a ∧ _)
  rw [born_exchange]
  constructor
  · rintro ⟨hb,hm⟩
    exact ⟨hb,fun k hk => (hm k hk).symm⟩
  · rintro ⟨hb,hm⟩
    exact ⟨hb,fun k hk => (hm k hk).symm⟩

theorem incident_exchange (q : Nat → Annotation V H I) (t : Nat) :
    Incident (exchange q) t ↔ ∃ k, k ≤ t ∧ Active q t k t := by
  constructor
  · rintro ⟨j,hj⟩
    obtain ⟨hj,a,b,l,ha,hb,hr⟩ := (active_iff_ray (exchange q) t t j).mp hj
    exact ⟨j,hj,(active_iff_ray q t j t).mpr
      ⟨by omega,b,a,l,hb,ha,(ray_exchange q a b l).mp hr⟩⟩
  · rintro ⟨k,hk,hact⟩
    obtain ⟨_,a,b,l,ha,hb,hr⟩ := (active_iff_ray q t k t).mp hact
    exact ⟨k,(active_iff_ray (exchange q) t t k).mpr
      ⟨hk,b,a,l,hb,ha,(ray_exchange q b a l).mpr hr⟩⟩

/-- With X free, the permanent relation is R(q_b,q_a), not R(q_a,q_b). -/
theorem permanent_exchange (q : Nat → Annotation V H I) (n : Nat) :
    Permanent (exchange q) n ↔
      ∃ a b, a ≤ b ∧ b ≤ n ∧ Born q b a ∧ MatchForever q a b := by
  simp only [Permanent, born_exchange, MatchForever, exchange]

end NSSE.P0PeriodicIsolation
