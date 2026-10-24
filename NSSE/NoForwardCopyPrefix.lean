import NSSE.GeneralCopyGrid

/-! A general no-forward-copy criterion and the arithmetic kernel of the
internal-ray free-frontier family. No general entailment decider is claimed. -/
namespace NSSE.NoForwardCopyPrefix
open PeriodicCopyHeadNormalization GeneralCopyGrid
variable {V H I : Type*}

def NoForwardBirth (q : Nat → Annotation V H I) (N : Nat) : Prop :=
  ∀ a b, a ≤ N → b < a → ¬ Born q a b

/-- For a fixed seed, absence of forward births is exactly absence of all
forward copies, including those with arbitrarily long propagation. -/
theorem noForward_iff_sources (q : Nat → Annotation V H I) (N : Nat) :
    NoForwardBirth q N ↔ ∀ k j, Active q N k j → j ≤ k := by
  constructor
  · intro hn k j ha
    obtain ⟨hj,a,b,r,has,hbt,hr⟩ := (active_iff_ray q N k j).mp ha
    by_contra h
    exact hn a b (by omega) (by omega) hr.1
  · intro hs a b ha hb hbirth
    have hactive : Active q N b a := (active_iff_ray q N b a).mpr
      ⟨ha,a,b,0,by omega,by omega,(ray_zero q a b).mpr hbirth⟩
    have := hs b a hactive
    omega

def seen (q : Nat → Annotation V H I) : Nat → Set V
  | 0 => ∅
  | k+1 => seen q k ∪ (q k).lower

theorem mem_seen (q : Nat → Annotation V H I) (k : Nat) (v : V) :
    v ∈ seen q k ↔ ∃ b, b < k ∧ v ∈ (q b).lower := by
  induction k with
  | zero => simp [seen]
  | succ k ih =>
    change (v ∈ seen q k ∨ v ∈ (q k).lower) ↔ _
    rw [ih]
    constructor
    · rintro (⟨b,hb,hv⟩ | hv)
      · exact ⟨b,by omega,hv⟩
      · exact ⟨k,by omega,hv⟩
    · rintro ⟨b,hb,hv⟩
      by_cases h : b < k
      · exact Or.inl ⟨b,h,hv⟩
      · have : b = k := by omega
        exact Or.inr (this ▸ hv)

/-- Only the union of earlier lower sets is needed to detect a forward birth. -/
theorem noForward_iff_seen (q : Nat → Annotation V H I) (N : Nat) :
    NoForwardBirth q N ↔
      ∀ a, a ≤ N → ∀ v, v ∈ (q a).upper → v ∉ seen q a := by
  constructor
  · intro hn a ha v hu hs
    obtain ⟨b,hb,hl⟩ := (mem_seen q a v).mp hs
    exact hn a b ha hb ⟨v,hu,hl⟩
  · intro hn a b ha hb hbirth
    obtain ⟨v,hu,hl⟩ := hbirth
    exact hn a ha v hu ((mem_seen q a v).mpr ⟨b,hb,hl⟩)

/-- Rows no longer depend on future source positions. This concerns the raw
copy grid; the semantic top-prefix cone-closing lemma is separate. -/
theorem prefix_only (q : Nat → Annotation V H I) (N k j : Nat)
    (hn : NoForwardBirth q N) (hk : k ≤ N) :
    Active q N k j ↔ Active q k k j := by
  rw [active_truncate q k N k j hk]
  exact ⟨fun h => ⟨h,(noForward_iff_sources q N).mp hn k j h⟩,And.left⟩

/-- Child-index word 0^a 1^b 0^c 1, extended with 1 beyond its end. -/
def bit (a b c j : Nat) : Bool :=
  if j < a then false else if j < a+b then true else if j < a+b+c then false else true

/-- A ray born at an initial zero-run position and at the first position
AFTER the third block starts reaches the free frontier iff c<=a+1.
This quantifies over all run lengths, rather than a bounded test grid. -/
theorem internal_ray_threshold (a b c : Nat) (hb : 0 < b) (hc : 0 < c) :
    (∃ ell, ell ≤ a ∧ ∀ d, d < c →
      bit a b c (ell+d) = bit a b c (a+b+1+d)) ↔ c ≤ a+1 := by
  constructor
  · rintro ⟨ell,hell,hm⟩
    by_contra h
    have he : ell+(a-ell) = a := by omega
    have hh := hm (a-ell) (by omega)
    rw [he] at hh
    have h₁ : ¬ a < a := by omega
    have h₂ : a < a+b := by omega
    have h₃ : ¬ a+b+1+(a-ell) < a := by omega
    have h₄ : ¬ a+b+1+(a-ell) < a+b := by omega
    have h₅ : a+b+1+(a-ell) < a+b+c := by omega
    simp [bit,h₁,h₂,h₃,h₄,h₅] at hh
  · intro h
    refine ⟨a+1-c,by omega,?_⟩
    intro d hd
    by_cases hlast : d+1 = c
    · have he : a+1-c+d = a := by omega
      have ht : a+b+1+d = a+b+c := by omega
      rw [he,ht]
      simp [bit,show ¬ a < a by omega,show a < a+b by omega,
        show ¬ a+b+c < a by omega,show ¬ a+b+c < a+b by omega]
    · have he : a+1-c+d < a := by omega
      have h₁ : ¬ a+b+1+d < a := by omega
      have h₂ : ¬ a+b+1+d < a+b := by omega
      have h₃ : a+b+1+d < a+b+c := by omega
      simp [bit,he,h₁,h₂,h₃]

end NSSE.NoForwardCopyPrefix
