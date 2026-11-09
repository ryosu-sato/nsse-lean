import NSSE.P0Cotree
import NSSE.P0SuffixMatrix

/-! Every finite family of decorated words has a union/join cotree when
the terminal labels differ. The construction partitions by the next head,
then by the next letter, and removes a common decorated letter. Thus it
applies to the actual suffix graph, not only to an abstract supplied tree. -/
namespace NSSE.P0SuffixCotree
open P0SuffixWords P0SuffixMatrix P0Cotree P0DDeadReader P0DDeadColor
variable {V Q A H : Type*} [DecidableEq V]

def Edge (endX endY : H) (s t : List (H × A)) : Prop :=
  ¬ Rel endX endY s t ∨ ¬ Rel endX endY t s

def BeginsHead (h : H) (s : List (H × A)) : Prop := ∃ a t, s = (h,a)::t
def Begins (h : H) (a : A) (s : List (H × A)) : Prop := ∃ t, s = (h,a)::t

theorem head_cross (endX endY h : H) (hne : endX ≠ endY) (s t : List (H × A))
    (hs : BeginsHead h s) (ht : ¬ BeginsHead h t) :
    Edge endX endY s t ∧ Edge endX endY t s := by
  obtain ⟨a,u,rfl⟩ := hs
  cases t with
  | nil =>
    have hh := terminal_join endX endY h a u hne
    exact ⟨hh.symm,hh⟩
  | cons x t =>
    obtain ⟨k,b⟩ := x
    have hk : h ≠ k := by intro he; subst k; exact ht ⟨b,t,rfl⟩
    have hh := different_heads endX endY h k a b u t hk
    exact ⟨Or.inl hh.1,Or.inl hh.2⟩

theorem letter_cross (endX endY h : H) (a : A) (s t : List (H × A))
    (hs : Begins h a s) (ht : BeginsHead h t) (ht' : ¬ Begins h a t) :
    ¬ Edge endX endY s t ∧ ¬ Edge endX endY t s := by
  obtain ⟨u,rfl⟩ := hs
  obtain ⟨b,v,rfl⟩ := ht
  have hab : a ≠ b := by intro he; subst b; exact ht' ⟨v,rfl⟩
  have hh := different_letters endX endY h a b u v hab
  exact ⟨fun he => he.elim (fun h => h hh.1) (fun h => h hh.2),
    fun he => he.elim (fun h => h hh.2) (fun h => h hh.1)⟩

theorem bounded_family (endX endY : H) (hne : endX ≠ endY) (n : Nat)
    (S : Finset V) (word : V → List (H × A)) (hs : S.Nonempty)
    (hlen : ∀ v ∈ S, (word v).length ≤ n) :
    HasCotree (fun a b => Edge endX endY (word a) (word b)) S := by
  classical
  induction n generalizing S word with
  | zero =>
    apply constant _ true S hs
    intro a ha b hb _
    have haw : word a = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (hlen a ha))
    have hbw : word b = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (hlen b hb))
    simp [haw,hbw,Edge,Rel,hne]
  | succ n ihn =>
    revert hs hlen
    refine Finset.strongInductionOn S ?_
    intro S ih hs hlen
    have hrec (T : Finset V) (hT : T ⊂ S) (hTne : T.Nonempty) :
        HasCotree (fun a b => Edge endX endY (word a) (word b)) T :=
      ih T hT hTne (fun v hv => hlen v (hT.1 hv))
    by_cases hall : ∀ v ∈ S, word v = []
    · apply constant _ true S hs
      intro a ha b hb _
      simp [hall a ha,hall b hb,Edge,Rel,hne]
    · obtain ⟨v,hv,hvne⟩ : ∃ v ∈ S, word v ≠ [] := by push_neg at hall; exact hall
      cases hwv : word v with
      | nil => exact False.elim (hvne hwv)
      | cons x u =>
        obtain ⟨h,a⟩ := x
        by_cases hh : ∀ z ∈ S, BeginsHead h (word z)
        · by_cases ha : ∀ z ∈ S, Begins h a (word z)
          · have htlen (z : V) (hz : z ∈ S) : (word z).tail.length ≤ n := by
              obtain ⟨t,ht⟩ := ha z hz
              have := hlen z hz
              simp only [ht,List.length_cons,List.tail_cons] at *
              omega
            have ht := ihn S (fun z => (word z).tail) hs htlen
            apply congr _ _ S ht
            intro x hx y hy
            obtain ⟨s,hxw⟩ := ha x hx
            obtain ⟨t,hyw⟩ := ha y hy
            simp only [hxw,hyw,List.tail_cons,Edge,same_letter]
          · have hn : ∃ z ∈ S, ¬ Begins h a (word z) := by push_neg at ha; exact ha
            apply partition _ false S (fun z => Begins h a (word z)) ⟨v,hv,u,hwv⟩ hn hrec
            intro x hx hxp y hy hyp
            have hc := letter_cross endX endY h a (word x) (word y) hxp (hh y hy) hyp
            simp [hc.1,hc.2]
        · have hn : ∃ z ∈ S, ¬ BeginsHead h (word z) := by push_neg at hh; exact hh
          apply partition _ true S (fun z => BeginsHead h (word z)) ⟨v,hv,a,u,hwv⟩ hn hrec
          intro x hx hxp y hy hyp
          have hc := head_cross endX endY h hne (word x) (word y) hxp hyp
          simp [hc.1,hc.2]

theorem actual (J : Reader Q A H) (w : List A) (hc : Complete J w) (hne : J.endX ≠ J.endY) :
    HasCotree (fun a b : Fin (w.length+1) => Adjacent J w a b) Finset.univ := by
  have ht := bounded_family J.endX J.endY hne w.length (Finset.univ : Finset (Fin (w.length+1)))
    (tailWord J w) Finset.univ_nonempty (by
      intro v _
      simp only [tailWord,List.length_drop,decorate_length]
      omega)
  apply congr _ _ _ ht
  intro a _ b _
  simp only [Edge,Adjacent,tailWord_exact J w hc]

end NSSE.P0SuffixCotree
