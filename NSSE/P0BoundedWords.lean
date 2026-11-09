import NSSE.P0DDeadDecision
import Mathlib.Data.Finset.Lattice.Union

/-! Executable finite enumeration of all words up to a supplied length,
with exact membership and accepted-candidate specifications. -/
namespace NSSE.P0BoundedWords
open P0DDeadReader P0DDeadDecision
variable {Q A H : Type*} [DecidableEq A]

def words (alphabet : Finset A) : Nat → Finset (List A)
  | 0 => {[]}
  | n+1 => insert [] (alphabet.biUnion (fun a => (words alphabet n).image (List.cons a)))

theorem mem_words (alphabet : Finset A) (n : Nat) (w : List A) :
    w ∈ words alphabet n ↔ w.length ≤ n ∧ ∀ a ∈ w, a ∈ alphabet := by
  induction n generalizing w with
  | zero => cases w <;> simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons a w =>
      simp only [words,Finset.mem_insert,Finset.mem_biUnion,Finset.mem_image,
        List.cons_ne_nil,false_or,List.cons.injEq]
      constructor
      · rintro ⟨b,hb,v,hv,hba,hvw⟩
        subst b; subst v
        have ha := hb
        have hw := hv
        obtain ⟨hlen,hletters⟩ := (ih w).mp hw
        exact ⟨by simpa using hlen,by simpa using And.intro ha hletters⟩
      · rintro ⟨hlen,hletters⟩
        have hh : a ∈ alphabet ∧ ∀ b ∈ w, b ∈ alphabet := by simpa using hletters
        exact ⟨a,hh.1,w,(ih w).mpr ⟨by simpa using hlen,hh.2⟩,rfl,rfl⟩

def candidates [DecidableEq Q] [DecidableEq H] (J : Reader Q A H)
    (bd : DecidableRel J.birth) (alphabet : Finset A) (n : Nat) : Finset (List A) :=
  (words alphabet n).filter (fun w => inspect J bd w = true)

theorem mem_candidates [DecidableEq Q] [DecidableEq H] (J : Reader Q A H)
    (bd : DecidableRel J.birth) (alphabet : Finset A) (n : Nat) (w : List A) :
    w ∈ candidates J bd alphabet n ↔
      (w.length ≤ n ∧ ∀ a ∈ w, a ∈ alphabet) ∧ Accepted J w := by
  simp only [candidates,Finset.mem_filter,mem_words,inspect_correct]

def search [DecidableEq Q] [DecidableEq H] (J : Reader Q A H)
    (bd : DecidableRel J.birth) (alphabet : Finset A) (n : Nat) : Bool :=
  decide (candidates J bd alphabet n).Nonempty

theorem search_correct [DecidableEq Q] [DecidableEq H] (J : Reader Q A H)
    (bd : DecidableRel J.birth) (alphabet : Finset A) (n : Nat) :
    search J bd alphabet n = true ↔
      ∃ w, (w.length ≤ n ∧ ∀ a ∈ w, a ∈ alphabet) ∧ Accepted J w := by
  simp only [search,decide_eq_true_eq,Finset.Nonempty,mem_candidates]

end NSSE.P0BoundedWords
