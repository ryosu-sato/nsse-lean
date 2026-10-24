import NSSE.SubtypeTerms
import NSSE.StoredFiniteSatisfiability

namespace NSSE.StoredSubtypeTerm

inductive Term (n : Nat) where
  | var (x : Fin n)
  | bot
  | top
  | node (children : List (Term n))

variable {n : Nat}

def WellFormed (d : Nat) : Term n → Prop
  | .var _ | .bot | .top => True
  | .node cs => cs.length=d ∧ ∀ t ∈ cs, WellFormed d t

def denote (d : Nat) : Term n → SubtypeTerms.Term n d
  | .var x => .var x
  | .bot => .bot
  | .top => .top
  | .node cs =>
    let ds := cs.map (denote d)
    .node (fun i => ds[i.val]?.getD .bot)

mutual
def equal : Term n → Term n → Bool × Nat
  | .var x, .var y => let r := FiniteValuationLookup.equalNat x.val y.val; (r.1,1+r.2)
  | .bot, .bot => (true,1)
  | .top, .top => (true,1)
  | .node as, .node bs => let r := equalLists as bs; (r.1,1+r.2)
  | _, _ => (false,1)
termination_by a _ => sizeOf a

def equalLists : List (Term n) → List (Term n) → Bool × Nat
  | [], [] => (true,1)
  | a::as, b::bs => let h := equal a b; let t := equalLists as bs; (h.1 && t.1,1+h.2+t.2)
  | _, _ => (false,1)
termination_by as _ => sizeOf as
end

theorem correct (a b : Term n) : (equal a b).1=true ↔ a=b := by
  apply equal.induct
    (motive1 := fun a b => (equal a b).1=true ↔ a=b)
    (motive2 := fun as bs => (equalLists as bs).1=true ↔ as=bs)
  all_goals
    intros
    simp_all [equal,equalLists,FiniteValuationLookup.equalNat_correct,Fin.ext_iff]
  · rename_i t u hv hb ht hn
    intro h
    subst u
    cases t with
    | var x => exact hv x x rfl rfl
    | bot => exact hb rfl rfl
    | top => exact ht rfl rfl
    | node cs => exact hn cs cs rfl rfl
  · rename_i xs ys hz hc
    intro h
    subst ys
    cases xs with
    | nil => exact hz rfl rfl
    | cons x xs => exact hc x xs x xs rfl rfl

def weight : Term n → Nat
  | .var x => x.val+1
  | .bot | .top => 1
  | .node cs => 1+(cs.map (fun t => 1+weight t)).sum

theorem weight_pos (t : Term n) : 1 ≤ weight t := by
  cases t <;> simp [weight]

theorem bound (a b : Term n) : (equal a b).2 ≤ 2*weight a := by
  apply equal.induct
    (motive1 := fun a b => (equal a b).2 ≤ 2*weight a)
    (motive2 := fun as bs => (equalLists as bs).2 ≤ 1+2*(as.map (fun t => 1+weight t)).sum)
  all_goals
    intros
    simp_all only [equal,equalLists,weight,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil]
    try omega
  · rename_i x y
    have h := FiniteValuationLookup.equalNat_bound x.val y.val
    omega
  · rename_i t u _ _ _ _
    have h := weight_pos t
    omega
/-- Structural correspondence; not an uncharged executable compiler. -/
def pack {d : Nat} : SubtypeTerms.Term n d → Term n
  | .var x => .var x
  | .bot => .bot
  | .top => .top
  | .node c => .node (List.ofFn (fun i => pack (c i)))

theorem pack_wellFormed {d : Nat} (t : SubtypeTerms.Term n d) : WellFormed d (pack t) := by
  induction t with
  | var x => simp [pack,WellFormed]
  | bot => simp [pack,WellFormed]
  | top => simp [pack,WellFormed]
  | node c ih =>
    simp only [pack,WellFormed,List.length_ofFn]
    refine ⟨trivial,?_⟩
    intro t ht
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
    exact ih i

theorem denote_pack {d : Nat} (t : SubtypeTerms.Term n d) : denote d (pack t) = t := by
  induction t with
  | var x => simp [pack,denote]
  | bot => simp [pack,denote]
  | top => simp [pack,denote]
  | node c ih =>
    simp only [pack,denote]
    congr 1
    funext i
    simp [List.getElem?_eq_getElem,ih]

theorem pack_injective (d : Nat) : Function.Injective (pack (n := n) (d := d)) := by
  intro a b h
  have he := congrArg (denote d) h
  simpa only [denote_pack] using he

theorem packed_equal {d : Nat} (a b : SubtypeTerms.Term n d) :
    (equal (pack a) (pack b)).1 = true ↔ a=b := by
  rw [correct]
  exact (pack_injective d).eq_iff
end NSSE.StoredSubtypeTerm
