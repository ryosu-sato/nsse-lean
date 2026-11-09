import NSSE.MultiConstructorShapeGrammar

/-! The actual pair rank supplies quadratic stabilization and height for
the two-sided grammar. No rank is an argument of the model program. -/
namespace NSSE.MultiConstructorShapeRank
open MultiConstructorConstraints MultiConstructorShapeTokens MultiConstructorShapeHead
open MultiConstructorShapeGrammar MultiConstructorFiniteTrees MultiConstructorTokens MultiConstructorPairGraph
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

def measure (rank : Pair n → Nat) (s : State n) : Nat := (Finset.product s.1 s.2).sup (fun p => 1+rank p)

theorem measure_bound (rank : Pair n → Nat) (hr : ∀ p, rank p < n*n) (s : State n) : measure rank s ≤ n*n := by
  apply Finset.sup_le
  intro p _
  have := hr p
  omega

theorem measure_pos (phi : Constraints arity n) (rank : Pair n → Nat) (s : State n) (h : H)
    (hh : head phi s = .node h) : 0 < measure rank s := by
  obtain ⟨⟨g,hg⟩,⟨k,hk⟩⟩ := node_nonempty phi s h hh
  obtain ⟨a,_,⟨x,hx,_⟩,_⟩ := (mem_lowerPins phi _ _).mp hg
  obtain ⟨b,_,⟨y,hy,_⟩,_⟩ := (mem_upperPins phi _ _).mp hk
  have hb : 1+rank (x,y) ≤ measure rank s := Finset.le_sup (f := fun p => 1+rank p) (Finset.mem_product.mpr ⟨hx,hy⟩)
  omega

theorem measure_decreases (phi : Constraints arity n) (hn : ¬LabelClash phi) (rank : Pair n → Nat)
    (hr : ∀ p q, Reach phi p q → rank q < rank p) (s : State n) (hs : Coherent phi s)
    (h : H) (hh : head phi s = .node h) (i : Nat) : measure rank (next phi s i) < measure rank s := by
  apply (Finset.sup_lt_iff (measure_pos phi rank s h hh)).mpr
  rintro ⟨c,e⟩ hce
  obtain ⟨hc,he⟩ := Finset.mem_product.mp hce
  obtain ⟨x,hx,y,hy,hm⟩ := child_pair phi hn s hs i c e hc he
  have hd := hr (x,y) (c,e) (one_reach phi hm)
  have hb : 1+rank (x,y) ≤ measure rank s := Finset.le_sup (f := fun p => 1+rank p) (Finset.mem_product.mpr ⟨hx,hy⟩)
  omega

theorem stable (phi : Constraints arity n) (hn : ¬LabelClash phi) (rank : Pair n → Nat)
    (hr : ∀ p q, Reach phi p q → rank q < rank p) (k : Nat) :
    ∀ s, Coherent phi s → measure rank s < k → unfold phi k s = unfold phi (k+1) s := by
  induction k with
  | zero => intro s _ hk; omega
  | succ k ih =>
    intro s hs hk
    cases he : head phi s with
    | bot => simp [unfold,he]
    | top => simp [unfold,he]
    | node h =>
      simp only [unfold,he]
      congr 1
      funext i
      apply ih _ (next_coherent phi hn s hs i.val)
      have hd := measure_decreases phi hn rank hr s hs h he i.val
      omega

theorem bounded_equation (phi : Constraints arity n) (hn : ¬LabelClash phi) (hc : ¬Cycle phi)
    (s : State n) (hs : Coherent phi s) :
    unfold phi (n*n+1) s = match head phi s with
      | .bot => .bot
      | .top => .top
      | .node h => .node h (fun i => unfold phi (n*n+1) (next phi s i.val)) := by
  obtain ⟨rank,hb,hr⟩ := exists_rank phi hc
  have hm : measure rank s < n*n+1 := by have := measure_bound rank hb s; omega
  rw [stable phi hn rank hr (n*n+1) s hs hm]
  rfl

theorem height_measure (phi : Constraints arity n) (hn : ¬LabelClash phi) (rank : Pair n → Nat)
    (hr : ∀ p q, Reach phi p q → rank q < rank p) (k : Nat) :
    ∀ s, Coherent phi s → height (unfold phi k s) ≤ measure rank s := by
  induction k with
  | zero => intro s _; exact Nat.zero_le _
  | succ k ih =>
    intro s hs
    cases he : head phi s with
    | bot => simp [unfold,he,height]
    | top => simp [unfold,he,height]
    | node h =>
      simp only [unfold,he,height]
      apply Nat.succ_le_iff.mpr
      apply (Finset.sup_lt_iff (measure_pos phi rank s h he)).mpr
      intro i _
      exact (ih _ (next_coherent phi hn s hs i.val)).trans_lt (measure_decreases phi hn rank hr s hs h he i.val)

theorem height_bound (phi : Constraints arity n) (hn : ¬LabelClash phi) (hc : ¬Cycle phi)
    (k : Nat) (s : State n) (hs : Coherent phi s) : height (unfold phi k s) ≤ n*n := by
  obtain ⟨rank,hb,hr⟩ := exists_rank phi hc
  exact (height_measure phi hn rank hr k s hs).trans (measure_bound rank hb s)

theorem model_height_bound (phi : Constraints arity n) (hn : ¬LabelClash phi) (hc : ¬Cycle phi)
    (x : Fin n) : height (model phi x) ≤ n*n := height_bound phi hn hc _ _ (initial_coherent phi x)

end NSSE.MultiConstructorShapeRank
