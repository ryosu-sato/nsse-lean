import NSSE.MultiVarianceShapeGrammar

/-! The actual signed pair graph supplies quadratic stabilization and
height. The executable shape model has fixed input-derived fuel; the
existential descending rank occurs ONLY in its correctness proof. -/
namespace NSSE.MultiVarianceShapeRank
open MultiConstructorConstraints (Constraints)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceModelTokens MultiVarianceShapeTokens
open MultiVarianceShapeHead MultiVarianceShapeGrammar MultiVarianceFiniteTrees MultiVariancePairGraph
open MultiConstructorFiniteTrees (height)
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

def measure (rank : Pair n → Nat) (S : State n) : Nat := (Finset.product S.1 S.2).sup (fun p => 1+rank p)

theorem measure_bound (rank : Pair n → Nat) (hr : ∀ p, rank p<n*n) (S : State n) : measure rank S≤n*n := by
  apply Finset.sup_le
  intro p _
  have := hr p
  omega

theorem measure_pos (phi : Constraints arity n) (rank : Pair n → Nat) (S : State n) (h : H)
    (hh : head phi S=.node h) : 0<measure rank S := by
  obtain ⟨⟨g,hg⟩,⟨k,hk⟩⟩ := node_nonempty phi S h hh
  obtain ⟨a,_,ha,_⟩ := (mem_lowerPins phi _ _).mp hg
  obtain ⟨b,_,hb,_⟩ := (mem_upperPins phi _ _).mp hk
  have hm : 1+rank (a.parent,b.parent)≤measure rank S :=
    Finset.le_sup (f := fun p => 1+rank p) (Finset.mem_product.mpr ⟨ha,hb⟩)
  omega

variable (pol : Polarity arity)

theorem measure_decreases (phi : Constraints arity n) (rank : Pair n → Nat)
    (hr : ∀ p q, Reach pol phi p q → rank q<rank p) (S : State n) (hs : Compatible pol phi S)
    (h : H) (hh : head phi S=.node h) (i : Fin (arity h)) :
    measure rank (move pol phi S h i)<measure rank S := by
  apply (Finset.sup_lt_iff (measure_pos phi rank S h hh)).mpr
  rintro ⟨c,e⟩ hce
  obtain ⟨hc,he⟩ := Finset.mem_product.mp hce
  obtain ⟨x,hx,y,hy,hm⟩ := child_pair pol phi S hs h i c e hc he
  have hd := hr (x,y) (c,e) (one_reach pol phi hm)
  have hb : 1+rank (x,y)≤measure rank S :=
    Finset.le_sup (f := fun p => 1+rank p) (Finset.mem_product.mpr ⟨hx,hy⟩)
  omega

theorem stable (phi : Constraints arity n) (rank : Pair n → Nat)
    (hr : ∀ p q, Reach pol phi p q → rank q<rank p) (k : Nat) :
    ∀ S, Compatible pol phi S → measure rank S<k → unfold pol phi k S=unfold pol phi (k+1) S := by
  induction k with
  | zero => intro S _ hk; omega
  | succ k ih =>
    intro S hs hk
    cases he : head phi S with
    | bot => simp [unfold,he]
    | top => simp [unfold,he]
    | node h =>
      simp only [unfold,he]
      congr 1
      funext i
      apply ih _ (move_compatible pol phi S hs h i)
      have hd := measure_decreases pol phi rank hr S hs h he i
      omega

theorem bounded_equation (phi : Constraints arity n) (hc : ¬Cycle pol phi)
    (S : State n) (hs : Compatible pol phi S) :
    unfold pol phi (n*n+1) S=match head phi S with
      | .bot => .bot
      | .top => .top
      | .node h => .node h (fun i => unfold pol phi (n*n+1) (move pol phi S h i)) := by
  obtain ⟨rank,hb,hr⟩ := exists_rank pol phi hc
  have hm : measure rank S<n*n+1 := by have := measure_bound rank hb S; omega
  rw [stable pol phi rank hr (n*n+1) S hs hm]
  rfl

theorem height_measure (phi : Constraints arity n) (rank : Pair n → Nat)
    (hr : ∀ p q, Reach pol phi p q → rank q<rank p) (k : Nat) :
    ∀ S, Compatible pol phi S → height (unfold pol phi k S)≤measure rank S := by
  induction k with
  | zero => intro S _; exact Nat.zero_le _
  | succ k ih =>
    intro S hs
    cases he : head phi S with
    | bot => simp [unfold,he,height]
    | top => simp [unfold,he,height]
    | node h =>
      simp only [unfold,he,height]
      apply Nat.succ_le_iff.mpr
      apply (Finset.sup_lt_iff (measure_pos phi rank S h he)).mpr
      intro i _
      exact (ih _ (move_compatible pol phi S hs h i)).trans_lt
        (measure_decreases pol phi rank hr S hs h he i)

theorem height_bound (phi : Constraints arity n) (hc : ¬Cycle pol phi) (k : Nat)
    (S : State n) (hs : Compatible pol phi S) : height (unfold pol phi k S)≤n*n := by
  obtain ⟨rank,hb,hr⟩ := exists_rank pol phi hc
  exact (height_measure pol phi rank hr k S hs).trans (measure_bound rank hb S)

theorem model_height_bound (phi : Constraints arity n) (hc : ¬Cycle pol phi) (x : Fin n) :
    height (model pol phi x)≤n*n := height_bound pol phi hc _ _ (start_compatible pol phi x)

end NSSE.MultiVarianceShapeRank
