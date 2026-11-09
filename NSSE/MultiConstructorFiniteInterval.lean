import NSSE.MultiConstructorPairGraph

/-! Each supported-pair edge descends inside a finite tree lying between
the two original values. No monotonicity of tree height under subtyping
is assumed. A graph cycle therefore excludes every finite model. -/
namespace NSSE.MultiConstructorFiniteInterval
open MultiConstructorConstraints MultiConstructorFiniteTrees MultiConstructorPairGraph
variable {H : Type*} {arity : H → Nat} {n : Nat}

theorem child_between (h : H) (a b : Fin (arity h) → Tree arity) (t : Tree arity)
    (hl : MultiConstructorFiniteTrees.Tree.node h a ≤ t) (hu : t ≤ MultiConstructorFiniteTrees.Tree.node h b) (i : Fin (arity h)) :
    ∃ u : Tree arity, a i ≤ u ∧ u ≤ b i ∧ height u < height t := by
  cases t with
  | bot => exact False.elim (node_not_le_bot h a hl)
  | top => exact False.elim (top_not_le_node h b hu)
  | node g c =>
    have hg : h = g := node_head_eq hl
    subst g
    exact ⟨c i,(node_le_node h a c).mp hl i,(node_le_node h c b).mp hu i,child_height_lt h c i⟩

theorem move_interval (phi : Constraints arity n) (rho : Fin n → Tree arity) (hs : Satisfies finiteAlgebra phi rho)
    {p q : Pair n} (hm : Move phi p q) (t : Tree arity) (hl : rho p.1 ≤ t) (hu : t ≤ rho p.2) :
    ∃ u : Tree arity, rho q.1 ≤ u ∧ u ≤ rho q.2 ∧ height u < height t := by
  obtain ⟨_,a,ha,b,hb,hap,hpb,i,j,hh,hij,hqi,hjq⟩ := hm
  cases a with | mk x h ac =>
    cases b with | mk y g bc =>
      dsimp only at hh i j hij hap hpb hqi hjq
      subst g
      have he : i = j := Fin.ext hij
      subst j
      have hlo : MultiConstructorFiniteTrees.Tree.node h (fun k => rho (ac k)) ≤ t :=
        (hs.2.1 _ ha).trans ((support_sound finiteAlgebra phi rho hs hap).trans hl)
      have hhi : t ≤ MultiConstructorFiniteTrees.Tree.node h (fun k => rho (bc k)) :=
        hu.trans ((support_sound finiteAlgebra phi rho hs hpb).trans (hs.1 _ hb))
      obtain ⟨u,ha',hb',ht⟩ := child_between h _ _ t hlo hhi i
      exact ⟨u,(support_sound finiteAlgebra phi rho hs hqi).trans ha',
        hb'.trans (support_sound finiteAlgebra phi rho hs hjq),ht⟩

theorem reach_interval (phi : Constraints arity n) (rho : Fin n → Tree arity) (hs : Satisfies finiteAlgebra phi rho)
    {p q : Pair n} (hr : Reach phi p q) (t : Tree arity) (hl : rho p.1 ≤ t) (hu : t ≤ rho p.2) :
    ∃ u : Tree arity, rho q.1 ≤ u ∧ u ≤ rho q.2 ∧ height u < height t := by
  induction hr generalizing t with
  | single hm => exact move_interval phi rho hs hm t hl hu
  | tail _ hm ih =>
    obtain ⟨u,hlu,huu,htu⟩ := ih t hl hu
    obtain ⟨v,hlv,huv,htv⟩ := move_interval phi rho hs hm u hlu huu
    exact ⟨v,hlv,huv,htv.trans htu⟩

theorem solution_no_cycle (phi : Constraints arity n) (rho : Fin n → Tree arity)
    (hs : Satisfies finiteAlgebra phi rho) : ¬Cycle phi := by
  rintro ⟨p,hp⟩
  have hbad : ∀ k : Nat, ∀ t : Tree arity, height t = k → rho p.1 ≤ t → t ≤ rho p.2 → False := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro t ht hl hu
      obtain ⟨u,huL,huU,hut⟩ := reach_interval phi rho hs hp t hl hu
      exact ih (height u) (by omega) u rfl huL huU
  exact hbad _ (rho p.1) rfl le_rfl (support_sound finiteAlgebra phi rho hs (reach_source phi hp))

theorem finite_sat_no_cycle (phi : Constraints arity n) (hs : Satisfiable finiteAlgebra phi) : ¬Cycle phi := by
  obtain ⟨rho,hr⟩ := hs
  exact solution_no_cycle phi rho hr

end NSSE.MultiConstructorFiniteInterval
