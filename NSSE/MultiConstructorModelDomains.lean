import NSSE.MultiConstructorModelTokens

/-! Actual model bounds discharge all original token-domain guards.
Only the appropriate nonextreme root assumptions are needed. -/
namespace NSSE.MultiConstructorModelDomains
open MultiConstructorTrees MultiConstructorConstraints MultiConstructorTokens MultiConstructorRawTrace
open MultiConstructorRawValidity
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

omit [DecidableEq H] in
theorem label_upper (e : Label H) (h : H) (hne : e ≠ .bot) (hle : e ≤ .node h) : e = .node h := by
  rcases hle with he | he | he
  · exact False.elim (hne he)
  · cases he
  · exact he

omit [DecidableEq H] in
theorem label_lower (e : Label H) (h : H) (hne : e ≠ .top) (hle : .node h ≤ e) : e = .node h := by
  rcases hle with he | he | he
  · cases he
  · exact False.elim (hne he)
  · exact he.symm

theorem upper_pin (phi : Constraints arity n) (rho : Fin n → Tree arity) (hs : Satisfies allAlgebra phi rho)
    (s : Row n) (t : Tree arity) (hu : ∀ u ∈ s.1, t ≤ rho u) (hne : t.label [] ≠ .bot)
    (h : H) (hh : h ∈ upperPins phi s.1) : t.label [] = .node h := by
  obtain ⟨a,ha,⟨u,huS,hua⟩,he⟩ := (mem_upperPins phi s.1 h).mp hh
  have ht := (hu u huS).trans ((support_sound allAlgebra phi rho hs hua).trans (hs.1 a ha))
  apply label_upper _ h hne
  simpa only [allAlgebra,MultiConstructorTrees.Tree.node_label_nil,he] using ht []

theorem lower_pin (phi : Constraints arity n) (rho : Fin n → Tree arity) (hs : Satisfies allAlgebra phi rho)
    (s : Row n) (t : Tree arity) (hl : ∀ v ∈ s.2, rho v ≤ t) (hne : t.label [] ≠ .top)
    (h : H) (hh : h ∈ lowerPins phi s.2) : t.label [] = .node h := by
  obtain ⟨a,ha,⟨v,hvS,hav⟩,he⟩ := (mem_lowerPins phi s.2 h).mp hh
  have ht := (hs.2.1 a ha).trans ((support_sound allAlgebra phi rho hs hav).trans (hl v hvS))
  apply label_lower _ h hne
  simpa only [allAlgebra,MultiConstructorTrees.Tree.node_label_nil,he] using ht []

theorem upper_facts (phi : Constraints arity n) (rho : Fin n → Tree arity) (hs : Satisfies allAlgebra phi rho)
    (s : Row n) (t : Tree arity) (hu : ∀ u ∈ s.1, t ≤ rho u) (hne : t.label [] ≠ .bot) :
    (upperPins phi s.1).card ≤ 1 ∧ (∀ u ∈ s.1, ∀ b ∈ phi.bot, ¬Support phi u b) ∧
      UpperDomain phi s (t.label []) := by
  have hp := upper_pin phi rho hs s t hu hne
  refine ⟨?_,?_,?_⟩
  · apply Finset.card_le_one.mpr
    intro g hg h hh
    exact Label.node.inj ((hp g hg).symm.trans (hp h hh))
  · intro u hus b hb hub
    have ht : t ≤ ⊥ := (hu u hus).trans ((support_sound allAlgebra phi rho hs hub).trans_eq (hs.2.2.1 b hb))
    exact hne (le_antisymm (ht []) bot_le)
  · cases ht : t.label [] with
    | bot => exact False.elim (hne ht)
    | top =>
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro h hh
      have he := hp h hh
      rw [ht] at he
      cases he
    | node h =>
      intro g hg
      have he := hp g hg
      rw [ht] at he
      exact (Label.node.inj he).symm

theorem lower_facts (phi : Constraints arity n) (rho : Fin n → Tree arity) (hs : Satisfies allAlgebra phi rho)
    (s : Row n) (t : Tree arity) (hl : ∀ v ∈ s.2, rho v ≤ t) (hne : t.label [] ≠ .top) :
    (lowerPins phi s.2).card ≤ 1 ∧ (∀ v ∈ s.2, ∀ a ∈ phi.top, ¬Support phi a v) ∧
      LowerDomain phi s (t.label []) := by
  have hp := lower_pin phi rho hs s t hl hne
  refine ⟨?_,?_,?_⟩
  · apply Finset.card_le_one.mpr
    intro g hg h hh
    exact Label.node.inj ((hp g hg).symm.trans (hp h hh))
  · intro v hvs a ha hav
    have ht : ⊤ ≤ t := (le_of_eq (hs.2.2.2 a ha).symm).trans
      ((support_sound allAlgebra phi rho hs hav).trans (hl v hvs))
    exact hne (le_antisymm le_top (ht []))
  · cases ht : t.label [] with
    | top => exact False.elim (hne ht)
    | bot =>
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro h hh
      have he := hp h hh
      rw [ht] at he
      cases he
    | node h =>
      intro g hg
      have he := hp g hg
      rw [ht] at he
      exact (Label.node.inj he).symm

theorem valid_domains (phi : Constraints arity n) (rho : Fin n → Tree arity) (hs : Satisfies allAlgebra phi rho)
    (s : Row n) (a b : Tree arity) (hu : ∀ u ∈ s.1, a ≤ rho u) (hl : ∀ v ∈ s.2, rho v ≤ b)
    (ha : a.label [] ≠ .bot) (hb : b.label [] ≠ .top) :
    Valid phi s ∧ UpperDomain phi s (a.label []) ∧ LowerDomain phi s (b.label []) := by
  have hx := upper_facts phi rho hs s a hu ha
  have hy := lower_facts phi rho hs s b hl hb
  exact ⟨⟨hx.1,hy.1,hx.2.1,hy.2.1⟩,hx.2.2,hy.2.2⟩

end NSSE.MultiConstructorModelDomains
