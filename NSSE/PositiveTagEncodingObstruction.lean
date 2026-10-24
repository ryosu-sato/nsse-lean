import NSSE.FiniteSubtypeTrees
import NSSE.SubtypeTerms
import NSSE.AbsorbingSubtypeTrees

/-! Positive existential constraints cannot define an order-embedded tagged
multi-constructor domain inside the one-constructor finite and arbitrary tree models.
This is an obstruction to one reduction strategy, not to decidability. -/
namespace NSSE.PositiveTagEncodingObstruction
open FiniteSubtypeTrees SubtypeTerms
variable {d n : Nat}

def meet : Tree d → Tree d → Tree d
  | .bot, _ => .bot
  | .top, b => b
  | .node _, .bot => .bot
  | .node a, .top => .node a
  | .node a, .node b => .node (fun i => meet (a i) (b i))

theorem meet_le_left (a b : Tree d) : meet a b ≤ a := by
  induction a generalizing b with
  | bot => exact .bot _
  | top => exact .top _
  | node a ih =>
    cases b with
    | bot => exact .bot _
    | top => exact le_refl _
    | node b => exact Below.node (fun i => ih i (b i))

theorem meet_le_right (a b : Tree d) : meet a b ≤ b := by
  induction a generalizing b with
  | bot => exact .bot _
  | top => exact le_refl _
  | node a ih =>
    cases b with
    | bot => exact le_refl _
    | top => exact .top _
    | node b => exact Below.node (fun i => ih i (b i))

theorem le_meet {c a b : Tree d} (ha : c ≤ a) (hb : c ≤ b) : c ≤ meet a b := by
  induction ha generalizing b with
  | bot a => exact .bot _
  | top c => exact hb
  | @node c a h ih =>
    cases hb with
    | top _ => exact Below.node h
    | node hb => exact Below.node (fun i => ih i (hb i))

theorem meet_mono {a b c e : Tree d} (h : a ≤ c) (h' : b ≤ e) :
    meet a b ≤ meet c e :=
  le_meet (le_trans (meet_le_left _ _) h) (le_trans (meet_le_right _ _) h')

theorem eval_meet (rho sigma : Fin n → Tree d) (t : Term n d) :
    eval (constructor d) (fun x => meet (rho x) (sigma x)) t =
      meet (eval (constructor d) rho t) (eval (constructor d) sigma t) := by
  induction t with
  | var x => rfl
  | bot => rfl
  | top => rfl
  | node c ih =>
    change Tree.node (fun i => eval (constructor d) (fun x => meet (rho x) (sigma x)) (c i)) =
      Tree.node (fun i => meet (eval (constructor d) rho (c i)) (eval (constructor d) sigma (c i)))
    exact congrArg Tree.node (funext ih)

theorem holds_meet (rho sigma : Fin n → Tree d) (l : Literal n d)
    (hr : Holds (constructor d) rho l) (hs : Holds (constructor d) sigma l) :
    Holds (constructor d) (fun x => meet (rho x) (sigma x)) l := by
  cases l with
  | le a b =>
    change eval _ _ a ≤ eval _ _ b
    rw [eval_meet, eval_meet]
    exact meet_mono hr hs
  | eq a b =>
    change eval _ _ a = eval _ _ b
    rw [eval_meet, eval_meet]
    exact congrArg₂ meet hr hs

theorem satisfies_meet (Q : Query n d) (rho sigma : Fin n → Tree d)
    (hr : Satisfies (constructor d) Q rho) (hs : Satisfies (constructor d) Q sigma) :
    Satisfies (constructor d) Q (fun x => meet (rho x) (sigma x)) := by
  intro l hl
  exact holds_meet rho sigma l (hr l hl) (hs l hl)

/-- One free output variable and any finite number of existential auxiliaries.
The query's conclusion is unused: only its positive premises define P. -/
def PositiveDefinable (P : Tree d → Prop) : Prop :=
  ∃ n, ∃ Q : Query (n+1) d, ∀ t,
    P t ↔ ∃ rho, Satisfies (constructor d) Q rho ∧ rho 0 = t

theorem positive_closed_meet {P : Tree d → Prop} (hP : PositiveDefinable P)
    {a b : Tree d} (ha : P a) (hb : P b) : P (meet a b) := by
  obtain ⟨n,Q,hQ⟩ := hP
  obtain ⟨rho,hr,er⟩ := (hQ a).mp ha
  obtain ⟨sigma,hs,es⟩ := (hQ b).mp hb
  apply (hQ _).mpr
  refine ⟨fun x => meet (rho x) (sigma x), satisfies_meet Q rho sigma hr hs, ?_⟩
  exact congrArg₂ meet er es

/-- General image obstruction. Distinct constructor minima have only bottom
as a common lower bound. If their encodings are constructor-rooted, their
meet is nonbottom, so the image cannot be positively defined, even with
arbitrarily many existential auxiliary variables and nested terms. -/
theorem image_not_positive {A : Type*} [PartialOrder A] [OrderBot A]
    (encode : A → Tree d)
    (reflect : ∀ a b, encode a ≤ encode b → a ≤ b)
    (bottom : encode ⊥ = .bot)
    (a b : A) (disjoint : ∀ z, z ≤ a → z ≤ b → z = ⊥)
    (ca cb : Fin d → Tree d)
    (ea : encode a = .node ca) (eb : encode b = .node cb) :
    ¬ PositiveDefinable (fun t => ∃ z, encode z = t) := by
  intro hp
  obtain ⟨z,hz⟩ := positive_closed_meet hp (⟨a,rfl⟩ : ∃ z, encode z = encode a)
    (⟨b,rfl⟩ : ∃ z, encode z = encode b)
  have za : z ≤ a := reflect z a (hz ▸ meet_le_left (encode a) (encode b))
  have zb : z ≤ b := reflect z b (hz ▸ meet_le_right (encode a) (encode b))
  have zbot := disjoint z za zb
  rw [zbot,bottom,ea,eb] at hz
  cases hz

/-- No particular tag layout is assumed: incomparability already forces
both encoded values to be constructor-rooted. -/
theorem disjoint_pair_image_not_positive {A : Type*} [PartialOrder A] [OrderBot A]
    (encode : A → Tree d)
    (reflect : ∀ a b, encode a ≤ encode b → a ≤ b)
    (bottom : encode ⊥ = .bot)
    (a b : A) (hab : ¬ a ≤ b) (hba : ¬ b ≤ a)
    (disjoint : ∀ z, z ≤ a → z ≤ b → z = ⊥) :
    ¬ PositiveDefinable (fun t => ∃ z, encode z = t) := by
  have root (x y : A) (hxy : ¬ x ≤ y) (hyx : ¬ y ≤ x) :
      ∃ c, encode x = .node c := by
    cases h : encode x with
    | bot => exact False.elim (hxy (reflect x y (h ▸ bot_le)))
    | top => exact False.elim (hyx (reflect y x (h ▸ le_top)))
    | node c => exact ⟨c,rfl⟩
  obtain ⟨ca,ea⟩ := root a b hab hba
  obtain ⟨cb,eb⟩ := root b a hba hab
  exact image_not_positive encode reflect bottom a b disjoint ca cb ea eb

/-- Every two constructor-rooted single-constructor values share this
nonbottom lower bound, independent of tags, arity, and payloads. -/
theorem spurious_common_lower (a b : Fin d → Tree d) :
    ∃ z : Tree d, z ≤ .node a ∧ z ≤ .node b ∧ ¬ z ≤ .bot := by
  refine ⟨.node (fun _ => .bot), Below.node (fun _ => .bot _),
    Below.node (fun _ => .bot _), ?_⟩
  intro h
  cases h

end NSSE.PositiveTagEncodingObstruction

namespace NSSE.PositiveTagEncodingObstruction.AllTrees
open AbsorbingSubtypeTrees SubtypeTerms
variable {d n : Nat}

private theorem nonzero_min_ne_one (a b : Fin 3) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : min a b ≠ 1) : a = 2 ∧ b = 2 := by
  rw [min_def] at h
  split at h <;> omega

/-- Pointwise minimum is an actual absorbing tree, including infinite inputs. -/
def meet (a b : Tree d) : Tree d where
  label w := min (a.label w) (b.label w)
  absorbs p q h := by
    by_cases ha : a.label p = 0
    · rw [a.absorbs p q (by simp [ha]), ha]
      simp
    by_cases hb : b.label p = 0
    · rw [b.absorbs p q (by simp [hb]), hb]
      simp
    obtain ⟨ha2,hb2⟩ := nonzero_min_ne_one _ _ ha hb h
    rw [a.absorbs p q (by simp [ha2]), b.absorbs p q (by simp [hb2])]

theorem meet_le_left (a b : Tree d) : meet a b ≤ a := fun _ => min_le_left _ _
theorem meet_le_right (a b : Tree d) : meet a b ≤ b := fun _ => min_le_right _ _
theorem meet_mono {a b c e : Tree d} (h : a ≤ c) (h' : b ≤ e) :
    meet a b ≤ meet c e := fun w => min_le_min (h w) (h' w)

theorem meet_node (a b : Fin d → Tree d) :
    meet (node a) (node b) = node (fun i => meet (a i) (b i)) := by
  ext w
  cases w <;> rfl

theorem eval_meet (rho sigma : Fin n → Tree d) (t : Term n d) :
    eval (constructor d) (fun x => meet (rho x) (sigma x)) t =
      meet (eval (constructor d) rho t) (eval (constructor d) sigma t) := by
  induction t with
  | var x => rfl
  | bot => rfl
  | top => rfl
  | node c ih =>
    change node _ = meet (node _) (node _)
    rw [meet_node]
    exact congrArg node (funext ih)

theorem satisfies_meet (Q : Query n d) (rho sigma : Fin n → Tree d)
    (hr : Satisfies (constructor d) Q rho) (hs : Satisfies (constructor d) Q sigma) :
    Satisfies (constructor d) Q (fun x => meet (rho x) (sigma x)) := by
  intro l hl
  have hrl := hr l hl
  have hsl := hs l hl
  cases l with
  | le a b =>
    change eval _ _ a ≤ eval _ _ b
    rw [eval_meet, eval_meet]
    exact meet_mono hrl hsl
  | eq a b =>
    change eval _ _ a = eval _ _ b
    rw [eval_meet, eval_meet]
    exact congrArg₂ meet hrl hsl

def PositiveDefinable (P : Tree d → Prop) : Prop :=
  ∃ n, ∃ Q : Query (n+1) d, ∀ t,
    P t ↔ ∃ rho, Satisfies (constructor d) Q rho ∧ rho 0 = t

theorem positive_closed_meet {P : Tree d → Prop} (hP : PositiveDefinable P)
    {a b : Tree d} (ha : P a) (hb : P b) : P (meet a b) := by
  obtain ⟨n,Q,hQ⟩ := hP
  obtain ⟨rho,hr,er⟩ := (hQ a).mp ha
  obtain ⟨sigma,hs,es⟩ := (hQ b).mp hb
  apply (hQ _).mpr
  exact ⟨fun x => meet (rho x) (sigma x), satisfies_meet Q rho sigma hr hs,
    congrArg₂ meet er es⟩

theorem image_not_positive {A : Type*} [PartialOrder A] [OrderBot A]
    (encode : A → Tree d)
    (reflect : ∀ a b, encode a ≤ encode b → a ≤ b)
    (bottom : encode ⊥ = ⊥)
    (a b : A) (disjoint : ∀ z, z ≤ a → z ≤ b → z = ⊥)
    (ca cb : Fin d → Tree d)
    (ea : encode a = node ca) (eb : encode b = node cb) :
    ¬ PositiveDefinable (fun t => ∃ z, encode z = t) := by
  intro hp
  obtain ⟨z,hz⟩ := positive_closed_meet hp (⟨a,rfl⟩ : ∃ z, encode z = encode a)
    (⟨b,rfl⟩ : ∃ z, encode z = encode b)
  have za : z ≤ a := reflect z a (hz ▸ meet_le_left (encode a) (encode b))
  have zb : z ≤ b := reflect z b (hz ▸ meet_le_right (encode a) (encode b))
  have zbot := disjoint z za zb
  rw [zbot,bottom,ea,eb,meet_node] at hz
  have hr := congrArg (fun t : Tree d => t.label []) hz
  change (0 : Fin 3) = 1 at hr
  cases hr

theorem disjoint_pair_image_not_positive {A : Type*} [PartialOrder A] [OrderBot A]
    (encode : A → Tree d)
    (reflect : ∀ a b, encode a ≤ encode b → a ≤ b)
    (bottom : encode ⊥ = ⊥)
    (a b : A) (hab : ¬ a ≤ b) (hba : ¬ b ≤ a)
    (disjoint : ∀ z, z ≤ a → z ≤ b → z = ⊥) :
    ¬ PositiveDefinable (fun t => ∃ z, encode z = t) := by
  have root (x y : A) (hxy : ¬ x ≤ y) (hyx : ¬ y ≤ x) :
      ∃ c, encode x = node c := by
    rcases root_cases (encode x) with h | h | h
    · exact False.elim (hxy (reflect x y (h ▸ bot_le)))
    · exact h
    · exact False.elim (hyx (reflect y x (h ▸ le_top)))
  obtain ⟨ca,ea⟩ := root a b hab hba
  obtain ⟨cb,eb⟩ := root b a hba hab
  exact image_not_positive encode reflect bottom a b disjoint ca cb ea eb

end NSSE.PositiveTagEncodingObstruction.AllTrees
