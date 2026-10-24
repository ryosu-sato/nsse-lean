import NSSE.FiniteSubtypeSafety

/-! # Absorbing path projection and the semantic P-edge argument

Projection keeps bottom and top fixed after a leaf. It is monotone and
turns the original partial-subtree safety predicate into a root test.
The periodic argument is a general proof, not bounded tree enumeration.
-/

namespace NSSE.FiniteSubtypeProjection

open FiniteSubtypeTrees FiniteSubtypeSafety ForwardTableAutomaton

variable {d : Nat}

def project : Tree d → List (Fin d) → Tree d
  | t, [] => t
  | .bot, _ :: _ => .bot
  | .top, _ :: _ => .top
  | .node children, i :: path => project (children i) path

@[simp] theorem project_nil (t : Tree d) : project t [] = t := by cases t <;> rfl
@[simp] theorem project_bot (path : List (Fin d)) : project .bot path = .bot := by
  cases path <;> rfl
@[simp] theorem project_top (path : List (Fin d)) : project .top path = .top := by
  cases path <;> rfl

theorem project_cons (t : Tree d) (i : Fin d) (path : List (Fin d)) :
    project t (i :: path) = project (project t [i]) path := by
  cases t <;> simp [project]

theorem project_append (t : Tree d) (a b : List (Fin d)) :
    project t (a ++ b) = project (project t a) b := by
  induction a generalizing t with
  | nil => simp
  | cons i a ih =>
      rw [List.cons_append, project_cons t i (a ++ b), ih, project_cons t i a]

theorem project_mono {a b : Tree d} (h : a ≤ b) (path : List (Fin d)) :
    project a path ≤ project b path := by
  change Below a b at h
  induction h generalizing path with
  | bot b => simpa only [project_bot] using (bot_le : (⊥ : Tree d) ≤ project b path)
  | top a => simpa only [project_top] using (le_top : project a path ≤ (⊤ : Tree d))
  | node h ih =>
      cases path with
      | nil => exact Below.node h
      | cons i path => exact ih i path

def RootSafe (side : Side) (a b : Tree d) : Prop :=
  match side with
  | .left => a = .top → b = .top
  | .right => b = .bot → a = .bot

theorem hits_bot (target : Tree d) (path : List (Fin d)) :
    Hits .bot target path ↔ target = .bot := by
  constructor
  · rintro ⟨pref, _, h⟩
    cases pref with
    | nil => exact (Option.some.inj h).symm
    | cons i pref => cases h
  · rintro rfl
    exact ⟨[], List.nil_prefix, rfl⟩

theorem hits_top (target : Tree d) (path : List (Fin d)) :
    Hits .top target path ↔ target = .top := by
  constructor
  · rintro ⟨pref, _, h⟩
    cases pref with
    | nil => exact (Option.some.inj h).symm
    | cons i pref => cases h
  · rintro rfl
    exact ⟨[], List.nil_prefix, rfl⟩

theorem hasNode_bot (path : List (Fin d)) : ¬ HasNode .bot path := by
  cases path <;> simp [HasNode, atPath]

theorem hasNode_top (path : List (Fin d)) : ¬ HasNode .top path := by
  cases path <;> simp [HasNode, atPath]

theorem hasNode_cons (children : Fin d → Tree d) (i : Fin d) (path : List (Fin d)) :
    HasNode (.node children) (i :: path) ↔ HasNode (children i) path := Iff.rfl

theorem safe_iff_project (side : Side) (a b : Tree d) (path : List (Fin d)) :
    Safe side a b path ↔ RootSafe side (project a path) (project b path) := by
  induction path generalizing a b with
  | nil => cases side <;> cases a <;> cases b <;>
      simp [Safe, HasNode, atPath, RootSafe]
  | cons i path ih =>
      cases a with
      | bot => cases side <;> simp [Safe, hits_bot, RootSafe, project]
      | top =>
          cases b with
          | bot => cases side <;> simp [Safe, hits_bot, hits_top, hasNode_bot,
              hasNode_top, RootSafe, project]
          | top => cases side <;> simp [Safe, hits_top, RootSafe, project]
          | node b =>
              have hi := ih .top (b i)
              cases side <;>
                simpa [Safe, hits_top, hasNode_top, hasNode_cons,
                  hits_cons_node b .top (by intro h; cases h), RootSafe, project] using hi
      | node a =>
          cases b with
          | bot =>
              have hi := ih (a i) .bot
              cases side <;>
                simpa [Safe, hits_bot, hasNode_bot, hasNode_cons,
                  hits_cons_node a .bot (by intro h; cases h), RootSafe, project] using hi
          | top => cases side <;> simp [Safe, hits_top, RootSafe, project]
          | node b => exact (safe_cons_nodes side a b i path).trans (ih (a i) (b i))

theorem rootSafe_of_le {a b : Tree d} (h : a ≤ b) (side : Side) : RootSafe side a b := by
  cases side with
  | left => intro he; subst a; exact le_antisymm le_top h
  | right => intro he; subst b; exact le_antisymm h bot_le

theorem rootSafe_mono (side : Side) {a a' b b' : Tree d}
    (ha : a ≤ a') (hb : b' ≤ b) (h : RootSafe side a' b') : RootSafe side a b := by
  cases side with
  | left =>
      intro he
      have he' : a' = .top := rootSafe_of_le ha .left he
      exact rootSafe_of_le hb .left (h he')
  | right =>
      intro he
      have he' : b' = .bot := rootSafe_of_le hb .right he
      exact rootSafe_of_le ha .right (h he')

theorem safe_mono (side : Side) {a a' b b' : Tree d}
    (ha : a ≤ a') (hb : b' ≤ b) {path : List (Fin d)}
    (h : Safe side a' b' path) : Safe side a b path :=
  (safe_iff_project side a b path).mpr (rootSafe_mono side
    (project_mono ha path) (project_mono hb path) ((safe_iff_project side a' b' path).mp h))

theorem safe_append (side : Side) (a b : Tree d) (path tail : List (Fin d)) :
    Safe side a b (path ++ tail) ↔ Safe side (project a path) (project b path) tail := by
  simp only [safe_iff_project, project_append]

theorem project_absorbing {t leaf : Tree d} (hleaf : leaf = .bot ∨ leaf = .top)
    {pref path : List (Fin d)} (hp : pref <+: path) (he : project t pref = leaf) :
    project t path = leaf := by
  rcases hp with ⟨rest, rfl⟩
  rw [project_append, he]
  rcases hleaf with rfl | rfl <;> simp

/-- The word relation used by P-edges: every power prefix prefixes one
additional root followed by itself. Empty roots and empty tails are included. -/
theorem prefix_root_self {α : Type*} (root tail : List α) (k : Nat)
    (hp : tail <+: Language.wordPower root k) : tail <+: root ++ tail := by
  have h₁ : tail <+: Language.wordPower root (k + 1) := hp.trans (by
    rw [Language.wordPower_succ_right]
    exact List.prefix_append _ _)
  have h₂ : root ++ tail <+: Language.wordPower root (k + 1) := by
    rw [Language.wordPower_succ]
    exact (List.prefix_append_right_inj root).mpr hp
  exact List.prefix_of_prefix_length_le h₁ h₂ (by simp)

theorem periodic_left (a b : Tree d) (root tail : List (Fin d))
    (h : project a root ≤ b) (hp : tail <+: root ++ tail) : Safe .left a b tail := by
  apply (safe_iff_project .left a b tail).mpr
  intro ht
  have he := project_absorbing (Or.inr rfl) hp ht
  rw [project_append] at he
  exact rootSafe_of_le (project_mono h tail) .left he

theorem periodic_right (a b : Tree d) (root tail : List (Fin d))
    (h : a ≤ project b root) (hp : tail <+: root ++ tail) : Safe .right a b tail := by
  apply (safe_iff_project .right a b tail).mpr
  intro ht
  have he := project_absorbing (Or.inl rfl) hp ht
  rw [project_append] at he
  exact rootSafe_of_le (project_mono h tail) .right he

end NSSE.FiniteSubtypeProjection
