import NSSE.Polarity

/-!
# Polarity, instantiated to the live-system templates  [v103]

Concrete literal templates of the live-unsafety systems (notes v95):
plain φ-literals, the three spine-family skeletons (T, F, G; children
determined by the node), and the three coupling encodings
(T_ε ≤ x, F_ε ≤ y, y ≤ G_ε per [NP03] §3.2). We prove `TemplatesOK`
for this system, so the abstract polarity theorem applies:
**Lemma 5 of the frontier theory is now Lean-proved end-to-end.**

No `sorry`; no imports beyond `NSSE.Polarity`.
-/

namespace NSSE.PolarityInstance

open NSSE.Polarity NSSE.Polarity.Class

inductive Fam | T | F | G
deriving DecidableEq

inductive V (P : Type) where
  | pl (p : P)
  | node (f : Fam) (π : List Bool)
deriving DecidableEq

open V Fam

variable {P : Type} [DecidableEq P]

def side : V P → Class
  | .pl _ => plain
  | .node .T _ => leftish
  | .node .F _ => leftish
  | .node .G _ => rightish

set_option linter.unusedSectionVars false

/-- Lower literals f(a₁,a₂) ≤ a of the live system. Parameters: the
    coupling variables (plains) and φ's own lower literals. -/
inductive FLE (x y u₁ z₁ u₂ z₂ u₃ z₃ : P)
    (PhiF : P → P → P → Prop) : V P → V P → V P → Prop where
  | phi {a b c : P} : PhiF a b c → FLE x y u₁ z₁ u₂ z₂ u₃ z₃ PhiF (pl a) (pl b) (pl c)
  | skelT (π : List Bool) :
      FLE x y u₁ z₁ u₂ z₂ u₃ z₃ PhiF (node .T (π ++ [false])) (node .T (π ++ [true])) (node .T π)
  | skelF (π : List Bool) :
      FLE x y u₁ z₁ u₂ z₂ u₃ z₃ PhiF (node .F (π ++ [false])) (node .F (π ++ [true])) (node .F π)
  | skelG (π : List Bool) :
      FLE x y u₁ z₁ u₂ z₂ u₃ z₃ PhiF (node .G (π ++ [false])) (node .G (π ++ [true])) (node .G π)
  | coup1 : FLE x y u₁ z₁ u₂ z₂ u₃ z₃ PhiF (node .T []) (pl u₁) (pl z₁)
  | coup2 : FLE x y u₁ z₁ u₂ z₂ u₃ z₃ PhiF (node .F []) (pl u₂) (pl z₂)
  | coup3 : FLE x y u₁ z₁ u₂ z₂ u₃ z₃ PhiF (pl y) (pl u₃) (pl z₃)

/-- Upper literals b ≤ f(b₁,b₂) of the live system. -/
inductive LEF (x y u₁ z₁ u₂ z₂ u₃ z₃ : P)
    (PhiL : P → P → P → Prop) : V P → V P → V P → Prop where
  | phi {a b c : P} : PhiL a b c → LEF x y u₁ z₁ u₂ z₂ u₃ z₃ PhiL (pl a) (pl b) (pl c)
  | skelT (π : List Bool) :
      LEF x y u₁ z₁ u₂ z₂ u₃ z₃ PhiL (node .T π) (node .T (π ++ [false])) (node .T (π ++ [true]))
  | skelF (π : List Bool) :
      LEF x y u₁ z₁ u₂ z₂ u₃ z₃ PhiL (node .F π) (node .F (π ++ [false])) (node .F (π ++ [true]))
  | skelG (π : List Bool) :
      LEF x y u₁ z₁ u₂ z₂ u₃ z₃ PhiL (node .G π) (node .G (π ++ [false])) (node .G (π ++ [true]))
  | coup1 : LEF x y u₁ z₁ u₂ z₂ u₃ z₃ PhiL (pl z₁) (pl x) (pl u₁)
  | coup2 : LEF x y u₁ z₁ u₂ z₂ u₃ z₃ PhiL (pl z₂) (pl y) (pl u₂)
  | coup3 : LEF x y u₁ z₁ u₂ z₂ u₃ z₃ PhiL (pl z₃) (node .G []) (pl u₃)

-- class facts
theorem leftOK_pl (p : P) : leftOK (side (P := P)) (pl p) := Or.inl rfl
theorem leftOK_T (π) : leftOK (side (P := P)) (node .T π) := Or.inr rfl
theorem leftOK_F (π) : leftOK (side (P := P)) (node .F π) := Or.inr rfl
theorem rightOK_pl (p : P) : rightOK (side (P := P)) (pl p) := Or.inl rfl
theorem rightOK_G (π) : rightOK (side (P := P)) (node .G π) := Or.inr rfl

/-- Shorthand: a pair with good classes is PolOK. -/
theorem polOK_of (s t : V P) (hs : leftOK (side (P := P)) s)
    (ht : rightOK (side (P := P)) t) : PolOK side s t := Or.inl ⟨hs, ht⟩

set_option maxHeartbeats 800000 in
/-- The concrete templates satisfy `TemplatesOK`. -/
theorem templates_ok (x y u₁ z₁ u₂ z₂ u₃ z₃ : P)
    (PhiF PhiL : P → P → P → Prop) :
    TemplatesOK (FLE x y u₁ z₁ u₂ z₂ u₃ z₃ PhiF)
                (LEF x y u₁ z₁ u₂ z₂ u₃ z₃ PhiL) side := by
  intro a₁ a₂ a b b₁ b₂ hf hl hpol
  cases hf with
  | phi hp =>
    -- FLE kids plain: left components fine; right components:
    cases hl with
    | skelT κ =>
      -- premise (pl _, node T κ): rightOK fails and not equal → False
      cases hpol with
      | inl h =>
        cases h.2 with
        | inl hc => cases hc
        | inr hc => cases hc
      | inr h => cases h
    | skelF κ =>
      cases hpol with
      | inl h =>
        cases h.2 with
        | inl hc => cases hc
        | inr hc => cases hc
      | inr h => cases h
    | phi _ => exact ⟨polOK_of _ _ (leftOK_pl _) (rightOK_pl _),
                      polOK_of _ _ (leftOK_pl _) (rightOK_pl _)⟩
    | skelG κ => exact ⟨polOK_of _ _ (leftOK_pl _) (rightOK_G _),
                        polOK_of _ _ (leftOK_pl _) (rightOK_G _)⟩
    | coup1 => exact ⟨polOK_of _ _ (leftOK_pl _) (rightOK_pl _),
                      polOK_of _ _ (leftOK_pl _) (rightOK_pl _)⟩
    | coup2 => exact ⟨polOK_of _ _ (leftOK_pl _) (rightOK_pl _),
                      polOK_of _ _ (leftOK_pl _) (rightOK_pl _)⟩
    | coup3 => exact ⟨polOK_of _ _ (leftOK_pl _) (rightOK_G _),
                      polOK_of _ _ (leftOK_pl _) (rightOK_pl _)⟩
  | skelT π =>
    cases hl with
    | skelT κ =>
      -- premise (node T π, node T κ): needs equality → π = κ
      cases hpol with
      | inl h =>
        cases h.2 with
        | inl hc => cases hc
        | inr hc => cases hc
      | inr h =>
        cases h
        exact ⟨Or.inr rfl, Or.inr rfl⟩
    | skelF κ =>
      cases hpol with
      | inl h =>
        cases h.2 with
        | inl hc => cases hc
        | inr hc => cases hc
      | inr h => cases h
    | phi _ => exact ⟨polOK_of _ _ (leftOK_T _) (rightOK_pl _),
                      polOK_of _ _ (leftOK_T _) (rightOK_pl _)⟩
    | skelG κ => exact ⟨polOK_of _ _ (leftOK_T _) (rightOK_G _),
                        polOK_of _ _ (leftOK_T _) (rightOK_G _)⟩
    | coup1 => exact ⟨polOK_of _ _ (leftOK_T _) (rightOK_pl _),
                      polOK_of _ _ (leftOK_T _) (rightOK_pl _)⟩
    | coup2 => exact ⟨polOK_of _ _ (leftOK_T _) (rightOK_pl _),
                      polOK_of _ _ (leftOK_T _) (rightOK_pl _)⟩
    | coup3 => exact ⟨polOK_of _ _ (leftOK_T _) (rightOK_G _),
                      polOK_of _ _ (leftOK_T _) (rightOK_pl _)⟩
  | skelF π =>
    cases hl with
    | skelT κ =>
      cases hpol with
      | inl h =>
        cases h.2 with
        | inl hc => cases hc
        | inr hc => cases hc
      | inr h => cases h
    | skelF κ =>
      cases hpol with
      | inl h =>
        cases h.2 with
        | inl hc => cases hc
        | inr hc => cases hc
      | inr h =>
        cases h
        exact ⟨Or.inr rfl, Or.inr rfl⟩
    | phi _ => exact ⟨polOK_of _ _ (leftOK_F _) (rightOK_pl _),
                      polOK_of _ _ (leftOK_F _) (rightOK_pl _)⟩
    | skelG κ => exact ⟨polOK_of _ _ (leftOK_F _) (rightOK_G _),
                        polOK_of _ _ (leftOK_F _) (rightOK_G _)⟩
    | coup1 => exact ⟨polOK_of _ _ (leftOK_F _) (rightOK_pl _),
                      polOK_of _ _ (leftOK_F _) (rightOK_pl _)⟩
    | coup2 => exact ⟨polOK_of _ _ (leftOK_F _) (rightOK_pl _),
                      polOK_of _ _ (leftOK_F _) (rightOK_pl _)⟩
    | coup3 => exact ⟨polOK_of _ _ (leftOK_F _) (rightOK_G _),
                      polOK_of _ _ (leftOK_F _) (rightOK_pl _)⟩
  | skelG π =>
    -- FLE head node G π: leftOK fails → premise must be equality
    cases hpol with
    | inl h =>
      cases h.1 with
      | inl hc => cases hc
      | inr hc => cases hc
    | inr h =>
      -- b = node G π; the only LEF with a G-node head is skelG π
      cases hl with
      | phi _ => cases h
      | skelT κ => cases h
      | skelF κ => cases h
      | skelG κ =>
        cases h
        exact ⟨Or.inr rfl, Or.inr rfl⟩
      | coup1 => cases h
      | coup2 => cases h
      | coup3 => cases h
  | coup1 =>
    cases hl with
    | skelT κ =>
      cases hpol with
      | inl h =>
        cases h.2 with
        | inl hc => cases hc
        | inr hc => cases hc
      | inr h => cases h
    | skelF κ =>
      cases hpol with
      | inl h =>
        cases h.2 with
        | inl hc => cases hc
        | inr hc => cases hc
      | inr h => cases h
    | phi _ => exact ⟨polOK_of _ _ (leftOK_T _) (rightOK_pl _),
                      polOK_of _ _ (leftOK_pl _) (rightOK_pl _)⟩
    | skelG κ => exact ⟨polOK_of _ _ (leftOK_T _) (rightOK_G _),
                        polOK_of _ _ (leftOK_pl _) (rightOK_G _)⟩
    | coup1 => exact ⟨polOK_of _ _ (leftOK_T _) (rightOK_pl _),
                      polOK_of _ _ (leftOK_pl _) (rightOK_pl _)⟩
    | coup2 => exact ⟨polOK_of _ _ (leftOK_T _) (rightOK_pl _),
                      polOK_of _ _ (leftOK_pl _) (rightOK_pl _)⟩
    | coup3 => exact ⟨polOK_of _ _ (leftOK_T _) (rightOK_G _),
                      polOK_of _ _ (leftOK_pl _) (rightOK_pl _)⟩
  | coup2 =>
    cases hl with
    | skelT κ =>
      cases hpol with
      | inl h =>
        cases h.2 with
        | inl hc => cases hc
        | inr hc => cases hc
      | inr h => cases h
    | skelF κ =>
      cases hpol with
      | inl h =>
        cases h.2 with
        | inl hc => cases hc
        | inr hc => cases hc
      | inr h => cases h
    | phi _ => exact ⟨polOK_of _ _ (leftOK_F _) (rightOK_pl _),
                      polOK_of _ _ (leftOK_pl _) (rightOK_pl _)⟩
    | skelG κ => exact ⟨polOK_of _ _ (leftOK_F _) (rightOK_G _),
                        polOK_of _ _ (leftOK_pl _) (rightOK_G _)⟩
    | coup1 => exact ⟨polOK_of _ _ (leftOK_F _) (rightOK_pl _),
                      polOK_of _ _ (leftOK_pl _) (rightOK_pl _)⟩
    | coup2 => exact ⟨polOK_of _ _ (leftOK_F _) (rightOK_pl _),
                      polOK_of _ _ (leftOK_pl _) (rightOK_pl _)⟩
    | coup3 => exact ⟨polOK_of _ _ (leftOK_F _) (rightOK_G _),
                      polOK_of _ _ (leftOK_pl _) (rightOK_pl _)⟩
  | coup3 =>
    cases hl with
    | skelT κ =>
      cases hpol with
      | inl h =>
        cases h.2 with
        | inl hc => cases hc
        | inr hc => cases hc
      | inr h => cases h
    | skelF κ =>
      cases hpol with
      | inl h =>
        cases h.2 with
        | inl hc => cases hc
        | inr hc => cases hc
      | inr h => cases h
    | phi _ => exact ⟨polOK_of _ _ (leftOK_pl _) (rightOK_pl _),
                      polOK_of _ _ (leftOK_pl _) (rightOK_pl _)⟩
    | skelG κ => exact ⟨polOK_of _ _ (leftOK_pl _) (rightOK_G _),
                        polOK_of _ _ (leftOK_pl _) (rightOK_G _)⟩
    | coup1 => exact ⟨polOK_of _ _ (leftOK_pl _) (rightOK_pl _),
                      polOK_of _ _ (leftOK_pl _) (rightOK_pl _)⟩
    | coup2 => exact ⟨polOK_of _ _ (leftOK_pl _) (rightOK_pl _),
                      polOK_of _ _ (leftOK_pl _) (rightOK_pl _)⟩
    | coup3 => exact ⟨polOK_of _ _ (leftOK_pl _) (rightOK_G _),
                      polOK_of _ _ (leftOK_pl _) (rightOK_pl _)⟩

/-- **Lemma 5, end-to-end in Lean**: polarity of the support relation
    of the live-system templates. -/
theorem polarity_live (x y u₁ z₁ u₂ z₂ u₃ z₃ : P)
    (PhiF PhiL : P → P → P → Prop) :
    ∀ s t, Supp (FLE x y u₁ z₁ u₂ z₂ u₃ z₃ PhiF)
                (LEF x y u₁ z₁ u₂ z₂ u₃ z₃ PhiL) s t →
      PolOK side s t :=
  polarity _ _ side (templates_ok x y u₁ z₁ u₂ z₂ u₃ z₃ PhiF PhiL)

end NSSE.PolarityInstance
