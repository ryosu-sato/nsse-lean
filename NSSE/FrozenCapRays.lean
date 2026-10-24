import NSSE.Cap
import Mathlib.Data.List.Infix
import Mathlib.Data.Fintype.Prod

/-!
# Cap witnesses freeze inside a prefix outside the regular part

The statements use the original outer-prefix cap semantics. Every covering
anchor and root of an extension is fixed by a pair of cuts inside the
excluded prefix. No arbitrary SOA right-end guard is introduced.
-/

namespace NSSE.FrozenCapRays

universe u
variable {α : Type u}

/-- Prefixes of a fixed anchored periodic ray, phrased using finite powers. -/
def Ray (anchor root w : List α) : Prop :=
  ∃ k : Nat, w <+: anchor ++ Language.wordPower root k

def RegularPart (c : CapComponent α) (w : List α) : Prop :=
  PrefixRoute c w ∨ SplitRoute c w

def regularCovered (E : CapExpression α) (w : List α) : Prop :=
  ∃ c ∈ E.caps, RegularPart c w

theorem prefixClosure_of_prefix {L : Language α} {x y : List α}
    (hxy : x <+: y) (hy : L y) : Language.prefixClosure L x := by
  obtain ⟨tail, htail⟩ := hxy
  exact ⟨tail, by rwa [htail]⟩

theorem prefixClosure_prefix {L : Language α} {x y : List α}
    (hxy : x <+: y) (hy : Language.prefixClosure L y) :
    Language.prefixClosure L x := by
  obtain ⟨tail, htail⟩ := hy
  exact prefixClosure_of_prefix (hxy.trans (List.prefix_append y tail)) htail

theorem take_eq_of_prefix {x y : List α} (hxy : x <+: y)
    {j : Nat} (hj : j ≤ x.length) : x.take j = y.take j := by
  have h := congrArg (List.take j) (List.prefix_iff_eq_take.mp hxy)
  simpa only [List.take_take, Nat.min_eq_left hj] using h

theorem regularPart_prefix (c : CapComponent α) {x y : List α}
    (hxy : x <+: y) (hy : RegularPart c y) : RegularPart c x := by
  rcases hy with hp | ⟨j, hj, hleft, hright⟩
  · exact Or.inl (prefixClosure_prefix hxy hp)
  · by_cases hxj : x.length ≤ j
    · exact Or.inl (prefixClosure_of_prefix
        (List.prefix_take_iff.mpr ⟨hxy, hxj⟩) hleft)
    · have hjx : j ≤ x.length := by omega
      exact Or.inr ⟨j, hjx, by rwa [take_eq_of_prefix hxy hjx],
        prefixClosure_prefix (hxy.drop j) hright⟩

theorem regularCovered_prefix (E : CapExpression α) {x y : List α}
    (hxy : x <+: y) (hy : regularCovered E y) : regularCovered E x := by
  obtain ⟨c, hc, hreg⟩ := hy
  exact ⟨c, hc, regularPart_prefix c hxy hreg⟩

theorem regularCovered_le_capCovered (E : CapExpression α)
    (hne : ∀ c ∈ E.caps, ∃ root, c.right root) (w : List α)
    (hw : regularCovered E w) : capCovered E w := by
  obtain ⟨c, hc, hreg⟩ := hw
  refine ⟨c, hc, ?_⟩
  rcases hreg with hp | hs
  · exact prefixRoute_capComponentCovers c w (hne c hc) hp
  · exact splitRoute_capComponentCovers c w hs

theorem ray_prefix {anchor root x y : List α} (hxy : x <+: y)
    (hy : Ray anchor root y) : Ray anchor root x := by
  obtain ⟨k, hk⟩ := hy
  exact ⟨k, hxy.trans hk⟩

/-- Exact reformulation of outer-prefix cap semantics, without nonempty-root
preprocessing or a positive-length hypothesis. -/
theorem capComponentCovers_iff_ray (c : CapComponent α) (w : List α) :
    capComponentCovers c w ↔
      ∃ anchor root, c.left anchor ∧ c.right root ∧ Ray anchor root w := by
  constructor
  · rintro ⟨outer, anchor, sigma, hword, hleft, root, k, rest, hright, hpower⟩
    refine ⟨anchor, root, hleft, hright, k, outer ++ rest, ?_⟩
    rw [hpower]
    simpa only [List.append_assoc] using congrArg (fun z => z ++ rest) hword
  · rintro ⟨anchor, root, hleft, hright, k, tail, hword⟩
    exact ⟨tail, anchor, Language.wordPower root k, hword, hleft,
      root, k, [], hright, by simp⟩

/-- EVERY accepted anchor/root ray covering an excluded prefix has its
positive root entirely before the end of that prefix, with literal contents fixed. -/
theorem freeze_ray (c : CapComponent α) (x anchor root : List α)
    (hout : ¬ RegularPart c x) (hleft : c.left anchor) (hright : c.right root)
    (hray : Ray anchor root x) :
    0 < root.length ∧ anchor.length + root.length < x.length ∧
      x.take anchor.length = anchor ∧ Word.factor x anchor.length root.length = root := by
  obtain ⟨k, hx⟩ := hray
  have hal : anchor.length < x.length := by
    by_contra hnot
    have hxa : x <+: anchor :=
      (List.isPrefix_append_of_length (by omega)).mp hx
    exact hout (Or.inl (prefixClosure_of_prefix hxa hleft))
  have hatake : x.take anchor.length = anchor := by
    simpa using take_eq_of_prefix hx hal.le
  cases k with
  | zero =>
      have hlen := hx.length_le
      simp [Language.wordPower] at hlen
      omega
  | succ k =>
      have hdrop : x.drop anchor.length <+: root ++ Language.wordPower root k := by
        simpa [Language.wordPower_succ] using hx.drop anchor.length
      have hpos : 0 < root.length := by
        by_contra hn
        have hnil : root = [] := List.length_eq_zero_iff.mp (by omega)
        have hlen := hdrop.length_le
        simp [hnil, Language.wordPower] at hlen
        omega
      have hend : anchor.length + root.length < x.length := by
        by_contra hn
        have hprefix : x.drop anchor.length <+: root :=
          (List.isPrefix_append_of_length (by simp only [List.length_drop]; omega)).mp hdrop
        apply hout
        exact Or.inr ⟨anchor.length, hal.le, by simpa only [hatake] using hleft,
          prefixClosure_of_prefix hprefix hright⟩
      refine ⟨hpos, hend, hatake, ?_⟩
      have hlen : root.length ≤ (x.drop anchor.length).length := by
        simp only [List.length_drop]
        omega
      simpa [Word.factor] using take_eq_of_prefix hdrop hlen

/-- Indices are literal cut pairs, not component/run identifiers. -/
abbrev Index (x : List α) := Fin x.length × Fin x.length

def anchorAt (x : List α) (i : Index x) : List α := x.take i.1.val

def rootAt (x : List α) (i : Index x) : List α := Word.factor x i.1.val i.2.val

def Enabled (E : CapExpression α) (x : List α) (i : Index x) : Prop :=
  0 < i.2.val ∧ i.1.val + i.2.val < x.length ∧
    (∃ c ∈ E.caps, c.left (anchorAt x i) ∧ c.right (rootAt x i)) ∧
    Ray (anchorAt x i) (rootAt x i) x

theorem card_index (x : List α) : Fintype.card (Index x) = x.length * x.length := by
  simp [Index]

/-- All cap coverage on the entire extension cone is exactly this FIXED
finite family of rays. Empty root languages need not be removed for this theorem. -/
theorem covered_extension_iff (E : CapExpression α) (x y : List α)
    (hout : ¬ regularCovered E x) (hxy : x <+: y) :
    capCovered E y ↔ ∃ i : Index x, Enabled E x i ∧ Ray (anchorAt x i) (rootAt x i) y := by
  constructor
  · rintro ⟨c, hc, hcover⟩
    obtain ⟨anchor, root, hleft, hright, hray⟩ := (capComponentCovers_iff_ray c y).mp hcover
    have hxray := ray_prefix hxy hray
    have hcout : ¬ RegularPart c x := fun h => hout ⟨c, hc, h⟩
    obtain ⟨hpos, hend, hatake, hroot⟩ := freeze_ray c x anchor root hcout hleft hright hxray
    let i : Index x := ⟨⟨anchor.length, by omega⟩, ⟨root.length, by omega⟩⟩
    have ha : anchorAt x i = anchor := hatake
    have hr : rootAt x i = root := hroot
    refine ⟨i, ?_, ?_⟩
    · exact ⟨hpos, hend, ⟨c, hc, by rwa [ha], by rwa [hr]⟩, by rwa [ha, hr]⟩
    · rwa [ha, hr]
  · rintro ⟨i, ⟨_, _, ⟨c, hc, hleft, hright⟩, _⟩, hray⟩
    exact ⟨c, hc, (capComponentCovers_iff_ray c y).mpr
      ⟨anchorAt x i, rootAt x i, hleft, hright, hray⟩⟩

theorem enabled_root_length (E : CapExpression α) (x : List α) (i : Index x)
    (hi : Enabled E x i) : (rootAt x i).length = i.2.val := by
  have hend := hi.2.1
  simp only [rootAt, Word.factor_length]
  exact Nat.min_eq_left (by omega)

theorem enabled_root_ne_nil (E : CapExpression α) (x : List α) (i : Index x)
    (hi : Enabled E x i) : rootAt x i ≠ [] := by
  apply List.length_pos_iff.mp
  rw [enabled_root_length E x i hi]
  exact hi.1

end NSSE.FrozenCapRays
