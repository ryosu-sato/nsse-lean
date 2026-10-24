import NSSE.SymbolicProjection
import NSSE.SymbolicPreimage
import NSSE.SymbolicControl
import NSSE.CanonicalConvolution
import Mathlib.Data.List.NodupEquivFin

/-!
# Explicit finite shape coding of padded columns

Presence masks are numbered by a proved complete, duplicate-free Boolean
enumeration. Present coordinates are explicitly listed. The resulting
sparse symbolic columns are in executable bijection with dense columns.
-/

namespace NSSE.ConvolutionShapes

open SymbolicAutomata

universe u v w
variable {D : Type u} {k l : Nat}

abbrev Mask (k : Nat) := Fin k → Bool

theorem tail_of_mem_pair (s : Mask k) (x : Mask (k + 1))
    (hx : x ∈ [Fin.cons false s, Fin.cons true s]) : Fin.tail x = s := by
  rcases List.mem_cons.mp hx with rfl | hx
  · simp
  · have hx' := List.mem_singleton.mp hx
    subst x
    simp

theorem masks_nodup (k : Nat) : (SymbolicComplement.masks k).Nodup := by
  induction k with
  | zero => simp [SymbolicComplement.masks]
  | succ k ih =>
      rw [SymbolicComplement.masks, List.nodup_flatMap]
      refine ⟨?_, ih.imp ?_⟩
      · intro s _
        simp
      · intro s t hst x hx ht
        exact hst ((tail_of_mem_pair s x hx).symm.trans (tail_of_mem_pair t x ht))

abbrev Shape (k : Nat) := Fin (SymbolicComplement.masks k).length

def maskEquiv (k : Nat) : Shape k ≃ Mask k :=
  List.Nodup.getEquivOfForallMemList (SymbolicComplement.masks k) (masks_nodup k)
    (SymbolicComplement.mem_masks k)

def mask (s : Shape k) : Mask k := maskEquiv k s
def code (a : Mask k) : Shape k := (maskEquiv k).symm a

@[simp] theorem mask_code (a : Mask k) : mask (code a) = a := (maskEquiv k).apply_symm_apply a
@[simp] theorem code_mask (s : Shape k) : code (mask s) = s := (maskEquiv k).symm_apply_apply s

def tapes (a : Mask k) : List (Fin k) := (List.finRange k).filter a

@[simp] theorem mem_tapes (a : Mask k) (i : Fin k) : i ∈ tapes a ↔ a i = true := by
  simp [tapes]

theorem tapes_nodup (a : Mask k) : (tapes a).Nodup :=
  (List.nodup_finRange k).filter a

def positionEquiv (a : Mask k) : Fin (tapes a).length ≃ {i // i ∈ tapes a} :=
  List.Nodup.getEquiv (tapes a) (tapes_nodup a)

def tape (a : Mask k) (j : Fin (tapes a).length) : Fin k := (positionEquiv a j).val

theorem tape_present (a : Mask k) (j : Fin (tapes a).length) : a (tape a j) = true :=
  (mem_tapes a _).mp (positionEquiv a j).property

def slot (a : Mask k) (i : Fin k) (hi : a i = true) : Fin (tapes a).length :=
  (positionEquiv a).symm ⟨i, (mem_tapes a i).mpr hi⟩

@[simp] theorem tape_slot (a : Mask k) (i : Fin k) (hi : a i = true) :
    tape a (slot a i hi) = i :=
  congrArg Subtype.val ((positionEquiv a).apply_symm_apply _)

@[simp] theorem slot_tape (a : Mask k) (j : Fin (tapes a).length)
    (hj : a (tape a j) = true) : slot a (tape a j) hj = j := by
  exact (positionEquiv a).symm_apply_apply j

def expand (a : Mask k) (xs : Fin (tapes a).length → D) : CanonicalConvolution.Column D k :=
  fun i => if hi : a i = true then some (xs (slot a i hi)) else none

@[simp] theorem active_expand (a : Mask k) (xs : Fin (tapes a).length → D) :
    CanonicalConvolution.active (expand a xs) = a := by
  funext i
  cases hi : a i <;> simp [CanonicalConvolution.active, expand, hi]

@[simp] theorem expand_tape (a : Mask k) (xs : Fin (tapes a).length → D)
    (j : Fin (tapes a).length) : expand a xs (tape a j) = some (xs j) := by
  simp [expand, tape_present]

def valuesOf (a : Mask k) (c : CanonicalConvolution.Column D k)
    (hc : CanonicalConvolution.active c = a) (j : Fin (tapes a).length) : D :=
  (c (tape a j)).get (by
    change CanonicalConvolution.active c (tape a j) = true
    rw [hc]
    exact tape_present a j)

theorem expand_valuesOf (a : Mask k) (c : CanonicalConvolution.Column D k)
    (hc : CanonicalConvolution.active c = a) : expand a (valuesOf a c hc) = c := by
  funext i
  by_cases hi : a i = true
  · simp only [expand, dif_pos hi, valuesOf, tape_slot]
    exact Option.some_get _
  · have hn : c i = none := by
      cases hci : c i with
      | none => rfl
      | some x =>
          have h := congrFun hc i
          exact (hi (by simpa [CanonicalConvolution.active, hci] using h.symm)).elim
    simp [expand, hi, hn]

theorem expand_injective (a : Mask k) :
    Function.Injective (expand a : (Fin (tapes a).length → D) → _) := by
  intro xs ys he
  funext j
  have h := congrFun he (tape a j)
  simpa using h

def arity (k : Nat) (s : Shape k) : Nat := (tapes (mask s)).length

abbrev Sparse (D : Type u) (k : Nat) := SymbolicAutomata.Column D (arity k)

def toDense (c : Sparse D k) : CanonicalConvolution.Column D k := expand (mask c.1) c.2

@[simp] theorem active_toDense (c : Sparse D k) :
    CanonicalConvolution.active (toDense c) = mask c.1 := active_expand _ _

def fromDense (c : CanonicalConvolution.Column D k) : Sparse D k :=
  ⟨code (CanonicalConvolution.active c),
    valuesOf _ c (mask_code _).symm⟩

@[simp] theorem toDense_fromDense (c : CanonicalConvolution.Column D k) :
    toDense (fromDense c) = c := expand_valuesOf _ c (mask_code _).symm

theorem toDense_injective : Function.Injective (toDense : Sparse D k → _) := by
  rintro ⟨s, xs⟩ ⟨t, ys⟩ he
  have hm : mask s = mask t := by
    simpa using congrArg CanonicalConvolution.active he
  have hst : s = t := (maskEquiv k).injective hm
  subst t
  have hxy : xs = ys := expand_injective (mask s) he
  subst ys
  rfl

@[simp] theorem fromDense_toDense (c : Sparse D k) : fromDense (toDense c) = c :=
  toDense_injective (toDense_fromDense _)

def columnEquiv (D : Type u) (k : Nat) : Sparse D k ≃ CanonicalConvolution.Column D k where
  toFun := toDense
  invFun := fromDense
  left_inv := fromDense_toDense
  right_inv := toDense_fromDense

/-- Coordinate selection between any two masks related by a tape map. -/
def pick (a : Mask k) (b : Mask l) (f : Fin l → Fin k) (hb : b = a ∘ f)
    (j : Fin (tapes b).length) : Fin (tapes a).length :=
  slot a (f (tape b j)) (by simpa only [hb, Function.comp_apply] using tape_present b j)

theorem expand_pick (a : Mask k) (b : Mask l) (f : Fin l → Fin k) (hb : b = a ∘ f)
    (xs : Fin (tapes a).length → D) :
    expand b (xs ∘ pick a b f hb) = expand a xs ∘ f := by
  funext i
  by_cases hi : b i = true
  · have ha : a (f i) = true := by simpa only [hb, Function.comp_apply] using hi
    simp only [expand, dif_pos hi, Function.comp_apply, pick, tape_slot, dif_pos ha]
  · have ha : ¬ a (f i) = true := by simpa only [hb, Function.comp_apply] using hi
    simp [expand, hi, ha]

def maskPresent (a : Mask k) : Bool := (List.finRange k).any a

@[simp] theorem present_toDense (c : Sparse D k) :
    CanonicalConvolution.present (toDense c) = maskPresent (mask c.1) := by
  simp only [CanonicalConvolution.present, active_toDense, maskPresent]

def plan (f : Fin l → Fin k) : SymbolicProjection.Plan (arity k) (arity l) :=
  fun s => if maskPresent (mask s ∘ f) then
    .keep (code (mask s ∘ f)) (pick (mask s) _ f (mask_code _)) else .erase

theorem plan_toDense (f : Fin l → Fin k) (c : Sparse D k) :
    (SymbolicProjection.mapColumn (plan f) c).map toDense =
      CanonicalConvolution.projectColumn f (toDense c) := by
  have hp : CanonicalConvolution.present (toDense c ∘ f) = maskPresent (mask c.1 ∘ f) := by
    unfold CanonicalConvolution.present maskPresent
    congr 1
    funext i
    exact congrFun (active_toDense c) (f i)
  by_cases h : maskPresent (mask c.1 ∘ f) = true
  · simp only [SymbolicProjection.mapColumn, plan, if_pos h, SymbolicProjection.Action.map,
      Option.map_some, CanonicalConvolution.projectColumn, hp, if_pos h]
    apply congrArg some
    exact expand_pick _ _ f (mask_code _) c.2
  · simp [SymbolicProjection.mapColumn, plan, h, SymbolicProjection.Action.map,
      CanonicalConvolution.projectColumn, hp]

theorem project_toDense (f : Fin l → Fin k) (w : List (Sparse D k)) :
    (w.filterMap (SymbolicProjection.mapColumn (plan f))).map toDense =
      CanonicalConvolution.project f (w.map toDense) := by
  simp only [List.map_filterMap, CanonicalConvolution.project, List.filterMap_map]
  congr 1
  funext c
  exact plan_toDense f c

theorem map_toDense_injective : Function.Injective (List.map (toDense : Sparse D k → _)) := by
  intro v w he
  have h := congrArg (List.map fromDense) he
  simpa [List.map_map, Function.comp_def] using h

def allowed (a b : Mask k) : Bool :=
  maskPresent b && decide (∀ i, b i = true → a i = true)

def paddingControl (k : Nat) :
    SymbolicControl.Control (Option (Mask k)) (SymbolicComplement.masks k).length where
  states := SymbolicComplement.states k
  complete := SymbolicComplement.mem_states k
  start := some (fun _ => true)
  step S s := match S with
    | none => none
    | some a => if allowed a (mask s) then some (mask s) else none
  final := Option.isSome

theorem allowed_toDense (a : Mask k) (c : Sparse D k) :
    CanonicalConvolution.stepAllowed a (toDense c) = allowed a (mask c.1) := by
  simp only [CanonicalConvolution.stepAllowed, present_toDense, active_toDense, allowed]

theorem control_step_toDense (S : Option (Mask k)) (c : Sparse D k) :
    ((paddingControl k).toDFA D).step S c =
      (CanonicalConvolution.monitor D k).step S (toDense c) := by
  cases S <;> simp only [paddingControl, SymbolicControl.Control.toDFA,
    CanonicalConvolution.monitor, allowed_toDense, active_toDense]

theorem control_run_toDense (S : Option (Mask k)) (w : List (Sparse D k)) :
    ((paddingControl k).toDFA D).runFrom S w =
      (CanonicalConvolution.monitor D k).runFrom S (w.map toDense) := by
  induction w generalizing S with
  | nil => rfl
  | cons c w ih =>
      simp only [List.map_cons, NSSE.DFA.runFrom_cons]
      rw [← control_step_toDense]
      exact ih _

theorem paddingControl_correct (w : List (Sparse D k)) :
    ((paddingControl k).toDFA D).Accepts w ↔ CanonicalConvolution.Canonical (w.map toDense) := by
  rw [← CanonicalConvolution.monitor_correct]
  change (((paddingControl k).toDFA D).runFrom (some (fun _ => true)) w).isSome = true ↔ _
  rw [control_run_toDense]
  rfl

open FirstOrder FirstOrder.Language
variable {L : FirstOrder.Language.{v, w}} {P : Type*} {n : Nat}

abbrev WordAutomaton (L : FirstOrder.Language.{v, w}) (P : Type*) (n k : Nat) :=
  Automaton L P n (SymbolicComplement.masks k).length (arity k)

def enforcePadding (A : WordAutomaton L P n k) :
    WordAutomaton L P ((paddingControl k).pairs n).length k :=
  SymbolicControl.compile A (paddingControl k)

theorem enforcePadding_correct (A : WordAutomaton L P n k) [L.Structure D]
    (p : P → D) (w : List (Sparse D k)) :
    (enforcePadding A).Accepts p w ↔
      A.Accepts p w ∧ CanonicalConvolution.Canonical (w.map toDense) := by
  rw [enforcePadding, SymbolicControl.compile_correct, paddingControl_correct]

def denseAccepts (A : WordAutomaton L P n k) [L.Structure D]
    (p : P → D) (w : List (CanonicalConvolution.Column D k)) : Prop :=
  A.Accepts p (w.map fromDense)

def tupleAccepts (A : WordAutomaton L P n k) [L.Structure D]
    (p : P → D) (t : CanonicalConvolution.Tuple D k) : Prop :=
  denseAccepts A p (CanonicalConvolution.encode t)

theorem enforcePadding_tuple (A : WordAutomaton L P n k) [L.Structure D]
    (p : P → D) (t : CanonicalConvolution.Tuple D k) :
    tupleAccepts (enforcePadding A) p t ↔ tupleAccepts A p t := by
  unfold tupleAccepts denseAccepts
  rw [enforcePadding_correct]
  simp [List.map_map, Function.comp_def, CanonicalConvolution.canonical_encode]

/-- Existential selection of entire WORDS, with padding enforced in the actual compiler. -/
def projectWords (f : Fin l → Fin k) (A : WordAutomaton L P n k) :
    WordAutomaton L P ((paddingControl k).pairs n).length l :=
  SymbolicProjection.compile (plan f) (enforcePadding A)

theorem projectWords_correct (f : Fin l → Fin k) (A : WordAutomaton L P n k)
    [L.Structure D] (p : P → D) (t : CanonicalConvolution.Tuple D l) :
    tupleAccepts (projectWords f A) p t ↔
      ∃ s : CanonicalConvolution.Tuple D k, tupleAccepts A p s ∧ s ∘ f = t := by
  change (projectWords f A).Accepts p ((CanonicalConvolution.encode t).map fromDense) ↔ _
  rw [projectWords, SymbolicProjection.compile_correct]
  change _ ↔ ∃ s : CanonicalConvolution.Tuple D k,
    denseAccepts A p (CanonicalConvolution.encode s) ∧ s ∘ f = t
  rw [← CanonicalConvolution.tuple_image_iff (denseAccepts A p) f t]
  constructor
  · rintro ⟨v, hv, he⟩
    obtain ⟨ha, hc⟩ := (enforcePadding_correct A p v).mp hv
    refine ⟨v.map toDense, (CanonicalConvolution.monitor_correct _).mpr hc, ?_, ?_⟩
    · simpa [denseAccepts, List.map_map, Function.comp_def] using ha
    · have h := congrArg (List.map toDense) he
      rw [project_toDense] at h
      simpa [List.map_map, Function.comp_def] using h
  · rintro ⟨v, hc, ha, he⟩
    refine ⟨v.map fromDense, ?_, ?_⟩
    · apply (enforcePadding_correct A p _).mpr
      exact ⟨ha, by simpa [List.map_map, Function.comp_def] using
        (CanonicalConvolution.monitor_correct _).mp hc⟩
    · apply map_toDense_injective
      rw [project_toDense]
      simpa [List.map_map, Function.comp_def] using he

theorem projectWords_canonical (f : Fin l → Fin k) (A : WordAutomaton L P n k)
    [L.Structure D] (p : P → D) (w : List (Sparse D l))
    (hw : (projectWords f A).Accepts p w) : CanonicalConvolution.Canonical (w.map toDense) := by
  obtain ⟨v, hv, rfl⟩ := (SymbolicProjection.compile_correct (plan f) (enforcePadding A) p w).mp hw
  rw [project_toDense]
  exact CanonicalConvolution.canonical_project f ((enforcePadding_correct A p v).mp hv).2

/-- Complement is intersected with canonical padding in the syntax, not merely in a theorem premise. -/
def complementWords (A : WordAutomaton L P n k) :=
  enforcePadding (SymbolicComplement.compile A)

theorem complementWords_correct (A : WordAutomaton L P n k) [L.Structure D]
    (p : P → D) (t : CanonicalConvolution.Tuple D k) :
    tupleAccepts (complementWords A) p t ↔ ¬ tupleAccepts A p t := by
  rw [complementWords, enforcePadding_tuple]
  exact SymbolicComplement.compile_correct A p _

theorem complementWords_canonical (A : WordAutomaton L P n k) [L.Structure D]
    (p : P → D) (w : List (Sparse D k)) (hw : (complementWords A).Accepts p w) :
    CanonicalConvolution.Canonical (w.map toDense) :=
  ((enforcePadding_correct (SymbolicComplement.compile A) p w).mp hw).2

theorem project_sparse_encode (f : Fin l → Fin k) (t : CanonicalConvolution.Tuple D k) :
    ((CanonicalConvolution.encode t).map fromDense).filterMap
        (SymbolicProjection.mapColumn (plan f)) =
      (CanonicalConvolution.encode (t ∘ f)).map fromDense := by
  apply map_toDense_injective
  rw [project_toDense]
  simp [List.map_map, Function.comp_def, CanonicalConvolution.project_encode]

/-- Pull a relation back to a larger/reindexed tuple of variables. Unused
tapes may continue after all selected tapes end, and arguments may repeat. -/
def pullbackWords (f : Fin l → Fin k) (A : WordAutomaton L P n l) :=
  enforcePadding (SymbolicPreimage.compile (plan f) A)

theorem pullbackWords_correct (f : Fin l → Fin k) (A : WordAutomaton L P n l)
    [L.Structure D] (p : P → D) (t : CanonicalConvolution.Tuple D k) :
    tupleAccepts (pullbackWords f A) p t ↔ tupleAccepts A p (t ∘ f) := by
  rw [pullbackWords, enforcePadding_tuple]
  unfold tupleAccepts denseAccepts
  rw [SymbolicPreimage.compile_correct, project_sparse_encode]

theorem pullbackWords_canonical (f : Fin l → Fin k) (A : WordAutomaton L P n l)
    [L.Structure D] (p : P → D) (w : List (Sparse D k))
    (hw : (pullbackWords f A).Accepts p w) : CanonicalConvolution.Canonical (w.map toDense) :=
  ((enforcePadding_correct (SymbolicPreimage.compile (plan f) A) p w).mp hw).2

/-- Existentially quantify the first WORD variable, not one current letter. -/
def existsWord (A : WordAutomaton L P n (k + 1)) := projectWords Fin.succ A

theorem existsWord_correct (A : WordAutomaton L P n (k + 1)) [L.Structure D]
    (p : P → D) (t : CanonicalConvolution.Tuple D k) :
    tupleAccepts (existsWord A) p t ↔
      ∃ x : List D, tupleAccepts A p (Fin.cons x t) := by
  rw [existsWord, projectWords_correct]
  constructor
  · rintro ⟨s, hs, he⟩
    refine ⟨s 0, ?_⟩
    have hrec : Fin.cons (s 0) t = s := by
      rw [← he]
      exact Fin.cons_self_tail s
    rwa [hrec]
  · rintro ⟨x, hx⟩
    exact ⟨Fin.cons x t, hx, by funext i; simp⟩

def forallWord (A : WordAutomaton L P n (k + 1)) :=
  complementWords (existsWord (complementWords A))

theorem forallWord_correct (A : WordAutomaton L P n (k + 1)) [L.Structure D]
    (p : P → D) (t : CanonicalConvolution.Tuple D k) :
    tupleAccepts (forallWord A) p t ↔
      ∀ x : List D, tupleAccepts A p (Fin.cons x t) := by
  simp [forallWord, complementWords_correct, existsWord_correct]

end NSSE.ConvolutionShapes
