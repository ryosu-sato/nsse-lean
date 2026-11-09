import NSSE.MultiVarianceRawSpine

/-! Actual signed head selection from original literal lists. Each frame
uses its own sign to select the applicable old bounds. No head ordering
or semantic oracle is supplied. -/
namespace NSSE.MultiVarianceSelectorHead
open MultiConstructorConstraints (Bound Constraints)
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceSpineSuffixes
open MultiVarianceLabelBounds MultiVarianceClashCharacterization MultiVarianceLocalDecision
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

def candidates (phi : Constraints arity n) (F : Frame n) : List H :=
  (((if F.sign then phi.lower else phi.upper).filter (fun b => b.parent ∈ F.x)).map Bound.head) ++
    (((if !F.sign then phi.lower else phi.upper).filter (fun b => b.parent ∈ F.y)).map Bound.head)

def framePins (phi : Constraints arity n) (F : Frame n) : Finset H :=
  pins phi F.sign F.x ∪ pins phi (!F.sign) F.y

theorem mem_candidates (phi : Constraints arity n) (F : Frame n) (h : H) :
    h ∈ candidates phi F ↔ h ∈ framePins phi F := by
  simp only [candidates,framePins,pins,Finset.mem_union,List.mem_append,List.mem_toFinset]

def choose (phi : Constraints arity n) (F : Frame n) (fallback : H) : H :=
  match candidates phi F with
  | [] => fallback
  | h::_ => h

def Ready (phi : Constraints arity n) (F : Frame n) (h : H) : Prop :=
  Compatible phi F.sign F.x (.node h) ∧ Compatible phi (!F.sign) F.y (.node h)

def readyDecision (phi : Constraints arity n) (F : Frame n) (h : H) : Decidable (Ready phi F h) := by
  letI := compatibleDecision phi F.sign F.x (.node h)
  letI := compatibleDecision phi (!F.sign) F.y (.node h)
  unfold Ready
  infer_instance

theorem compatible_pin (phi : Constraints arity n) (r : Bool) (S : MultiVarianceModelTokens.Tokens n)
    (h k : H) (hc : Compatible phi r S (.node h)) (hp : k ∈ pins phi r S) : k=h := by
  obtain ⟨b,hb,hm,rfl⟩ := (mem_pins phi r S k).mp hp
  have hbound : LabelBound phi (!r) b.parent (.node b.head) := by
    apply Or.inl
    exact ⟨b,by cases r <;> exact hb,rfl,rfl⟩
  have hh := hc b.parent hm (.node b.head) hbound
  cases r <;> simp only [Bool.false_eq_true,if_false,if_true,MultiConstructorTrees.Label.node_le_node] at hh
  · exact hh.symm
  · exact hh

theorem ready_pins (phi : Constraints arity n) (F : Frame n) (h : H) (hr : Ready phi F h) :
    ∀ k ∈ framePins phi F, k=h := by
  intro k hk
  rcases Finset.mem_union.mp hk with hk | hk
  · exact compatible_pin phi F.sign F.x h k hr.1 hk
  · exact compatible_pin phi (!F.sign) F.y h k hr.2 hk

theorem choose_forced (phi : Constraints arity n) (F : Frame n) (fallback h : H)
    (hr : Ready phi F h) (hp : (framePins phi F).Nonempty) : choose phi F fallback=h := by
  cases he : candidates phi F with
  | nil =>
    obtain ⟨k,hk⟩ := hp
    have hm := (mem_candidates phi F k).mpr hk
    rw [he] at hm
    exact False.elim (List.not_mem_nil hm)
  | cons k ks =>
    rw [choose,he]
    exact ready_pins phi F h hr k ((mem_candidates phi F k).mp (by rw [he]; exact List.mem_cons_self))

theorem choose_unpinned (phi : Constraints arity n) (F : Frame n) (fallback : H)
    (hp : framePins phi F = ∅) : choose phi F fallback=fallback := by
  have he : candidates phi F=[] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro k hk
    have hm := (mem_candidates phi F k).mp hk
    rw [hp] at hm
    exact Finset.not_mem_empty _ hm
  rw [choose,he]

def Empty (F : Frame n) : Prop := F.x=∅ ∧ F.y=∅

def emptyDecision (F : Frame n) : Decidable (Empty F) := by unfold Empty; infer_instance

theorem empty_pins (phi : Constraints arity n) (F : Frame n) (he : Empty F) : framePins phi F=∅ := by
  simp only [framePins,he.1,he.2,pins_empty,Finset.union_empty]

omit [DecidableEq H] in
theorem empty_ready (phi : Constraints arity n) (F : Frame n) (he : Empty F) (h : H) : Ready phi F h := by
  constructor
  · intro z hz
    rw [he.1] at hz
    exact False.elim (Finset.not_mem_empty _ hz)
  · intro z hz
    rw [he.2] at hz
    exact False.elim (Finset.not_mem_empty _ hz)

variable (pol : Polarity arity)

theorem unpinned_move_empty (phi : Constraints arity n) (F : Frame n) (h : H) (i : Fin (arity h))
    (hp : framePins phi F=∅) : Empty (physicalMove pol phi F h i) := by
  obtain ⟨hx,hy⟩ := Finset.union_eq_empty.mp hp
  constructor
  · exact advance_of_no_pin pol phi F.sign F.x h i (by rw [hx]; exact Finset.not_mem_empty _)
  · exact advance_of_no_pin pol phi (!F.sign) F.y h i (by rw [hy]; exact Finset.not_mem_empty _)

theorem move_nonempty_pins (phi : Constraints arity n) (F : Frame n) (h : H) (i : Fin (arity h))
    (hn : ¬Empty (physicalMove pol phi F h i)) : (framePins phi F).Nonempty := by
  by_contra hp
  exact hn (unpinned_move_empty pol phi F h i (Finset.not_nonempty_iff_eq_empty.mp hp))

end NSSE.MultiVarianceSelectorHead
