import NSSE.MultiVarianceModelTokens
import NSSE.MultiVarianceSpineClasses

/-! Original-support one-sided tokens.  `upper = true` means an upper
bound position; a negative child exchanges that role.  All heads are
retained in pins, while actual child moves require the current head. -/
namespace NSSE.MultiVarianceSpineTokens
open MultiConstructorConstraints (Bound Constraints)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceGlobal
open MultiVarianceModelTokens (Tokens State)
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n m : Nat}
variable (pol : Polarity arity) (phi : Constraints arity n)

def nextRole (upper negative : Bool) : Bool := if negative then !upper else upper

def Closed (upper : Bool) (S : Tokens n) : Prop :=
  ∀ x ∈ S, ∀ y, (if upper then Support pol phi y x else Support pol phi x y) → y ∈ S

def initial (upper : Bool) (x : Fin n) : Tokens n :=
  if upper then MultiVarianceModelTokens.down pol phi x else MultiVarianceModelTokens.up pol phi x

theorem initial_closed (upper : Bool) (x : Fin n) : Closed pol phi upper (initial pol phi upper x) := by
  intro u hu v hs
  cases upper <;> simp only [initial,Bool.false_eq_true,if_false,if_true,
    MultiVarianceModelTokens.mem_up,MultiVarianceModelTokens.mem_down] at hu hs ⊢
  · exact hu.trans hs
  · exact hs.trans hu

def pins (upper : Bool) (S : Tokens n) : Finset H :=
  (((if upper then phi.lower else phi.upper).filter (fun b => b.parent ∈ S)).map Bound.head).toFinset

theorem mem_pins (upper : Bool) (S : Tokens n) (h : H) :
    h ∈ pins phi upper S ↔ ∃ b ∈ (if upper then phi.lower else phi.upper), b.parent ∈ S ∧ b.head = h := by
  simp only [pins,List.mem_toFinset,List.mem_map,List.mem_filter,decide_eq_true_eq,and_assoc]

def advance (upper : Bool) (S : Tokens n) (h : H) (i : Fin (arity h)) : Tokens n :=
  MultiVarianceModelTokens.children pol phi (if upper then phi.lower else phi.upper)
    S h i.val (!(nextRole upper (pol h i)))

theorem mem_advance (upper : Bool) (S : Tokens n) (h : H) (i : Fin (arity h)) (v : Fin n) :
    v ∈ advance pol phi upper S h i ↔
      ∃ p cs, (⟨p,h,cs⟩ : Bound arity n) ∈ (if upper then phi.lower else phi.upper) ∧
        p ∈ S ∧ (if nextRole upper (pol h i) then Support pol phi v (cs i) else Support pol phi (cs i) v) := by
  rw [advance,MultiVarianceModelTokens.mem_children_typed]
  cases nextRole upper (pol h i) <;> rfl

theorem advance_closed (upper : Bool) (S : Tokens n) (h : H) (i : Fin (arity h)) :
    Closed pol phi (nextRole upper (pol h i)) (advance pol phi upper S h i) := by
  intro x hx y hxy
  obtain ⟨p,cs,hb,hp,hs⟩ := (mem_advance pol phi upper S h i x).mp hx
  apply (mem_advance pol phi upper S h i y).mpr
  refine ⟨p,cs,hb,hp,?_⟩
  cases hn : nextRole upper (pol h i) <;> simp only [hn,Bool.false_eq_true,if_false,if_true] at hs hxy ⊢
  · exact hs.trans hxy
  · exact hxy.trans hs

theorem advance_of_no_pin (upper : Bool) (S : Tokens n) (h : H) (i : Fin (arity h))
    (hp : h ∉ pins phi upper S) : advance pol phi upper S h i = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro v hv
  obtain ⟨p,cs,hb,hmem,_⟩ := (mem_advance pol phi upper S h i v).mp hv
  exact hp ((mem_pins phi upper S h).mpr ⟨⟨p,h,cs⟩,hb,hmem,rfl⟩)

@[simp] theorem pins_empty (upper : Bool) : pins phi upper (∅ : Tokens n) = ∅ := by
  ext h
  simp [mem_pins]

@[simp] theorem advance_empty (upper : Bool) (h : H) (i : Fin (arity h)) :
    advance pol phi upper ∅ h i = ∅ :=
  advance_of_no_pin pol phi upper ∅ h i (by simp)

def move (S : State n) (h : H) (i : Fin (arity h)) : State n :=
  if pol h i then (advance pol phi true S.2 h i,advance pol phi false S.1 h i)
  else (advance pol phi false S.1 h i,advance pol phi true S.2 h i)

def StateClosed (S : State n) : Prop := Closed pol phi false S.1 ∧ Closed pol phi true S.2

theorem move_closed (S : State n) (h : H) (i : Fin (arity h)) : StateClosed pol phi (move pol phi S h i) := by
  have hL := advance_closed pol phi false S.1 h i
  have hR := advance_closed pol phi true S.2 h i
  cases hp : pol h i <;> simp only [move,hp,nextRole,Bool.not_false,Bool.not_true,
    Bool.false_eq_true,if_false,if_true,StateClosed] at hL hR ⊢
  · exact ⟨hL,hR⟩
  · exact ⟨hR,hL⟩

/-- This is one directed birth; the callers retain every physical rail pair. -/
def Birth (r : Bool) (S : Tokens n) (t : Bool) (T : Tokens n) : Prop :=
  r = false ∧ t = true ∧ ∃ u ∈ S, ∃ v ∈ T, Support pol phi u v

def inspectBirth (r : Bool) (S : Tokens n) (t : Bool) (T : Tokens n) : Bool :=
  !r && t && decide ((S ∩ T).Nonempty)

omit [DecidableEq H] in
theorem birth_iff_inter (S T : Tokens n) (hc : Closed pol phi false S) :
    (∃ u ∈ S, ∃ v ∈ T, Support pol phi u v) ↔ (S ∩ T).Nonempty := by
  constructor
  · rintro ⟨u,hu,v,hv,hs⟩
    exact ⟨v,Finset.mem_inter.mpr ⟨hc u hu v hs,hv⟩⟩
  · rintro ⟨v,hv⟩
    obtain ⟨hu,ht⟩ := Finset.mem_inter.mp hv
    exact ⟨v,hu,v,ht,.refl v⟩

omit [DecidableEq H] in
theorem inspectBirth_correct (r : Bool) (S : Tokens n) (t : Bool) (T : Tokens n)
    (hc : Closed pol phi r S) : inspectBirth r S t T = true ↔ Birth pol phi r S t T := by
  cases r <;> cases t <;> simp only [inspectBirth,Birth,Bool.not_false,Bool.not_true,
    Bool.false_and,Bool.true_and,Bool.and_false,Bool.and_true,Bool.false_eq_true,
    false_and,true_and,Bool.true_eq_false,and_false,decide_eq_true_eq]
  exact (birth_iff_inter pol phi S T hc).symm

/-- Physical rails retain identity; their bound roles are recovered from sign. -/
structure Frame (n : Nat) where
  sign : Bool
  x : Tokens n
  y : Tokens n
  deriving DecidableEq, Fintype

def rolePair (F : Frame n) : State n := if F.sign then (F.y,F.x) else (F.x,F.y)

def physicalMove (F : Frame n) (h : H) (i : Fin (arity h)) : Frame n :=
  ⟨nextRole F.sign (pol h i),advance pol phi F.sign F.x h i,
    advance pol phi (!F.sign) F.y h i⟩

theorem physicalMove_rolePair (F : Frame n) (h : H) (i : Fin (arity h)) :
    rolePair (physicalMove pol phi F h i) = move pol phi (rolePair F) h i := by
  cases hs : F.sign <;> cases hp : pol h i <;>
    simp [rolePair,physicalMove,move,nextRole,hs,hp]

theorem card_frames : Fintype.card (Frame n) = 2*4^n := by
  let e : Frame n ≃ Bool × State n :=
    ⟨fun F => (F.sign,F.x,F.y),fun p => ⟨p.1,p.2.1,p.2.2⟩,by intro F; rfl,by intro p; rfl⟩
  rw [Fintype.card_congr e,Fintype.card_prod,Fintype.card_bool,MultiVarianceModelTokens.card_states]

abbrev Letter (arity : H → Nat) := (h : H) × Fin (arity h)

def runPhysical : Frame n → List (Letter arity) → Frame n
  | F, [] => F
  | F, a::w => runPhysical (physicalMove pol phi F a.1 a.2) w

def runRoles : State n → List (Letter arity) → State n
  | S, [] => S
  | S, a::w => runRoles (move pol phi S a.1 a.2) w

theorem run_rolePair (F : Frame n) (w : List (Letter arity)) :
    rolePair (runPhysical pol phi F w) = runRoles pol phi (rolePair F) w := by
  induction w generalizing F with
  | nil => rfl
  | cons a w ih =>
    simp only [runPhysical,runRoles,ih,physicalMove_rolePair]

theorem run_x_empty (F : Frame n) (w : List (Letter arity)) (he : F.x = ∅) :
    (runPhysical pol phi F w).x = ∅ := by
  induction w generalizing F with
  | nil => exact he
  | cons a w ih =>
    apply ih
    simp only [physicalMove,he,advance_empty]

theorem run_y_empty (F : Frame n) (w : List (Letter arity)) (he : F.y = ∅) :
    (runPhysical pol phi F w).y = ∅ := by
  induction w generalizing F with
  | nil => exact he
  | cons a w ih =>
    apply ih
    simp only [physicalMove,he,advance_empty]

theorem run_roles_closed (S : State n) (w : List (Letter arity)) (hc : StateClosed pol phi S) :
    StateClosed pol phi (runRoles pol phi S w) := by
  induction w generalizing S with
  | nil => exact hc
  | cons a w ih => exact ih _ (move_closed pol phi S a.1 a.2)

end NSSE.MultiVarianceSpineTokens
