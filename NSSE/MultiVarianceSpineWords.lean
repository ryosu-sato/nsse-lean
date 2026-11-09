import NSSE.MultiVarianceRawSpine

/-! Construct actual separating-spine syntax from current-head letters.
Physical terminal labels are converted to lower/upper roles using the
FINAL raw sign, independently of any selector state. -/
namespace NSSE.MultiVarianceSpineWords
open MultiConstructorTrees (Label)
open MultiVarianceSpineSeparation MultiVarianceSpineTokens MultiVarianceTokenExact
open MultiVarianceSpineSuffixes MultiVarianceLiteralGeometry
variable {H : Type*} {arity : H → Nat}

def ofLetters (w : List (Letter arity)) (a b : Label H) : Spine arity :=
  w.foldr (fun h s => .step h.1 h.2 s) (.stop a b)

@[simp] theorem path_ofLetters (w : List (Letter arity)) (a b : Label H) :
    path (ofLetters w a b)=w := by
  induction w <;> simp_all [ofLetters,path]

@[simp] theorem depth_ofLetters (w : List (Letter arity)) (a b : Label H) :
    (ofLetters w a b).depth=w.length := by
  induction w <;> simp_all [ofLetters,Spine.depth]

@[simp] theorem valid_ofLetters (w : List (Letter arity)) (a b : Label H) :
    (ofLetters w a b).Valid ↔ ¬a ≤ b := by
  induction w <;> simp_all [ofLetters,Spine.Valid]

theorem suffix_ofLetters (w : List (Letter arity)) (a b : Label H) (d : Nat) :
    suffix (ofLetters w a b) d = ofLetters (w.drop d) a b := by
  induction d generalizing w with
  | zero => rfl
  | succ d ih =>
    cases w with
    | nil => rfl
    | cons h w => exact ih w

theorem terminal_ofLetters (w : List (Letter arity)) (a b : Label H) :
    suffix (ofLetters w a b) w.length = .stop a b := by
  rw [suffix_ofLetters,List.drop_length]
  rfl

def physical (w : List (Letter arity)) (sign : Bool) (ex ey : Label H) : Spine arity :=
  ofLetters w (if sign then ey else ex) (if sign then ex else ey)

@[simp] theorem physical_path (w : List (Letter arity)) (sign : Bool) (ex ey : Label H) :
    path (physical w sign ex ey)=w := path_ofLetters _ _ _

@[simp] theorem physical_depth (w : List (Letter arity)) (sign : Bool) (ex ey : Label H) :
    (physical w sign ex ey).depth=w.length := depth_ofLetters _ _ _

theorem physical_valid (w : List (Letter arity)) (sign : Bool) (ex ey : Label H) :
    (physical w sign ex ey).Valid ↔ if sign then ¬ey ≤ ex else ¬ex ≤ ey := by
  cases sign <;> exact valid_ofLetters _ _ _

theorem physical_terminal (w : List (Letter arity)) (sign side : Bool) (ex ey : Label H) :
    label (suffix (physical w sign ex ey) w.length) (roleOf sign side) = if side then ey else ex := by
  unfold physical
  rw [terminal_ofLetters]
  cases sign <;> cases side <;> rfl

end NSSE.MultiVarianceSpineWords
