import NSSE.FiniteControlColors
import Lean.Elab.Tactic.Omega

/-!
# Finite levels colored by depth and control value

Every tree layer receives one slot for each control value and two additional
structural markers.  The layer is the high digit and the slot is the low
digit.  Idempotent-colored slots decode to their control value; marker slots
decode to the unit.
-/

namespace NSSE

universe v

namespace Enumeration

def colorWidth
    [DecidableEq M] (elements : Enumeration M) : Nat :=
  elements.normalized.values.length + 2

theorem colorWidth_pos
    [DecidableEq M] (elements : Enumeration M) :
    0 < elements.colorWidth := by
  simp [colorWidth]

def encodeLevel
    [DecidableEq M] (elements : Enumeration M)
    {layers : Nat} (layer : Fin layers)
    (offset : Fin elements.colorWidth) :
    Fin (layers * elements.colorWidth) :=
  ⟨layer.1 * elements.colorWidth + offset.1, by
    have hlayer :
        layer.1 + 1 ≤ layers :=
      Nat.succ_le_of_lt layer.2
    have hmul :=
      Nat.mul_le_mul_right
        elements.colorWidth hlayer
    calc
      layer.1 * elements.colorWidth + offset.1 <
          layer.1 * elements.colorWidth +
            elements.colorWidth := by
              exact Nat.add_lt_add_left offset.2 _
      _ = (layer.1 + 1) * elements.colorWidth := by
            rw [Nat.add_mul, Nat.one_mul]
      _ ≤ layers * elements.colorWidth := hmul⟩

@[simp] theorem encodeLevel_val
    [DecidableEq M] (elements : Enumeration M)
    {layers : Nat} (layer : Fin layers)
    (offset : Fin elements.colorWidth) :
    (elements.encodeLevel layer offset).1 =
      layer.1 * elements.colorWidth + offset.1 :=
  rfl

def colorOffset
    [DecidableEq M] (elements : Enumeration M)
    (color :
      Fin elements.normalized.values.length) :
    Fin elements.colorWidth :=
  ⟨color.1, by
    unfold colorWidth
    omega⟩

def leftMarkerOffset
    [DecidableEq M] (elements : Enumeration M) :
    Fin elements.colorWidth :=
  ⟨elements.normalized.values.length, by
    unfold colorWidth
    omega⟩

def rightMarkerOffset
    [DecidableEq M] (elements : Enumeration M) :
    Fin elements.colorWidth :=
  ⟨elements.normalized.values.length + 1, by
    unfold colorWidth
    omega⟩

def coloredLevel
    [DecidableEq M] (elements : Enumeration M)
    {layers : Nat} (layer : Fin layers)
    (color :
      Fin elements.normalized.values.length) :
    Fin (layers * elements.colorWidth) :=
  elements.encodeLevel layer
    (elements.colorOffset color)

def leftMarkerLevel
    [DecidableEq M] (elements : Enumeration M)
    {layers : Nat} (layer : Fin layers) :
    Fin (layers * elements.colorWidth) :=
  elements.encodeLevel layer elements.leftMarkerOffset

def rightMarkerLevel
    [DecidableEq M] (elements : Enumeration M)
    {layers : Nat} (layer : Fin layers) :
    Fin (layers * elements.colorWidth) :=
  elements.encodeLevel layer elements.rightMarkerOffset

theorem encodeLevel_layer_lt
    [DecidableEq M] (elements : Enumeration M)
    {layers : Nat}
    {lower upper : Fin layers}
    (hlayer : lower.1 < upper.1)
    (lowerOffset upperOffset : Fin elements.colorWidth) :
    (elements.encodeLevel lower lowerOffset).1 <
      (elements.encodeLevel upper upperOffset).1 := by
  have hwidth := elements.colorWidth_pos
  have hlowerOffset := lowerOffset.2
  have hmul :=
    Nat.mul_le_mul_right elements.colorWidth
      (Nat.succ_le_of_lt hlayer)
  simp only [encodeLevel_val]
  have hbelow :
      lower.1 * elements.colorWidth + lowerOffset.1 <
        (lower.1 + 1) * elements.colorWidth := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_lt_add_left lowerOffset.2 _
  have habove :
      upper.1 * elements.colorWidth ≤
        upper.1 * elements.colorWidth + upperOffset.1 :=
    Nat.le_add_right _ _
  exact Nat.lt_of_lt_of_le hbelow
    (Nat.le_trans hmul habove)

theorem colored_lt_leftMarker
    [DecidableEq M] (elements : Enumeration M)
    {layers : Nat} (layer : Fin layers)
    (color :
      Fin elements.normalized.values.length) :
    (elements.coloredLevel layer color).1 <
      (elements.leftMarkerLevel layer).1 := by
  simp [coloredLevel, leftMarkerLevel,
    encodeLevel, colorOffset, leftMarkerOffset]

theorem leftMarker_lt_rightMarker
    [DecidableEq M] (elements : Enumeration M)
    {layers : Nat} (layer : Fin layers) :
    (elements.leftMarkerLevel layer).1 <
      (elements.rightMarkerLevel layer).1 := by
  simp [leftMarkerLevel, rightMarkerLevel,
    encodeLevel, leftMarkerOffset, rightMarkerOffset]

theorem rightMarker_layer_lt
    [DecidableEq M] (elements : Enumeration M)
    {layers : Nat} {lower upper : Fin layers}
    (hlayer : lower.1 < upper.1) :
    (elements.rightMarkerLevel lower).1 <
      (elements.rightMarkerLevel upper).1 := by
  exact elements.encodeLevel_layer_lt hlayer
    elements.rightMarkerOffset
    elements.rightMarkerOffset

theorem rightMarker_lt_leftMarker_of_layer_lt
    [DecidableEq M] (elements : Enumeration M)
    {layers : Nat} {lower upper : Fin layers}
    (hlayer : lower.1 < upper.1) :
    (elements.rightMarkerLevel lower).1 <
      (elements.leftMarkerLevel upper).1 := by
  exact elements.encodeLevel_layer_lt hlayer
    elements.rightMarkerOffset
    elements.leftMarkerOffset

theorem rightMarker_lt_colored_of_layer_lt
    [DecidableEq M] (elements : Enumeration M)
    {layers : Nat} {lower upper : Fin layers}
    (hlayer : lower.1 < upper.1)
    (color :
      Fin elements.normalized.values.length) :
    (elements.rightMarkerLevel lower).1 <
      (elements.coloredLevel upper color).1 := by
  exact elements.encodeLevel_layer_lt hlayer
    elements.rightMarkerOffset
    (elements.colorOffset color)

def decodedColor?
    [DecidableEq M] (elements : Enumeration M)
    {layers : Nat}
    (level : Fin (layers * elements.colorWidth)) :
    Option
      (Fin elements.normalized.values.length) :=
  let offset := level.1 % elements.colorWidth
  if hcolor :
      offset < elements.normalized.values.length then
    some ⟨offset, hcolor⟩
  else
    none

@[simp] theorem decodedColor_coloredLevel
    [DecidableEq M] (elements : Enumeration M)
    {layers : Nat} (layer : Fin layers)
    (color :
      Fin elements.normalized.values.length) :
    elements.decodedColor?
        (elements.coloredLevel layer color) =
      some color := by
  have hmod :
      (layer.1 * elements.colorWidth + color.1) %
          elements.colorWidth =
        color.1 := by
    rw [Nat.mul_comm layer.1 elements.colorWidth]
    rw [Nat.mul_add_mod]
    rw [Nat.mod_eq_of_lt]
    exact Nat.lt_trans color.2 (by
      unfold colorWidth
      omega)
  unfold decodedColor? coloredLevel
  simp only [encodeLevel_val, colorOffset]
  simp [hmod, color.2]

@[simp] theorem decodedColor_leftMarkerLevel
    [DecidableEq M] (elements : Enumeration M)
    {layers : Nat} (layer : Fin layers) :
    elements.decodedColor?
        (elements.leftMarkerLevel layer) =
      none := by
  have hmod :
      (layer.1 * elements.colorWidth +
          elements.normalized.values.length) %
          elements.colorWidth =
        elements.normalized.values.length := by
    rw [Nat.mul_comm layer.1 elements.colorWidth,
      Nat.mul_add_mod, Nat.mod_eq_of_lt]
    unfold colorWidth
    omega
  unfold decodedColor? leftMarkerLevel
  simp only [encodeLevel_val, leftMarkerOffset]
  simp [hmod]

@[simp] theorem decodedColor_rightMarkerLevel
    [DecidableEq M] (elements : Enumeration M)
    {layers : Nat} (layer : Fin layers) :
    elements.decodedColor?
        (elements.rightMarkerLevel layer) =
      none := by
  have hmod :
      (layer.1 * elements.colorWidth +
          (elements.normalized.values.length + 1)) %
          elements.colorWidth =
        elements.normalized.values.length + 1 := by
    rw [Nat.mul_comm layer.1 elements.colorWidth,
      Nat.mul_add_mod, Nat.mod_eq_of_lt]
    unfold colorWidth
    omega
  unfold decodedColor? rightMarkerLevel
  simp only [encodeLevel_val, rightMarkerOffset]
  simp [hmod]

end Enumeration

namespace ControlMonoid

def coloredIdempotentAt
    [DecidableEq M] (C : ControlMonoid M)
    (elements : Enumeration M) {layers : Nat}
    (level :
      Fin (layers * elements.colorWidth)) : M :=
  match elements.decodedColor? level with
  | some color => C.idempotentColor elements color
  | none => C.one

theorem coloredIdempotentAt_idempotent
    [DecidableEq M] (C : ControlMonoid M)
    (elements : Enumeration M) {layers : Nat}
    (level :
      Fin (layers * elements.colorWidth)) :
    C.Idempotent
      (C.coloredIdempotentAt elements level) := by
  unfold coloredIdempotentAt
  split
  · exact C.idempotentColor_idempotent elements _
  · exact C.mul_one C.one

@[simp] theorem coloredIdempotentAt_coloredLevel
    [DecidableEq M] (C : ControlMonoid M)
    (elements : Enumeration M) {layers : Nat}
    (layer : Fin layers) (value : M)
    (hvalue : C.Idempotent value) :
    C.coloredIdempotentAt elements
        (elements.coloredLevel layer
          (elements.canonicalIndex value)) =
      value := by
  simp [coloredIdempotentAt, hvalue]

@[simp] theorem coloredIdempotentAt_leftMarkerLevel
    [DecidableEq M] (C : ControlMonoid M)
    (elements : Enumeration M) {layers : Nat}
    (layer : Fin layers) :
    C.coloredIdempotentAt elements
        (elements.leftMarkerLevel layer) =
      C.one := by
  simp [coloredIdempotentAt]

@[simp] theorem coloredIdempotentAt_rightMarkerLevel
    [DecidableEq M] (C : ControlMonoid M)
    (elements : Enumeration M) {layers : Nat}
    (layer : Fin layers) :
    C.coloredIdempotentAt elements
        (elements.rightMarkerLevel layer) =
      C.one := by
  simp [coloredIdempotentAt]

end ControlMonoid

end NSSE
