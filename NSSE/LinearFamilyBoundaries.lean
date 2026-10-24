import NSSE.LinearFamilyAddress

/-!
# Affine event boundaries of a linear word family

Each stage contributes a start boundary, the end of its powered zone, and
the end of its fixed separator. These are the event positions used in the
order-type split of Lemma A.1.
-/

namespace NSSE

universe u

namespace LinearWordFamily

def stageStartPosition
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity) : Nat :=
  family.initial.length +
    ∑ earlier ∈ precedingIndices index,
      (parameters earlier *
        (family.pump earlier).length +
        (family.separator earlier).length)

def stageStartExpression
    (family : LinearWordFamily α arity)
    (index : Fin arity) :
    NatLinearExpr arity where
  constant :=
    family.initial.length +
      ∑ earlier ∈ precedingIndices index,
        (family.separator earlier).length
  coefficient := fun earlier =>
    if earlier < index
    then (family.pump earlier).length
    else 0

def pumpEndPosition
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity) : Nat :=
  family.stageStartPosition parameters index +
    parameters index * (family.pump index).length

def pumpEndExpression
    (family : LinearWordFamily α arity)
    (index : Fin arity) :
    NatLinearExpr arity :=
  (family.stageStartExpression index).add
    ((NatLinearExpr.varExpr index).scale
      (family.pump index).length)

def separatorEndPosition
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity) : Nat :=
  family.pumpEndPosition parameters index +
    (family.separator index).length

def separatorEndExpression
    (family : LinearWordFamily α arity)
    (index : Fin arity) :
    NatLinearExpr arity :=
  (family.pumpEndExpression index).add
    (.const (family.separator index).length)

theorem stageStartPosition_eq_expression
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity) :
    family.stageStartPosition parameters index =
      (family.stageStartExpression index).Eval
        parameters := by
  classical
  unfold stageStartPosition stageStartExpression
    NatLinearExpr.Eval
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  simp only [precedingIndices]
  rw [Finset.sum_add_distrib]
  simp [Nat.mul_comm, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]

theorem pumpEndPosition_eq_expression
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity) :
    family.pumpEndPosition parameters index =
      (family.pumpEndExpression index).Eval
        parameters := by
  rw [pumpEndPosition, pumpEndExpression,
    NatLinearExpr.eval_add,
    NatLinearExpr.eval_scale,
    NatLinearExpr.eval_variable,
    family.stageStartPosition_eq_expression]
  simp [Nat.mul_comm]

theorem separatorEndPosition_eq_expression
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity) :
    family.separatorEndPosition parameters index =
      (family.separatorEndExpression index).Eval
        parameters := by
  rw [separatorEndPosition, separatorEndExpression,
    NatLinearExpr.eval_add,
    NatLinearExpr.eval_const,
    family.pumpEndPosition_eq_expression]

theorem stageStart_le_pumpEnd
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity) :
    family.stageStartPosition parameters index ≤
      family.pumpEndPosition parameters index := by
  simp [pumpEndPosition]

theorem pumpEnd_le_separatorEnd
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity) :
    family.pumpEndPosition parameters index ≤
      family.separatorEndPosition parameters index := by
  simp [separatorEndPosition]

theorem stage_boundaries_ordered
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity) :
    family.stageStartPosition parameters index ≤
      family.pumpEndPosition parameters index ∧
    family.pumpEndPosition parameters index ≤
      family.separatorEndPosition parameters index :=
  ⟨family.stageStart_le_pumpEnd parameters index,
    family.pumpEnd_le_separatorEnd parameters index⟩

/-- The next stage starts where the current separator ends. -/
theorem separatorEnd_eq_nextStageStart
    (family : LinearWordFamily α (arity + 1))
    (parameters : Fin (arity + 1) → Nat)
    (index : Fin arity) :
    family.separatorEndPosition parameters index.castSucc =
      family.stageStartPosition parameters index.succ := by
  classical
  unfold separatorEndPosition pumpEndPosition
    stageStartPosition precedingIndices
  have hdecompose :
      (Finset.univ.filter fun earlier : Fin (arity + 1) =>
          earlier < index.succ) =
        insert index.castSucc
          (Finset.univ.filter fun earlier =>
            earlier < index.castSucc) := by
    ext earlier
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_insert]
    simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff]
    change earlier.val < index.val + 1 ↔
      earlier.val = index.val ∨ earlier.val < index.val
    omega
  rw [hdecompose, Finset.sum_insert]
  · simp [Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  · simp

end LinearWordFamily

end NSSE
