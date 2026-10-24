import NSSE.RankedFiniteResponseHandlers

/-!
# A concrete complete finite mismatch registry

Two local IDs suffice: the mismatch terminal bit itself.  Both response
edges share one ranked side root, so the table handles every attachment
without storing any interval coordinates.
-/

namespace NSSE

def canonicalBoolEnumeration : Enumeration Bool where
  values := [false, true]
  complete := by
    intro value
    cases value <;> simp

def canonicalRankRealizes
    (rootRank : SideRank height) :
    SideRank height → NatInterval → Prop :=
  fun rank _interval => rank = rootRank

def canonicalRankedMismatchRoot
    (control : Ctl) (cut : Cut) (rootRank : SideRank height) :
    RankedInitialSideRoot height Ctl Cut where
  control := control
  cut := cut
  rank := rootRank

def canonicalRankedMismatchEdges
    (control : Ctl) (cut : Cut) (rootRank : SideRank height) :
    List
      (RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
        Wire LoopId Guard Bool QClass) :=
  [({
      control := control
      cut := cut
      parent := rootRank
      child := .bounded control cut (.inr false)
    } : RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
      Wire LoopId Guard Bool QClass),
   ({
      control := control
      cut := cut
      parent := rootRank
      child := .bounded control cut (.inr true)
    } : RankedFiniteAttachmentResponseEdge height Ctl Cut Ori Macro
      Wire LoopId Guard Bool QClass)]

def canonicalRankedMismatchRegistry
    [DecidableEq α]
    (control : Ctl) (cut : Cut) (rootRank : SideRank height) :
    RankedMismatchResponseRegistry
      (α := α)
      (Ori := Ori) (Macro := Macro) (Wire := Wire)
      (LoopId := LoopId) (Guard := Guard) (LocalId := Bool)
      (QClass := QClass)
      height (canonicalRankRealizes rootRank)
      [canonicalRankedMismatchRoot control cut rootRank]
      (canonicalRankedMismatchEdges
        (Ori := Ori) (Macro := Macro) (Wire := Wire)
        (LoopId := LoopId) (Guard := Guard) (QClass := QClass)
        control cut rootRank)
      (fun bit => bit) where
  entry := by
    intro attachment
    let bit :=
      attachment.toIntervalWordAttachment.orderedAttachment
        |>.mismatchTerminal
    refine {
      root := canonicalRankedMismatchRoot control cut rootRank
      root_mem := by simp
      root_realizes := rfl
      localId := bit
      terminal_registered := rfl
      edge_mem := ?_
    }
    cases hbit :
      attachment.toIntervalWordAttachment.orderedAttachment
        |>.mismatchTerminal <;>
      simp [bit, hbit, canonicalRankedMismatchEdges,
        canonicalRankedMismatchRoot]

theorem canonicalRankedMismatchRegistry_handles_all
    [DecidableEq α]
    (control : Ctl) (cut : Cut) (rootRank : SideRank height)
    (attachment : ForestWordAttachment α) :
    ∃ entry :
        RankedMismatchResponseEntry height
          (canonicalRankRealizes rootRank) attachment
          [canonicalRankedMismatchRoot control cut rootRank]
          (canonicalRankedMismatchEdges
            (Ori := Ori) (Macro := Macro) (Wire := Wire)
            (LoopId := LoopId) (Guard := Guard) (QClass := QClass)
            control cut rootRank)
          (fun bit => bit),
      entry.root =
        canonicalRankedMismatchRoot control cut rootRank := by
  let registry :=
    canonicalRankedMismatchRegistry
      (α := α) (Ori := Ori) (Macro := Macro) (Wire := Wire)
      (LoopId := LoopId) (Guard := Guard) (QClass := QClass)
      control cut rootRank
  exact ⟨registry.entry attachment, rfl⟩

end NSSE
