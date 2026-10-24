import NSSE.RegisteredAttachmentMismatchResponse

/-!
# Canonical singleton registration of a local mismatch

A concrete ordered attachment can register its mismatch decision under
the unique `Unit` local ID.  The existing registered mismatch response
theorem can then be applied directly with this registration.
-/

namespace NSSE

universe u

def OrderedInsertionAttachment.canonicalMismatchTerminal
    [DecidableEq α] (attachment : OrderedInsertionAttachment α) :
    Unit → Bool :=
  fun _ => attachment.mismatchTerminal

def OrderedInsertionAttachment.canonicalRegisteredMismatch
    [DecidableEq α] (attachment : OrderedInsertionAttachment α) :
    RegisteredLocalMismatch α Unit
      attachment.canonicalMismatchTerminal where
  attachment := attachment
  localId := ()
  terminal_registered := rfl

@[simp] theorem OrderedInsertionAttachment.canonicalMismatchTerminal_unit
    [DecidableEq α] (attachment : OrderedInsertionAttachment α) :
    attachment.canonicalMismatchTerminal () =
      attachment.mismatchTerminal :=
  rfl

end NSSE
