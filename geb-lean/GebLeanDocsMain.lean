import GebLeanDocs.Root

open Verso.Genre.Manual

/-! # Generator entry point

Passes the root `Part` to `manualMain`. Outside the library.
-/

/-- Generate the ramified-recurrence manual. -/
def main (args : List String) : IO UInt32 :=
  manualMain (%doc GebLeanDocs.Root)
    (options := args)
    (config := {
      sourceLink := some "https://github.com/anoma/geb",
      issueLink := some "https://github.com/anoma/geb/issues"
    })
