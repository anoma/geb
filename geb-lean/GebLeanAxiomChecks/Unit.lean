import GebLeanMeta

/-! # Unit tests for `GebLeanMeta.offendingAxioms`

Example-based checks of the pure axiom classifier behind the
`detectNonstandardAxiom` linter.
-/

open Lean GebLeanMeta

-- Permitted axioms produce no offenders.
#guard offendingAxioms #[``propext, ``Quot.sound] == #[]
#guard offendingAxioms #[``Classical.choice] == #[]
-- `sorryAx` is reported.
#guard offendingAxioms #[``sorryAx] == #[``sorryAx]
-- Mixed input: only the non-standard axiom survives.
#guard offendingAxioms #[``propext, ``Classical.choice, ``sorryAx]
  == #[``sorryAx]
