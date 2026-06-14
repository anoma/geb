import GebLean.Era
import GebLean.LawvereER

/-!
# Era basis completeness bridge

Relates the denotations of `Era` terms (`Tm.eval eraInterp`) to the
Kalmár elementary functions as formalised by `ERMor1`
(`GebLean/LawvereER.lean`).

## Main statements

* `era_sound_er` — every `ETm` denotes an `ERMor1` function
  (the inclusion `Era ⊆ E³`).

## References

* Prunescu, Sauras-Altuzarra, Shunia, arXiv:2505.23787.

## Tags

elementary recursive, substitution basis, completeness
-/

namespace GebLean.EraCompleteness

open Era

end GebLean.EraCompleteness
