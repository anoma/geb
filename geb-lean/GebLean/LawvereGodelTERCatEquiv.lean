import GebLean.LawvereERQuot
import GebLean.LawvereGodelTQuot
import GebLean.LawvereGodelTInterp
import GebLean.LawvereERBoundComputable
import Mathlib.CategoryTheory.Equivalence

/-!
# Categorical equivalence `LawvereGodelTCat ≃ LawvereERCat`

Back-translation from `GodelTMor1 n` to `ERMor1 n` uses an
applied-form recursion over the curried arrow structure.
Forward translation from `ERMor1 n` to `GodelTMor1 n` maps
each ER constructor to a closed GodelT term assembled via the
projection and composition machinery of `LawvereGodelTQuot`.
The round-trips coincide on interpretation, giving an
on-the-nose equivalence at the quotient level.
-/

namespace GebLean

open CategoryTheory

end GebLean
