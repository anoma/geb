import GebLean.LawvereER
import GebLean.LawvereERQuot
import GebLean.LawvereKSim
import GebLean.LawvereKSimInterp
import GebLean.LawvereKSimMajorization
import GebLean.LawvereKSimQuot
import GebLean.Utilities.ERAMajorants
import GebLean.Utilities.ERSimultaneousBoundedRec

/-!
# Forward functor `kToER : KMor1 → ERMor1` (level ≤ 2)

Realises Tourlakis 2018 §0.1.0.44 ⊆-direction pointwise:
every K^sim morphism of level ≤ 2 translates structurally
to an `ERMor1` term, with the simrec node routed through
`ERMor1.simultaneousBoundedRec` (step 2) using the bound
from `KMor1.majorize_by_componentBound` (step 4).
Master design §3.5.
-/

namespace GebLean

end GebLean
