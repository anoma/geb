import GebLean.LawvereER
import GebLean.LawvereERBoundComputable
import GebLean.Utilities.ERArith
import GebLean.Utilities.SzudzikSeq

/-!
# Szudzik-based simrec helpers for `kToER`

ER-side combinators packing a `(k+1)`-tuple of ER values
into a single ℕ via iterated right-associated Szudzik
pairing, the inverse component-extraction term, and the
packed base/step builders for translating a K^sim
`simrec` term to an `ERMor1` term using
`ERMor1.boundedRec`.

The pack/unpack ER terms compose `ERMor1.natPair`,
`ERMor1.natUnpairFst`, and `ERMor1.natUnpairSnd` per the
sequence-encoding rules of `Nat.seqPack` and
`Nat.seqAt` from `Utilities/SzudzikSeq.lean`.

See `docs/plans/2026-04-29-lawvere-k-sim-ktoer-design.md`,
component C5.
-/

namespace GebLean

end GebLean
