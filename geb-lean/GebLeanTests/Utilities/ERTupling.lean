import GebLean.Utilities.ERTupling

/-!
# Tests for `ERMor1.tuplePack`, `ERMor1.tupleAt`,
# `ERMor1.PolyBound.ofTuplePack`,
# `ERMor1.PolyBound.ofTupleAt`.

ER-side fixed-length k-tuple Szudzik pairing infrastructure
for the ER ↔ K^sim_2 categorical equivalence.  See
`GebLean.Utilities.ERTupling` and master design §3.1
in `docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`.

Note on test discipline: ER-side `.interp` evaluation goes
through Gödel-numbering primitives (`natPair`,
`natUnpairFst`, `natUnpairSnd`) whose kernel-reduction is
slow even on small inputs.  This file uses `#guard` only
for the trivial-arity case (`k = 0`, where `tuplePack 0 =
proj 0` and no `natPair` is invoked).  Higher-arity ER-side
correctness is already established universally by the
`@[simp]` theorems `ERMor1.interp_tuplePack` and
`ERMor1.interp_tupleAt` in
`GebLean.Utilities.ERTupling`; concrete `#guard`-style
checks at higher arity would either (a) trigger the slow
ER kernel-reduction or (b) require manual `Fin.cases`
dispatch to recognize concrete `Fin (k+1)` indices as
`Fin.castSucc` / `Fin.last`.  Neither adds coverage beyond
the universal proof.
-/

open GebLean

-- ER-side smoke #guards: trivial-arity (`k = 0`) case only.
-- `tuplePack 0 = proj 0`, so no `natPair` evaluation.
#guard (ERMor1.tuplePack 0).interp ![5] = 5
#guard (ERMor1.tupleAt 0 0).interp ![17] = 17

-- ER-side boundary examples: PolyBound shape verification.
-- These access struct fields directly — no `.interp`
-- evaluation, so kernel reduction is fast.

example :
    (ERMor1.PolyBound.ofTuplePack 1).degree = 2 := rfl

example :
    (ERMor1.PolyBound.ofTuplePack 1).coefficient = 9 := rfl

example :
    (ERMor1.PolyBound.ofTuplePack 1).constant = 0 := rfl
