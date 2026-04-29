import GebLean
import GebLean.PLang.BTPair

namespace GebLeanTests.PLang.BTPair

open GebLean

/-! ## Encoding leaves at small alphabets -/

#guard encodeBTn 0 (BTα.leaf (0 : Fin 1)) = 0
#guard encodeBTn 1 (BTα.leaf (0 : Fin 2)) = 0
#guard encodeBTn 1 (BTα.leaf (1 : Fin 2)) = 1
#guard encodeBTn 2 (BTα.leaf (2 : Fin 3)) = 2

/-! ## Encoding one-level nodes -/

#guard
  encodeBTn 1
    (BTα.node (BTα.leaf (0 : Fin 2)) (BTα.leaf (1 : Fin 2))) =
    2 + Nat.pair 0 1

#guard
  encodeBTn 0 (BTα.node (BTα.leaf (0 : Fin 1))
    (BTα.leaf (0 : Fin 1))) = 1

/-! ## Round-trips on small naturals -/

#guard encodeBTn 0 (decodeBTn 0 0) = 0
#guard encodeBTn 0 (decodeBTn 0 5) = 5
#guard encodeBTn 0 (decodeBTn 0 17) = 17
#guard encodeBTn 1 (decodeBTn 1 7) = 7
#guard encodeBTn 2 (decodeBTn 2 11) = 11

/-! ## Alphabet shift sanity -/

#guard
  encodeBTn 1
    ((equivBTnBTm 2 1).toFun (BTα.leaf (1 : Fin 3))) =
    encodeBTn 2 (BTα.leaf (1 : Fin 3))

/-! ## Perfect-tree encoding values

The unlabeled-tree sequence `encodeBT (fullBT d)` is
`0, 1, 4, 25, 676, 458329`, which is OEIS A003095(d+1) − 1
(equivalently, the count of binary trees of depth ≤ d, minus
one). -/

#guard encodeBT (fullBT 0) = 0
#guard encodeBT (fullBT 1) = 1
#guard encodeBT (fullBT 2) = 4
#guard encodeBT (fullBT 3) = 25
#guard encodeBT (fullBT 4) = 676
#guard encodeBT (fullBT 5) = 458329

/-! ## Labeled perfect-tree values for small (n, d) -/

#guard encodeBTn 1 (fullBTn 1 0) = 1
#guard encodeBTn 2 (fullBTn 2 0) = 2
#guard encodeBTn 1 (fullBTn 1 1) = 2 + Nat.pair 1 1
#guard encodeBTn 0 (fullBTn 0 3) = 25

end GebLeanTests.PLang.BTPair
