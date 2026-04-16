import GebLean.Utilities.SzudzikSeq

/-!
# Tests for `Nat.seqPack`, `Nat.seqAt`, `Nat.treeFoldOnCode`,
# `Nat.tupleRecN`.
-/

open Nat

-- seqPack / seqAt round-trip on a small list
#guard seqAt (seqPack [3, 7, 11]) 0 = 3
#guard seqAt (seqPack [3, 7, 11]) 1 = 7
#guard seqAt (seqPack [3, 7, 11]) 2 = 11

-- treeFoldOnCode on a small tree.
-- code(leaf) = 0; code(branch l r) = 1 + pair(code l)(code r).
-- Folding with h₀ = 1 and h₁ = (+) counts leaves.
-- leaf: 1 leaf.
-- branch leaf leaf: 2 leaves; code is 1 + pair 0 0 = 1.
#guard treeFoldOnCode 1 (fun l r => l + r) 0 = 1
#guard treeFoldOnCode 1 (fun l r => l + r)
  (Nat.pair 0 0 + 1) = 2

-- tupleRecN: 2-ary mutual recursion.
-- step swaps the two slots each iteration.
-- Starting from (0, 1), after 3 iterations we have (1, 0).
#guard tupleRecN
  (fun (i : Fin 2) => if i = 0 then 0 else 1)
  (fun _ acc => fun i => if i = 0 then acc 1 else acc 0)
  3 0 = 1
#guard tupleRecN
  (fun (i : Fin 2) => if i = 0 then 0 else 1)
  (fun _ acc => fun i => if i = 0 then acc 1 else acc 0)
  3 1 = 0
#guard tupleRecN
  (fun (i : Fin 2) => if i = 0 then 0 else 1)
  (fun _ acc => fun i => if i = 0 then acc 1 else acc 0)
  0 0 = 0
