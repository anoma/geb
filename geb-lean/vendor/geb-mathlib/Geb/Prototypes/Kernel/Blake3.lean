/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.ToDual
public import Aesop

set_option doc.verso true in
/-!
# BLAKE3

The hash function BLAKE3 \[OConnorAumassonNevesWilcoxOHearn2020\] in its default mode, with a
32-byte digest, as the specification states it: the compression function over sixteen 32-bit
words, chunks of 1024 bytes compressed a 64-byte block at a time, and the binary tree of chunk
chaining values merged on a stack as the chunks arrive, the root's compression flagged. It is
the host binding of the hash written in Geb, which computes the same function by arithmetic on
natural numbers, and the hash of the multihashes of Geb's identifiers. Its tests are the
official test vectors.

## Main definitions

* {lit}`Blake3.compress` — the compression function.
* {lit}`Blake3.hash` — the 32-byte digest of a list of bytes.

## References

* \[OConnorAumassonNevesWilcoxOHearn2020\] — the specification.

## Tags

hash, BLAKE3, content identity
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Blake3

/-- The initialization vector: the first eight words of SHA-256's. -/
def iv : List UInt32 :=
  [0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB,
    0x5BE0CD19]

/-- The permutation of the message words between rounds. -/
def msgPermutation : List ℕ := [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]

/-- The flag of a chunk's first block. -/
def chunkStart : UInt32 := 1
/-- The flag of a chunk's last block. -/
def chunkEnd : UInt32 := 2
/-- The flag of a parent node. -/
def parent : UInt32 := 4
/-- The flag of the root. -/
def root : UInt32 := 8

/-- A word rotated right. -/
def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- A word of a list, zero beyond its end. -/
def wordAt (ws : List UInt32) (i : ℕ) : UInt32 := ws.getD i 0

/-- A list with one word replaced. -/
def put (ws : List UInt32) (i : ℕ) (w : UInt32) : List UInt32 := ws.set i w

/-- The quarter-round mixing function {lit}`G` on the state's words {lit}`a`, {lit}`b`,
{lit}`c` and {lit}`d` with two message words. -/
def g (st : List UInt32) (a b c d : ℕ) (mx my : UInt32) : List UInt32 :=
  let va := wordAt st a + wordAt st b + mx
  let vd := rotr (wordAt st d ^^^ va) 16
  let vc := wordAt st c + vd
  let vb := rotr (wordAt st b ^^^ vc) 12
  let va := va + vb + my
  let vd := rotr (vd ^^^ va) 8
  let vc := vc + vd
  let vb := rotr (vb ^^^ vc) 7
  put (put (put (put st a va) b vb) c vc) d vd

/-- One round: the columns, then the diagonals. -/
def round (st m : List UInt32) : List UInt32 :=
  let st := g st 0 4 8 12 (wordAt m 0) (wordAt m 1)
  let st := g st 1 5 9 13 (wordAt m 2) (wordAt m 3)
  let st := g st 2 6 10 14 (wordAt m 4) (wordAt m 5)
  let st := g st 3 7 11 15 (wordAt m 6) (wordAt m 7)
  let st := g st 0 5 10 15 (wordAt m 8) (wordAt m 9)
  let st := g st 1 6 11 12 (wordAt m 10) (wordAt m 11)
  let st := g st 2 7 8 13 (wordAt m 12) (wordAt m 13)
  g st 3 4 9 14 (wordAt m 14) (wordAt m 15)

/-- The message words permuted. -/
def permute (m : List UInt32) : List UInt32 := msgPermutation.map (wordAt m)

/-- The compression function: sixteen words from a chaining value of eight, a block of sixteen
message words, a 64-bit counter, the block's length and its flags. -/
def compress (cv m : List UInt32) (counter : ℕ) (len : ℕ) (flags : UInt32) : List UInt32 :=
  let st0 := cv ++ iv.take 4 ++
    [(counter % 2 ^ 32).toUInt32, (counter / 2 ^ 32).toUInt32, len.toUInt32, flags]
  let (st, _) := (List.range 7).foldl (fun (p : List UInt32 × List UInt32) _ ↦
    (round p.1 p.2, permute p.2)) (st0, m)
  (List.range 8).map (fun i ↦ wordAt st i ^^^ wordAt st (i + 8)) ++
    (List.range 8).map (fun i ↦ wordAt st (i + 8) ^^^ wordAt cv i)

/-- The little-endian words of a block of at most 64 bytes, padded with zeros. -/
def words (block : List UInt8) : List UInt32 :=
  (List.range 16).map fun i ↦
    (List.range 4).foldl
      (fun w j ↦ w ||| ((block.getD (4 * i + j) 0).toUInt32 <<< (8 * j).toUInt32)) 0

/-- The little-endian bytes of words. -/
def bytesOf (ws : List UInt32) : List UInt8 :=
  ws.flatMap fun w ↦ (List.range 4).map fun j ↦ (w >>> (8 * j).toUInt32).toUInt8

/-- The bytes of a list in consecutive pieces of a size, at least one, the last possibly
shorter or empty. -/
def pieces (n : ℕ) (bs : List UInt8) : List (List UInt8) :=
  (List.range (max 1 ((bs.length + n - 1) / n))).map fun i ↦ (bs.drop (n * i)).take n

/-- A compression not yet made: a chaining value, a block's words, a counter, the block's length
and its flags. Compressed with the root's flag, it gives the digest; otherwise, its first eight
words are a chaining value. -/
structure Output where
  /-- The chaining value. -/
  cv : List UInt32
  /-- The block's words. -/
  block : List UInt32
  /-- The counter. -/
  counter : ℕ
  /-- The block's length. -/
  len : ℕ
  /-- The flags. -/
  flags : UInt32

/-- The chaining value an output gives. -/
def Output.chainingValue (o : Output) : List UInt32 :=
  (compress o.cv o.block o.counter o.len o.flags).take 8

/-- The output of a chunk of at most 1024 bytes, its blocks but the last compressed. -/
def chunkOutput (counter : ℕ) (chunk : List UInt8) : Output :=
  let blocks := pieces 64 chunk
  let n := blocks.length
  let cv := (blocks.take (n - 1)).zipIdx.foldl (fun cv (b : List UInt8 × ℕ) ↦
    (compress cv (words b.1) counter 64 (if b.2 == 0 then chunkStart else 0)).take 8) iv
  let last := blocks.getD (n - 1) []
  ⟨cv, words last, counter, last.length, (if n == 1 then chunkStart else 0) ||| chunkEnd⟩

/-- The output of a parent node over two chaining values. -/
def parentOutput (l r : List UInt32) : Output := ⟨iv, l ++ r, 0, 64, parent⟩

/-- A chunk's chaining value pushed onto the stack of subtrees' chaining values, merging each
pair of completed subtrees: as many merges as trailing zero bits of the number of chunks
completed. -/
def push (stack : List (List UInt32)) (cv : List UInt32) (total : ℕ) : List (List UInt32) :=
  let (st, c, _) := (List.range 64).foldl (fun (p : List (List UInt32) × List UInt32 × ℕ) _ ↦
    let (st, c, t) := p
    if t % 2 == 0 && t != 0 then
      match st with
      | l :: rest => (rest, (parentOutput l c).chainingValue, t / 2)
      | [] => (st, c, 0)
    else (st, c, 0)) (stack, cv, total)
  c :: st

/-- The 32-byte digest of a list of bytes. -/
def hash (bs : List UInt8) : List UInt8 :=
  let chunks := pieces 1024 bs
  let n := chunks.length
  let stack := (chunks.take (n - 1)).zipIdx.foldl (fun st (c : List UInt8 × ℕ) ↦
    push st (chunkOutput c.2 c.1).chainingValue (c.2 + 1)) []
  let out := stack.foldl (fun o l ↦ parentOutput l o.chainingValue)
    (chunkOutput (n - 1) (chunks.getD (n - 1) []))
  bytesOf ((compress out.cv out.block out.counter out.len (out.flags ||| root)).take 8)

end Geb.Blake3

end
