# Primitive Recursion Correspondence and Non-Fullness

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Prove that LawvereBTQuotCat computes exactly
the primitive recursive functions on binary trees, and
that the interpretation functor into Type is not full
(the Ackermann function is not in the image).

**Architecture:** We establish a Primcodable instance for
BT (encoding binary trees as natural numbers via Cantor
pairing), show that BT.fold preserves primitive
recursiveness (via mathlib's `Primrec.nat_omega_rec'`),
prove by BTMor1.ind that every morphism in the Lawvere
theory computes a primitive recursive function, then
derive non-fullness from mathlib's
`not_primrec2_ack`.

**Tech Stack:** Lean 4, mathlib
(`Mathlib.Computability.Primrec.Basic`,
`Mathlib.Computability.Primrec.List`,
`Mathlib.Computability.Ackermann`), existing
GebLean Lawvere BT infrastructure.

**Key references:**

- `Mathlib.Computability.Primrec.Basic`: `Nat.Primrec`,
  `Primrec`, `Primcodable`, `Primrec.nat_rec`
- `Mathlib.Computability.Primrec.List`:
  `Primrec.nat_omega_rec'` (well-founded PR recursion)
- `Mathlib.Computability.Ackermann`: `ack`,
  `not_primrec2_ack`, `not_nat_primrec_ack_self`,
  `exists_lt_ack_of_nat_primrec`
- `GebLean/LawvereBTInterp.lean`: `interpFunctor`,
  `interpU_complete`, `BTMor1.interpU`,
  `BT.fold`, `quoteBT`

---

## File Structure

| File | Responsibility |
|------|----------------|
| Create: `GebLean/LawvereBTPrimrec.lean` | All new code |
| Modify: `GebLean.lean` | Add import |

All new code goes in one file since the components
form a linear dependency chain.  The file imports
`GebLean.LawvereBTInterp` (for the Lawvere theory
infrastructure) and `Mathlib.Computability.Ackermann`
(for Primrec + Ackermann).

---

## Conventions

Per CLAUDE.md:

- Line length max 80 characters
- `autoImplicit = false`, `relaxedAutoImplicit = false`
- No `sorry`, no `admit`, no `Classical`, no
  `noncomputable`, no `axiom`
- Namespace: `namespace GebLean ... end GebLean`
- Build after every definition: `lake build`
- Test: `lake test`
- Write one definition at a time, get it compiling
  before moving on
- Use underscores `_` (not sorry) to see goal types

---

### Task 1: File skeleton and BT encoding

**Files:**

- Create: `GebLean/LawvereBTPrimrec.lean`
- Modify: `GebLean.lean` (add import)

- [ ] **Step 1: Create the file with imports and
  module docstring**

```lean
import GebLean.LawvereBTInterp
import Mathlib.Computability.Ackermann

/-!
# Primitive Recursion and Non-Fullness

Proves that every morphism in `LawvereBTQuotCat`
computes a primitive recursive function (under a
Goedel encoding `BT <-> Nat`), and that the
interpretation functor `interpFunctor` is not full
(the Ackermann function is not in the image).
-/

namespace GebLean

open CategoryTheory

end GebLean
```

- [ ] **Step 2: Add import to GebLean.lean**

Add `import GebLean.LawvereBTPrimrec` to
`GebLean.lean` (in alphabetical position, after the
existing `LawvereBTQuot` import).

- [ ] **Step 3: Build to verify imports work**

Run: `lake build GebLean.LawvereBTPrimrec`
Expected: builds successfully (empty file).

- [ ] **Step 4: Define `encodeBT` and `decodeBT`**

Inside the namespace, define the encoding:

```lean
/-- Goedel encoding of binary trees into
natural numbers.  Maps `BT.leaf` to `0` and
`BT.node l r` to `Nat.pair (encodeBT l)
(encodeBT r) + 1`. -/
def encodeBT : BT.{0} -> Nat :=
  BT.fold 0 (fun el er =>
    Nat.pair el er + 1)

/-- Decoding natural numbers back to binary
trees.  Inverse of `encodeBT`. -/
def decodeBT : Nat -> BT.{0}
  | 0 => BT.leaf
  | n + 1 =>
    let p := Nat.unpair n
    BT.node (decodeBT p.1) (decodeBT p.2)
```

- [ ] **Step 5: Build and verify**

Run: `lake build GebLean.LawvereBTPrimrec`

- [ ] **Step 6: Prove round-trip `decodeBT_encodeBT`**

```lean
theorem decodeBT_encodeBT (bt : BT.{0}) :
    decodeBT (encodeBT bt) = bt := by
  _
```

Prove by BT structural induction (following the
pattern in `fold_eta_gen` in LawvereBTInterp.lean).
The leaf case reduces by `BT.fold_leaf`;
the node case uses `BT.fold_node`,
`Nat.unpair_pair`, and the IH.

- [ ] **Step 7: Build and verify**

Run: `lake build GebLean.LawvereBTPrimrec`

- [ ] **Step 8: Commit**

```bash
git add GebLean/LawvereBTPrimrec.lean GebLean.lean
git commit -m "feat: BT Goedel encoding"
```

---

### Task 2: Primcodable BT instance

**Files:**

- Modify: `GebLean/LawvereBTPrimrec.lean`

- [ ] **Step 1: Prove `encodeBT` is injective**

```lean
theorem encodeBT_injective :
    Function.Injective encodeBT := by
  intro a b h
  rw [<- decodeBT_encodeBT a,
    <- decodeBT_encodeBT b, h]
```

- [ ] **Step 2: Define the Encodable instance**

```lean
instance : Encodable BT.{0} where
  encode := encodeBT
  decode n := some (decodeBT n)
  encodek bt := by
    simp [decodeBT_encodeBT]
```

Note: `decode` returns `Option`; we return `some`
always since `decodeBT` is total.  The `encodek`
field requires `decode (encode bt) = some bt`.

- [ ] **Step 3: Build and verify**

Run: `lake build GebLean.LawvereBTPrimrec`

- [ ] **Step 4: Prove `encodeBT` is `Nat.Primrec`**

This requires showing `encodeBT` (as a function
`Nat -> Nat` via the encoding) is primitive
recursive.  Use `Primrec.nat_omega_rec'` with
the tree structure:

```lean
private theorem encodeBT_primrec :
    Nat.Primrec (fun n =>
      Encodable.encode
        (encodeBT (decodeBT n))) := by
  _
```

The measure is `n` itself (decodeBT on smaller
numbers gives smaller trees).  The children of
`decodeBT (n+1)` are `decodeBT (Nat.unpair n).1`
and `decodeBT (Nat.unpair n).2`, both with smaller
encodings.  The recombination is `Nat.pair + 1`.

Factor out helper lemmas as needed.  The proof
will compose `Nat.Primrec.pair`, `Nat.Primrec.succ`,
`Nat.Primrec.unpair` (from
`Mathlib.Data.Nat.Pairing`).

- [ ] **Step 5: Define the `Primcodable BT` instance**

```lean
instance : Primcodable BT.{0} where
  prim := _
```

The `prim` field requires `Nat.Primrec` of the
encode-decode round-trip.  Use `encodeBT_primrec`.

- [ ] **Step 6: Build and verify**

Run: `lake build GebLean.LawvereBTPrimrec`

- [ ] **Step 7: Commit**

```bash
git add GebLean/LawvereBTPrimrec.lean
git commit -m "feat: Primcodable instance for BT"
```

---

### Task 3: BT.fold preserves Primrec

**Files:**

- Modify: `GebLean/LawvereBTPrimrec.lean`

- [ ] **Step 1: State the theorem**

```lean
/-- `BT.fold` with primitive recursive base
and step produces a primitive recursive
function. -/
theorem bt_fold_primrec
    {b : BT.{0}} {s : BT.{0} -> BT.{0} ->
      BT.{0}}
    (hs : Primrec2 s) :
    Primrec (BT.fold b s) := by
  _
```

Note: `b` is a constant (always Primrec), so
we don't need a separate hypothesis for it.
`s` needs to be Primrec2.

- [ ] **Step 2: Prove using `Primrec.nat_omega_rec'`**

Apply `Primrec.nat_omega_rec'` from
`Mathlib.Computability.Primrec.List` with:

- `f := BT.fold b s` (the function to show is
  Primrec)
- `m := fun bt => Encodable.encode bt` (the
  measure -- encoding size)
- `l := fun bt => match bt with | BT.leaf => []
  | BT.node l r => [l, r]` (the children list)
- `g := fun bt results => match bt, results with
  | BT.leaf, [] => some b
  | BT.node _ _, [vl, vr] => some (s vl vr)
  | _, _ => none` (the recombination function)

**Proof obligations:**

1. `Primrec m`: encoding is Primrec (from Task 2)
2. `Primrec l`: children-list function is Primrec
   (case analysis on the encoding, using
   `Nat.unpair`)
3. `Primrec2 g`: recombination is Primrec (case
   analysis + `hs`)
4. `Ord`: children have smaller measure. Show
   `Encodable.encode l < Encodable.encode
   (BT.node l r)` and similarly for `r`.  This
   follows from `Nat.pair` properties:
   `Nat.left_lt_pair` and `Nat.right_lt_pair`
   (or similar).
5. `H`: `g bt ((l bt).map (BT.fold b s)) =
   some (BT.fold b s bt)`.  Verify by cases on
   `bt` using `BT.fold_leaf` and `BT.fold_node`.

Factor out each proof obligation as a separate
`have` or private lemma.

- [ ] **Step 3: Build and verify**

Run: `lake build GebLean.LawvereBTPrimrec`

- [ ] **Step 4: Commit**

```bash
git add GebLean/LawvereBTPrimrec.lean
git commit -m "feat: BT.fold preserves Primrec"
```

---

### Task 4: interpU computes Primrec functions

**Files:**

- Modify: `GebLean/LawvereBTPrimrec.lean`

- [ ] **Step 1: State the unary version (arity 1)**

```lean
/-- Every `BTMor1 1` term computes a primitive
recursive function `BT -> BT`. -/
theorem interpU_unary_primrec
    (t : BTMor1 1) :
    Primrec (fun bt : BT.{0} =>
      t.interpU (fun _ => bt)) := by
  _
```

- [ ] **Step 2: Prove by BTMor1.ind on t**

Use `BTMor1.ind` with a motive that tracks
primitive recursiveness.

A simpler approach: prove the arity-1 case
directly using the interpU computation lemmas:

- `proj 0`: `interpU_proj` gives `fun bt => bt`
  (identity, Primrec)
- `leaf`: `interpU_leaf` gives `fun _ => BT.leaf`
  (constant, Primrec)
- `branch l r`: `interpU_branch` gives
  `fun bt => BT.node (l.interpU ...) (r.interpU
  ...)` (Primrec by IH + `Primrec2` of
  `BT.node`)
- `fold m f g tree j`: `interpU_fold` gives
  `fun bt => BT.fold base step (tree.interpU ...)
  j` where `base` and `step` are assembled from
  `f` and `g`.  Primrec by IH + Task 3
  (`bt_fold_primrec`).

The fold case is the key: it uses `bt_fold_primrec`
from Task 3.

For the general arity version (Fin n -> BT), the
context `Fin n -> BT` needs a Primcodable instance.
This can be derived from `Primcodable BT` (Task 2)
and `Primcodable (Fin n -> BT)` (from
`Primcodable.finArrow` or similar in mathlib).
Check if this instance exists; if not, it may need
to be constructed.

Factor out the fold case as a separate lemma if
it is large.

**Note on PolyFix representation:** The
`BTMor1.ind` step function receives PolyFix.mk
forms.  Use the `polyFixMk_eq_proj/leaf/branch/fold`
conversion lemmas (from `LawvereBT.lean`) to
convert to named constructors, then apply the
interpU computation lemmas.  Follow the pattern
used in `interpU_complete` (double match +
conversion).

- [ ] **Step 3: Build and verify**

Run: `lake build GebLean.LawvereBTPrimrec`

- [ ] **Step 4: Commit**

```bash
git add GebLean/LawvereBTPrimrec.lean
git commit -m "feat: interpU computes Primrec functions"
```

---

### Task 5: Non-fullness of interpFunctor

**Files:**

- Modify: `GebLean/LawvereBTPrimrec.lean`

- [ ] **Step 1: Define the Ackermann-on-BT function**

```lean
/-- The Ackermann function transported to
binary trees via the Goedel encoding. -/
def ackOnBT : BT.{0} -> BT.{0} :=
  fun bt => decodeBT
    (ack (encodeBT bt) (encodeBT bt))
```

- [ ] **Step 2: Prove `ackOnBT` is not Primrec**

```lean
theorem ackOnBT_not_primrec :
    ¬ Primrec ackOnBT := by
  intro h
  -- If ackOnBT is Primrec, then
  -- fun n => ack n n is Primrec (compose
  -- with encode/decode which are Primrec).
  have : Primrec (fun n : Nat =>
      ack n n) := by
    _  -- compose h with encodeBT, decodeBT
  exact not_nat_primrec_ack_self
    (Primrec.nat_iff.mp this)
```

The reasoning: if
`ackOnBT = decodeBT . (fun n => ack n n)
. encodeBT` is Primrec, and both `encodeBT` and
`decodeBT` are Primrec (with Primrec inverses),
then `fun n => ack n n` is Primrec.  But
`not_nat_primrec_ack_self` (from
`Mathlib.Computability.Ackermann`) says it is not.

- [ ] **Step 3: Build and verify**

Run: `lake build GebLean.LawvereBTPrimrec`

- [ ] **Step 4: State and prove non-fullness**

```lean
/-- The interpretation functor from the Lawvere
theory of parameterized binary tree objects into
`Type` is not full.  The Ackermann function
(transported to binary trees) is a computable
function `BT -> BT` that is not in the image of
any morphism in the Lawvere theory, since
all such morphisms compute primitive recursive
functions. -/
theorem interpFunctor_not_full :
    ¬ interpFunctor.{0}.Full := by
  intro hfull
  have hmor := hfull.map_surjective
    (fun (ctx : Fin 1 -> BT.{0}) =>
      (fun (_ : Fin 1) =>
        ackOnBT (ctx 0)))
  obtain ⟨f, hf⟩ := hmor
  have hprim : Primrec ackOnBT := by
    _  -- extract from f, hf, and
       -- interpU_unary_primrec
  exact ackOnBT_not_primrec hprim
```

The extraction step requires:

1. `f : LawvereBTQuotCat.Hom 1 1`
   (a quotient morphism)
2. `hf : interpFunctor.map f = (fun ctx =>
   fun _ => ackOnBT (ctx 0))`
3. Lift `f` through the quotient to get
   `f_raw : BTMorN 1 1` (a tuple of BTMor1 1)
4. `f_raw 0 : BTMor1 1` is the component
5. By `interpU_unary_primrec (f_raw 0)`:
   the function is Primrec
6. Use `hf` to show this function = `ackOnBT`
7. Contradiction

- [ ] **Step 5: Build and verify**

Run: `lake build GebLean.LawvereBTPrimrec`

- [ ] **Step 6: Run full build and tests**

Run: `lake build && lake test`
Expected: all pass, no warnings.

- [ ] **Step 7: Axiom check**

Create a temporary file to check axioms:

```lean
-- in a temporary test
#print axioms GebLean.interpFunctor_not_full
```

Expected: only `propext`, `Classical.choice`,
`Quot.sound` (standard axioms).

- [ ] **Step 8: Commit**

```bash
git add GebLean/LawvereBTPrimrec.lean
git commit -m \
  "feat: non-fullness of BT interpretation"
```

---

## Risk Assessment

| Phase | Risk | Mitigation |
|-------|------|------------|
| Task 1 | Low | Standard encoding |
| Task 2 | Medium | May need custom proof |
| Task 3 | Medium-High | `nat_omega_rec'` setup |
| Task 4 | Medium | PolyFix conversion |
| Task 5 | Low | Direct from mathlib |

**Highest risk**: Task 3 (connecting BT.fold to
`nat_omega_rec'`).  If `nat_omega_rec'` is
hard to apply, an alternative is to inline the
course-of-values recursion proof directly using
`Nat.Primrec.prec` and the BT encoding structure.

**Total estimate**: ~650-850 lines of Lean code
across all tasks.
