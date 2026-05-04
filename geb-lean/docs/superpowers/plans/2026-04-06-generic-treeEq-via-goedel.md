# Generic treeEq via Goedel Encoding

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Define a generic `treeEq : cfpProd p.T p.T ⟶ p.T`
for any `HasPBTO` category using only `p.elim` with
tree-valued carriers (no function types, no `IsSeparator`,
no `HasBoolDichotomy`), via Goedel encoding of trees as
unary nats + nat comparison.  Prove computation rules
(`treeEq_ℓℓ`, `treeEq_ℓβ`, `treeEq_βℓ`, `treeEq_ββ`) and
PER properties (`treeEq_bool`, `treeEq_refl`, `treeEq_symm`,
`treeEq_trans`).

**Architecture:** Encode each tree as a unary natural number
(right-spine tree) via Cantor pairing, compare nats via
truncated subtraction.  The construction uses `p.elim` with
carriers `p.T` and `cfpProd p.T p.T` (for triangular
numbers).  The `treeEq_ββ` computation rule follows from
Cantor-pairing injectivity.  Each layer (`natArith`,
`cantorPair`, `goedelEncode`, `treeEq`) exposes its own
universal-property interface so downstream code never
touches internals.  The existing iteration-based `treeEq`
in `TreeLogic.lean` is superseded and can be removed after
this construction is validated.

**Tech Stack:** Lean 4, `HasPBTO` / `p.elim` / `p.elim_uniq`
(`LawvereBT.lean`), `cfpProd` / `cfpLift` / `cfpMap`
(`Utilities/ComputableLimits.lean`), `boolAnd` / `isLeafEndo`
(`TreeLogic.lean`).

**Validated at BT level:** The function-mining experiment in
`TypePBTO.lean` (lines 932-1356) confirmed all definitions
compile and basic computation rules hold using only
`BT.fold` with carriers `BT` and `BT x BT`.  The
categorical translation replaces `BT.fold` with `p.elim`,
`BT.caseOn` with `treeIte`/`isLeafEndo`, and `BT.node`
with `p.beta`.

---

## File Structure

- **Create:** `GebLean/NatArith.lean` -- internal NNO
  arithmetic on right-spine nats: `natPred`, `natTri`,
  `cantorPair`, `natTruncSub`, `natEq`, with computation
  rules and key properties (Cantor-pairing injectivity).
  ~600-1000 lines.

- **Create:** `GebLean/TreeGoedel.lean` -- Goedel encoding
  `treeToNat : p.T ⟶ p.T`, its computation rules, and
  injectivity.  ~200-400 lines.

- **Create:** `GebLean/TreeEqGoedel.lean` -- the new
  `treeEqG : cfpProd p.T p.T ⟶ p.T` defined as
  `cfpMap treeToNat treeToNat ≫ natEq`, with all
  computation rules and PER properties.  ~300-500 lines.

- **Modify:** `GebLean/TreePER.lean` -- update `HasTreeEq`
  to use the new generic `treeEqG` (or provide a generic
  instance).

- **Modify:** `GebLean.lean` -- add imports for new modules.

The existing `TreeLogic.lean` is NOT modified in this plan.
The iteration-based `treeEq` stays as-is until the new one
is fully validated, at which point a separate cleanup task
removes the superseded code.

---

## Task 1: natPred and natTruncSub

**Files:**

- Create: `GebLean/NatArith.lean`

### Step 1: File skeleton and natPred

- [ ] Create `GebLean/NatArith.lean` with imports,
  namespace, universe/variable declarations matching
  `TreeLogic.lean` style.

- [ ] Define `natPred : p.T ⟶ p.T` as `treeRightEndo`
  (predecessor on right-spine nats: `pred(leaf) = leaf`,
  `pred(branch(_, n)) = n`).

- [ ] Prove `natPred_ℓ : p.ℓ ≫ natPred = p.ℓ` (zero
  maps to zero).  Uses `ℓ_treeRightEndo` from
  `TreeLogic.lean`.

- [ ] Prove `natPred_natSucc : natSucc ≫ natPred = 𝟙 p.T`
  (pred of succ is identity).  Uses `β_treeRightEndo` and
  `cfpLift_snd`.

- [ ] Run `lake build` to verify.

### Step 2: natTruncSub

- [ ] Define `natTruncSub : cfpProd p.T p.T ⟶ p.T` as
  `p.elim (𝟙 p.T) (cfpSnd p.T p.T ≫ natPred)`.  This
  folds on the second argument (the subtrahend), applying
  `natPred` to the accumulator (the minuend) at each
  successor step.  Semantics: `natTruncSub(n, m)` returns
  `n - m` (truncated at zero).

- [ ] Prove `natTruncSub_ℓ`:
  `cfpInsertSnd p.ℓ p.T ≫ natTruncSub = 𝟙 p.T`
  (subtracting zero gives the original).

- [ ] Prove `natTruncSub_β`:
  `cfpMap (𝟙 p.T) p.β ≫ natTruncSub =
   cfpLiftAssoc natTruncSub natTruncSub ≫
     (cfpSnd p.T p.T ≫ natPred)` (the step equation).

- [ ] Prove `natTruncSub_self : cfpLift (𝟙 p.T) (𝟙 p.T) ≫
  natTruncSub = cfpTerminalFrom p.T ≫ p.ℓ` (self-
  subtraction is zero).  This requires `p.elim_uniq`: show
  `cfpLift (𝟙 p.T) (𝟙 p.T) ≫ natTruncSub` satisfies
  the same base/step as the constant-leaf morphism.

- [ ] Run `lake build` to verify.

### Step 3: natEq

- [ ] Define `natEq : cfpProd p.T p.T ⟶ p.T` as
  `cfpLift
    (natTruncSub)
    (cfpSwap p.T p.T ≫ natTruncSub) ≫
   natPlus ≫ isLeafEndo`.
  Semantics: `natEq(m, n) = isLeafEndo(|m - n|)` where
  `|m - n| = (m ∸ n) + (n ∸ m)`.

- [ ] Prove `natEq_refl : cfpLift (𝟙 p.T) (𝟙 p.T) ≫
  natEq = cfpTerminalFrom p.T ≫ p.ℓ` (reflexivity).
  Uses `natTruncSub_self` + `natPlus_ℓℓ` + `isLeafEndo_ℓ`.

- [ ] Prove `natEq_bool : natEq ≫ isLeafEndo = natEq`
  (Boolean-valued).  Uses `isLeafEndo_idem`.

- [ ] Prove `natEq_symm : cfpSwap p.T p.T ≫ natEq = natEq`
  (symmetry).  The definition is manifestly symmetric
  because swapping the two `natTruncSub` arguments inside
  `natPlus` doesn't change the sum (via `natPlus_comm` if
  available, or by direct argument).

  NOTE: `natPlus` commutativity on unary nats may need a
  separate proof.  Unlike general `natPlus` on arbitrary
  trees (which isn't commutative), `natPlus` on RIGHT-SPINE
  nats IS commutative.  This can be proved via `p.elim_uniq`
  by showing both orderings satisfy the same recursion.
  Alternatively, use the `boolAnd_comm`-style trick:
  `natPlus` on right-spine nats = `p.elim` with a specific
  base/step, and swapping arguments gives the same `p.elim`.

- [ ] Run `lake build` to verify.

### Step 4: Build, verify, commit

```bash
lake build && lake test
```

- [ ] Add `import GebLean.NatArith` to `GebLean.lean`.

- [ ] Run `lake build` to verify full project.

---

## Task 2: Triangular Numbers and Cantor Pairing

**Files:**

- Modify: `GebLean/NatArith.lean`

### Step 1: natTri (triangular numbers)

- [ ] Define `natTri : p.T ⟶ p.T` via `p.elim` with
  carrier `cfpProd p.T p.T` (a paramorphism tracking
  `(currentIndex, runningSum)`).  Base: `(leaf, leaf)` =
  `(0, 0)`.  Step: `((iL, sL), (iR, sR)) ↦
  (natSucc(iR), natPlus(natSucc(iR), sR))`.  Project
  second component for the final result.

  Concretely:
  ```
  natTriHelper : cfpProd cfpTerminal p.T ⟶
      cfpProd p.T p.T :=
    p.elim
      (cfpLift p.ℓ p.ℓ)
      (cfpLift
        (cfpSnd p.T p.T ≫ cfpFst p.T p.T ≫ natSucc)
        (cfpLift
          (cfpSnd p.T p.T ≫ cfpFst p.T p.T ≫ natSucc)
          (cfpSnd p.T p.T ≫ cfpSnd p.T p.T) ≫
          natPlus))
  natTri : p.T ⟶ p.T :=
    cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
      natTriHelper ≫ cfpSnd p.T p.T
  ```

- [ ] Prove `natTri_ℓ : p.ℓ ≫ natTri = p.ℓ`
  (tri(0) = 0).

- [ ] Prove `natTri_natSucc`:
  `natSucc ≫ natTri = cfpLift natTri natSucc ≫ natPlus`
  (tri(n+1) = tri(n) + (n+1)).  This requires relating
  the helper's step to the triangular-number recurrence.

- [ ] Run `lake build` to verify.

### Step 2: cantorPair

- [ ] Define `cantorPair : cfpProd p.T p.T ⟶ p.T` as
  `cfpLift (cfpLift (cfpFst p.T p.T) (cfpSnd p.T p.T) ≫
    natPlus ≫ natTri) (cfpFst p.T p.T) ≫ natPlus`.
  Semantics: `cantorPair(m, n) = tri(m + n) + m`.

- [ ] Prove `cantorPair` computation rules at specific
  values (e.g., `cantorPair(0, 0) = 0`,
  `cantorPair(1, 0) = 1`, `cantorPair(0, 1) = 1`)
  as sanity checks.

- [ ] Run `lake build` to verify.

### Step 3: Cantor-pairing injectivity

- [ ] Prove `cantorPair_injective`:
  `cfpLift (cfpLift a b ≫ cantorPair)
           (cfpLift c d ≫ cantorPair) ≫ natEq =
   cfpLift (cfpLift a c ≫ natEq)
           (cfpLift b d ≫ natEq) ≫ boolAnd`.
  Semantics: `cantorPair(a,b) = cantorPair(c,d)` iff
  `a = c` AND `b = d`.

  This is the KEY LEMMA for `treeEq_ββ`.  The proof uses
  the algebraic properties of `natTri` and `natPlus`.
  Specifically: `cantorPair(a,b) = cantorPair(c,d)` iff
  `tri(a+b) + a = tri(c+d) + c`.  By the standard
  Cantor-pairing injectivity argument (involving the
  triangular-number gap), this implies `a+b = c+d` AND
  `a = c`, hence `b = d`.

  The categorical proof uses `p.elim_uniq` and the
  computation rules of `natTri`, `natPlus`, and `natEq`.

  NOTE: This is the hardest proof in the plan.  The
  BT-level version in `TypePBTO.lean` proves this for
  specific BT values via structural induction on naturals.
  The categorical version must use `p.elim_uniq` instead.
  If this proof exceeds ~400 lines, consider proving it
  for `LawvereBTQuotCat` specifically (via `interpFunctor`)
  and deferring the fully generic version.

- [ ] Run `lake build` to verify.

### Step 4: Build, verify, commit

```bash
lake build && lake test
```

---

## Task 3: Goedel Encoding

**Files:**

- Create: `GebLean/TreeGoedel.lean`

### Step 1: treeToNat

- [ ] Create `GebLean/TreeGoedel.lean` with imports from
  `NatArith.lean`.

- [ ] Define `treeToNat : p.T ⟶ p.T` as
  `cfpLift (cfpTerminalFrom p.T) (𝟙 p.T) ≫
   p.elim p.ℓ (cantorPair ≫ natSucc)`.
  Semantics: `treeToNat(leaf) = 0`,
  `treeToNat(branch(l, r)) =
    succ(cantorPair(treeToNat(l), treeToNat(r)))`.

- [ ] Prove `treeToNat_ℓ : p.ℓ ≫ treeToNat = p.ℓ`
  (leaf encodes to zero).

- [ ] Prove `treeToNat_β`:
  `p.β ≫ treeToNat = cfpMap treeToNat treeToNat ≫
    cantorPair ≫ natSucc`
  (branch encodes via Cantor pairing + successor).

- [ ] Run `lake build` to verify.

### Step 2: treeToNat injectivity

- [ ] Prove `treeToNat_injective`:
  `cfpMap treeToNat treeToNat ≫ natEq = treeEqG`
  where `treeEqG` is defined in the next task.
  Alternatively, prove the component-wise injectivity:
  `cfpLift (a ≫ treeToNat) (b ≫ treeToNat) ≫ natEq =
   cfpLift a b ≫ treeEqG`.

  Actually, the injectivity proof is intertwined with the
  definition of `treeEqG`.  Defer this to Task 4 and
  prove the following intermediate instead:

- [ ] Prove `treeToNat_β_injective`:
  `cfpLift (p.β ≫ treeToNat) (p.β ≫ treeToNat) ≫ natEq =
   cfpLift
     (cfpMap treeToNat treeToNat ≫ cantorPair)
     (cfpMap treeToNat treeToNat ≫ cantorPair) ≫ natEq`.
  This relates equality of branch-encoded nats to equality
  of their Cantor-pair representations (canceling the
  shared `natSucc` on both sides).

- [ ] Run `lake build` to verify.

### Step 3: Build, verify, commit

```bash
lake build && lake test
```

- [ ] Add `import GebLean.TreeGoedel` to `GebLean.lean`.

---

## Task 4: treeEqG and Computation Rules

**Files:**

- Create: `GebLean/TreeEqGoedel.lean`

### Step 1: Definition

- [ ] Create `GebLean/TreeEqGoedel.lean`.

- [ ] Define `treeEqG : cfpProd p.T p.T ⟶ p.T` as
  `cfpMap treeToNat treeToNat ≫ natEq`.

### Step 2: Boolean-valuedness

- [ ] Prove `treeEqG_bool : treeEqG ≫ isLeafEndo =
  treeEqG`.  Uses `natEq_bool`.

### Step 3: Leaf computation rules

- [ ] Prove `treeEqG_ℓℓ`:
  `cfpLift p.ℓ p.ℓ ≫ treeEqG = p.ℓ`.
  Uses `treeToNat_ℓ` + `natEq_refl`.

- [ ] Prove `treeEqG_ℓβ`:
  `cfpLift (cfpTerminalFrom D ≫ p.ℓ)
    (cfpLift g1 g2 ≫ p.β) ≫ treeEqG =
   cfpTerminalFrom D ≫ treeFalse`.
  Uses `treeToNat_ℓ` + `treeToNat_β`:
  `treeToNat(leaf) = 0` and
  `treeToNat(branch(g1, g2)) = succ(something)`.
  So `natEq(0, succ(k)) = treeFalse` because
  `natTruncSub(succ(k), 0) = succ(k) ≠ 0`.

- [ ] Prove `treeEqG_βℓ`: symmetric to `treeEqG_ℓβ`.

### Step 4: Branch-branch computation rule (the prize)

- [ ] Prove `treeEqG_ββ`:
  `cfpMap p.β p.β ≫ treeEqG =
   cfpLift
     (cfpLift (cfpFst _ _ ≫ cfpFst p.T p.T)
              (cfpSnd _ _ ≫ cfpFst p.T p.T) ≫ treeEqG)
     (cfpLift (cfpFst _ _ ≫ cfpSnd p.T p.T)
              (cfpSnd _ _ ≫ cfpSnd p.T p.T) ≫ treeEqG)
   ≫ boolAnd`.

  Proof outline:
  1. Unfold both sides via `treeToNat_β`:
     `treeToNat(β(a, b)) = natSucc(cantorPair(enc(a), enc(b)))`.
  2. LHS becomes:
     `natEq(succ(cantorPair(enc(a), enc(b))),
            succ(cantorPair(enc(c), enc(d))))`.
  3. Cancel the `succ` on both sides:
     `= natEq(cantorPair(enc(a), enc(b)),
              cantorPair(enc(c), enc(d)))`.
     (Prove `natEq(succ(m), succ(n)) = natEq(m, n)` as a
     helper lemma.)
  4. Apply `cantorPair_injective`:
     `= boolAnd(natEq(enc(a), enc(c)),
                natEq(enc(b), enc(d)))`.
  5. Refold: `natEq(enc(a), enc(c)) = treeEqG(a, c)` and
     `natEq(enc(b), enc(d)) = treeEqG(b, d)`.
  6. Result: `boolAnd(treeEqG(a, c), treeEqG(b, d))`. QED.

- [ ] Run `lake build` to verify.

### Step 5: Build, verify, commit

```bash
lake build && lake test
```

- [ ] Add `import GebLean.TreeEqGoedel` to `GebLean.lean`.

---

## Task 5: PER Properties of treeEqG

**Files:**

- Modify: `GebLean/TreeEqGoedel.lean`

### Step 1: Reflexivity

- [ ] Prove `treeEqG_refl`:
  `cfpLift (𝟙 p.T) (𝟙 p.T) ≫ treeEqG =
   cfpTerminalFrom p.T ≫ p.ℓ`.
  Proof: `cfpLift (𝟙 p.T) (𝟙 p.T) ≫
    cfpMap treeToNat treeToNat ≫ natEq
    = cfpLift treeToNat treeToNat ≫ natEq`
    (since `cfpMap f f` applied to the diagonal gives
    `cfpLift f f`).  Then `cfpLift treeToNat treeToNat ≫
    natEq = cfpLift (𝟙 p.T) (𝟙 p.T) ≫ natEq ∘ something
    ... actually simpler:
    `cfpLift (𝟙 ≫ treeToNat) (𝟙 ≫ treeToNat) ≫ natEq
    = cfpLift treeToNat treeToNat ≫ natEq`
    and the diagonal means both components are equal, so
    `natEq_refl` applies (via pre-composition with
    `treeToNat`).

### Step 2: Symmetry

- [ ] Prove `treeEqG_symm`:
  `cfpSwap p.T p.T ≫ treeEqG = treeEqG`.
  Proof: `cfpSwap ≫ cfpMap treeToNat treeToNat ≫ natEq
    = cfpMap treeToNat treeToNat ≫ cfpSwap ≫ natEq`
    (swapping commutes with `cfpMap f f`), then
    `cfpSwap ≫ natEq = natEq` by `natEq_symm`.

### Step 3: Transitivity

- [ ] Prove `treeEqG_trans : EqTransitive treeEqG`.
  This requires showing the `boolAnd`-implication equation
  for transitivity.  The proof uses:
  1. `QuantTransitive treeEqG` at the Prop level: if
     `treeEqG(a, b) = ℓ` and `treeEqG(b, c) = ℓ`, then
     `treeEqG(a, c) = ℓ`.  This follows from:
     `treeToNat(a) = treeToNat(b)` (as nats) and
     `treeToNat(b) = treeToNat(c)` implies
     `treeToNat(a) = treeToNat(c)` (transitivity of
     nat equality).
  2. `quantTransitive_implies_eq` to convert Prop-level
     to equational.  NOTE: this step uses `IsSeparator` +
     `HasBoolDichotomy`.  If we want to avoid these,
     prove equational transitivity directly using the
     `boolAnd_eq_elim` / `elim_uniq` techniques.

  If the fully-generic proof is too hard, parameterize
  by `IsSeparator` + `HasBoolDichotomy` (matching the
  existing `TreePERLimits.lean` pattern) and note this
  as a future simplification target.

- [ ] Run `lake build` to verify.

### Step 4: Build, verify, commit

```bash
lake build && lake test
```

---

## Task 6: HasTreeEq Instance and Integration

**Files:**

- Modify: `GebLean/TreeEqGoedel.lean`
- Modify: `GebLean/TreePER.lean` (if needed)
- Modify: `GebLean/TreePERLawvereBT.lean`

### Step 1: Generic HasTreeEq

- [ ] Define `hasTreeEqGoedel : HasTreeEq C` (or
  parameterized by `IsSeparator` + `HasBoolDichotomy` if
  Task 5's transitivity requires them) using `treeEqG`
  and all the proved properties.

  If fully generic (no extra hypotheses):
  ```
  def hasTreeEqGoedel : HasTreeEq C where
    treeEq := treeEqG
    treeEq_bool := treeEqG_bool
    treeEq_refl := treeEqG_refl
    treeEq_symm := treeEqG_symm
    treeEq_trans := treeEqG_trans
    treeEq_ℓℓ := treeEqG_ℓℓ
    treeEq_ℓβ := treeEqG_ℓβ  -- may need form adaptation
    treeEq_βℓ := treeEqG_βℓ
    treeEq_ββ := treeEqG_ββ
  ```

  NOTE: The `HasTreeEq` field signatures (in
  `TreePER.lean` line 307+) use `cfpMap p.ℓ p.β` etc.,
  not `cfpLift (cfpTerminalFrom D ≫ p.ℓ) ...`.  Verify
  the signatures match or adapt the proofs.

### Step 2: LawvereBTQuotCat instance

- [ ] Add to `TreePERLawvereBT.lean`:
  ```
  def lawvereBTQuotCat_hasTreeEq :
      HasTreeEq LawvereBTQuotCat :=
    hasTreeEqGoedel  -- or with hSep hBD if needed
  ```

### Step 3: Build, verify, commit

```bash
lake build && lake test
```

---

## Dependencies

```text
Task 1 (natPred, natTruncSub, natEq)
  └── Task 2 (natTri, cantorPair, injectivity)
        └── Task 3 (treeToNat, encoding)
              └── Task 4 (treeEqG, computation rules)
                    └── Task 5 (PER properties)
                          └── Task 6 (HasTreeEq, integration)
```

Tasks are strictly sequential.

---

## Risk Assessment

### High confidence

- Tasks 1, 3, 4 (steps 1-3): definitions and leaf
  computation rules are mechanical translations from the
  BT-level implementations in `TypePBTO.lean`.

### Medium confidence

- Task 2 Step 1 (natTri): the paramorphism carrier
  `cfpProd p.T p.T` requires careful `cfpLift`/`cfpMap`
  plumbing at the categorical level.

- Task 4 Step 4 (treeEqG_ββ): depends on
  `cantorPair_injective` + `natEq_succ_cancel`.  The
  proof structure is clear but the equational plumbing
  may be substantial.

- Task 5 Step 2 (symmetry): depends on `natEq_symm`,
  which depends on `natPlus` commutativity on right-spine
  nats.  May require a separate lemma.

### Research frontier

- Task 2 Step 3 (cantorPair_injective): the categorical
  proof of Cantor-pairing injectivity from `p.elim_uniq`
  is non-trivial.  The BT-level proof uses structural
  induction on natural numbers.  The categorical version
  needs `p.elim_uniq` on the right-spine-nat sub-type.
  Estimated 200-400 lines for this single lemma.

- Task 5 Step 3 (transitivity): if the generic version
  requires `IsSeparator` + `HasBoolDichotomy`, this is
  acceptable (matches the existing PER construction
  pattern).  If we find a way to avoid them (via the
  `boolAnd_eq_elim` technique), that's a bonus.
