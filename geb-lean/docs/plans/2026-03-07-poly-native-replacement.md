# Polynomial Native Type Replacement Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans
> to implement this plan task-by-task.

**Goal:** Replace all Lean-native inductive types, structures, and
recursive type definitions in `PolyAlg.lean` (other than `PolyFix`
itself) with polynomial versions defined as `PolyFix` of appropriate
`PolyEndo`s, and prove them isomorphic.

**Architecture:** For each native Lean type `T : B → Type u`, we:

1. Identify the base type `B` that the type family is indexed over.
   When a type has multiple indices (e.g. `Nat → X → Type`), we
   uncurry to a single index type (e.g. `Nat × X`).  The
   equivalence `familySliceEquiv` witnesses that families of types
   over `B` correspond to objects of `Over B`.
2. Define a polynomial endofunctor `P_T : PolyEndo B` whose
   constructors at each base point `b : B` match those of `T b`.
   Each constructor becomes a position (index) of the polynomial;
   each recursive argument becomes a child in the family.
   Non-recursive types use empty families.
3. Prove `PolyFix P_T b ≅ T b` by writing maps in both directions
   and showing they compose to the identity.

For `Prop`-valued types, we produce a `Type`-valued `PolyFix` and
quotient by `trueSetoid` to obtain a subsingleton, then show
logical equivalence with the `Prop` version.  See
`Quotient.trueSetoid_subsingleton` in `SetoidCat.lean`,
`DepCategoryData.truncateWitnesses` in `DepCategoryAdjunction.lean`,
and `Skeleton.lean` (with its use in `Polynomial.lean` line 3273)
for examples.

**Tech Stack:** Lean 4, mathlib (`CategoryTheory.Over`,
`Endofunctor.Algebra`)

---

## Task 1: PolyCofixApprox (line 645)

**Dependency:** None (depends only on `PolyEndo` infrastructure).

**Base type:** `Nat × X`

**Lean definition:**

```lean
inductive PolyCofixApprox (P : PolyEndo X) : Nat → X → Type u where
  | continue : (x : X) → PolyCofixApprox P 0 x
  | intro {n : Nat} (x : X) (i : polyBetweenIndex X X P x)
      (children : ∀ (e : (polyBetweenFamily X X P x i).left),
        PolyCofixApprox P n ((polyBetweenFamily X X P x i).hom e)) :
      PolyCofixApprox P (n + 1) x
```

**Polynomial definition:**

```lean
def polyCofixApproxPoly (P : PolyEndo X) : PolyEndo (Nat × X) :=
  fun ⟨n, x⟩ => match n with
  | 0 => ccrObjMk (fun (_ : PUnit) =>
      overEmpty (Nat × X))
  | n + 1 => ccrObjMk
      (fun (i : polyBetweenIndex X X P x) =>
        Over.mk (f := fun (e : (polyBetweenFamily X X P x i).left) =>
          (n, (polyBetweenFamily X X P x i).hom e)))
```

At base point `(0, x)`:

- One position (`PUnit`), no children (empty family).
- Corresponds to the `continue` constructor.

At base point `(n + 1, x)`:

- Positions: `polyBetweenIndex X X P x` (the polynomial's index at `x`).
- At position `i`, children indexed by
  `(polyBetweenFamily X X P x i).left`, each mapping to
  `(n, (polyBetweenFamily X X P x i).hom e)`.
- Corresponds to the `intro` constructor.

**Isomorphism:** `PolyFix (polyCofixApproxPoly P) (n, x) ≅ PolyCofixApprox P n x`

- Forward: structural recursion on `PolyFix`, matching the `PUnit`
  index at depth 0 to `continue`, and `polyBetweenIndex` at
  depth `n + 1` to `intro`.
- Backward: structural recursion on `PolyCofixApprox`, mapping
  `continue` to `PolyFix.mk _ PUnit.unit (PEmpty.elim ·)`,
  and `intro` to `PolyFix.mk _ i (fun e => rec (children e))`.

**Files:**

- Modify: `GebLean/PolyAlg.lean` (insert definitions after line 644,
  before the current `PolyCofixApprox`)

**Steps:**

1. Define `polyCofixApproxPoly`.
2. Build with `lake build` to confirm the definition compiles.
3. Define the forward map
   `polyCofixApproxFromPoly : PolyFix`
   `(polyCofixApproxPoly P) (n, x) → PolyCofixApprox P n x`.
4. Build.
5. Define the backward map
   `polyCofixApproxToPoly : PolyCofixApprox P n x →`
   `PolyFix (polyCofixApproxPoly P) (n, x)`.
6. Build.
7. Prove `polyCofixApproxFromPoly ∘ polyCofixApproxToPoly = id` (by
   induction on `PolyCofixApprox`).
8. Build.
9. Prove `polyCofixApproxToPoly ∘ polyCofixApproxFromPoly = id` (by
   induction on `PolyFix`).
10. Build.
11. Package into an equivalence/isomorphism.
12. Build and test (`lake build && lake test`).
13. Commit.

---

## Task 2: PolyCofixAgree (line 677)

**Dependency:** Task 1 (PolyCofixApprox).

**Base type:**
`Σ (n : Nat) (x : X), PolyCofixApprox P n x × PolyCofixApprox P (n + 1) x`

(Once Task 1 is done, the polynomial version would use `PolyFix
(polyCofixApproxPoly P)` in place of `PolyCofixApprox`.)

**Lean definition:**

```lean
inductive PolyCofixAgree (P : PolyEndo X) :
    {n : Nat} → {x : X} →
    PolyCofixApprox P n x → PolyCofixApprox P (n + 1) x → Prop where
  | continue (x : X) (y : PolyCofixApprox P 1 x) :
      PolyCofixAgree P (.continue x) y
  | intro {n : Nat} {x : X} {i : polyBetweenIndex X X P x}
      (f : ∀ e, PolyCofixApprox P n (...))
      (f' : ∀ e, PolyCofixApprox P (n + 1) (...))
      (h : ∀ e, PolyCofixAgree P (f e) (f' e)) :
      PolyCofixAgree P (.intro x i f) (.intro x i f')
```

**Polynomial definition:**

Let `B_agree P` be the base type above.  The polynomial
`polyCofixAgreePoly P : PolyEndo (B_agree P)` is defined by case
analysis on the pair of approximations at each base point:

At `⟨0, x, continue x, y⟩` (any `y : Approx 1 x`):

- One position (`PUnit`), no children.
- Corresponds to `continue`.

At `⟨n + 1, x, intro x i f, intro x i f'⟩` (matching indices `i`):

- One position (`PUnit`), children indexed by
  `(polyBetweenFamily X X P x i).left`.
- Child at `e` maps to
  `⟨n, fiber e, f e, f' e⟩`.
- Corresponds to `intro`.

At all other base points (mismatched constructors or indices):

- Empty index (`PEmpty`), so `PolyFix` is uninhabited there.

Since `PolyCofixAgree` is `Prop`-valued, the `Type`-valued
`PolyFix` should be quotiented via `trueSetoid` to produce a
subsingleton, then shown logically equivalent to the `Prop` version.

**Steps:**

1. Define the base type `B_agree`.
2. Define `polyCofixAgreePoly`.
3. Build.
4. Define forward and backward maps.
5. Build after each.
6. Prove roundtrip properties.
7. Apply `trueSetoid` quotient for the subsingleton property.
8. Build and test.
9. Commit.

---

## Task 3: PolyCofix (line 783)

**Dependency:** Tasks 1 and 2.

**Nature:** This is a dependent record (structure), not an inductive
type.  It combines `∀ n, PolyCofixApprox P n x` with
`∀ n, PolyCofixAgree P (approx n) (approx (n + 1))`.

This cannot be expressed as a `PolyFix` because it involves an
infinite product (`∀ n`).  The task is to redefine `PolyCofix` so
that its fields reference the polynomial versions of
`PolyCofixApprox` and `PolyCofixAgree` (from Tasks 1 and 2)
instead of the Lean-native versions.

**Steps:**

1. Define `PolyCofix'` using polynomial components:
   `approx : ∀ n, PolyFix (polyCofixApproxPoly P) (n, x)` and
   `consistent` using the polynomial agree type.
2. Build.
3. Prove `PolyCofix' P x ≅ PolyCofix P x` using the isomorphisms
   from Tasks 1 and 2.
4. Build and test.
5. Commit.

---

## Task 4: PolyFreeMLeafPos (line 3612)

**Dependency:** None beyond `PolyFix` and `polyTranslate`.

**Base type:** `Σ x, PolyFreeMShape P x`

(where `PolyFreeMShape P x = PolyFreeM (overTerminal X) P x =
PolyFix (polyTranslate (overTerminal X) P) x`)

**Lean definition:**

```lean
def PolyFreeMLeafPos (P : PolyEndo X) {x : X} :
    PolyFreeMShape P x → Type u
  | PolyFix.mk _ (Sum.inl _) _ => PUnit
  | PolyFix.mk _ (Sum.inr p) children =>
    Σ (e : (polyBetweenFamily X X P x p).left),
      PolyFreeMLeafPos P (children e)
```

**Polynomial definition:**

```lean
def polyFreeMLeafPosPoly (P : PolyEndo X) :
    PolyEndo (Σ x, PolyFreeMShape P x) :=
  fun ⟨x, t⟩ => match t with
  | PolyFix.mk _ (Sum.inl _) _ =>
    ccrObjMk (fun (_ : PUnit) =>
      overEmpty (Σ x, PolyFreeMShape P x))
  | PolyFix.mk _ (Sum.inr p) children =>
    ccrObjMk
      (fun (e : (polyBetweenFamily X X P x p).left) =>
        Over.mk (f := fun (_ : PUnit) =>
          ⟨(polyBetweenFamily X X P x p).hom e, children e⟩))
```

At a leaf `(x, mk _ (inl a) _)`:

- One position (`PUnit`), no children. Single element = `PUnit`.

At an internal node `(x, mk _ (inr p) children)`:

- Positions: `(polyBetweenFamily X X P x p).left` (pick a child).
- At position `e`: one child (`PUnit`-indexed), mapping to
  `⟨fiber e, children e⟩`.
- This is a list/path: each node picks one child edge and continues.

**Steps:**

1. Define `polyFreeMLeafPosPoly`.
2. Build.
3. Define forward and backward maps.
4. Build after each.
5. Prove roundtrip.
6. Build and test.
7. Commit.

---

## Task 5: PolyCofreePathSeg (line 3979)

**Dependency:** None beyond `PolyEndo` infrastructure.

**Base type:** `X`

**Lean definition:**

```lean
structure PolyCofreePathSeg (P : PolyEndo X) where
  fiber : X
  idx : polyBetweenIndex X X P fiber
  childIdx : (polyBetweenFamily X X P fiber idx).left
```

This is a non-recursive sigma type.  As a `PolyFix`, it is a
single-layer tree with no recursive children.

**Polynomial definition:**

```lean
def polyCofreePathSegPoly (P : PolyEndo X) : PolyEndo X :=
  fun x => ccrObjMk
    (fun (i : Σ (idx : polyBetweenIndex X X P x),
              (polyBetweenFamily X X P x idx).left) =>
      overEmpty X)
```

At base point `x`:

- Positions:
  `Σ (idx : polyBetweenIndex X X P x), (polyBetweenFamily X X P x idx).left`.
- No children (empty family).
- `PolyFix` of this = just the index type (one-layer tree).

The isomorphism sends `PolyFix.mk x ⟨idx, childIdx⟩ _` to
`⟨x, idx, childIdx⟩` and vice versa.

**Steps:**

1. Define `polyCofreePathSegPoly`.
2. Build.
3. Define forward and backward maps.
4. Build after each.
5. Prove roundtrip (straightforward since no recursion).
6. Build and test.
7. Commit.

---

## Task 6: PolyCofreeAnnotPosAt (line 3989)

**Dependency:** Task 3 (PolyCofix, for `PolyCofreeShape`).

**Base type:** `Nat × (Σ x, PolyCofreeShape P x)`

**Lean definition:**

```lean
def PolyCofreeAnnotPosAt (P : PolyEndo X) {x : X}
    (s : PolyCofreeShape P x) : Nat → Type u
  | 0 => PUnit
  | n + 1 =>
    Σ (e : (polyBetweenFamily X X P x s.head.2).left),
      PolyCofreeAnnotPosAt P (s.children e) n
```

**Polynomial definition:**

```lean
def polyCofreeAnnotPosAtPoly (P : PolyEndo X) :
    PolyEndo (Nat × (Σ x, PolyCofreeShape P x)) :=
  fun ⟨n, x, s⟩ => match n with
  | 0 => ccrObjMk (fun (_ : PUnit) =>
      overEmpty (Nat × (Σ x, PolyCofreeShape P x)))
  | n + 1 => ccrObjMk
      (fun (e : (polyBetweenFamily X X P x s.head.2).left) =>
        Over.mk (f := fun (_ : PUnit) =>
          (n, ⟨(polyBetweenFamily X X P x s.head.2).hom e,
               s.children e⟩)))
```

At `(0, (x, s))`:

- One position (`PUnit`), no children.  Corresponds to `PUnit`.

At `(n + 1, (x, s))`:

- Positions: the child edge type
  `(polyBetweenFamily X X P x s.head.2).left`.
- At position `e`: one child (via `PUnit`), mapping to
  `(n, ⟨fiber e, s.children e⟩)`.
- This is a path: pick an edge, descend one level, repeat.

**Steps:**

1. Define `polyCofreeAnnotPosAtPoly`.
2. Build.
3. Define forward and backward maps.
4. Build after each.
5. Prove roundtrip.
6. Build and test.
7. Commit.

---

## Task 7: PolyCofreeAnnotPosAtM (line 4273)

**Dependency:** Task 3 (PolyCofix, for `PolyCofreeM`).

**Base type:** `Nat × (Σ x, PolyCofreeM A P x)`

This has the same structure as Task 6, with `PolyCofreeM A P`
in place of `PolyCofreeShape P` (which is
`PolyCofreeM (overTerminal X) P`).

**Polynomial definition:**

```lean
def polyCofreeAnnotPosAtMPoly (A : Over X) (P : PolyEndo X) :
    PolyEndo (Nat × (Σ x, PolyCofreeM A P x)) :=
  fun ⟨n, x, m⟩ => match n with
  | 0 => ccrObjMk (fun (_ : PUnit) =>
      overEmpty (Nat × (Σ x, PolyCofreeM A P x)))
  | n + 1 => ccrObjMk
      (fun (e : (polyBetweenFamily X X (polyScale A P)
                   x m.head).left) =>
        Over.mk (f := fun (_ : PUnit) =>
          (n, ⟨(polyBetweenFamily X X (polyScale A P)
                  x m.head).hom e,
               m.children e⟩)))
```

**Steps:**

1. Define `polyCofreeAnnotPosAtMPoly`.
2. Build.
3. Define forward and backward maps.
4. Build after each.
5. Prove roundtrip.
6. Build and test.
7. Commit.

---

## Ordering Constraints

```text
Task 1 (PolyCofixApprox)
  └─► Task 2 (PolyCofixAgree)
        └─► Task 3 (PolyCofix)
              ├─► Task 6 (PolyCofreeAnnotPosAt)
              └─► Task 7 (PolyCofreeAnnotPosAtM)

Task 4 (PolyFreeMLeafPos) — independent
Task 5 (PolyCofreePathSeg) — independent
```

Tasks 4 and 5 can be done in parallel with Tasks 1-3.
Tasks 6 and 7 depend on Task 3.
