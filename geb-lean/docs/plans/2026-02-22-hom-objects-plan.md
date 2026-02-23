# Hom-Objects Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use
> superpowers:executing-plans to implement this plan
> task-by-task.

**Goal:** Define internal hom-objects `[Q, R]` for
`PolyFunctorBetweenCat.{u, u} X Y` and prove the currying
adjunction `Hom(P x Q, R) = Hom(P, [Q, R])`, culminating in
a `MonoidalClosed` instance.

**Architecture:** Three-layer construction (representable ->
copresheaf -> general) built compositionally from existing
universal constructions (identity, coproducts, terminal,
composition, Kan extensions). Rep-level currying reuses
`polyBetweenLKanAdj`.

**Tech Stack:** Lean 4, Mathlib (categories, monoidal closed),
existing GebLean infrastructure (CCR, polynomial functors,
products/coproducts/limits/Kan extensions in PolyUMorph.lean).

**References:**

- Idris formulas: `.claude/docs/SlicePolyUMorph.idr`
  lines 1014-1802
- Design: `docs/plans/2026-02-22-hom-objects-design.md`

---

All new code goes in `GebLean/PolyUMorph.lean`, in a new
section `HomObjects` inserted before `end GebLean` (line 2300).

## Task 1: Terminal CCR Object

**Files:**

- Modify: `GebLean/PolyUMorph.lean` (insert before
  `end GebLean`)

**Context:**
The terminal object in `CoprodCovarRepCat (Over X)` has one
position (`PUnit`) and initial family
(`Over.mk (PEmpty.elim : PEmpty -> X)`). Morphism uniqueness:
any CCR object has exactly one morphism to the terminal
(reindex to `PUnit.unit`, fiber morphism from initial).

Corresponds to Idris `spfdTerminal` (line 1014):

```text
spfdTerminal dom cod = SPFD (\_ => Unit) (\_, _, _ => Void)
```

### Step 1: Define the terminal CCR object

Open a new section `HomObjects` with universe/variable
declarations matching the LeftKanExtension section. Define:

```lean
section HomObjects

universe u

variable {X Y : Type u}

def ccrTerminalObj :
    CoprodCovarRepCat.{u, u + 1, u + 1} (Over X) :=
  ccrObjMk (fun _ : PUnit.{u + 1} =>
    Over.mk (PEmpty.elim : PEmpty.{u + 1} → X))
```

Build to verify compilation.

### Step 2: Define the unique morphism to terminal

```lean
def ccrTerminalFrom
    (c : CoprodCovarRepCat.{u, u + 1, u + 1} (Over X)) :
    c ⟶ ccrTerminalObj (X := X) :=
  ccrHomMk
    (fun _ => PUnit.unit)
    (fun i => Over.homMk PEmpty.elim (by ext x; exact x.elim))
```

Build to verify.

### Step 3: Prove uniqueness

```lean
theorem ccrTerminalFrom_unique
    (c : CoprodCovarRepCat.{u, u + 1, u + 1} (Over X))
    (f : c ⟶ ccrTerminalObj (X := X)) :
    f = ccrTerminalFrom c := by
  ...
```

The proof should use `ccrHom_ext_subst` (or similar
extensionality) --- showing that any two morphisms to terminal
agree because the reindex and fiber morphisms are forced. The
reindex must land in `PUnit` (unique element), and the fiber
morphism is from initial (unique by `PEmpty.elim`).

Build and verify.

### Step 4: Build and run tests

Run `lake build` and `lake test`. Fix any issues.

---

## Task 2: Constant Endofunctor (`polyBetweenConst`)

**Files:**

- Modify: `GebLean/PolyUMorph.lean` (continue in `HomObjects`
  section)

**Context:**
The constant endofunctor `Const(a)` on `Over X` sends every
object to `a`. As a polynomial functor
`PolyFunctorBetweenCat X X`, at each `x : X`:

- Positions: fiber of `a` over `x`,
  i.e. `{ b : a.left // a.hom b = x }`
- Family: each position maps to the terminal CCR object

Corresponds to Idris `SPFDataConst` (line 379):

```text
SPFDataConst dom x = SPFD x (\_, _, _ => Void)
```

The positions being fibers of `a` and directions being empty
means `coprod_{fibers} Hom(initial, B) = fibers`, recovering
`a` upon evaluation.

### Step 1: Define `polyBetweenConst`

```lean
def polyBetweenConst (a : Over X) :
    PolyFunctorBetweenCat.{u, u} X X :=
  fun x => ccrObjMk
    (fun _ : { b : a.left // a.hom b = x } =>
      Over.mk (PEmpty.elim : PEmpty.{u + 1} → X))
```

Build to verify.

### Step 2: Prove functoriality of `polyBetweenConst`

We need `polyBetweenConst` to be functorial in `a`, i.e.,
given `f : a ⟶ b` in `Over X`, produce a morphism
`polyBetweenConst a ⟶ polyBetweenConst b`. At each `x`:

- Reindex: map fibers via `f.left`
- Fiber morphism: from initial to initial (unique)

```lean
def polyBetweenConstMap {a b : Over X} (f : a ⟶ b) :
    (polyBetweenConst a : PolyFunctorBetweenCat X X) ⟶
    polyBetweenConst b :=
  fun x => ccrHomMk
    (fun ⟨v, hv⟩ => ⟨f.left v, ...⟩)
    (fun _ => Over.homMk PEmpty.elim
      (by ext x; exact x.elim))
```

The subtype proof `f.left v`'s fiber membership uses
`f.w` (the `Over X` morphism compatibility).

Build to verify.

### Step 3: Build and run tests

Run `lake build` and `lake test`.

---

## Task 3: FlipEither Endofunctor

**Files:**

- Modify: `GebLean/PolyUMorph.lean`

**Context:**
`polyBetweenFlipEither a = polyBetweenId X + polyBetweenConst a`
(binary coproduct in `PolyFunctorBetweenCat X X`). This
represents the endofunctor `A |-> A + a` on `Over X`.

Uses the existing `HasFiniteCoproducts` instance
(line 1493) to form the binary coproduct via
`Limits.coprod`.

Corresponds to Idris `spfdFlipEither` (line 1428):

```text
spfdFlipEither a =
  spfdCoproduct (SPFDid w) (SPFDataConst w a)
```

### Step 1: Define `polyBetweenFlipEither`

```lean
def polyBetweenFlipEither (a : Over X) :
    PolyFunctorBetweenCat.{u, u} X X :=
  Limits.coprod
    (polyBetweenId (X := X))
    (polyBetweenConst a)
```

This uses `HasBinaryCoproducts` (from
`HasFiniteCoproducts`). Build to verify type-checks.

### Step 2: Build and run tests

Run `lake build` and `lake test`.

---

## Task 4: Representable Hom Object (`ccrRepHomObj`)

**Files:**

- Modify: `GebLean/PolyUMorph.lean`

**Context:**
Given `a : Over X` and `r : CoprodCovarRepCat (Over X)`,
the representable hom-object is `r` composed with
`flipEither(a)`. Since `polyBetweenComp` takes two PFBs,
we embed `r` as the constant PFB `fun _ : PUnit => r` and
evaluate at `PUnit.unit`.

Corresponds to Idris `spfdRepHomObj` (line 1487):

```text
spfdRepHomObj q r =
  SPFDcomp dom dom Unit r (spfdFlipEither q)
```

### Step 1: Define `ccrRepHomObj`

```lean
def ccrRepHomObj (a : Over X)
    (r : CoprodCovarRepCat.{u, u + 1, u + 1} (Over X)) :
    CoprodCovarRepCat.{u, u + 1, u + 1} (Over X) :=
  polyBetweenComp
    (fun _ : PUnit.{u + 1} => r)
    (polyBetweenFlipEither a)
    PUnit.unit
```

Build to verify.

### Step 2: Verify the right adjoint connection

`ccrRepHomObj a r` should equal
`polyBetweenPrecompFunctor (polyBetweenFlipEither a)`
applied to the constant PFB at `r`, evaluated at
`PUnit.unit`. Verify this is definitional or prove the
equality.

```lean
theorem ccrRepHomObj_eq_precomp (a : Over X)
    (r : CoprodCovarRepCat.{u, u + 1, u + 1} (Over X)) :
    ccrRepHomObj a r =
    (polyBetweenPrecompFunctor
      (polyBetweenFlipEither a)).obj
      (fun _ : PUnit.{u + 1} => r) PUnit.unit := by
  rfl  -- or unfold + ext
```

Build to verify.

### Step 3: Build and run tests for `ccrRepHomObj`

---

## Task 5: Copresheaf Hom Object (`ccrCoprHomObj`)

**Files:**

- Modify: `GebLean/PolyUMorph.lean`

**Context:**
Given `q, r : CoprodCovarRepCat (Over X)`, the copresheaf
hom-object is `Prod_{i : ccrIndex q} ccrRepHomObj
(ccrFamily q i) r`. This is a set-indexed product using
`ccrProdData` from `Families.lean:1006`.

Corresponds to Idris `spfdCoprHomObj` (line 1594):

```text
spfdCoprHomObj q r =
  spfdSetProduct (\ep => spfdRepHomObj (spfdDir q () ep) r)
```

### Step 1: Define `ccrCoprHomObj`

The set-indexed product in CCR is available via
`ccrProdData`. Check what API it provides --- likely
`ProdData.prod` gives the product object.

```lean
def ccrCoprHomObj
    (q r : CoprodCovarRepCat.{u, u + 1, u + 1}
      (Over X)) :
    CoprodCovarRepCat.{u, u + 1, u + 1} (Over X) :=
  ProdData.prod
    (fun i : ccrIndex q => ccrRepHomObj (ccrFamily q i) r)
```

Build to verify. If `ProdData.prod` is not the right API,
check `Families.lean` for the correct product construction
name.

### Step 2: Build and run tests for `ccrCoprHomObj`

---

## Task 6: General Hom Object (`polyBetweenHomObj`)

**Files:**

- Modify: `GebLean/PolyUMorph.lean`

**Context:**
Given `Q, R : PolyFunctorBetweenCat X Y`, the hom-object
is defined pointwise: `[Q, R](y) = ccrCoprHomObj (Q y) (R y)`.

Corresponds to Idris `spfdHomObj` (line 1700):

```text
spfdHomObj q r = SPFDataFamToProdUnit $
  \ec => spfdCoprHomObj
    (SPFDataProdToFamUnit q ec)
    (SPFDataProdToFamUnit r ec)
```

In our setting, `SPFDataProdToFamUnit P ec = P ec`
(just evaluation) and `SPFDataFamToProdUnit F = F`
(just the function itself), so the Lean version is
trivially pointwise.

### Step 1: Define `polyBetweenHomObj`

```lean
def polyBetweenHomObj
    (Q R : PolyFunctorBetweenCat.{u, u} X Y) :
    PolyFunctorBetweenCat.{u, u} X Y :=
  fun y => ccrCoprHomObj (Q y) (R y)
```

Build to verify.

### Step 2: Define `polyBetweenHomFunctor`

The hom-object should be functorial in the second argument
(contravariant in the first, covariant in the second).
For `MonoidalClosed`, we need `ihom Q : PFB ⥤ PFB` which
is the functor `R ↦ [Q, R]`. Define this functor.

The map on morphisms: given `alpha : R ⟶ R'`, produce
`[Q, R] ⟶ [Q, R']`. At each `y`, this is a morphism
`ccrCoprHomObj (Q y) (R y) ⟶ ccrCoprHomObj (Q y) (R' y)`.
Each factor of the product is
`ccrRepHomObj (ccrFamily (Q y) i) (R y)`, and `alpha`
induces a morphism on each factor via the functoriality
of `polyBetweenComp` in its first argument.

This may require defining `ccrRepHomMap` and
`ccrCoprHomMap` first.

Build to verify.

### Step 3: Build and run tests for hom functoriality

---

## Task 7: Lan-Product Isomorphism

**Files:**

- Modify: `GebLean/PolyUMorph.lean`

**Context:**
The central new result connecting the Kan extension to
products. For `a : Over X` and
`p : CoprodCovarRepCat (Over X)`:

```text
Lan_{flipEither(a)}(p) = p * yoneda(a)
```

where `yoneda(a)` is the representable copresheaf
`ccrObjMk (fun _ : PUnit => a)`.

Unpacking: `Lan_{flipEither(a)}(p)` has (by definition of
`polyBetweenLKanObj`):

- Positions: `ccrIndex p`
- Family at `ip`:
  `polyBetweenEval (flipEither a) (ccrFamily p ip)`
  = evaluation of `A |-> A + a` at `ccrFamily p ip`
  = `ccrFamily p ip + a` (as `Over X` objects)

Meanwhile `p * yoneda(a)` (product in CCR) has:

- Positions: `ccrIndex p x PUnit = ccrIndex p`
  (product with one-position object)
- Family at `(ip, *)`:
  `ccrFamily p ip + ccrFamily (yoneda a) * = ccrFamily p ip + a`

So the positions and families match up to canonical
isomorphisms. The isomorphism in CCR at each `x` is:

Forward: reindex by `fun ip => (ip, PUnit.unit)`,
fiber morphism uses the iso `(B + a) = (B + a)`.

Backward: reindex by `fun (ip, _) => ip`,
fiber morphism is the same iso in reverse.

### Step 1: Define the representable copresheaf

```lean
def ccrYoneda (a : Over X) :
    CoprodCovarRepCat.{u, u + 1, u + 1} (Over X) :=
  ccrObjMk (fun _ : PUnit.{u + 1} => a)
```

Build to verify.

### Step 2: State and prove the Lan-product isomorphism

First state it. This may need several helper lemmas about
how `polyBetweenEval` of `polyBetweenFlipEither a` at `B`
relates to `B + a` in `Over X`, and how the product in CCR
with `ccrYoneda a` relates to coproduct of families in
`Over X`. Use the factoring-out-lemmas technique from
CLAUDE.md.

This is the most technically involved proof. Approach:

1. Define forward and backward maps
2. Prove roundtrip in each direction
3. Bundle as `Iso` in CCR

Build and verify at each sub-step.

### Step 3: Lift to PFB level

State the isomorphism at the `PolyFunctorBetweenCat` level
(pointwise from the CCR level).

Build to verify.

### Step 4: Build and run tests for Lan-product iso

---

## Task 8: Rep-Level Currying via Kan Adjunction

**Files:**

- Modify: `GebLean/PolyUMorph.lean`

**Context:**
Using the Lan-product isomorphism (Task 7) and
`polyBetweenLKanAdj` (existing), derive:

```text
Hom(p * yoneda(a), r)
  = Hom(Lan_{flipEither(a)}(p), r)  [via Lan-product iso]
  = Hom(p, precomp_{flipEither(a)}(r))  [polyBetweenLKanAdj]
  = Hom(p, ccrRepHomObj a r)  [by definition]
```

This gives a natural isomorphism `Hom(- * yoneda(a), r) =
Hom(-, ccrRepHomObj a r)` at the copresheaf level.

### Step 1: Compose the natural isomorphisms

Use `Equiv.trans` to compose:

1. The iso from `Hom(p * yoneda(a), r)` to
   `Hom(Lan(p), r)` (via Lan-product iso, precomposition)
2. `polyBetweenLKanCoreHomEquiv` (the existing Kan
   adjunction equivalence)

```lean
def ccrRepHomEquiv (a : Over X)
    (p r : CoprodCovarRepCat ...) :
    (ccrProd p (ccrYoneda a) ⟶ r) ≃
    (p ⟶ ccrRepHomObj a r) := ...
```

Build to verify.

### Step 2: Prove naturality

The composed iso should be natural in both `p` and `r`.
This follows from naturality of both components.

Build to verify.

### Step 3: Build and run tests for rep currying

---

## Task 9: Copresheaf-Level Currying

**Files:**

- Modify: `GebLean/PolyUMorph.lean`

**Context:**
Using rep-level currying (Task 8) plus the adjunction chain:

```text
Hom(p * q, r)
  = Hom(coprod_i (p * yoneda(q_i)), r)
    [product-coproduct decomposition]
  = Prod_i Hom(p * yoneda(q_i), r)
    [coproduct-hom adjunction]
  = Prod_i Hom(p, ccrRepHomObj (q_i) r)
    [rep currying, Task 8]
  = Hom(p, Prod_i ccrRepHomObj (q_i) r)
    [product-hom adjunction]
  = Hom(p, ccrCoprHomObj q r)
    [definition of ccrCoprHomObj]
```

Each step is a natural isomorphism in CCR.

### Step 1: Product-coproduct decomposition

Prove that in CCR, `p * q = coprod_{i : ccrIndex q}
(p * ccrYoneda (ccrFamily q i))`. This is an isomorphism
since:

- `ccrIndex (p * q) = ccrIndex p x ccrIndex q`
- `ccrIndex (coprod_i (p * yoneda(q_i)))
  = Sigma_i (ccrIndex p x PUnit)
  = Sigma_i ccrIndex p`

The canonical iso swaps the sigma/product components.

```lean
def ccrProdCoprodDecomp
    (p q : CoprodCovarRepCat ...) :
    ccrProd p q ≅
    ccrCoprod (ccrIndex q)
      (fun i => ccrProd p (ccrYoneda (ccrFamily q i)))
```

Build to verify.

### Step 2: Coproduct-hom adjunction

Show `Hom(coprod_i F_i, R) = Prod_i Hom(F_i, R)` in CCR.
This should follow from the universal property of
coproducts.

### Step 3: Product-hom adjunction

Show `Prod_i Hom(P, G_i) = Hom(P, Prod_i G_i)` in CCR.
This follows from the universal property of products.

### Step 4: Compose all four isomorphisms

Compose via `Equiv.trans`:

1. Product-coproduct decomposition (Step 1)
2. Coproduct-hom (Step 2)
3. Rep currying at each factor (Task 8)
4. Product-hom (Step 3)

```lean
def ccrCoprHomEquiv
    (p q r : CoprodCovarRepCat ...) :
    (ccrProd p q ⟶ r) ≃ (p ⟶ ccrCoprHomObj q r) := ...
```

Build to verify.

### Step 5: Prove naturality

Follows from naturality of each component.

### Step 6: Build and run tests

---

## Task 10: General Currying and MonoidalClosed

**Files:**

- Modify: `GebLean/PolyUMorph.lean`

**Context:**
Lift from copresheaf level (Task 9) to the general PFB
level pointwise, then package as `MonoidalClosed`.

### Step 1: General currying adjunction

```lean
def polyBetweenHomEquiv
    (P Q R : PolyFunctorBetweenCat.{u, u} X Y) :
    (polyBetweenProdObj P Q ⟶ R) ≃
    (P ⟶ polyBetweenHomObj Q R) := ...
```

This applies `ccrCoprHomEquiv` at each `y : Y` and
assembles pointwise. Use `FamilyCat.hom_ext` for
the equivalence.

Build to verify.

### Step 2: CartesianMonoidalCategory instance

Construct `CartesianMonoidalCategory` for
`PolyFunctorBetweenCat.{u, u} X Y` using
`CartesianMonoidalCategory.ofChosenFiniteProducts`
with:

- Terminal limit cone: `polyBetweenProd PEmpty.{u+1} ...`
  (empty product = terminal object)
- Binary product limit cones: from existing
  `polyBetweenProd` and projection/lift infrastructure

This step may require several helper lemmas to package
our explicit products into the form expected by
`ofChosenFiniteProducts` (providing `IsTerminal` and
`LimitCone` for `pair X Y`).

Build to verify.

### Step 3: Closed instance for each Q

```lean
instance polyBetweenClosed
    (Q : PolyFunctorBetweenCat.{u, u} X Y) :
    Closed Q where
  rightAdj := polyBetweenHomFunctor Q
  adj := ...  -- from polyBetweenHomEquiv + naturality
```

The adjunction `tensorLeft Q ⊣ polyBetweenHomFunctor Q`
is built from `polyBetweenHomEquiv` via
`Adjunction.mkOfHomEquiv`.

Build to verify.

### Step 4: MonoidalClosed instance

```lean
instance : MonoidalClosed
    (PolyFunctorBetweenCat.{u, u} X Y) where
  closed := polyBetweenClosed
```

Build to verify.

### Step 5: Build and run tests

Run `lake build` and `lake test`. Verify no warnings.
Check axioms with `#print axioms`.

---

## Dependency Graph

```text
Task 1 (Terminal CCR) ──> Task 2 (Const)
                              |
                              v
                         Task 3 (FlipEither)
                              |
                              v
                         Task 4 (RepHom) ────────> Task 7 (Lan-Product Iso)
                              |                         |
                              v                         v
                         Task 5 (CoprHom)          Task 8 (Rep Currying)
                              |                         |
                              v                         v
                         Task 6 (HomObj)           Task 9 (Copr Currying)
                              |                         |
                              v                         v
                         Task 10 (MonoidalClosed) <─────┘
```

## Risk Areas

1. **Universe levels**: The interplay of `u`, `u+1` in CCR
   indices/families and `Over X` may require careful attention.
   Use `_` placeholders to let Lean infer, and check with
   `lean_goal` when stuck.

2. **Lan-product isomorphism** (Task 7): The most technically
   novel proof. If stuck, use the factoring-out-lemmas
   technique. The iso itself should be straightforward at the
   level of positions/families, but transporting through
   `polyBetweenEval` of `polyBetweenFlipEither` may involve
   dependent type issues.

3. **Product-coproduct decomposition** (Task 9 Step 1):
   Swapping `Sigma/Prod` components in the dependent setting
   may require `HEq` reasoning similar to the Kan extension
   proofs.

4. **CartesianMonoidalCategory setup** (Task 10 Step 2):
   Getting the explicit product cones into the right form for
   `ofChosenFiniteProducts` may be tedious. Consider whether
   `noncomputable` can be accepted for just this instance, or
   whether custom `ChosenFiniteProducts` data is needed.

5. **Definitional vs propositional equality**: Many steps should
   be definitional (`rfl`), but Lean may not reduce through
   `Limits.coprod` (which goes through `HasColimit` machinery).
   If this causes friction, consider defining
   `polyBetweenFlipEither` directly using `polyBetweenCoprod`
   rather than `Limits.coprod`.
