# Parameterized List Object Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Define parameterized snoclist objects (PSOs) and
cons-list objects (PLOs) with Is/Has factoring, establish
PBTO-PSTO correspondence via enriched carrier, and derive
PLTO from PSTO via reversal.

**Architecture:** Two new files.  `GebLean/PSO.lean` defines
`IsPSO`, `HasPSO`, `IsPSTO = IsPSO T T`, `HasPSTO`, the
PSO(1)-PNNO correspondence, and the PBTO-to-PSTO instance.
`GebLean/PLO.lean` defines `IsPLO`, `HasPLO`,
`IsPLTO = IsPLO T T`, `HasPLTO`, and the PSTO-PLTO reversal.

**Tech Stack:** Lean 4, mathlib (CategoryTheory), product
utilities from `GebLean/Utilities/ComputableLimits.lean`,
`HasPBTO` and `HasNNO` from `GebLean/LawvereBT.lean`.

**References:**

- `GebLean/LawvereBT.lean` -- `HasPBTO`, `HasNNO`
- `GebLean/TreeLogic.lean` -- Paramorphism (for comparison)
- `GebLean/Utilities/ComputableLimits.lean` -- Product utils
- `docs/parameterized-list-object.md` -- Mathematical background
- `.claude/docs/TreeCalculus.idr` -- Idris 2 implementation
- Bauer's mutual-recursion trick:
  <https://cs.stackexchange.com/a/144184>

---

## Phase 1: PSO and PSTO

### Task 1: Create PSO.lean with imports and helper

**Files:**

- Create: `GebLean/PSO.lean`

- [ ] **Step 1: Create file with module header**

```lean
import GebLean.LawvereBT

/-!
# Parameterized Snoclist Objects

Defines the parameterized snoclist object (PSO) for an
arbitrary element type `B`, the parameterized
snoclist-of-trees object (PSTO) as a PSO with `B = L`,
and constructions relating PSOs, PNNOs, and PBTOs.

The PSO is the parameterized initial algebra of the
functor `X |-> 1 + X x B`.  Its elimination rule gives,
for `f : A -> X` and `g : X x B -> X`, a unique
`phi : A x L -> X` satisfying `phi(a, nil) = f(a)` and
`phi(a, snoc(l, b)) = g(phi(a, l), b)`.

The correspondence with binary trees uses
left-associative structure: `branch(l, b) = snoc(l, b)`,
making PSTO the natural intermediary for PBTO
conversions.
-/

namespace GebLean

open CategoryTheory

universe v u
```

- [ ] **Step 2: Add the step-equation helper**

This helper extracts `(phi(a, l), b)` from `A x (L x B)`
and pairs them as `X x B`.  Analogous to `cfpLiftAssoc`
for the PBTO step equation.

```lean
variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C]

/-- From `A x (L x B)`, extract `(phi(a, l), b)`
into `X x B`.  The recursive result comes first
(from `(a, l)` via `phi`), and the element `b`
comes second.  Used in the step equation of PSO
elimination. -/
def cfpLiftRecElem {A L B X : C}
    (φ : cfpProd A L ⟶ X) :
    cfpProd A (cfpProd L B) ⟶ cfpProd X B :=
  cfpLift
    (cfpAssocFst A L B ≫ φ)
    (cfpSnd A (cfpProd L B) ≫ cfpSnd L B)
```

- [ ] **Step 3: Build and verify**

Run: `lake build GebLean.PSO`
Expected: Success with no warnings.

- [ ] **Step 4: Commit**

```bash
git add GebLean/PSO.lean
git commit -m "PSO: file skeleton and cfpLiftRecElem"
```

---

### Task 2: Define IsPSO class

**Files:**

- Modify: `GebLean/PSO.lean`

- [ ] **Step 1: Write the IsPSO class**

```lean
/-- A parameterized snoclist object of `B`:
object `L` with `nil : 1 -> L` and
`snoc : L x B -> L` satisfying the universal
property of the left fold.  For any `f : A -> X`
and `g : X x B -> X`, there exists a unique
`phi : A x L -> X` with `phi(a, nil) = f(a)` and
`phi(a, snoc(l, b)) = g(phi(a, l), b)`. -/
class IsPSO (C : Type u) [Category.{v} C]
    [HasChosenFiniteProducts C]
    (B : C) (L : C) where
  /-- Empty snoclist. -/
  nil : cfpTerminal ⟶ L
  /-- Append an element. -/
  snoc : cfpProd L B ⟶ L
  /-- Left fold elimination. -/
  elim : ∀ {A X : C},
    (A ⟶ X) → (cfpProd X B ⟶ X) →
    (cfpProd A L ⟶ X)
  /-- Base case: `phi(a, nil) = f(a)`. -/
  elim_nil : ∀ {A X : C}
    (f : A ⟶ X) (g : cfpProd X B ⟶ X),
    cfpInsertSnd nil A ≫ elim f g = f
  /-- Step case:
  `phi(a, snoc(l, b)) = g(phi(a, l), b)`. -/
  elim_snoc : ∀ {A X : C}
    (f : A ⟶ X) (g : cfpProd X B ⟶ X),
    cfpMap (𝟙 A) snoc ≫ elim f g =
      cfpLiftRecElem (elim f g) ≫ g
  /-- Uniqueness. -/
  elim_uniq : ∀ {A X : C}
    (f : A ⟶ X) (g : cfpProd X B ⟶ X)
    (φ : cfpProd A L ⟶ X),
    cfpInsertSnd nil A ≫ φ = f →
    cfpMap (𝟙 A) snoc ≫ φ =
      cfpLiftRecElem φ ≫ g →
    φ = elim f g
```

- [ ] **Step 2: Build and verify**

Run: `lake build GebLean.PSO`
Expected: Success with no warnings.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PSO.lean
git commit -m "PSO: define IsPSO class"
```

---

### Task 3: Define HasPSO, IsPSTO, HasPSTO

**Files:**

- Modify: `GebLean/PSO.lean`

- [ ] **Step 1: Define HasPSO**

```lean
/-- A category has a parameterized snoclist object
of `B`: an object `L` with `IsPSO B L`. -/
class HasPSO (C : Type u) [Category.{v} C]
    [HasChosenFiniteProducts C] (B : C) where
  /-- The snoclist object. -/
  L : C
  /-- The PSO instance. -/
  [isPSO : IsPSO C B L]

attribute [instance] HasPSO.isPSO
```

- [ ] **Step 2: Define IsPSTO and HasPSTO**

```lean
/-- An object `T` is a parameterized
snoclist-of-trees object: a PSO of itself. -/
abbrev IsPSTO (C : Type u) [Category.{v} C]
    [HasChosenFiniteProducts C] (T : C) :=
  IsPSO C T T

/-- A category has a parameterized
snoclist-of-trees object. -/
class HasPSTO (C : Type u) [Category.{v} C]
    [HasChosenFiniteProducts C] where
  /-- The tree/snoclist object. -/
  T : C
  /-- The PSTO instance. -/
  [isPSTO : IsPSTO C T]

attribute [instance] HasPSTO.isPSTO
```

- [ ] **Step 3: Add HasPSTO-to-HasPSO instance**

```lean
instance (priority := 100) pstoToHasPSO
    [p : HasPSTO C] : HasPSO C p.T where
  L := p.T
```

- [ ] **Step 4: Build and verify**

Run: `lake build GebLean.PSO`
Expected: Success with no warnings.

- [ ] **Step 5: Commit**

```bash
git add GebLean/PSO.lean
git commit -m "PSO: define HasPSO, IsPSTO, HasPSTO"
```

---

### Task 4: PSO(1) corresponds to PNNO

**Files:**

- Modify: `GebLean/PSO.lean`

- [ ] **Step 1: Construct IsPSO from HasNNO**

`snoc : L x 1 -> L` becomes `s : N -> N` via
`N x 1 ~ N`.  The step `g : X x 1 -> X` becomes
`g' : X -> X` via `X x 1 ~ X`.

```lean
section PSO_Terminal_NNO

variable [nno : HasNNO C]

instance nnoToIsPSO :
    IsPSO C (cfpTerminal (h := h)) nno.N where
  nil := nno.z
  snoc := cfpFst nno.N cfpTerminal ≫ nno.s
  elim := fun {A X} f g =>
    nno.elim f
      (cfpLift (𝟙 X) (cfpTerminalFrom X) ≫ g)
  elim_nil := _
  elim_snoc := _
  elim_uniq := _

end PSO_Terminal_NNO
```

Fill in proofs one at a time, building after each.

- [ ] **Step 2: Prove elim_nil**
- [ ] **Step 3: Prove elim_snoc**
- [ ] **Step 4: Prove elim_uniq**
- [ ] **Step 5: Build and verify**

Run: `lake build GebLean.PSO`
Expected: Success with no warnings.

- [ ] **Step 6: Commit**

```bash
git add GebLean/PSO.lean
git commit -m "PSO: PNNO gives PSO for terminal"
```

---

## Phase 2: PBTO to PSTO

### Task 5: Enriched-carrier components

**Files:**

- Modify: `GebLean/PSO.lean`

- [ ] **Step 1: Define base and step morphisms**

The PBTO catamorphism targets `cfpProd T X`.
Step maps `((t1,x1), (t2,x2))` to
`(branch(t1,t2), g(x1,t2))`: `x1` is the recursive
result on the left (accumulated snoclist), `t2` is
the right subtree (element as data).

```lean
section PBTO_to_PSTO

variable [p : HasPBTO C]

private def pstoBase {A X : C} (f : A ⟶ X) :
    A ⟶ cfpProd p.T X :=
  cfpLift (cfpTerminalFrom A ≫ p.ℓ) f

private def pstoStep {X : C}
    (g : cfpProd X p.T ⟶ X) :
    cfpProd (cfpProd p.T X) (cfpProd p.T X) ⟶
      cfpProd p.T X :=
  let TX := cfpProd p.T X
  let t1 : cfpProd TX TX ⟶ p.T :=
    cfpFst TX TX ≫ cfpFst p.T X
  let x1 : cfpProd TX TX ⟶ X :=
    cfpFst TX TX ≫ cfpSnd p.T X
  let t2 : cfpProd TX TX ⟶ p.T :=
    cfpSnd TX TX ≫ cfpFst p.T X
  cfpLift
    (cfpLift t1 t2 ≫ p.β)
    (cfpLift x1 t2 ≫ g)
```

- [ ] **Step 2: Build and verify**

Run: `lake build GebLean.PSO`
Expected: Success with no warnings.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PSO.lean
git commit -m "PSO: enriched-carrier for PBTO-to-PSTO"
```

---

### Task 6: Projection lemma

**Files:**

- Modify: `GebLean/PSO.lean`

- [ ] **Step 1: Prove fst of enriched cata = projection**

`theta = p.elim (pstoBase f) (pstoStep g)` has target
`cfpProd p.T X`.  Show `theta >> cfpFst p.T X` equals
`cfpSnd A p.T`.

Approach: show `theta >> cfpFst p.T X` satisfies the
PBTO catamorphism equations for
`(cfpTerminalFrom A >> leaf, branch)`.  Since
`cfpSnd A T` also satisfies these equations, by PBTO
uniqueness they are equal.

Factor out intermediate lemmas and fill in with
underscores, as per project workflow.

- [ ] **Step 2: Build and verify**

Run: `lake build GebLean.PSO`

- [ ] **Step 3: Commit**

```bash
git add GebLean/PSO.lean
git commit -m "PSO: projection lemma for PBTO-to-PSTO"
```

---

### Task 7: Main PBTO-to-PSTO instance

**Files:**

- Modify: `GebLean/PSO.lean`

- [ ] **Step 1: Define elimination and state instance**

```lean
private def pstoElim {A X : C}
    (f : A ⟶ X) (g : cfpProd X p.T ⟶ X) :
    cfpProd A p.T ⟶ X :=
  p.elim (pstoBase f) (pstoStep g) ≫
    cfpSnd p.T X

instance pbtoToIsPSTO [p : HasPBTO C] :
    IsPSTO C p.T where
  nil := p.ℓ
  snoc := p.β
  elim := fun f g => pstoElim f g
  elim_nil := _
  elim_snoc := _
  elim_uniq := _

instance pbtoToHasPSTO [p : HasPBTO C] :
    HasPSTO C where
  T := p.T

end PBTO_to_PSTO
```

- [ ] **Step 2: Prove elim_nil**

From `p.elim_l`:
`cfpInsertSnd leaf A >> theta = pstoBase f`, then
post-compose with `cfpSnd T X` to get `f`.

- [ ] **Step 3: Prove elim_snoc**

Use `p.elim_beta` to rewrite the PBTO step,
post-compose with `cfpSnd T X`, and show the result
equals `cfpLiftRecElem (pstoElim f g) >> g` using
the projection lemma.

Factor out intermediate lemmas as needed.

- [ ] **Step 4: Prove elim_uniq**

Given `psi` satisfying PSO equations, form
`theta' = cfpLift (cfpSnd A T) psi : A x T -> T x X`.
Show `theta'` satisfies PBTO catamorphism equations.
By PBTO uniqueness, `theta' = theta`, so
`psi = theta' >> cfpSnd T X = pstoElim f g`.

- [ ] **Step 5: Build and verify**

Run: `lake build GebLean.PSO`
Expected: Success with no warnings.

- [ ] **Step 6: Commit**

```bash
git add GebLean/PSO.lean
git commit -m "PSO: PBTO implies PSTO"
```

---

## Phase 3: PLO and PLTO

### Task 8: Create PLO.lean with IsPLO and HasPLO

**Files:**

- Create: `GebLean/PLO.lean`

- [ ] **Step 1: Create file with IsPLO class**

Mirror the PSO structure with reversed argument order:
`cons : B x L -> L` and `g : B x X -> X`.

```lean
import GebLean.PSO

/-!
# Parameterized List Objects

Defines the parameterized (cons-)list object (PLO)
for an arbitrary element type `B`, the parameterized
list-of-trees object (PLTO) as a PLO with `B = L`,
and the equivalence between PSTO and PLTO via
reversal.
-/

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C]

/-- From `A x (B x L)`, extract `(b, phi(a, l))`
into `B x X`.  The element comes first, and the
recursive result comes second.  Used in the step
equation of PLO elimination. -/
def cfpLiftElemRec {A B L X : C}
    (φ : cfpProd A L ⟶ X) :
    cfpProd A (cfpProd B L) ⟶ cfpProd B X :=
  cfpLift
    (cfpSnd A (cfpProd B L) ≫ cfpFst B L)
    (cfpAssocSnd A B L ≫ φ)

/-- A parameterized (cons-)list object of `B`:
object `L` with `nil : 1 -> L` and
`cons : B x L -> L` satisfying the universal
property of the right fold. -/
class IsPLO (C : Type u) [Category.{v} C]
    [HasChosenFiniteProducts C]
    (B : C) (L : C) where
  /-- Empty list. -/
  nil : cfpTerminal ⟶ L
  /-- Prepend an element. -/
  cons : cfpProd B L ⟶ L
  /-- Right fold elimination. -/
  elim : ∀ {A X : C},
    (A ⟶ X) → (cfpProd B X ⟶ X) →
    (cfpProd A L ⟶ X)
  /-- Base case: `phi(a, nil) = f(a)`. -/
  elim_nil : ∀ {A X : C}
    (f : A ⟶ X) (g : cfpProd B X ⟶ X),
    cfpInsertSnd nil A ≫ elim f g = f
  /-- Step case:
  `phi(a, cons(b, l)) = g(b, phi(a, l))`. -/
  elim_cons : ∀ {A X : C}
    (f : A ⟶ X) (g : cfpProd B X ⟶ X),
    cfpMap (𝟙 A) cons ≫ elim f g =
      cfpLiftElemRec (elim f g) ≫ g
  /-- Uniqueness. -/
  elim_uniq : ∀ {A X : C}
    (f : A ⟶ X) (g : cfpProd B X ⟶ X)
    (φ : cfpProd A L ⟶ X),
    cfpInsertSnd nil A ≫ φ = f →
    cfpMap (𝟙 A) cons ≫ φ =
      cfpLiftElemRec φ ≫ g →
    φ = elim f g
```

- [ ] **Step 2: Define HasPLO, IsPLTO, HasPLTO**

```lean
class HasPLO (C : Type u) [Category.{v} C]
    [HasChosenFiniteProducts C] (B : C) where
  L : C
  [isPLO : IsPLO C B L]

attribute [instance] HasPLO.isPLO

abbrev IsPLTO (C : Type u) [Category.{v} C]
    [HasChosenFiniteProducts C] (T : C) :=
  IsPLO C T T

class HasPLTO (C : Type u) [Category.{v} C]
    [HasChosenFiniteProducts C] where
  T : C
  [isPLTO : IsPLTO C T]

attribute [instance] HasPLTO.isPLTO

instance (priority := 100) pltoToHasPLO
    [p : HasPLTO C] : HasPLO C p.T where
  L := p.T
```

- [ ] **Step 3: Build and verify**

Run: `lake build GebLean.PLO`
Expected: Success with no warnings.

- [ ] **Step 4: Commit**

```bash
git add GebLean/PLO.lean
git commit -m "PLO: define IsPLO, HasPLO, IsPLTO, HasPLTO"
```

---

## Phase 4: PSTO to PLTO via reversal

### Task 9: Define reversal and PSTO-PLTO equivalence

**Files:**

- Modify: `GebLean/PLO.lean`

- [ ] **Step 1: Define rev using PSO elimination**

Given `IsPSTO C T`, define `rev : T -> T` by folding
with `f = nil` and `g(acc, b) = cons(b, acc)`:
the snoc-list fold that reverses into a cons-list.

Since this is a PSTO (B = L = T), elements are
themselves trees, and `cons(b, acc)` reverses one
level.  To reverse at every level, the fold should
recursively reverse each element: `g(acc, b) =
cons(rev(b), acc)`.  This recursive reversal can be
expressed as a single PSO fold on an enriched carrier.

- [ ] **Step 2: Show IsPSTO implies IsPLTO**

Use `rev` to define the PLO elimination:
`phi_cons(a, l) = phi_snoc(a, rev(l))`.

Prove base, step, and uniqueness equations.

- [ ] **Step 3: Show IsPLTO implies IsPSTO**

Similarly, define `rev'` using PLO elimination
(reversing a cons-list into a snoclist) and derive
the PSO elimination from the PLO elimination.

- [ ] **Step 4: Build and verify**

Run: `lake build GebLean.PLO`
Expected: Success with no warnings.

- [ ] **Step 5: Commit**

```bash
git add GebLean/PLO.lean
git commit -m "PLO: PSTO-PLTO equivalence via reversal"
```

---

## Phase 5: Register and test

### Task 10: Register modules and full build

**Files:**

- Modify: `GebLean.lean` (root module)

- [ ] **Step 1: Add imports**

Add `import GebLean.PSO` and `import GebLean.PLO`
to `GebLean.lean` in alphabetical position.

- [ ] **Step 2: Build and test**

Run: `lake build` then `lake test`
Expected: Success with no warnings, all tests pass.

- [ ] **Step 3: Commit**

```bash
git add GebLean.lean
git commit -m "Register PSO and PLO modules"
```

---

## Phase 6: Investigate PSTO implies PBTO

### Task 11: Research PSTO-to-PBTO direction

**Files:**

- Modify: `GebLean/PSO.lean`
- Modify:
  `.session/workstreams/parameterized-list-object.md`

This task is exploratory.

- [ ] **Step 1: Try T-as-stack enriched carrier**

Since T is a snoclist of T's, use carrier
`cfpProd X T` where T accumulates pending right
subtrees.  The PSO fold pushes elements onto the
stack; a second PSO fold drains the stack.  Try
this first — it stays within the PSO structure
without needing PNNO.

- [ ] **Step 2: Try Bauer's mutual-recursion trick**

If Step 1 fails, use the parameter as a "slice"
to encode mutual recursion.  See
<https://cs.stackexchange.com/a/144184>.

- [ ] **Step 3: Try via PNNO**

If Step 2 fails, derive PNNO from PSTO via
PSO(1), then use PNNO iteration.

- [ ] **Step 4: Document findings**

Record results in workstream and docs.
