# Internal Presheaf--Grothendieck Equivalence Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize the equivalence between internal presheaves on
an internal category in a presheaf topos and ordinary presheaves on
the Grothendieck construction of the externalized functor, then
generalize to FunctorData-valued internal categories via the
reflective embedding of Cat.

**Architecture:** The implementation proceeds in four phases.
Phase A externalizes `PshInternalCat D` to a functor `D^op => Cat`
by evaluating the internal category structure pointwise.  Phase B
defines internal presheaves (actions/modules for the internal
category monoid).  Phase C constructs the equivalence with
presheaves on the Grothendieck construction.  Phase D generalizes
from Cat-valued to FunctorData-valued functors via the reflective
adjunction `L -| Phi`.

**Tech Stack:** Lean 4, mathlib (CategoryTheory, Grothendieck,
Mon\_), existing GebLean infrastructure (PshInternalCat,
presheafPullback, GrothendieckContra, CategoryJudgments,
CatJudgmentAdjunction)

---

## File Structure

- `GebLean/PshInternalExternalize.lean` (create):
  Externalization functor
  `PshInternalCat C => C^op => Cat`,
  pointwise category extraction, functoriality
- `GebLean/PshInternalPresheaf.lean` (create):
  `PshInternalPresheaf` structure, morphisms,
  category instance
- `GebLean/PshInternalGrothendieck.lean` (create):
  Equivalence
  `PshInternalPresheaf(X) ~= Psh(Gr(ext(X)))`
- `GebLean/FunctorDataInternalCat.lean` (create):
  FunctorData-valued internal categories,
  reflection to Cat, copresheaf-on-product
  perspective
- `GebLean/PshInternalCat.lean` (modify):
  Extract pointwise evaluation helpers into
  standalone lemmas for reuse
- `GebLean.lean` (modify):
  Add imports for new modules
- `test/TestPshInternalPresheaf.lean` (create):
  Tests for internal presheaf constructions
- `test/TestPshInternalGrothendieck.lean` (create):
  Tests for the Grothendieck equivalence

---

## Phase A: Externalization

### Task 1: Pointwise Category Extraction

Extract a small category from a `PshInternalCat` at each stage
`c : C^op` by evaluating presheaves and natural transformations
pointwise.

**Files:**

- Create: `GebLean/PshInternalExternalize.lean`
- Reference: `GebLean/PshInternalCat.lean:22-115` (PshInternalCat
  structure, component definitions)
- Reference: `GebLean/Utilities/Presheaf.lean:166-270`
  (presheafPullback infrastructure)

- [ ] **Step 1: Create file with imports and section**

```lean
import GebLean.PshInternalCat
import GebLean.Utilities.Grothendieck
import Mathlib.CategoryTheory.Category.Cat

namespace GebLean

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C]
variable (X : PshInternalCat.{u, v, w} C)

section PointwiseCategory
```

- [ ] **Step 2: Define the pointwise object and morphism types**

At each `c : C^op`, the internal category yields a type of
objects and a type of morphisms:

```lean
abbrev PshInternalCat.fiberObj
    (c : Cᵒᵖ) : Type w :=
  X.objPresheaf.obj c

abbrev PshInternalCat.fiberMor
    (c : Cᵒᵖ) : Type w :=
  X.morPresheaf.obj c
```

Build, verify no errors.

- [ ] **Step 3: Define source, target, identity at a stage**

```lean
abbrev PshInternalCat.fiberSrc
    (c : Cᵒᵖ) :
    X.fiberMor c -> X.fiberObj c :=
  X.src.app c

abbrev PshInternalCat.fiberTgt
    (c : Cᵒᵖ) :
    X.fiberMor c -> X.fiberObj c :=
  X.tgt.app c

abbrev PshInternalCat.fiberId
    (c : Cᵒᵖ) :
    X.fiberObj c -> X.fiberMor c :=
  X.idMap.app c
```

Build, verify no errors.

- [ ] **Step 4: Define composable pairs at a stage**

The composable pairs at stage `c` are the presheaf pullback
of `tgt` and `src` evaluated at `c`.  This is
`{ (m1, m2) | fiberTgt m1 = fiberSrc m2 }`.

```lean
abbrev PshInternalCat.fiberCompPairs
    (c : Cᵒᵖ) : Type w :=
  (presheafPullback X.tgt X.src).obj c
```

Verify this matches the expected sigma type by writing a
`#check` or by inspecting via `lean_goal`.

Build, verify no errors.

- [ ] **Step 5: Define composition at a stage**

```lean
abbrev PshInternalCat.fiberComp
    (c : Cᵒᵖ) :
    X.fiberCompPairs c -> X.fiberMor c :=
  X.compMap.app c
```

Build, verify no errors.

- [ ] **Step 6: Prove category axioms at each stage**

Prove the category laws by evaluating the internal category
axioms (which hold as natural transformation equalities) at the
stage `c`.  Each axiom of PshInternalCat (from the Mon\_ monoid
structure in the span bicategory endomorphism category) yields a
pointwise equality at `c`.

The identity laws and associativity arise from the monoid axioms
`X.cat.one_mul`, `X.cat.mul_one`, `X.cat.mul_assoc` evaluated
at the appropriate components.

Define:

```lean
instance PshInternalCat.fiberCategory
    (c : Cᵒᵖ) :
    Category (X.fiberObj c) where
  Hom a b := { m : X.fiberMor c //
    X.fiberSrc c m = a /\ X.fiberTgt c m = b }
  id a := <proof using fiberId and id axioms>
  comp f g := <proof using fiberComp and comp axioms>
  id_comp := <proof from one_mul>
  comp_id := <proof from mul_one>
  assoc := <proof from mul_assoc>
```

Use underscores to inspect goals at each step.  Derive the
proofs from the monoid axioms of `X.cat` evaluated at `c`.
This is the most technically involved step: the monoid axioms
are stated as equalities of 1-cells in the span bicategory
endomorphism category, and evaluating them at `c` requires
unfolding the span composition (pullback) and checking that
the pointwise maps agree.

Build after each sub-proof.  If any individual axiom is
hard, factor it into a separate lemma.

- [ ] **Step 7: Build and verify**

Run `lake build` and `lake test`.  Fix all errors before
proceeding.

- [ ] **Step 8: Commit**

```bash
git add GebLean/PshInternalExternalize.lean
git commit -m "feat: pointwise category extraction from PshInternalCat"
```

### Task 2: Externalization Functor

Build the functor `ext : PshInternalCat C => C^op => Cat` and
verify functoriality (restriction along morphisms of `C` gives
functors between fiber categories).

**Files:**

- Modify: `GebLean/PshInternalExternalize.lean`

- [ ] **Step 1: Define restriction functor on objects and morphisms**

For a morphism `f : c' --> c` in `C^op`, the restriction maps
`objPresheaf.map f` and `morPresheaf.map f` yield a functor
between the fiber categories.  The functor laws follow from
naturality of `src`, `tgt`, `idMap`, `compMap`.

```lean
def PshInternalCat.fiberRestrict
    {c c' : Cᵒᵖ} (f : c ⟶ c') :
    X.fiberObj c ⥤ X.fiberObj c' where
  obj a := X.objPresheaf.map f a
  map m := <subtype constructed from morPresheaf.map f m.val,
            with src/tgt proofs from naturality>
  map_id := <from naturality of idMap>
  map_comp := <from naturality of compMap>
```

Build after defining, using underscores for proofs initially.

- [ ] **Step 2: Prove restriction functoriality**

Show that `fiberRestrict (f >>> g) = fiberRestrict f >>> fiberRestrict g`
and `fiberRestrict (id c) = id`.  These follow from `Functor.map_id`
and `Functor.map_comp` of the underlying presheaves.

```lean
theorem PshInternalCat.fiberRestrict_id
    (c : Cᵒᵖ) :
    X.fiberRestrict (𝟙 c) = 𝟙 _ := by
  <proof using objPresheaf.map_id, morPresheaf.map_id>

theorem PshInternalCat.fiberRestrict_comp
    {c c' c'' : Cᵒᵖ} (f : c ⟶ c') (g : c' ⟶ c'') :
    X.fiberRestrict (f ≫ g) =
      X.fiberRestrict f ⋙ X.fiberRestrict g := by
  <proof using objPresheaf.map_comp, morPresheaf.map_comp>
```

- [ ] **Step 3: Assemble the externalization functor on objects**

```lean
def PshInternalCat.externalize :
    Cᵒᵖ ⥤ Cat.{w, w} where
  obj c := Cat.of (X.fiberObj c)
  map f := (X.fiberRestrict f).toCatHom
  map_id c := Cat.Hom.ext (X.fiberRestrict_id c)
  map_comp f g := Cat.Hom.ext (X.fiberRestrict_comp f g)
```

Build, verify no errors.

- [ ] **Step 4: Extend externalization to PshInternalFunctor**

An internal functor `F : X --> Y` externalizes to a natural
transformation `ext(X) --> ext(Y)` whose component at `c` is the
functor given by evaluating `F.objMap` and `F.morMap` at `c`.

```lean
def PshInternalFunctor.externalize
    {X Y : PshInternalCat.{u, v, w} C}
    (F : PshInternalFunctor X Y) :
    X.externalize ⟶ Y.externalize where
  app c := (fiberFunctor F c).toCatHom
  naturality := <proof from naturality of objMap, morMap>
```

where `fiberFunctor` constructs the functor at each stage from
the compatibility conditions of PshInternalFunctor.

- [ ] **Step 5: Prove the externalization is functorial**

Show `externalize` preserves identity and composition of
internal functors.

- [ ] **Step 6: Build and verify**

Run `lake build` and `lake test`.

- [ ] **Step 7: Commit**

```bash
git add GebLean/PshInternalExternalize.lean
git commit -m "feat: externalization functor PshInternalCat -> [C^op, Cat]"
```

### Task 3: Equivalence at Discrete Unit

Verify that the externalization at `Discrete Unit` is compatible
with the existing `catPshInternalEquiv`.

**Files:**

- Modify: `GebLean/PshInternalExternalize.lean`
- Reference: `GebLean/PshInternalCat.lean:1419-1426`
  (catPshInternalEquiv)

- [ ] **Step 1: State the compatibility theorem**

For `X : PshInternalCat (Discrete Unit)`, the fiber category at
the unique object should be isomorphic to `pshInternalCatToCat X`
(the extraction used in catPshInternalEquiv).

```lean
def externalize_unit_compat
    (X : PshInternalCat.{0, 0, w} (Discrete Unit)) :
    X.fiberObj (Opposite.op (Discrete.mk ())) ≅
      icObj X := by
  <construct isomorphism>
```

This should be straightforward since both constructions evaluate
the same presheaf at the same point.

- [ ] **Step 2: Prove the isomorphism is a category equivalence**

Show the isomorphism respects the category structures on both
sides.

- [ ] **Step 3: Build, verify, commit**

Run `lake build` and `lake test`.

```bash
git add GebLean/PshInternalExternalize.lean
git commit -m "feat: externalization compatibility with catPshInternalEquiv"
```

---

## Phase B: Internal Presheaves

### Task 4: PshInternalPresheaf Structure

Define internal presheaves (right actions) for an internal
category in a presheaf topos.

**Files:**

- Create: `GebLean/PshInternalPresheaf.lean`
- Reference: `GebLean/Utilities/Presheaf.lean:220-270`
  (presheafPullback, presheafPullbackLift)
- Reference: `GebLean/PshInternalCat.lean:22-115`

- [ ] **Step 1: Create file with imports**

```lean
import GebLean.PshInternalCat
import GebLean.PshInternalExternalize

namespace GebLean

open CategoryTheory

universe u v w
```

- [ ] **Step 2: Define the internal presheaf structure**

An internal presheaf on `X : PshInternalCat C` consists of a
"fiber" presheaf with a projection to the object presheaf, an
action by the morphism presheaf, and axioms.

```lean
structure PshInternalPresheaf
    {C : Type u} [Category.{v} C]
    (X : PshInternalCat.{u, v, w} C) where
  /-- The presheaf of elements. -/
  fiber : Cᵒᵖ ⥤ Type w
  /-- Projection to the object presheaf of X. -/
  proj : fiber ⟶ X.objPresheaf
  /-- The action of morphisms on elements.
      The domain is the pullback of `proj` and `X.src`:
      pairs `(e, m)` with `proj(e) = src(m)`. -/
  action :
    presheafPullback proj X.src ⟶ fiber
  /-- The action maps to the target of the morphism. -/
  action_tgt :
    action ≫ proj =
      presheafPullbackSnd proj X.src ≫ X.tgt
  /-- Acting by the identity morphism is the identity. -/
  action_id :
    presheafPullbackLift proj X.src
      (𝟙 fiber) (proj ≫ X.idMap)
      (by <proof that proj = proj >>> idMap >>> src>) ≫
    action = 𝟙 fiber
  /-- Acting by a composite morphism equals acting
      sequentially. -/
  action_assoc :
    <appropriate diagram involving compMap commutes>
```

The `action_id` and `action_assoc` axioms encode that the
identity morphism of X acts trivially and that the action
respects composition in X.  The precise statements involve
mediating through the pullback universal property.

Use underscores to determine the exact types of `action_id`
and `action_assoc` by inspecting goals.

Build after each field.

- [ ] **Step 3: Define convenience accessors**

```lean
abbrev PshInternalPresheaf.fiberAt
    (P : PshInternalPresheaf X) (c : Cᵒᵖ) :
    Type w :=
  P.fiber.obj c

abbrev PshInternalPresheaf.projAt
    (P : PshInternalPresheaf X)
    (c : Cᵒᵖ) :
    P.fiberAt c -> X.fiberObj c :=
  P.proj.app c
```

- [ ] **Step 4: Build and verify**

Run `lake build` and `lake test`.

- [ ] **Step 5: Commit**

```bash
git add GebLean/PshInternalPresheaf.lean
git commit -m "feat: PshInternalPresheaf structure definition"
```

### Task 5: Internal Presheaf Morphisms and Category

Define morphisms between internal presheaves and prove they form
a category.

**Files:**

- Modify: `GebLean/PshInternalPresheaf.lean`

- [ ] **Step 1: Define morphisms**

A morphism of internal presheaves is a natural transformation
between fiber presheaves that commutes with projection and
action.

```lean
structure PshInternalPresheafHom
    {X : PshInternalCat.{u, v, w} C}
    (P Q : PshInternalPresheaf X) where
  /-- The map between fiber presheaves. -/
  map : P.fiber ⟶ Q.fiber
  /-- Commutes with projection. -/
  proj_comm : map ≫ Q.proj = P.proj
  /-- Commutes with action. -/
  action_comm :
    presheafPullbackLift Q.proj X.src
      (presheafPullbackFst P.proj X.src ≫ map)
      (presheafPullbackSnd P.proj X.src)
      (by rw [Category.assoc, proj_comm,
              presheafPullbackCondition]) ≫
    Q.action =
    P.action ≫ map
```

Build, verify no errors.

- [ ] **Step 2: Define identity and composition**

```lean
def PshInternalPresheafHom.id
    (P : PshInternalPresheaf X) :
    PshInternalPresheafHom P P where
  map := 𝟙 P.fiber
  proj_comm := Category.id_comp _
  action_comm := <proof>

def PshInternalPresheafHom.comp
    {P Q R : PshInternalPresheaf X}
    (f : PshInternalPresheafHom P Q)
    (g : PshInternalPresheafHom Q R) :
    PshInternalPresheafHom P R where
  map := f.map ≫ g.map
  proj_comm := by
    rw [Category.assoc, g.proj_comm, f.proj_comm]
  action_comm := <proof>
```

- [ ] **Step 3: Prove category axioms**

```lean
instance PshInternalPresheaf.category
    (X : PshInternalCat.{u, v, w} C) :
    Category (PshInternalPresheaf X) where
  Hom := PshInternalPresheafHom
  id := PshInternalPresheafHom.id
  comp := PshInternalPresheafHom.comp
  id_comp := <proof via ext>
  comp_id := <proof via ext>
  assoc := <proof via ext>
```

The key extensionality principle: two internal presheaf
morphisms are equal iff their underlying natural
transformations (`map` fields) are equal.

- [ ] **Step 4: Build and verify**

Run `lake build` and `lake test`.

- [ ] **Step 5: Commit**

```bash
git add GebLean/PshInternalPresheaf.lean
git commit -m "feat: category of internal presheaves"
```

### Task 6: Span-Bicategory Module Interpretation

Relate the direct definition of PshInternalPresheaf to the
span-bicategory module perspective: an internal presheaf is a
right module for the monoid `X.cat` in the endomorphism monoidal
category, acting via span composition from a terminal 0-cell.

**Files:**

- Modify: `GebLean/PshInternalPresheaf.lean`
- Reference: `GebLean/PshSpanBicategory.lean`
- Reference: `Mathlib.CategoryTheory.Monoidal.Mon_`

- [ ] **Step 1: Define the span-bicategory formulation**

A right module for `X.cat` consists of:

- A 1-cell
  `S : PshSpanBicat.Hom (terminal) X.objs`
  (a span `1 <-- fiber --> Ob`)
- An action 2-cell composing S with X.cat's
  underlying 1-cell

State the structure and note its equivalence to
`PshInternalPresheaf`.

```lean
structure PshInternalModule
    (X : PshInternalCat.{u, v, w} C) where
  carrier : PshProdOver
    (Functor.star (Cᵒᵖ) (Type w)) X.objPresheaf
  action : pshProdOverComp carrier X.morSpan ⟶ carrier
  action_id : <unit axiom>
  action_assoc : <associativity axiom>
```

- [ ] **Step 2: Construct equivalence between the two formulations**

Show `PshInternalPresheaf X ~= PshInternalModule X` by
translating between the pullback-based and span-composition-based
action maps.

- [ ] **Step 3: Build, verify, commit**

Run `lake build` and `lake test`.

```bash
git add GebLean/PshInternalPresheaf.lean
git commit -m "feat: span-bicategory module interpretation of internal presheaves"
```

---

## Phase C: Grothendieck Equivalence

### Task 7: Grothendieck Construction of Externalized Internal Category

Apply the existing `GrothendieckContra` to the externalized
functor to obtain the total category.

**Files:**

- Create: `GebLean/PshInternalGrothendieck.lean`
- Reference: `GebLean/PshInternalExternalize.lean`
- Reference: `GebLean/Utilities/Grothendieck.lean:64-80`

- [ ] **Step 1: Create file and define the total category**

```lean
import GebLean.PshInternalExternalize
import GebLean.PshInternalPresheaf

namespace GebLean

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C]
variable (X : PshInternalCat.{u, v, w} C)

def PshInternalCat.grothendieck :
    Cat.{max v w, max u w} :=
  GrothendieckContraCat X.externalize
```

Build, verify the universe levels work out.

- [ ] **Step 2: Examine the concrete structure**

Verify that objects of `X.grothendieck` are pairs
`(c : C, x : X.fiberObj (op c))` and morphisms are pairs
`(f : c --> c', phi : x --> restrict(f)(x'))`.

Use `#check` and `lean_hover_info` to confirm the concrete
types.

- [ ] **Step 3: Build and commit**

```bash
git add GebLean/PshInternalGrothendieck.lean
git commit -m "feat: Grothendieck construction of externalized internal category"
```

### Task 8: Comparison Functor (Internal Presheaves to Presheaves on Grothendieck)

Construct the functor from internal presheaves on X to
presheaves on the Grothendieck total category.

**Files:**

- Modify: `GebLean/PshInternalGrothendieck.lean`

- [ ] **Step 1: Define the functor on objects**

An internal presheaf `P : PshInternalPresheaf X` gives a
presheaf on `Gr(ext(X))^op` as follows.  At an object
`(c, x)` of the Grothendieck category, the value is the
fiber of `P` over `x` at stage `c`:
  `{ e : P.fiberAt c | P.projAt c e = x }`

For a morphism `(f, phi) : (c, x) --> (c', x')`, the
restriction acts by `P.fiber.map (op f)` followed by
`P.action` along `phi`.

```lean
def PshInternalPresheaf.toGrothendieckPresheaf
    {X : PshInternalCat.{u, v, w} C}
    (P : PshInternalPresheaf X) :
    X.grothendieck.α^op ⥤ Type w where
  obj p :=
    let ⟨c, x⟩ := p.unop
    { e : P.fiberAt (Opposite.op c) //
      P.projAt (Opposite.op c) e = x }
  map f :=
    <construct using P.fiber.map and P.action>
  map_id := <proof>
  map_comp := <proof>
```

Build one field at a time using underscores.

- [ ] **Step 2: Define the functor on morphisms**

A morphism of internal presheaves `f : P --> Q` induces a
natural transformation between the corresponding
Grothendieck presheaves.

```lean
def PshInternalPresheafHom.toGrothendieckNatTrans
    {P Q : PshInternalPresheaf X}
    (f : PshInternalPresheafHom P Q) :
    P.toGrothendieckPresheaf ⟶
    Q.toGrothendieckPresheaf where
  app p := fun ⟨e, he⟩ =>
    ⟨f.map.app _ e, by rw [<proj_comm>; exact he]⟩
  naturality := <proof>
```

- [ ] **Step 3: Assemble the comparison functor**

```lean
def comparisonFunctor
    (X : PshInternalCat.{u, v, w} C) :
    PshInternalPresheaf X ⥤
    (X.grothendieck.α^op ⥤ Type w) where
  obj := PshInternalPresheaf.toGrothendieckPresheaf
  map := PshInternalPresheafHom.toGrothendieckNatTrans
  map_id := <proof>
  map_comp := <proof>
```

- [ ] **Step 4: Build and commit**

```bash
git add GebLean/PshInternalGrothendieck.lean
git commit -m "feat: comparison functor internal presheaves to Grothendieck"
```

### Task 9: Inverse Functor and Equivalence

Construct the inverse direction and prove the equivalence.

**Files:**

- Modify: `GebLean/PshInternalGrothendieck.lean`

- [ ] **Step 1: Define the inverse functor on objects**

Given a presheaf `G : Gr(ext(X))^op => Type w`, construct an
internal presheaf on X.  The fiber presheaf at stage `c` is
the disjoint union over objects `x : X.fiberObj c`:
  `fiber.obj c = Sigma (x : X.fiberObj c), G.obj (op (c, x))`

The projection sends `(x, e)` to `x`.  The action uses `G.map`
applied to the Grothendieck morphism `(id_c, m)` where `m` is
the internal morphism.

```lean
def grothendieckPresheafToInternal
    (G : X.grothendieck.α^op ⥤ Type w) :
    PshInternalPresheaf X where
  fiber := <sigma-type presheaf>
  proj := <first projection>
  action := <using G.map on identity-base morphisms>
  action_tgt := <proof>
  action_id := <proof using G.map_id>
  action_assoc := <proof using G.map_comp>
```

Build one field at a time.

- [ ] **Step 2: Define the inverse functor on morphisms**

Natural transformations `G --> G'` induce internal presheaf
morphisms.

- [ ] **Step 3: Assemble the inverse functor**

```lean
def inverseFunctor
    (X : PshInternalCat.{u, v, w} C) :
    (X.grothendieck.α^op ⥤ Type w) ⥤
    PshInternalPresheaf X where
  obj := grothendieckPresheafToInternal X
  map := <constructed above>
  map_id := <proof>
  map_comp := <proof>
```

- [ ] **Step 4: Prove unit isomorphism**

Show that `inverseFunctor >>> comparisonFunctor ~= id`.
At an object `G`, the round-trip produces a presheaf on
Gr(ext(X)) that at `(c, x)` gives
`{ (x', e) : Sigma ... | x' = x }`, which is isomorphic
to `G.obj (op (c, x))` by the sigma-over-equality
contraction.

```lean
def unitIso (X : PshInternalCat.{u, v, w} C) :
    inverseFunctor X ⋙ comparisonFunctor X ≅
    𝟭 _ := by
  <construct natural isomorphism>
```

- [ ] **Step 5: Prove counit isomorphism**

Show that `comparisonFunctor >>> inverseFunctor ~= id`.
At an internal presheaf `P`, the round-trip produces an
internal presheaf whose fiber at `c` is
`Sigma (x : X.fiberObj c), { e | proj e = x }`, which is
isomorphic to `P.fiberAt c` by the sigma-subtype
equivalence.

```lean
def counitIso (X : PshInternalCat.{u, v, w} C) :
    comparisonFunctor X ⋙ inverseFunctor X ≅
    𝟭 _ := by
  <construct natural isomorphism>
```

- [ ] **Step 6: Assemble the equivalence**

```lean
def pshInternalGrothendieckEquiv
    (X : PshInternalCat.{u, v, w} C) :
    PshInternalPresheaf X ≌
    (X.grothendieck.α^op ⥤ Type w) :=
  Equivalence.mk
    (comparisonFunctor X)
    (inverseFunctor X)
    (counitIso X).symm
    (unitIso X)
```

- [ ] **Step 7: Build and verify**

Run `lake build` and `lake test`.

- [ ] **Step 8: Commit**

```bash
git add GebLean/PshInternalGrothendieck.lean
git commit -m "feat: equivalence PshInternalPresheaf ≌ Psh(Grothendieck)"
```

---

## Phase D: FunctorData Generalization

### Task 10: FunctorData-Valued Internal Categories

Define internal categories where the fiber data is valued in
`FunctorData(Type)` (copresheaves on `CategoryJudgments.Obj`)
rather than in `Cat`.

**Files:**

- Create: `GebLean/FunctorDataInternalCat.lean`
- Reference: `GebLean/CategoryJudgments.lean:242-259`
  (FunctorData structure)
- Reference: `GebLean/CatJudgmentAdjunction.lean:2363-2398`
  (LFunctor, PhiFunctor)
- Reference: `GebLean/CatValuedFunctor.lean:133-136`
  (phiWhiskering\_reflective)

- [ ] **Step 1: Create file with imports**

```lean
import GebLean.PshInternalExternalize
import GebLean.PshInternalGrothendieck
import GebLean.CatValuedFunctor

namespace GebLean

open CategoryTheory CategoryJudgments

universe u v w
```

- [ ] **Step 2: Define FunctorData-valued functors on D^op**

A FunctorData-valued functor on `D^op` assigns to each `d` a
`FunctorData (Type w)` — a proto-category with objects,
morphisms, identities, and composition data (but not
necessarily satisfying category axioms).

This is equivalent to a functor `D^op => (Obj => Type w)`,
i.e., a functor `D^op x Obj => Type w`, i.e., a copresheaf
on `D^op x Obj`.

```lean
abbrev FunctorDataFunctor
    (D : Type u) [Category.{v} D] :=
  D ⥤ FunctorData (Type w)
```

Note: since `FunctorData (Type w)` has a category instance
(from functorDataEquivCat), this is a standard functor
category.

- [ ] **Step 3: Define the copresheaf-on-product equivalence**

Using `functorDataIsoCat`:
`FunctorData(Type w) ~= (Obj => Type w)`, the functor
category `[D^op, FunctorData(Type w)]` is equivalent to
`[D^op, [Obj, Type w]]` which by currying/uncurrying is
`[D^op x Obj, Type w]`.

```lean
def functorDataFunctorEquivCopresheaf
    (D : Type u) [Category.{v} D] :
    FunctorDataFunctor.{u, v, w} D ≌
    (D × Obj ⥤ Type w) := by
  <construct via functorDataEquivCat and currying>
```

This uses the fact that `[C, [D, E]] ~= [C x D, E]` which
is available in mathlib as
`Functor.Currying.functorCategoryEquivalence` or similar.

- [ ] **Step 4: Build and commit**

```bash
git add GebLean/FunctorDataInternalCat.lean
git commit -m "feat: FunctorData-valued functors and copresheaf-on-product equivalence"
```

### Task 11: Reflection to Cat-Valued and Grothendieck Connection

Use the reflective adjunction `L -| Phi` to reflect
FunctorData-valued functors to Cat-valued functors, then
apply the Grothendieck construction.

**Files:**

- Modify: `GebLean/FunctorDataInternalCat.lean`
- Reference: `GebLean/CatValuedFunctor.lean:86-103`
  (lWhiskering, phiWhiskering, adjunction)

- [ ] **Step 1: Define the reflection from FunctorData-valued to Cat-valued**

Using `lWhiskering D^op`:
`[D^op, FunctorData(Type)] => [D^op, BundledOverCategoryData]`
which is then equivalent to `[D^op, Cat]` via the category
equivalence on BundledOverCategoryData.

```lean
def reflectToCat
    {D : Type u} [Category.{v} D]
    (F : Dᵒᵖ ⥤ FunctorData (Type u)) :
    Dᵒᵖ ⥤ Cat.{u, u} :=
  F ⋙ LFunctor ⋙ overToCatFunctor
```

(Adjust based on the exact composition chain in the codebase.)

- [ ] **Step 2: Define the Grothendieck construction of the reflected functor**

```lean
def FunctorDataFunctor.grothendieck
    {D : Type u} [Category.{v} D]
    (F : Dᵒᵖ ⥤ FunctorData (Type u)) :
    Cat :=
  GrothendieckContraCat (reflectToCat F)
```

- [ ] **Step 3: State the adjunction between FD-Grothendieck and Cat-Grothendieck**

The adjunction `L -| Phi` lifts to an adjunction between
the Grothendieck constructions.  State this:

```lean
theorem grothendieck_adjunction
    {D : Type u} [Category.{v} D]
    (F : Dᵒᵖ ⥤ FunctorData (Type u)) :
    <appropriate adjunction statement relating
     Grothendieck of F to Grothendieck of reflectToCat F>
```

The precise formulation depends on how the Grothendieck
construction interacts with the adjunction.  Since `L` is a
left adjoint and Grothendieck is a colimit-like construction,
there should be a canonical comparison.

- [ ] **Step 4: Build and commit**

```bash
git add GebLean/FunctorDataInternalCat.lean
git commit -m "feat: reflection of FunctorData-valued functors to Cat and Grothendieck"
```

### Task 12: Integration and Connection to PshInternalCat

Connect the FunctorData perspective to the existing
PshInternalCat formulation: an internal category in `[D^op, Set]`
can be seen as a `D^op`-indexed family of `FunctorData` objects
(the pointwise proto-category data), and the internal category
axioms are the condition that each fiber is an actual category
(i.e., lies in the image of `Phi`).

**Files:**

- Modify: `GebLean/FunctorDataInternalCat.lean`

- [ ] **Step 1: Define the FunctorData extraction from PshInternalCat**

From a `PshInternalCat D`, extract at each `d` the
`FunctorData` consisting of the pointwise objects,
morphisms, identity, and composition data.

```lean
def PshInternalCat.toFunctorDataFunctor
    (X : PshInternalCat.{u, v, w} C) :
    Cᵒᵖ ⥤ FunctorData (Type w) where
  obj c := {
    objC := X.fiberObj c,
    morC := X.fiberMor c,
    dom := X.fiberSrc c,
    cod := X.fiberTgt c,
    idMor := X.fiberId c,
    -- remaining fields from composable-pairs structure
  }
  map f := <restriction NatTransData>
  map_id := <proof>
  map_comp := <proof>
```

- [ ] **Step 2: Show the extracted FunctorData lies in the image of Phi**

Since each fiber of a PshInternalCat is an actual category
(by Task 1), the FunctorData at each stage is in the
image of `PhiFunctor`.  The internal category axioms are
the condition for this:

```lean
theorem PshInternalCat.fiberInPhiImage
    (X : PshInternalCat.{u, v, w} C) (c : Cᵒᵖ) :
    <X.toFunctorDataFunctor.obj c is isomorphic to
     PhiFunctorObj of some BundledOverCategoryData> := by
  <proof>
```

- [ ] **Step 3: Show compatibility of the two Grothendieck constructions**

The Grothendieck construction of `reflectToCat(X.toFunctorDataFunctor)`
should be equivalent to `X.grothendieck` (from Phase C).

```lean
def grothendieckCompat
    (X : PshInternalCat.{u, v, w} C) :
    FunctorDataFunctor.grothendieck
      X.toFunctorDataFunctor ≅
    X.grothendieck := by
  <construct isomorphism>
```

- [ ] **Step 4: Build and verify full integration**

Run `lake build` and `lake test`.

- [ ] **Step 5: Commit**

```bash
git add GebLean/FunctorDataInternalCat.lean
git commit -m "feat: FunctorData integration with PshInternalCat and Grothendieck"
```

---

## Final Integration

### Task 13: Module Registration and Tests

Add imports to the root module and write integration tests.

**Files:**

- Modify: `GebLean.lean`
- Create: `test/TestPshInternalPresheaf.lean`
- Create: `test/TestPshInternalGrothendieck.lean`

- [ ] **Step 1: Add imports to GebLean.lean**

```lean
import GebLean.PshInternalExternalize
import GebLean.PshInternalPresheaf
import GebLean.PshInternalGrothendieck
import GebLean.FunctorDataInternalCat
```

- [ ] **Step 2: Write test for externalization**

Test that for a known internal category (e.g., the one
corresponding to a specific small category via
`catToPshInternalCat`), the externalization produces the
expected fiber categories.

```lean
-- test/TestPshInternalPresheaf.lean
import GebLean

open GebLean CategoryTheory

-- Test: externalization of catToPshInternalCat recovers
-- the original category
#guard <appropriate guard>
```

- [ ] **Step 3: Write test for the Grothendieck equivalence**

Test the round-trip on a concrete example: take a small
category, internalize it, form presheaves, and verify the
equivalence produces the expected presheaf category.

- [ ] **Step 4: Build and verify everything**

Run `lake build` and `lake test`.

- [ ] **Step 5: Commit**

```bash
git add GebLean.lean test/TestPshInternalPresheaf.lean \
  test/TestPshInternalGrothendieck.lean
git commit -m "feat: integration tests for internal presheaf Grothendieck equivalence"
```

---

## Summary of Dependencies

```text
Task 1 (pointwise extraction)
  |
  v
Task 2 (externalization functor) ---> Task 3 (Unit compat)
  |
  v
Task 4 (PshInternalPresheaf) ---> Task 5 (morphisms/category)
  |                                   |
  v                                   v
Task 6 (span-bicategory module)  Task 7 (Gr of ext)
                                      |
                                      v
                                 Task 8 (comparison functor)
                                      |
                                      v
                                 Task 9 (inverse + equivalence)
                                      |
Task 10 (FD-valued functors) --------+
  |
  v
Task 11 (reflect to Cat + Gr) ---> Task 12 (integration)
                                      |
                                      v
                                 Task 13 (tests + imports)
```

## Risk Assessment

**Highest risk:** Task 1, Step 6 (proving category axioms
pointwise from monoid axioms in the span bicategory).  The
monoid axioms involve span composition (pullbacks) and
evaluating them pointwise requires unfolding the pullback
universal property.  Mitigation: factor lemmas to relate
span-bicategory composition evaluated at a point to the
pointwise pullback of the component natural transformations.

**Medium risk:** Task 9 (inverse functor and round-trip proofs).
The sigma-subtype contractions needed for the unit and counit
isomorphisms can involve nontrivial dependent-type reasoning.
Mitigation: use `Sigma.mk` / `Subtype.val` extensionality and
`proof_irrel_heq` patterns from the utilities.

**Medium risk:** Task 11 (Grothendieck--adjunction interaction).
The precise statement of how the Grothendieck construction
interacts with the `L -| Phi` adjunction needs to be worked out
during implementation.  Mitigation: start with the concrete
compatibility (Task 12, Step 3) which is more tractable, and
derive the abstract statement from it.

**Lower risk:** Tasks 4-5 (internal presheaf structure and
category).  These are standard structure definitions following
patterns established by `PshInternalCat` and `PshInternalFunctor`.
