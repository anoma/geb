# PolyFunctorBetweenCat ≌ PresheafPRACat (Discrete) Equivalence

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:executing-plans to implement this plan
> task-by-task.  Steps use checkbox (`- [ ]`) syntax
> for tracking.

**Goal:** Prove that `PolyFunctorBetweenCat X Y` is
equivalent to `PresheafPRACat (Discrete X) (Discrete Y)`
when the base categories are discrete (types).

**Architecture:** The equivalence is built by composing
four categorical equivalences, each operating at one
level of the definition hierarchy.  Each step is a named
`def` producing an `Equivalence` or `NatIso`, and the
final equivalence is their composition.  Universe
annotations are explicit throughout.

**Tech Stack:** Lean 4, mathlib (`Discrete.opposite`,
`piEquivalenceFunctorDiscrete`, `Equivalence`,
`FullyFaithful`), existing GebLean infrastructure
(`familySliceEquiv`, `opToOp'`/`op'ToOp`,
`CoprodCovarRepCat'`, `CoprodCovarRepCat`,
`PresheafPRACat`, `praEvalAtFunctor`).

---

## File Structure

| File | Responsibility |
| ---- | -------------- |
| `GebLean/PresheafPRADiscrete.lean` | New |
| `GebLean.lean` | Add import |
| `test/PresheafPRADiscrete.lean` | Optional tests |

## Background

### Definitions to connect

```text
PolyFunctorBetweenCat X Y
  = FamilyCat (CoprodCovarRepCat' (Over X)) Y
  where CoprodCovarRepCat' uses op' and
        GrothendieckContra'

PresheafPRACat (Discrete X) (Discrete Y)
  = (Discrete Y)ᵒᵖ ⥤
      CoprodCovarRepCat ((Discrete X)ᵒᵖ ⥤ Type)
  where CoprodCovarRepCat uses op and
        Grothendieck
```

### Equivalence chain

```text
FamilyCat (CoprodCovarRepCat' (Over X)) Y
  ≌  (step 1: familySliceEquiv⁻¹ on Over X)
FamilyCat (CoprodCovarRepCat' (FamilyCat (Type) X)) Y
  ≌  (step 2: piEquivalenceFunctorDiscrete + op' stuff)
FamilyCat (CoprodCovarRepCat' ((Discrete X)ᵒᵖ' ⥤ Type)) Y
  ≌  (step 3: op'/op transfer on CoprodCovarRepCat)
FamilyCat (CoprodCovarRepCat ((Discrete X)ᵒᵖ ⥤ Type)) Y
  ≌  (step 4: piEquivalenceFunctorDiscrete +
              Discrete.opposite on Y)
((Discrete Y)ᵒᵖ ⥤ CoprodCovarRepCat ((Discrete X)ᵒᵖ ⥤ Type))
  = PresheafPRACat (Discrete X) (Discrete Y)
```

### Mathlib pieces

- `piEquivalenceFunctorDiscrete J C :
    (J → C) ≌ (Discrete J ⥤ C)`
- `Discrete.opposite α :
    (Discrete α)ᵒᵖ ≌ Discrete α`
- `familySliceEquiv :
    FamilyCat (Type u) Y ≌ Over Y`
  (in `GebLean/Polynomial.lean`)

### Op'/op transfer pieces (in Opposites.lean)

- `opToOp' : Cᵒᵖ ⥤ Cᵒᵖ'`
- `op'ToOp : Cᵒᵖ' ⥤ Cᵒᵖ`
- `opFunctorIsoOpFunctor' :
    Cat.opFunctor ≅ opFunctor'`

---

## Tasks

### Task 0: Verify prerequisites compile

**Files:**

- Read: `GebLean/Polynomial.lean` (familySliceEquiv)
- Read: `GebLean/Utilities/Opposites.lean` (op'/op)
- Read: `GebLean/PresheafPRA.lean` (PresheafPRACat)

- [ ] **Step 0.1:** In a scratch area, verify that
  `piEquivalenceFunctorDiscrete`,
  `Discrete.opposite`, `familySliceEquiv`,
  `opToOp'`/`op'ToOp` are all accessible and their
  universe levels are compatible.  Write explicit
  `#check` statements with universe annotations.

- [ ] **Step 0.2:** Verify that
  `PresheafPRACat (Discrete X) (Discrete Y)` with
  `v_I = 0, u_I = u, v_J = 0, u_J = u` unfolds to
  something equivalent to
  `(Discrete Y)ᵒᵖ ⥤ CoprodCovarRepCat ((Discrete X)ᵒᵖ ⥤ Type u)`.

- [ ] **Step 0.3:** Verify that
  `PolyFunctorBetweenCat X Y` unfolds to
  `FamilyCat (CoprodCovarRepCat' (Over X)) Y`.

### Task 1: CoprodCovarRepCat' ≌ CoprodCovarRepCat equivalence

**Files:**

- Modify: `GebLean/Utilities/Families.lean`

This is the op'/op transfer at the CoprodCovarRepCat
level.  Both are Grothendieck constructions on the
family functor composed with oppositization, but one
uses `op'`/`GrothendieckContra'` and the other uses
`op`/`Grothendieck`.

- [ ] **Step 1.1:** Define
  `ccrOp'OpEquiv (C : Type u) [Category.{v} C] :
    CoprodCovarRepCat'.{u, v, w} C ≌
      CoprodCovarRepCat.{u, v, w} C`
  using the `opToOp'`/`op'ToOp` functors composed
  with the Grothendieck equivalences.

- [ ] **Step 1.2:** Build and verify no errors.

### Task 2: Over X ≌ presheaf on Discrete X

**Files:**

- Modify: `GebLean/Utilities/Presheaf.lean` or
  create `GebLean/PresheafPRADiscrete.lean`

The equivalence `Over X ≌ ((Discrete X)ᵒᵖ ⥤ Type u)`
composes `familySliceEquiv⁻¹` with
`piEquivalenceFunctorDiscrete` and
`Discrete.opposite`.

- [ ] **Step 2.1:** Define the equivalence
  `overDiscretePresheafEquiv (X : Type u) :
    Over X ≌ ((Discrete X)ᵒᵖ ⥤ Type u)`.

  This composes:
  1. `familySliceEquiv.symm : Over X ≌ FamilyCat (Type u) X`
     = `Over X ≌ (X → Type u)`
  2. `piEquivalenceFunctorDiscrete X (Type u) :
       (X → Type u) ≌ (Discrete X ⥤ Type u)`
  3. Precomposition with `Discrete.opposite X :
       (Discrete X)ᵒᵖ ≌ Discrete X` to get
     `(Discrete X ⥤ Type u) ≌ ((Discrete X)ᵒᵖ ⥤ Type u)`

  Step 3 uses the equivalence
  `(Discrete.opposite X).congrRight (Type u)` or
  similar.

- [ ] **Step 2.2:** Build and verify.

### Task 3: Inner equivalence (CoprodCovarRepCat level)

**Files:**

- Modify: `GebLean/PresheafPRADiscrete.lean`

Combine Tasks 1 and 2 to get:
`CoprodCovarRepCat' (Over X) ≌
  CoprodCovarRepCat ((Discrete X)ᵒᵖ ⥤ Type u)`

- [ ] **Step 3.1:** Define
  `ccrOverDiscreteEquiv (X : Type u) :
    CoprodCovarRepCat' (Over X) ≌
      CoprodCovarRepCat ((Discrete X)ᵒᵖ ⥤ Type u)`
  by composing `ccrOp'OpEquiv` with the functorial
  lift of `overDiscretePresheafEquiv` through
  `CoprodCovarRepCat`.

  This may require a lemma that
  `CoprodCovarRepCat`/`CoprodCovarRepCat'` is
  functorial in `C` (which it is via
  `coprodCovarRepFunctor` for the unprimed version
  and existing infrastructure for the primed version).

- [ ] **Step 3.2:** Build and verify.

### Task 4: Outer equivalence (FamilyCat/presheaf level)

**Files:**

- Modify: `GebLean/PresheafPRADiscrete.lean`

Lift the inner equivalence through the family/presheaf
layer to get the full equivalence:
`PolyFunctorBetweenCat X Y ≌
  PresheafPRACat (Discrete X) (Discrete Y)`

- [ ] **Step 4.1:** Define
  `polyBetweenPresheafPRAEquiv (X Y : Type u) :
    PolyFunctorBetweenCat X Y ≌
      PresheafPRACat (Discrete X) (Discrete Y)`
  by composing `ccrOverDiscreteEquiv` lifted through
  `FamilyCat`/presheaf with the family-to-presheaf
  equivalence on `Y`.

  This uses:
  - `piEquivalenceFunctorDiscrete Y` composed with
    `Discrete.opposite Y` on the outer layer
  - The inner `ccrOverDiscreteEquiv X`

- [ ] **Step 4.2:** Build and verify.

### Task 5: Compatibility with evaluation

**Files:**

- Modify: `GebLean/PresheafPRADiscrete.lean`

Show that the equivalence is compatible with the
evaluation functors: the evaluation of a
`PolyFunctorBetweenCat` polynomial agrees with the
evaluation of its image under the equivalence via
`praEvalAtFunctor`.

- [ ] **Step 5.1:** State and prove
  `polyBetweenPresheafPRAEquiv_eval :
    polyBetweenEvalFunctor X Y P ≅
      praEvalAtFunctor ... (equiv.functor.obj P)`
  or an appropriate naturality statement.

- [ ] **Step 5.2:** Build, run `lake test`, verify.

### Task 6: Registration and documentation

**Files:**

- Modify: `GebLean.lean` (add import)
- Modify: `docs/presheaf-pra.md` (document the
  equivalence)
- Modify: `.session/workstreams/presheaf-pra.md`
  (update status)

- [ ] **Step 6.1:** Add
  `import GebLean.PresheafPRADiscrete` to
  `GebLean.lean`.

- [ ] **Step 6.2:** Update `docs/presheaf-pra.md` to
  document the discrete-category equivalence.

- [ ] **Step 6.3:** Run `lake build && lake test`.

- [ ] **Step 6.4:** Run `markdownlint-cli2` on
  changed markdown files.

## Universe level notes

- `PolyFunctorBetweenCat X Y` lives at universe `u`
  (both `X, Y : Type u`).
- `Discrete X` has `Category.{0}` (discrete
  morphisms are in `Prop`).
- `PresheafPRACat (Discrete X) (Discrete Y)` with
  `v_I = 0, u_I = u, v_J = 0, u_J = u` should
  produce compatible universe levels.
- The `w_I` parameter of `PresheafPRACat`
  corresponds to the presheaf value universe; for
  `Over X ≌ (X → Type u)`, this is `u`.
- The `w'` parameter (position universe) should
  also be `u` to match `PolyFunctorBetweenCat`.
- Every equivalence step must carry explicit
  universe annotations to prevent Lean from
  introducing phantom parameters.

## Dependencies

- Tasks 1 and 2 are independent and can be done in
  parallel.
- Task 3 depends on Tasks 1 and 2.
- Task 4 depends on Task 3.
- Task 5 depends on Task 4.
- Task 6 depends on Task 5.
