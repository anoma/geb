# Mendler-Lambek End-Power Completion Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans
> to implement this plan task-by-task.

**Goal:** Complete Phases 3 of the Mendler-Lambek end-power
formulation: prove the remaining gap (`ι_Z_ihomEvalAt_eq_ι_Y`),
define the natural isomorphism (Task 9b), and compose the final
equivalence (Task 9c).

**Architecture:** A concrete-first approach. Instantiate the
abstract construction for `Type v` (via presheaf over the terminal
category), prove the gap in that setting to discover what
categorical properties the proof requires, then generalize to the
abstract case (or add hypotheses if needed). Tasks 9b-9c are
compositional once the gap is filled.

**Tech Stack:** Lean 4 with mathlib. Existing infrastructure:
`PowersAndCopowers.lean` (Type v and presheaf instances),
`EndsAndCoends.lean` (typeEnd, typeCoend, typeHasTerminalWedge),
`MendlerLambekEndPower.lean` (all Phase 1-2 and partial Phase 3).

---

## Background: The Gap

File: `GebLean/MendlerLambekEndPower.lean:2377`

Statement:

```lean
private theorem ι_Z_ihomEvalAt_eq_ι_Y
    (pt : C)
    (twInner : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y))
    (twOuter : HasTerminalWedge
      (churchProf G pt twInner))
    (Y : C) :
    let Z := (ihom ((twInner Y).wedge.pt)).obj Y
    Multifork.ι twOuter.wedge Z ≫
    ihomEvalAt (bwdGlobalSection G pt twInner ≫
      innerEndMap G pt twInner Y) =
    Multifork.ι twOuter.wedge Y
```

Mathematical meaning: Two morphisms
`ImpredicativeGExtObj ⟶ [innerEnd_Y, Y]` are equal. The LHS
composes the outer end projection at
`Z = [innerEnd_Y, Y]` with `ihomEvalAt(gs ≫ m)`, which evaluates
the internal hom at a pushed-forward global section. The RHS is the
outer end projection at `Y`. This is the enriched Yoneda identity
for Church encodings: evaluating the Church encoding at one level
higher and then reducing recovers the original level.

### What has been proved (available lemmas)

1. `cgeChurchLeg_Z_ihomEvalAt`: the same equation holds after
   composing with `fwd` on the left
2. `copowerGExt_backward_forward`: `fwd ≫ bwd = 𝟙` (forward
   direction of the iso)
3. All per-component lemmas (churchComponent_Z_ihomEvalAt, etc.)
4. `fwd_comp_ι_eq_cgeChurchLeg`: `fwd ≫ ι Y = cgeChurchLeg Y`

### What has been tried and does not work

1. Section-retraction algebra (fwd split mono does not give
   bwd ≫ fwd = 𝟙)
2. Joint epicity of churchLift family (they lift into a limit)
3. isIso from epi + split mono (requires fwd epi)
4. Idempotent argument (needs Karoubi properties)
5. Left-cancellation of fwd (fwd is mono, not epi)
6. Direct wedge condition at ihomEvalAt(gs ≫ m) (circular)

### Equivalence

The gap is equivalent to
`bwd ≫ cgeChurchLeg Y = ι Y` (i.e., `bwd_comp_cgeChurchLeg`).
The proof chain from one to the other uses
`ι_cge_ihomMap_cgeChurchLeg`, `ihomEvalAt_natural`, and
`pre_comp_ihomEvalAt`. So any approach that proves either
statement suffices.

---

## Phase A: Type v Test Case

### Rationale

In `Type v`, internal homs are function types, copowers are
products, powers are function spaces, and ends/coends are explicit
set-theoretic constructions. The gap should reduce to function
extensionality and computation. Proving it concretely will:

1. Confirm the statement is true
2. Reveal which categorical properties the proof uses
3. Guide the abstract proof or identify missing hypotheses

`Type v` is equivalent to `PSh(𝟙)` (presheaves over the terminal
category), so all presheaf infrastructure applies.

### Task A1: Set up Type v context

Files:

- Create: `GebLean/MendlerLambekEndPowerTypeV.lean`

#### Step 1: Create file with imports and context

```lean
import GebLean.MendlerLambekEndPower
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Closed.Types

namespace GebLean

open CategoryTheory
```

Establish the necessary instances for `Type v`:

- `MonoidalCategory (Type v)` (from mathlib: cartesian monoidal)
- `MonoidalClosed (Type v)` (from mathlib: cartesian closed)
- `BraidedCategory (Type v)` (from mathlib: symmetric monoidal)
- `HasCopowers (Type v)` (from `PowersAndCopowers.lean`:
  `typesHasCopowers`)
- `HasPowers (Type v)` (from `PowersAndCopowers.lean`:
  `typesHasPowers`)

#### Step 2: Build and verify instances compile

Run `lake build` after adding the file. Fix any instance
resolution or universe issues.

### Task A2: Instantiate HasAllCopowerProfCoends for Type v

Files:

- Modify: `GebLean/MendlerLambekEndPowerTypeV.lean`

#### Step 1: Construct the instance

In `Type v`, coends exist as quotient types (via `typeCoend`).
The `typeHasInitialCowedge` instance from `EndsAndCoends.lean`
gives initial cowedges for `Type v`-valued profunctors. Since the
copower profunctor is `Type v`-valued when `C = Type v`, this
should provide `HasAllCopowerProfCoends G` for any
`G : (Type v)ᵒᵖ ⥤ Type v ⥤ Type v`.

Alternatively, use `HasAllHomToProfCoends.toCopowerProfCoends`
if `HasAllHomToProfCoends` is easier to establish.

#### Step 2: Build and verify

### Task A3: Construct terminal wedges for Type v

Files:

- Modify: `GebLean/MendlerLambekEndPowerTypeV.lean`

#### Step 1: Construct `twInner` for Type v

The inner profunctor `ihomPowerProf G pt Y` is a `Cᵒᵖ ⥤ C ⥤ C`
profunctor. In `Type v`, this becomes a profunctor valued in
`Type v`, for which `typeEndWedge_isTerminal` provides terminal
wedges. Wrap in a `HasTerminalWedge` value.

Note: `ihomPowerProf` uses `ihom` (internal hom in `C`), which
for `C = Type v` is the function type. The profunctor at
`(op A, B)` is `(G(B,A) → (B → pt) → Y)` (function space of the
internal hom applied to the power). Verify this matches
`typeEnd` expectations.

#### Step 2: Construct `twOuter` for Type v

The outer profunctor `churchProf G pt twInner` is also
`Cᵒᵖ ⥤ C ⥤ C`. In `Type v`, this should again be `Type v`-valued,
so `typeEndWedge_isTerminal` applies. Wrap in `HasTerminalWedge`.

#### Step 3: Build and verify

### Task A4: Prove ι_Z_ihomEvalAt_eq_ι_Y for Type v

Files:

- Modify: `GebLean/MendlerLambekEndPowerTypeV.lean`

#### Step 1: State the theorem for Type v

```lean
theorem ι_Z_ihomEvalAt_eq_ι_Y_typeV
    (G : (Type v)ᵒᵖ ⥤ Type v ⥤ Type v)
    [HasAllCopowerProfCoends G]
    (pt : Type v)
    (twInner : ...)
    (twOuter : ...)
    (Y : Type v) :
    ... := by
  _
```

#### Step 2: Explore the goal state

Use `lean_goal` to see what the goal looks like after unfolding
in Type v. The internal hom `[X, Y]` should be `X → Y`,
`ihomEvalAt p` should be `fun f => f (p ())`, and the end
projections should be function application.

#### Step 3: Try to complete proof

In Type v, the goal should reduce to: for any Church-encoded
element `c : ∀ Y, (innerEnd_Y → Y) → Y` (satisfying wedge
naturality), `c` at level `Z = (innerEnd_Y → Y)` evaluated at
the canonical global section equals `c` at level `Y`.

Try:

- `ext` / `funext` to reduce to pointwise
- `simp` with internal hom lemmas
- Direct computation using the wedge condition of the outer end

The wedge condition of `c` (the outer end element) says:
for any `f : Y₁ → Y₂`:

```text
c_{Y₁} ≫ postcompose f = c_{Y₂} ≫ precompose (innerEndMap f)
```

Apply this at `f = ihomEvalAt(gs ≫ m)` which goes `Z → Y`.

#### Step 4: Build and verify

### Task A5: Analyze proof dependencies

#### Step 1: Document findings

After proving the Type v case, document:

- Which categorical axioms the proof uses
- Whether the proof relies on extensionality (function ext)
- Whether it relies on cartesian closedness vs. monoidal closedness
- Whether the internal hom computation is needed or just
  naturality suffices

#### Step 2: Determine generalization strategy

Based on findings, choose one of:

(a) The proof generalizes directly: the same rewrite sequence
works in the abstract setting.

(b) Additional hypotheses are needed: identify the minimal set
(e.g., the category must be cartesian closed, or
`ihomEvalAt(gs ≫ m)` must be characterized by a universal
property).

(c) The statement needs restructuring: e.g., replace
`HasTerminalWedge` with explicit limit structure that provides
the needed computation rules.

---

## Phase B: General Proof

### Task B1: Prove or add hypotheses for ι_Z_ihomEvalAt_eq_ι_Y

Files:

- Modify: `GebLean/MendlerLambekEndPower.lean:2377-2390`

#### Step 1: Apply findings from Phase A

If the Type v proof generalizes:

- Replace the underscore at line 2390 with the proof
- Build and verify

If additional hypotheses are needed:

- Add them to the section variables or theorem statement
- Document in the workstream file why they are needed
- Verify they hold for Type v and presheaf categories

#### Step 2: Build and verify `lake build` passes with no warnings

### Task B2: Verify downstream lemmas compile

#### Step 1: Verify `bwd_comp_cgeChurchLeg` compiles (line 2395)

This should compile automatically once the gap is filled.

#### Step 2: Verify `impredicativeGExt_backward_forward` compiles (line 2419)

This should also compile automatically.

#### Step 3: Full build

Run `lake build` and `lake test`.

---

## Phase C: Tasks 9b and 9c

### Task C1: Assemble the iso

Files:

- Modify: `GebLean/MendlerLambekEndPower.lean` (after line 2437,
  before `end GebLean`)

#### Step 1: Define the iso at each `pt`

```lean
def impredicativeGExtCopowerIso
    (pt : C)
    (twInner : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y))
    (twOuter : HasTerminalWedge
      (churchProf G pt twInner)) :
    ImpredicativeGExtObj G pt twInner twOuter ≅
      CopowerGExtObj G pt where
  hom := impredicativeGExtToCopowerGExt
    G pt twInner twOuter
  inv := copowerGExtToImpredicativeGExt
    G pt twInner twOuter
  hom_inv_id := impredicativeGExt_backward_forward
    G pt twInner twOuter
  inv_hom_id := copowerGExt_backward_forward
    G pt twInner twOuter
```

#### Step 2: Build and verify the iso

### Task C2: Define powerEndGExtNatIso (Task 9b)

Files:

- Modify: `GebLean/MendlerLambekEndPower.lean`

#### Step 1: Define the natural isomorphism

```lean
def powerEndGExtNatIso
    (twInner : ∀ (pt Y : C),
      HasTerminalWedge (ihomPowerProf G pt Y))
    (twOuter : ∀ (pt : C),
      HasTerminalWedge
        (churchProf G pt (twInner pt))) :
    ImpredicativeGExtFunctor G twInner twOuter ≅
      GExtFunctor G :=
  NatIso.ofComponents
    (fun pt =>
      (impredicativeGExtCopowerIso G pt
        (twInner pt) (twOuter pt)).trans
      (copowerGExtIso G pt))
    (fun {pt₁ pt₂} h => by
      -- naturality: show the iso commutes with maps
      _)
```

The naturality proof requires showing that the iso components
commute with functorial maps. This should follow from the
naturality of `copowerGExtIso` and the definition of
`ImpredicativeGExtFunctor.map`.

#### Step 2: Prove naturality

Use `ext` or the injective characterization
(`copowerGExtHomEndEquiv.injective` + `HasCopowers.ext`) to
reduce to per-component equations.

#### Step 3: Build and verify naturality

### Task C3: Define mendlerLambekPowerEndFullEquiv (Task 9c)

Files:

- Modify: `GebLean/MendlerLambekEndPower.lean`

#### Step 1: Compose equivalences

```lean
def mendlerLambekPowerEndFullEquiv
    (twInner : ∀ (pt Y : C),
      HasTerminalWedge (ihomPowerProf G pt Y))
    (twOuter : ∀ (pt : C),
      HasTerminalWedge
        (churchProf G pt (twInner pt))) :
    PowerEndMendlerAlgebra G ≌
      ConventionalAlgebra
        (ImpredicativeGExtFunctor G twInner twOuter) :=
  mendlerLambekEndPowerEquiv.trans
    (Endofunctor.Algebra.equivOfNatIso
      (powerEndGExtNatIso G twInner twOuter).symm)
```

Note: `mendlerLambekEndPowerEquiv` is the existing equivalence
`PowerEndMendlerAlgebra G ≌ ConventionalAlgebra (GExtFunctor G)`.
`Endofunctor.Algebra.equivOfNatIso` transports along a natural
isomorphism of endofunctors.

Verify that `Endofunctor.Algebra.equivOfNatIso` exists in
mathlib. If not, it may need to be constructed (algebras of
naturally isomorphic endofunctors are equivalent categories).

#### Step 2: Build and verify the equivalence

### Task C4: Clean up

Files:

- Modify: `GebLean/MendlerLambekEndPowerTypeV.lean` (decide
  whether to keep, convert to test, or remove)
- Modify:
  `.session/workstreams/mendler-lambek-end-power-formulation.md`
  (mark Phase 3 complete)
- Verify: `lake build` and `lake test` pass

---

## Dependencies

```text
A1 → A2 → A3 → A4 → A5 → B1 → B2 → C1 → C2 → C3 → C4
```

All tasks are sequential. Phase A may reveal that Phase B
requires restructuring (adding hypotheses), which could affect
the signatures of C1-C3.

## Risk Assessment

- Phase A may reveal that the statement requires additional
  categorical structure beyond monoidal closedness + braiding.
  In that case, we add hypotheses and document the constraint.
- Task C2 naturality proof may be nontrivial if the
  functorial action of `ImpredicativeGExtFunctor` interacts
  with the iso in a way that requires highly specific unfolding.
- Task C3 depends on `Endofunctor.Algebra.equivOfNatIso`
  existing in mathlib. If not, we construct it (straightforward
  categorical argument).

## Existing Infrastructure to Reuse

- `typesHasCopowers`, `typesHasPowers`
  (`PowersAndCopowers.lean:192,366`)
- `typeEndWedge_isTerminal`, `typeHasTerminalWedge`
  (`EndsAndCoends.lean`)
- `typeCoendCowedge_isInitial`, `typeHasInitialCowedge`
  (`EndsAndCoends.lean`)
- `copowerGExtIso` (`RestrictedCoendAsColimit.lean:2867`)
- `mendlerLambekEndPowerEquiv`
  (`MendlerLambekEndPower.lean`, Phase 2)
- All helper lemmas listed in the workstream doc section
  "Available helper lemmas"
