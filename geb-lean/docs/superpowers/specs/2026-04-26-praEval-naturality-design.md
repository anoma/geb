# `praEval*` Naturality in `(I, J)` — Design (SUPERSEDED)

> **Status: SUPERSEDED 2026-04-26.**  This spec describes an
> attempt to make `praEvalAtFunctor` natural in `(I, J)`
> simultaneously, using a contraGrothendieck source nested over
> `(grothendieckContraFunctor (Cat × Cat)).obj
> presheafPRACatBifunctorUncurriedOp` and a new
> `FunctorBetweenContraContra` framework.  Implementation hit a
> variance mismatch in the cross-fibre map: the natural arrow
> direction (forward whisker on `Hom`-sets) is opposite to what
> the framework requires.  See
> `.session/workstreams/presheaf-pra.md` "Earlier (I, J)-natural
> attempt (abandoned)" for the analysis.
>
> The workstream was scoped down to fixed `I`.  See
> `2026-04-26-praEvalAtI-naturality-design.md` for the
> realised design (now complete on-branch, commits
> `c2672b92..d9b853af`).
>
> The full `(I, J)`-natural design will be revisited in a separate
> brainstorm using the fixed-`I` formula as a concrete reference;
> directions to consider include paranatural transformations
> between two-variance-in-`I` functors, lax-natural infrastructure,
> or restricted source-mor conventions.

Lifts the `praEvalAt*` constructions in `GebLean/PresheafPRA.lean` to
a flat-functor-between-Grothendiecks form natural in `(I, J)`,
mirroring the `praPolyDirectionsFunctor` pattern from the praDirections
v2 workstream.

## Status

Brainstorm complete 2026-04-26.  Revised 2026-04-26 (variance flip
plus ContraContra framework addition).  Implementation in progress;
session pause 2026-04-26.

**Phase A (new framework) DONE**: `FunctorBetweenContraContra`
abbrevs, structure, and `.toFunctor` extractor in
`GebLean/Utilities/Grothendieck.lean` (commits `64162066`,
`774ee96e`, `d9d08504`).

**praEval Tasks DONE**: target side (`praEvalTargetFibre`,
`praPolyEvalTarget` — commits `81a0369f`, `f9859d89`); source
side (`evalSourceData`, `praPolyEvalSource` — commit `46923c37`);
bundle base/fibre fields (`praPolyEvalData_baseFib`, `_fibFib` —
commits `f0f1f208`, `d701b401`).

**praEval Tasks REMAINING**: cross-fibre and coherence (Tasks
10–14), bundle assembly + functor + bridge (Tasks 15–17),
helper + bridge theorem (Tasks 18–19), tests + workstream notes
(Tasks 20–25).

## Goal

Construct `praPolyEvalFunctor : praPolyEvalSource ⥤ praPolyEvalTarget`,
the natural-in-`(I, J)` form of the polynomial functor evaluation
`praEvalAtFunctor`, plus its bridge lemmas, source-object helper,
bridge theorem, and tests.

## Scope

- **In scope:** functor-form natural construction (`praEvalAtFunctor`
  natural in `(I, J)`); source-object helper; `@[simp]` bridge
  theorem; tests.
- **Out of scope:** profunctor-form bridge theorem; full-faithfulness
  witnesses lifted to natural form; per-component accessor refactors
  (`praEvalAt`, `praEvalAt_index`, `praEvalAt_mor`, `praEvalAt_mk`
  retain current signatures); migration of `PresheafPRAUMorph.lean`
  references (none depend on `(I, J)`-naturality).

## Architecture

Mirrors `praPolyDirectionsFunctor`'s flat-functor-between-Grothendiecks
pattern in spirit (target Grothendieck, six-field bundle, three
`rfl` bridge lemmas, source-object helper, `@[simp]` bridge
theorem), but the SOURCE-side variance is inverted.

The variance flip stems from a fundamental difference between the
two settings: polynomial-functor-morphism *directions* split as
forward-positions / backward-directions (which is why praDirections
uses a covariant source Grothendieck with a `FunctorFromDataContra`
inner data shape), while polynomial-functor *evaluation* takes a
presheaf `Z` on `I` as INPUT — and presheaves are contravariant in
`I`.  So `Z`'s natural variance under an `I`-morphism is BACKWARD,
which forces the source Grothendieck to be CONTRAVARIANT in
`(J, I, P)`.

This requires a new U3 framework `FunctorBetweenContraContra` in
`GebLean/Utilities/Grothendieck.lean`, parallel to the existing
`FunctorBetweenCovContra`.  The new framework expresses
"covariant flat functor between two contra-Grothendiecks" — a
genuinely different variance combination from CovContra.  The
user's framing: such utility infrastructure should support all
variance combinations; we have one direction by historical
coincidence and adding the other is principled.

Other structural differences from praDirections:

- The source fibre is *constant in `P`* — the fibre Cat is
  `widenedPSh(I)`, depending only on `I`, not on the PRA `P`.
  Encoded with `Functor.const`.

## Source and Target Grothendiecks

### `praPolyEvalSource` (CONTRAVARIANT)

`praPolyEvalSource` is a CONTRA-Grothendieck:

```lean
def praPolyEvalSource :
    Cat.{...} :=
  (grothendieckContraFunctor
    ((grothendieckContraFunctor (Cat × Cat)).obj
      presheafPRACatBifunctorUncurriedOp)).obj evalSourceData
```

where `evalSourceData :
((grothendieckContraFunctor (Cat × Cat)).obj
presheafPRACatBifunctorUncurriedOp)ᵒᵖ ⥤ Cat` is a
*contravariant* functor whose:

- **`obj (op X)`** for `X = ((J, I), P)` returns `widenedPSh(I)`
  (constant in `P` — encoded via the `Functor.const`-style
  treatment, but at the `Cᵒᵖ ⥤ Cat` level rather than via
  `FunctorFromDataContra`).
- **`map g`** for `g : op X₁ → op X₂` (i.e., underlying C-mor
  `X₂ → X₁`, with underlying I-mor `f_I : I₂ → I₁` in Cat) returns
  the Cat-morphism `widenedPSh(I₁) ⥤ widenedPSh(I₂)` given by
  `presheafCatFunctor.map (op f_I)` widened through
  `catULiftFunctor2`.

Source objects: `((J, I), P, Z)` — 4 inputs.  Source-mors go
BACKWARD in `(J, I, P)` (because of the contra-Grothendieck), so
the I-component variance matches presheaves' contravariance
naturally.

### `praPolyEvalTarget`

Same outer shape as `praPolyDirectionsTarget`, with `J` substituted
for `I`:

```lean
def praPolyEvalTarget :
    Cat.{...} :=
  (grothendieckContraFunctor Cat.{v_J, u_J}).obj
    praEvalTargetFibre
```

where:

```lean
def praEvalTargetFibre :
    Cat.{v_J, u_J}ᵒᵖ ⥤ Cat.{...} :=
  presheafCatFunctor.{u_J, v_J, w'} ⋙
    catULiftFunctor2.{...} ⋙
    Cat.opFunctor.{...}
```

The three-stage `presheafCatFunctor ⋙ catULiftFunctor2 ⋙
Cat.opFunctor` pipeline matches `praDirectionsTargetFibre` exactly,
just at `J`-universes and using `w'` (positions universe) for the
target type universe instead of `w_I` (directions universe).

Target objects: `(J, op widened presheaf-on-J)`.

## New U3 Framework: `FunctorBetweenContraContra`

Added in `GebLean/Utilities/Grothendieck.lean` (parallel to the
existing `FunctorBetweenCovContra` section, ~lines 5155-5328 and
the extractor at ~lines 7370-7659).

The framework expresses a covariant functor
`(grothendieckContraFunctor C).obj G' ⥤
(grothendieckContraFunctor D).obj F` for `G' : Cᵒᵖ ⥤ Cat` and
`F : Dᵒᵖ ⥤ Cat`.

Six abbrevs (parallel to CovContra):

- `FunctorBetweenContraContraBaseFib := C ⥤ D`
- `FunctorBetweenContraContraFibFib (baseFib) :=
   ∀ c, G'.obj (op c) ⥤ F.obj (op (baseFib.obj c))`
- `FunctorBetweenContraContraFibHomCrossApp baseFib fibFib`,
  `FibHomCrossNat`, `BaseHomId`, `BaseHomComp` — analogous to
  CovContra, with the source-fibre input and transport adjusted
  for the source-side contravariance.

A `FunctorBetweenContraContraData` structure bundles all six,
plus a `.toFunctor` extractor.  The exact abbrev shapes are
worked out at implementation time, mirroring CovContra closely
where possible.

## The Bundle and Functor

```lean
private def praPolyEvalData :
    FunctorBetweenContraContraData.{...}
      evalSourceData
      praEvalTargetFibre where
  baseFib := …
  fibFib := …
  fibHomCrossApp := …
  fibHomCrossNat := …
  baseHomId := …
  baseHomComp := …

def praPolyEvalFunctor :
    praPolyEvalSource ⥤ praPolyEvalTarget :=
  FunctorBetweenContraContraData.toFunctor praPolyEvalData
```

The six bundle fields:

- **`baseFib : ((J, I), P) ↦ J`** — analog of praDirections's
  `((J, I), P) ↦ I`, projecting to the J component of the
  contra-Grothendieck base.
- **`fibFib X`** at `X = ((J, I), P)` — sends `Z : widenedPSh(I)`
  to `op widened (praEvalAtFunctor.obj P |>.obj Z)`.  The
  body unfolds (after unwidening Z) to `op (Σ_a Hom(praDirectionsAt
  P j a, Z))` as a presheaf on J, then re-widens.
- **`fibHomCrossApp f x`** — cross-fibre morphism for
  `f : ((J₁, I₁), P₁, Z₁) ⟶ ((J₂, I₂), P₂, Z₂)`, encoding how
  the polynomial-functor result on J₁ maps to the result on J₂
  under the source-mor.
- **`fibHomCrossNat`, `baseHomId`, `baseHomComp`** — the three
  coherence proofs, analogous to praDirections's Tasks 7.5–7.10.

The expectation is that `fibHomCrossApp` and the coherence proofs
are simpler than their praDirections analogues because the source
fibre is constant in `P` (so there's no `(homFiber f).app`-style
naturality structure to navigate).

## Bridge Lemmas

Three `rfl` bridge lemmas (analog of praDirections's Task 9):

```lean
theorem praPolyEvalFunctor_base
    (X : praPolyEvalSource) :
    GrothendieckContraFunctor.objBase
      (praPolyEvalFunctor.obj X) =
    (GrothendieckContraFunctor.objBase X.base).1 :=
  rfl

theorem praPolyEvalFunctor_fibre
    (X : praPolyEvalSource) :
    GrothendieckContraFunctor.objFiber
      (praPolyEvalFunctor.obj X) =
    (praPolyEvalData.fibFib X.base).obj X.fiber :=
  rfl

theorem praPolyEvalFunctor_map_app
    {X Y : praPolyEvalSource} (f : X ⟶ Y) :
    GrothendieckContraFunctor.homFiber
      (praPolyEvalFunctor.map f) =
    praPolyEvalData.fibHomCrossApp f.base X.fiber ≫
      (praEvalTargetFibre.map
        (praPolyEvalData.baseFib.map f.base).op).toFunctor.map
        ((praPolyEvalData.fibFib Y.base).map f.fiber) :=
  rfl
```

If any of the three fails to close by `rfl`, fall back to a short
`simp only` block with bundle-field unfolds (parallel to the
praDirections plan's fallback).

## Source-Object Helper

```lean
def praPolyEvalAtSourceObj
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
    (Z : Iᵒᵖ ⥤ Type w_I) :
    praPolyEvalSource.{u_I, v_I, u_J, v_J, w_I, w'} :=
  ⟨GrothendieckContraFunctor.mkObj (Cat.of Jᵒᵖ, Cat.of Iᵒᵖ) P,
   <widening of Z via ULiftHom.objUp (ULift.up Z)>⟩
```

The `<widening of Z>` mirrors `praPolyDirectionsAtSourceObj`'s
`ULiftHom.objUp (ULift.up …)` pattern from commit `ed74a7ff`.  The
exact universe annotations on `ULiftHom`/`ULift` are LSP-discovered
at implementation time.

## Bridge Theorem

```lean
@[simp] theorem praEvalAtFunctor_via_praPolyEvalFunctor
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
    (Z : Iᵒᵖ ⥤ Type w_I) :
    (praEvalAtFunctor I J).obj P |>.obj Z = <unwidening of fibre>
```

where `<unwidening of fibre>` unfolds
`(praPolyEvalFunctor.obj (praPolyEvalAtSourceObj P Z)).fiber.unop`
via the same `ULift.down`/`ULiftHom.objDown` chain that
`praDirectionsAt_via_praPolyDirectionsFunctor` used (commit
`b9daaca3`).

Proof aim: `rfl`.  Fallback: `simp only` with bridge lemmas.
Escalation contract: if neither closes, escalate with a precise
report on whether the proof is doable at greater cost or whether
the proof approach is unclear.

## Tests

New file `GebLeanTests/Utilities/PresheafPRAEvalNat.lean`,
registered in `GebLeanTests.lean`.  Five sections mirroring
`PresheafPRADirNat.lean`:

1. **Type-signature sanity** — `praPolyEvalFunctor`,
   `praPolyEvalSource`, `praPolyEvalTarget`, `praEvalTargetFibre`
   exist and have the expected `Cat`-level types at all-zero
   universes (allowing for the `Cat.{0, 1}`-style universe
   adjustments seen in `PresheafPRADirNat.lean`).
2. **Bridge-lemma collapse** — the three
   `praPolyEvalFunctor_{base,fibre,map_app}` lemmas hold at concrete
   inputs.
3. **Pointwise-accessor compatibility** — `praEvalAtFunctor` still
   produces the same `(Iᵒᵖ ⥤ Type w_I) ⥤ (Jᵒᵖ ⥤ Type _)` shape
   after the new natural form is added (no per-component
   breakage).
4. **Functoriality at a concrete morphism** —
   `praPolyEvalFunctor.map_id` and `.map_comp` at concrete inputs.
5. **Universe polymorphism** — the natural form works at mixed
   universes such as `{1, 0, 0, 0, 0, 0}` and `{0, 0, 1, 0, 0, 0}`.

Plus a bridge-theorem test exercising
`praEvalAtFunctor_via_praPolyEvalFunctor` at all-zero universes.

## Naming Conventions

- `praPolyEvalSource`, `praPolyEvalTarget` — Cat-level
  Grothendieck constructions (parallel `praPolyDirectionsSource`,
  `praPolyDirectionsTarget`).
- `praPolyEvalFunctor` — the natural-in-`(I, J)` flat functor
  (parallel `praPolyDirectionsFunctor`).
- `praPolyEvalData` — private bundle (parallel
  `praPolyDirectionsData`).
- `praEvalTargetFibre` — fibre functor for the target Grothendieck
  (parallel `praDirectionsTargetFibre`).
- `praPolyEvalAtSourceObj` — public source-object helper
  (parallel `praPolyDirectionsAtSourceObj`).
- `praEvalAtFunctor_via_praPolyEvalFunctor` — bridge theorem
  (parallel `praDirectionsAt_via_praPolyDirectionsFunctor`).

## File Placement

All new declarations land in
`GebLean/PresheafPRA.lean`, inside or after the
`section PresheafPRAEvalAt` block (which currently contains the
existing `praEvalAtProfunctor`, `praEvalAtFunctor`, full-faithfulness
witnesses, and per-component accessors).

The natural-form construction may be in its own subsection (e.g.,
`section PresheafPRAEvalNat` adjacent to `PresheafPRAEvalAt`) to
keep the section's responsibilities clearly bounded.

## Implementation notes accumulated 2026-04-26

These details were discovered during the in-progress execution
and are useful for the next session:

### Universe annotations

- `praEvalTargetFibre`: uses
  `presheafCatFunctor.{u_J, v_J, max w' u_I w_I}` (NOT just
  `w'`).  The `max w' u_I w_I` absorbs `ccrNewEvalCatFunctor`'s
  output universe inflation.  `presheafCatFunctor.{...}` for
  `J` uses `(u_J, v_J)`, the third argument is the Type-universe
  of presheaf values.
- `praPolyEvalTarget`: outer Cat universe annotation is
  `Cat.{max u_I u_J v_I v_J w_I w', max (u_I + 1) u_J v_I v_J
  (w_I + 1) (w' + 1)}` — note the `(u_I + 1)` (rather than
  `(u_J + 1)` as one might naively mirror from
  `praPolyDirectionsTarget`) — comes from absorbing
  `ccrNewEvalCatFunctor`'s output Cat.
- `praPolyEvalSource`: outer Cat universe is
  `Cat.{max u_I u_J v_I v_J w_I w', max (u_I + 1) (v_I + 1)
  (u_J + 1) (v_J + 1) (w_I + 1) (w' + 1)}` — note all FOUR `+1`
  shifts because the base is a double Grothendieck of `Cat × Cat`.

### `praPolyEvalData_fibFib` body shape (committed)

The body uses `Functor.whiskeringRight ⋯ |>.flip` inline (NOT
`praEvalAtFunctor`, which is defined later in the file):

```lean
CategoryTheory.ULiftHom.down ⋙
  CategoryTheory.ULift.downFunctor ⋙
  (((Functor.whiskeringRight
      (↑(GrothendieckContraFunctor.objBase X).1) _ _).obj
    (ccrNewEvalCatFunctor.{...}
      (↑(presheafCatFunctor.{u_I, v_I, w_I}.obj
        (Opposite.op
          (GrothendieckContraFunctor.objBase X).2))))).obj
    (GrothendieckContraFunctor.objFiber X)).flip ⋙
  CategoryTheory.ULift.upFunctor ⋙
  CategoryTheory.ULiftHom.up
```

The `.flip` on the inner functor handles the `Jᵒᵖ ⥤ Type _ ⥤
…` vs `(Iᵒᵖ ⥤ Type _) ⥤ Jᵒᵖ ⥤ Type _` transposition.  No final
`.op` on the outer widening (since `praEvalTargetFibre` no longer
has `Cat.opFunctor`).

### `FunctorBetweenContraContra` framework specifics

- The framework's `FibHomCrossApp` takes a TARGET-side input
  `x' : G.obj (op c')` (parametrised differently from CovContra's
  source-side `x : G.obj c`):

  ```lean
  ∀ {c c' : C} (f : c ⟶ c') (x' : G.obj (Opposite.op c')),
    (fibFib c).obj ((G.map f.op).toFunctor.obj x') ⟶
      (F.map (baseFib.map f).op).toFunctor.obj
        ((fibFib c').obj x')
  ```

- The framework includes an extra `GMapCompEq` /
  `GMapCompEqProof` helper not in CovContra, needed because the
  contravariant source's composition coherence requires equating
  `(G.map f.op) ∘ (G.map g.op)` with `G.map (f≫g).op`.  This
  affects the shape of `BaseHomComp`.
- The `.toFunctor` extractor uses
  `Grothendieck.functorTo (F ⋙ Cat.opFunctor) ⋯ |>.op`
  (a single `.op` lift, simpler than CovContra's `.rightOp`).

### Anticipated patterns for remaining tasks

- **Task 11** (`fibHomCrossApp` widened): the polynomial-functor-
  morphism action `(homFiber f) : objFiber c ⟶
  (presheafPRACatBifunctorUncurriedOp.map (homBase f).op).
  toFunctor.obj (objFiber c')` provides the natural
  transformation between polynomial functors at different `P`'s.
  The cross-fibre app encodes the resulting natural transformation
  between evaluations.  This is the most likely place for further
  design subtleties.
- **Tasks 13, 14** (identity, composition coherence): the
  praDirections analogs (Tasks 7.8, 7.10) closed by `rfl`
  end-to-end.  Plausible the praEval analogs do too, given the
  structural parallel.  Try `rfl` first; fall back to `simp only`
  with bridge lemmas; escalate if neither closes.
- **Task 12** (naturality): praDirections Task 7.6 needed a
  one-line `rfl` structural compat lemma plus a six-tactic
  naturality proof.  Plausible same shape applies.
- **Task 19** (bridge theorem `praEvalAtFunctor_via_praPoly
  EvalFunctor`): praDirections analog (Task 5 of the follow-up
  plan) closed by `rfl` after explicit universe annotations on
  `ULift.down` and `ULiftHom.objDown`.  Try same approach.

## Risks and Open Questions

1. **Source-fibre constancy in `P`**: the `Functor.const`-based
   source data has not been used elsewhere in the praDirections
   work; small risk of unexpected universe-elaboration or
   type-class-synthesis hiccups.  Mitigated by mirroring
   `sourceDataFib`'s exact universe annotations and falling back
   to explicit `show … from …` clauses if needed.
2. **`fibHomCrossApp` shape**: speculative simplification ("simpler
   than praDirections's analogue") needs implementation-time
   verification.  If the shape turns out to be more complex than
   expected, the same factoring-out-lemmas technique used in
   praDirections Tasks 7.5–7.10 applies.
3. **Bridge-theorem RHS shape**: discovered at implementation time
   via LSP, with `simp only` and escalation as fallbacks.  Same
   contract as the praDirections follow-up.
