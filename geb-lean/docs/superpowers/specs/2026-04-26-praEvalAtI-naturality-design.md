# `praEvalAt*` Naturality in `(J, P, Z)` at Fixed `I` — Design

Lifts `praEvalAtFunctor I J : PRACat I J ⥤ (PSh(I) ⥤ PSh(J))` to a
flat-functor-between-Grothendiecks form natural in `(J, P, Z)` at
fixed `I`.  Built as `(grothendieckContraFunctor Cat).map` of a
natural transformation between two `Catᵒᵖ ⥤ Cat` functors.

The eventual `(I, J)`-natural redesign is deferred to a later
workstream.  This fixed-`I` construction will serve as a concrete
reference for that later design — once the formula at fixed `I` is
known, the way `I` enters can be reasoned about explicitly, possibly
via a paranatural transformation between two-variance-in-`I`
functors or via lax-natural infrastructure.

## Status

Brainstorm complete 2026-04-26.

## Goal

Construct `praPolyEvalAtIFunctor I : praPolyEvalAtISource I ⥤
praPolyEvalTarget` (with `I` as a parameter), plus its bridge
lemmas, source-object helper, bridge theorem, and tests.

## Background and motivation

The previous in-flight design at
`2026-04-26-praEval-naturality-design.md` attempted to make the
construction natural in `(I, J, P, Z)` simultaneously, using a new
`FunctorBetweenContraContra` framework with a contravariant source
Grothendieck nested over `(grothendieckContraFunctor (Cat × Cat)).obj
presheafPRACatBifunctorUncurriedOp`.  Investigation during execution
uncovered a variance mismatch in the cross-fibre map:

- The framework's cross-fibre app type requires
  `(fibFib c).obj ((G.map f.op).obj x') ⟶ (F.map (baseFib.map f).op).obj
  ((fibFib c').obj x')`.
- Source endpoint involves `Hom_{PSh(I_source)}(F_i, Z₁)` (Z pulled
  back to source-side I).
- Target endpoint involves `Hom_{PSh(I_target)}(F_{i'}, Z')` (Z at
  target-side I).
- The natural map between these is the *forward whisker* `Hom_{PSh
  (I_target)}(_, _) → Hom_{PSh(I_source)}(_⋙f_I.op, _⋙f_I.op)`, which
  goes from the *target* endpoint *into* the source endpoint —
  opposite of what the framework requires.
- No natural arrow exists in the required direction (it would
  require a section of the forward whisker, which only exists in
  special cases).

Investigation of redesigning the target Grothendieck (option (b) in
the escalation) showed that any candidate redesign either suffers
the same direction mismatch or breaks Z-covariance for the
pure-Z-variation case.  Conclusion: `praEvalAt`'s `(I, J)`-naturality is
genuinely lax — `J`-naturality is strict but `I`-naturality is
up-to-inclusion via the forward whisker, and a single flat functor
between contraGrothendiecks cannot capture both Z-covariance at
fixed `I` and `I`-pullback-via-whisker simultaneously.

The decision: scope down to fixed `I` for now.  This will produce a
concrete formula for the natural-in-`(J, P, Z)` form.  Once that
formula is known, the way the construction varies with `I` becomes
explicit and the right mathematical object — possibly a paranatural
transformation between two-variance-in-`I` functors, or a 2-cell
between pseudofunctors — can be designed with full information.

## Scope

In scope:

- `praEvalAtBifunctor I J : PRACat I J × PSh(I) ⥤ PSh(J)` — the
  uncurried bifunctor (new public artifact, parallel to
  `praEvalAtProfunctor` and `praEvalAtFunctor`).
- `praPolyEvalAtISourceFib I : Catᵒᵖ ⥤ Cat` and
  `praPolyEvalAtISource I` — the source side at fixed `I`.
- `praPolyEvalAtINatTrans I` — the J-naturality natural
  transformation underlying `praPolyEvalAtIFunctor I`.
- `praPolyEvalAtIFunctor I : praPolyEvalAtISource I ⥤
  praPolyEvalTarget` — the final flat functor.
- Three rfl bridge lemmas (`_base`, `_fibre`, `_map_homFiber`).
- `praPolyEvalAtISourceObj I J P Z` — public source-object helper.
- `@[simp] praEvalAtFunctor_via_praPolyEvalAtIFunctor` — bridge
  theorem.
- 5-section test file `GebLeanTests/Utilities/PresheafPRAEvalAtINat
  .lean` plus a bridge-theorem test.
- Workstream notes update.

Out of scope (deferred):

- `(I, J)`-naturality.  After this fixed-`I` construction lands, a
  separate brainstorm/design session will use the resulting concrete
  formula to design the appropriate `I`-natural object.
- Profunctor-form bridge theorem — no analog needed.
- Per-component accessor refactors (`praEvalAt`, `praEvalAt_index`,
  `praEvalAt_mor`, `praEvalAt_mk` retain current signatures).
- Migration of `PresheafPRAUMorph.lean` references — no current
  dependents on a J-natural form.

## Pre-work: revert in-flight source-side commits

The following commits implementing the previous (I, J)-natural
attempt are reverted as part of this workstream:

- `46923c37` — `evalSourceData` + `praPolyEvalSource` (source side
  with the I-varying inner contraGrothendieck).
- `f0f1f208` — `praPolyEvalData_baseFib`.
- `d701b401` — `praPolyEvalData_fibFib`.

The following commits are kept:

- `81a0369f`, `f9859d89`, `d789a2ac` — target side
  (`praEvalTargetFibre`, `praPolyEvalTarget`).  These are
  parametrised only by `J` and are reusable as-is.
- `64162066`, `774ee96e`, `d9d08504` — `FunctorBetweenContraContra`
  framework in `Utilities/Grothendieck.lean`.  General-purpose
  infrastructure parallel to `FunctorBetweenCovContra`; useful
  regardless of whether this particular construction uses it.

## Architecture

```text
                         praPolyEvalAtIFunctor I
   praPolyEvalAtISource I ────────────────────────► praPolyEvalTarget
          │                                                 │
   contraGrothendieck                              contraGrothendieck
          │           grothendieckContraFunctor.map         │
          ▼                of NatTrans (rfl-naturality)     ▼
   praPolyEvalAtISourceFib I  ══════════════════►   praEvalTargetFibre
   (J ↦ widened (PRACat I J × PSh(I)))            (J ↦ widened PSh(J))

   per-J component of NatTrans = praEvalAtBifunctor I J widened
```

The structure relies on the strict identity
`praEvalAt (f_J^* P) Z = f_J^* (praEvalAt P Z)` — J-pullback
commutes with bifunctor evaluation.  This makes the underlying
NatTrans's naturality square `rfl` (or near-`rfl`).  Once we have
the NatTrans, applying `(grothendieckContraFunctor Cat).map` lifts
it to a flat functor between contraGrothendiecks.  All the cross-
fibre / coherence proofs that praDirections's `FunctorBetweenCovContra`
machinery handles are vacuous here, so we use
`grothendieckContraFunctor.map` directly rather than going through
the `FunctorBetweenContraContra` framework.

## The `praEvalAtBifunctor` (new public artifact)

```lean
def praEvalAtBifunctor (I J : Cat) :
    PresheafPRACat I J × ↑(presheafCat I) ⥤
      ((Cat.of Jᵒᵖ).α ⥤ Type _) :=
  Functor.uncurry.obj (praEvalAtFunctor I J)
```

Placed in `section PresheafPRAEvalAt` next to `praEvalAtFunctor`.

The exact universe annotations are LSP-discovered at implementation
time, mirroring `praEvalAtFunctor`'s annotations.

## The source side

### `praPolyEvalAtISourceFib`

A `Catᵒᵖ ⥤ Cat` functor sending `op J` to the widened product Cat
`PRACat I J × PSh(I)`.

Construction sketch:

```lean
def praPolyEvalAtISourceFib (I : Cat) :
    Cat.{v_J, u_J}ᵒᵖ ⥤ Cat.{...} :=
  let praFactor : Cat.{v_J, u_J}ᵒᵖ ⥤ Cat.{...} :=
    presheafPRACatBifunctor.flip.obj (Opposite.op (Cat.of Iᵒᵖ))
  let pshFactor : Cat.{v_J, u_J}ᵒᵖ ⥤ Cat.{...} :=
    (Functor.const _).obj (presheafCatFunctor.obj (Opposite.op I))
  -- product, with both factors widened to a common Cat universe
  let prodFactor : Cat.{v_J, u_J}ᵒᵖ ⥤ Cat.{...} :=
    <product of praFactor and pshFactor via Cat.prod or Functor.prod'>
  prodFactor ⋙ catULiftFunctor2.{...}
```

The exact form depends on what mathlib provides for products in
`Cat`-valued functors.  Options:

- Use `Functor.prod' : (A ⥤ B) → (A ⥤ C) → (A ⥤ B × C)` — gives a
  `Catᵒᵖ ⥤ Cat × Cat` functor; need to compose with a `Cat × Cat ⥤
  Cat` operation that takes a pair to its categorical product.
- Build by hand: `obj := fun opJ => Cat.of (PRACat I opJ.unop ×
  PSh(I))`, with `map := fun f => (praFactor.map f).prod (𝟙 _)`.

Implementation-time choice; both are reasonable.

### `praPolyEvalAtISource`

```lean
def praPolyEvalAtISource (I : Cat) :
    Cat.{...} :=
  (grothendieckContraFunctor Cat.{v_J, u_J}).obj
    (praPolyEvalAtISourceFib I)
```

Objects: pairs `(J, (P, Z))` with `J : Cat`, `P : PRACat I J`,
`Z : PSh(I)`, all widened.  Morphisms `(J_s, P_s, Z_s) ⟶ (J_t,
P_t, Z_t)`: triples `(f_J : J_s ⟶ J_t, f_P : P_s ⟶ f_J^* P_t,
η : Z_s ⟶ Z_t)`.

## The target side (unchanged)

`praEvalTargetFibre` and `praPolyEvalTarget` are kept exactly as
committed.  Both are parametrised only by `J` and do not reference
`I`, so they remain correct for the fixed-`I` construction.

```lean
def praEvalTargetFibre :
    Cat.{v_J, u_J}ᵒᵖ ⥤ Cat.{...} :=
  presheafCatFunctor.{u_J, v_J, max w' u_I w_I} ⋙
    catULiftFunctor2.{...}

def praPolyEvalTarget :
    Cat.{...} :=
  (grothendieckContraFunctor Cat.{v_J, u_J}).obj
    praEvalTargetFibre.{...}
```

## The natural transformation `praPolyEvalAtINatTrans`

```lean
def praPolyEvalAtINatTrans (I : Cat) :
    praPolyEvalAtISourceFib I ⟶ praEvalTargetFibre.{...} where
  app opJ :=
    -- a Cat-morphism from widened (PRACat I opJ.unop × PSh(I))
    -- to widened PSh(opJ.unop)
    -- via catULiftFunctor2.map of (praEvalAtBifunctor I opJ.unop)
    _  -- LSP-discovered exact universe annotations
  naturality {opJ_s opJ_t} f := by
    -- Reduces to: (f_J^*-on-PRACat × id) ⋙ praEvalAtBifunctor =
    --             praEvalAtBifunctor ⋙ f_J^*-on-PSh(J)
    -- Should be rfl modulo the catULiftFunctor2 widening
    rfl
```

Naturality is the strict identity that J-pullback commutes with
bifunctor evaluation; should be `rfl` after unfolding the widening.
Fallback: short `simp only` rewrite with bifunctor unfolds.

## The flat functor `praPolyEvalAtIFunctor`

```lean
def praPolyEvalAtIFunctor (I : Cat) :
    praPolyEvalAtISource I ⥤ praPolyEvalTarget :=
  ((grothendieckContraFunctor Cat.{v_J, u_J}).map
    (praPolyEvalAtINatTrans I)).toFunctor
```

The `(grothendieckContraFunctor Cat).map α` for `α : G ⟹ F` between
`Catᵒᵖ ⥤ Cat` functors gives a `Cat.Hom` (functor) between the
contraGrothendieck Cats; `.toFunctor` extracts the underlying
functor.

## Bridge lemmas (rfl-collapses)

Three bridge lemmas parallel to praDirections's
`praPolyDirectionsFunctor_{base,fibre,map}` (commit `821da820`):

```lean
@[simp] theorem praPolyEvalAtIFunctor_base
    (I : Cat) (X : praPolyEvalAtISource I) :
    GrothendieckContraFunctor.objBase
      ((praPolyEvalAtIFunctor I).obj X) =
    GrothendieckContraFunctor.objBase X :=
  rfl

@[simp] theorem praPolyEvalAtIFunctor_fibre
    (I : Cat) (X : praPolyEvalAtISource I) :
    GrothendieckContraFunctor.objFiber
      ((praPolyEvalAtIFunctor I).obj X) =
    (praPolyEvalAtINatTrans I).app
      (Opposite.op (GrothendieckContraFunctor.objBase X)) |>.obj
      (GrothendieckContraFunctor.objFiber X) :=
  rfl

@[simp] theorem praPolyEvalAtIFunctor_map_homFiber
    (I : Cat) {X Y : praPolyEvalAtISource I} (f : X ⟶ Y) :
    GrothendieckContraFunctor.homFiber
      ((praPolyEvalAtIFunctor I).map f) =
    <RHS LSP-discovered, mostly NatTrans-app-action> :=
  rfl
```

If any fails to close by `rfl`, fall back to a short `simp only`
rewrite with bridge unfolds.

## Source-object helper `praPolyEvalAtISourceObj`

```lean
def praPolyEvalAtISourceObj (I : Cat) (J : Cat)
    (P : PresheafPRACat I J) (Z : ↑(presheafCat I)) :
    praPolyEvalAtISource I :=
  GrothendieckContraFunctor.mkObj (Cat.of Jᵒᵖ)
    <widening of (P, Z) via ULiftHom.objUp ∘ ULift.up>
```

Public, mirrors `praPolyDirectionsAtSourceObj` (commit `ed74a7ff`).

## Bridge theorem `praEvalAtFunctor_via_praPolyEvalAtIFunctor`

```lean
@[simp] theorem praEvalAtFunctor_via_praPolyEvalAtIFunctor
    (I : Cat) (J : Cat) (P : PresheafPRACat I J)
    (Z : ↑(presheafCat I)) :
    (praEvalAtFunctor I J).obj P |>.obj Z =
    <unwidening of (praPolyEvalAtIFunctor I).obj
      (praPolyEvalAtISourceObj I J P Z) |>.fiber.unop>
```

Proof aim: `rfl` after explicit universe annotations on `ULift.down`
/ `ULiftHom.objDown` (per the praDirections analog at commit
`b9daaca3`).  Fallback: `simp only` with bridge lemmas.

## Tests

New file `GebLeanTests/Utilities/PresheafPRAEvalAtINat.lean`,
registered in `GebLeanTests.lean`.  Five sections plus a bridge-
theorem test:

1. **Type-signature sanity** — `praPolyEvalAtIFunctor`,
   `praPolyEvalAtISource`, `praPolyEvalAtISourceFib`,
   `praEvalAtBifunctor`, `praEvalTargetFibre`, `praPolyEvalTarget`
   exist with expected `Cat`-level types at concrete universes.
2. **Bridge-lemma collapse** — the three rfl-bridges hold at
   concrete inputs.
3. **Pointwise-accessor compatibility** — `praEvalAtFunctor` and
   friends (`praEvalAt`, `praEvalAt_index`, `praEvalAt_mor`,
   `praEvalAt_mk`) still produce expected shapes.
4. **Functoriality** — `(praPolyEvalAtIFunctor I).map_id` and
   `.map_comp` at concrete morphisms.
5. **Universe polymorphism** — works at mixed universes such as
   `{1, 0, 0, 0, 0, 0}`, `{0, 0, 1, 0, 0, 0}`.

Plus a bridge-theorem test exercising
`praEvalAtFunctor_via_praPolyEvalAtIFunctor` at all-zero universes.

## File placement

In `GebLean/PresheafPRA.lean`:

- `praEvalAtBifunctor` is added inside `section PresheafPRAEvalAt`
  next to `praEvalAtFunctor`.
- A new `section PresheafPRAEvalAtINat` is opened (placement: after
  `section PresheafPRAEvalAt`, or wherever fits the file's overall
  organization at implementation time).  This section contains
  `praEvalTargetFibre`, `praPolyEvalTarget` (already committed —
  may be moved into this section), `praPolyEvalAtISourceFib`,
  `praPolyEvalAtISource`, `praPolyEvalAtINatTrans`,
  `praPolyEvalAtIFunctor`, the three bridge lemmas,
  `praPolyEvalAtISourceObj`, and the bridge theorem.

## Naming Conventions

- `praEvalAtBifunctor` — uncurried bifunctor, parallel to
  `praEvalAtProfunctor`, `praEvalAtFunctor`.
- `praPolyEvalAtISourceFib`, `praPolyEvalAtISource` — source side
  at fixed `I`.
- `praEvalTargetFibre`, `praPolyEvalTarget` — target side
  (unchanged from in-flight commits).
- `praPolyEvalAtINatTrans` — the J-naturality NatTrans.
- `praPolyEvalAtIFunctor` — the final flat functor.
- `praPolyEvalAtISourceObj` — source-object helper.
- `praEvalAtFunctor_via_praPolyEvalAtIFunctor` — bridge theorem.

The `@I` mnemonic in artifact names indicates "fix `I`, take the
natural form in `(J, P, Z)`".  The eventual `(I, J)`-natural form
will use a different name, chosen during that future workstream.

## Risks and Open Questions

1. **Universe alignment for the source product**: combining
   `presheafPRACatBifunctor.flip.obj (op I)` with the constant
   `presheafCat I` factor requires both to live in compatible Cats.
   Both will be widened via `catULiftFunctor2`, exact universe
   annotations are LSP-discovered at implementation time.  Risk:
   small.  Mitigation: follow the universe-padding pattern from
   `praPolyEvalTarget`.
2. **`grothendieckContraFunctor.map` codomain shape**: gives a
   `Cat.Hom` between contraGrothendieck Cats; `.toFunctor` needed
   to land in `⥤`.  Risk: small; standard.
3. **Bridge-theorem `rfl`**: may require explicit universe
   annotations on `ULift.down` / `ULiftHom.objDown` (mirroring
   praDirections's bridge theorem at commit `b9daaca3`).  Risk:
   small.  Mitigation: `simp only` fallback with bridge lemmas.
4. **Source-product construction**: choice between using
   `Functor.prod'` with a Cat-product helper, vs.  a hand-rolled
   product, is made at implementation time.  Both are reasonable.

## Future Work (out of scope here)

After this fixed-`I` construction lands, the resulting concrete
formula will inform a brainstorm/design session for the appropriate
`I`-natural object.  Possibilities to explore include:

- A paranatural transformation between functors with two variances
  in `I` (one covariant, one contravariant).
- A 2-cell or pseudonatural transformation between pseudofunctors
  packaging the (J, P, Z)-natural form across varying `I`.
- A profunctor-style natural transformation that captures the lax
  `I`-naturality (forward whisker as a non-iso comparison map).
- Restriction of source-mors to those where `f_I` is fully
  faithful or an equivalence (so the forward whisker is iso).

Which of these (or a different direction) is appropriate will be
clearer once the fixed-`I` formula is in hand.
