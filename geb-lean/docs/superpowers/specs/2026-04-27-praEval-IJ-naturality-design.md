# `praEvalAt*` Naturality in `(I, J, P, Z)` (Lax in `I`) — Design

Lifts `praEvalAtFunctor` to a fully `(I, J, P, Z)`-natural form, captured
as a **lax natural transformation** between `Catᵒᵖ ⥤ Cat` functors over
the I-base.  The per-`I` component is the existing fixed-`I` flat
functor `praPolyEvalAtIFunctor I`; the lax structure encodes the
forward-whisker comparison for `I`-variations.

## Status

Brainstorm complete 2026-04-27.

## Goal

Construct `praPolyEvalLaxNatTrans : LaxNatTransContraData praPolyEvalSourceOverI
praPolyEvalTargetOverI`, the `(I, J, P, Z)`-natural-but-lax bundle representing
the type of the unapplied `praEval` operator.  The bundle's per-`I`
component is `praPolyEvalAtIFunctor I` (existing); the lax-comparison
data encodes `I`-naturality via the forward whisker.

Plus the supporting infrastructure (`LaxNatTransContraData` framework),
the source / target outer-base bifunctors (`praPolyEvalSourceOverI`,
`praPolyEvalTargetOverI`), bridges to the fixed-`I` form and to the
per-component `praEvalAt`, and tests.

## Background and motivation

### The categorical content

`praEvalAtFunctor I J : PRACat(I, J) ⥤ (PSh(I) ⥤ PSh(J))`, equivalently
`praEvalAtBifunctor I J : PRACat(I, J) × PSh(I) ⥤ PSh(J)`, evaluates a
presheaf PRA at a presheaf input.  Read pointwise:

```text
(praEvalAt P Z) j a = Hom_{PSh(I)}(F_{P, j, a}, Z)
```

where `F_{P, j, a}` is the directions presheaf at position `a` in fibre
`j`.  As `(I, J, P, Z)` varies, this presheaf-on-`J` varies — but the
naturality is asymmetric:

- **Strict in `J, P, Z`.**  The fixed-`I` form `praPolyEvalAtIFunctor I`
  (built in the praEvalAtI workstream, commits `c2672b92..d9b853af`)
  realizes this as a flat functor between contraGrothendiecks via a
  strict natural transformation `praPolyEvalAtINatTrans I`.  All
  naturality squares close by `rfl`.

- **Lax in `I`.**  When `I` varies via `f_I : I_s ⟶ I_t`, the natural
  comparison map between source and pulled-back target evaluations is
  the **forward whisker** on hom-sets:

  ```text
  Hom_{PSh(I_t)}(F, Z)  ↪  Hom_{PSh(I_s)}(F ⋙ f_I.op, Z ⋙ f_I.op)
                    g  ↦                              g ⋙ f_I.op
  ```

  This is an injection but not iso (would require a section, i.e., a
  left adjoint to whiskering, which is not strict).  At each `j` in the
  J-base of a fixed-`I_t` source object:

  ```text
  praEvalAt (P_t) (Z_t) (j) =
      Σ_{a : P_t.pos j} Hom_{PSh(I_t)}(F_{P_t, j, a}, Z_t)

  praEvalAt (f_I^* P_t) (f_I^* Z_t) (j) =
      Σ_{a : P_t.pos j} Hom_{PSh(I_s)}(F_{P_t, j, a} ⋙ f_I.op,
                                       Z_t ⋙ f_I.op)
  ```

  The forward whisker provides a natural inclusion of the LHS into the
  RHS.  The opposite direction does not exist on the nose.

### The motivating consumer

The (I, J)-natural form is needed for the type-checker of a programming
language in which "evaluation of a PRA functor" appears as an operator.
The fixed-`I` form `praPolyEvalAtIFunctor I` only suffices to type-check
the *partial application* of the operator at a specific `I`.  To assign
a type to the unapplied operator itself, the type-checker requires a
canonical mathematical object encoding the joint `(I, J, P, Z)`-naturality
— and that object must faithfully reflect the operator's actual
structure, including its laxness in `I`.

The bundled `LaxNatTransContraData` value built here **is** that type.
It does not collapse into a single Cat-arrow (such a collapse is
impossible as analyzed below); it stays as a structured bundle with
strict per-`I` components plus lax comparison data.

### Why a flat-functor lift does not exist

A strict flat functor `praPolyEvalSource ⥤ praPolyEvalTargetIJ` over
the joint `(Cat × Cat)`-base — the natural first attempt — does not
exist in any direction.  Working out the lift formula for an
`(grothendieckContraFunctor C).obj`-based total category:

- The lift formula constructs a target morphism
  `ψ_target : (α.app c_X).obj X.fiber ⟶
   (F.map h.op).obj((α.app c_Y).obj Y.fiber)`
  by composing `(α.app c_X).map ψ_source` with a comparison
  `(α.app c_X).obj((G.map h.op).obj Y.fiber) ⟶
   (F.map h.op).obj((α.app c_Y).obj Y.fiber)`.

- That comparison direction is the **OPLAX** direction (matching
  `OplaxNatTransContraData` of the existing primed framework).  For
  praEval, OPLAX would be
  `praEvalAt(f_I^* P_t)(f_I^* Z_t) ⟶ f_J^*(praEvalAt P_t Z_t)`, the
  inverse of the forward whisker — not naturally available.

- The forward whisker itself is in the **LAX** direction.  But LAX in
  the contra setting does not lift to a strict functor between
  contraGrothendiecks in either direction (the lift formula for either
  source-to-target or target-to-source requires inverses we lack).

So the natural object is not a flat functor.  Instead we package it as
a lax natural transformation between `Catᵒᵖ ⥤ Cat` functors at the
outer (I-only) level, with the existing fixed-`I` form as the per-`I`
component.

### Prior abandoned attempt

An earlier in-flight attempt (commits `81a0369f..d701b401`, source side
reverted by `c2672b92`) tried to build the (I, J)-natural form as a
strict flat functor between contraGrothendiecks via a new
`FunctorBetweenContraContra` framework.  This hit the variance mismatch
analyzed above.  The fixed-`I` workstream was the scope-down that
produced the per-`I` component; this workstream uses the per-`I` form
as the data of the bundle's `app` field.

The kept artifacts from the abandoned attempt remain reusable:
`praEvalTargetFibre`, `praPolyEvalTarget` (J-only target),
`FunctorBetweenContraContra` framework (general infrastructure).

## Scope

In scope:

- `LaxNatTransContraData` framework in `Utilities/Grothendieck.lean`,
  parallel to existing `OplaxNatTransContraData` but in the lax
  comparison direction and against `Cᵒᵖ ⥤ Cat` (unprimed).  Has `app`,
  `laxApp`, `laxNat`, `laxId`, `laxComp` fields and `id`, `comp`,
  `ofNatTrans` operations.  Does **not** have a `.toFunctor` extractor
  (the lift to a strict functor between contraGrothendiecks does not
  exist for lax-direction-in-contra; see Background above).

- `praPolyEvalSourceOverI : Catᵒᵖ ⥤ Cat` — outer-base source
  bifunctor sending `op I` to `praPolyEvalAtISource I`.  Constructed via
  curry of an `(I, J)`-bifunctor + `grothendieckContraFunctor Cat`.

- `praPolyEvalTargetOverI : Catᵒᵖ ⥤ Cat` — outer-base target bifunctor
  constant at `praPolyEvalTarget`.

- `praPolyEvalLaxNatTrans : LaxNatTransContraData praPolyEvalSourceOverI
  praPolyEvalTargetOverI` — the lax natural transformation bundle.

- Source-object helper `praPolyEvalSourceOverIObj` (mirror of
  `praPolyEvalAtISourceObj`).

- Strong bridge `praPolyEvalAtIFunctor_eq_praPolyEvalLaxNatTrans_app` —
  the per-`I` component of the bundle is exactly the fixed-`I` functor.

- Weak per-component bridge `praEvalAtFunctor_via_praPolyEvalLaxNatTrans`
  — directly relates per-component `praEvalAt` to the bundle.

- New test file `GebLeanTests/Utilities/PresheafPRAEvalNat.lean` with
  six sections (signature, framework sanity, bridge collapse,
  per-component compatibility, lax coherence, universe polymorphism).

- Workstream notes update (`.session/workstreams/presheaf-pra.md`).

Out of scope:

- `.toFunctor` extractor for `LaxNatTransContraData` (does not exist;
  see Background).

- A "lax functor between Grothendiecks" infrastructure that would let
  the bundle be expressed as a single Cat-arrow.  Speculative without a
  consumer that requires it.

- Symmetric infrastructure beyond the lax-direction case (no
  `OplaxNatTransContraFunctorData` here; that's a separate
  principled-symmetrization workstream if and when wanted).

- Profunctor-form natural extension (no analog of
  `praEvalAtProfunctor` promotion).

- Per-component accessor refactors (`praEvalAt`, `praEvalAt_index`,
  `praEvalAt_mor`, `praEvalAt_mk` retain current signatures).

- Migration of `PresheafPRAUMorph.lean` references — no current
  consumers depend on the (I, J)-natural form.

## Pre-work: revert in-flight commits

None.  The praEvalAtI workstream (which closed 2026-04-26 at commit
`d9b853af`) reverted the prior abandoned (I, J)-natural source side at
`c2672b92` and built the fixed-`I` form on top.  This workstream begins
from the current `terence/grothendieck` HEAD and only adds.

## Architecture

```text
                        praPolyEvalLaxNatTrans
            (LaxNatTransContraData over Catᵒᵖ ⥤ Cat, I-base)
          ┌────────────────────────────────────────────────┐
          │  app op I : praPolyEvalAtISource I              │
          │           ⥤ praPolyEvalTarget                   │
          │           = praPolyEvalAtIFunctor I             │
          │                                                 │
          │  laxApp (f_I) (x : praPolyEvalAtISource I_t):   │
          │    morphism in praPolyEvalTarget                │
          │    from (praPolyEvalAtIFunctor I_t).obj x       │
          │    to   (praPolyEvalAtIFunctor I_s).obj         │
          │           ((praPolyEvalSourceOverI.map f_I.op).obj x) │
          │    = forward whisker on the J-fiber of x        │
          │                                                 │
          │  laxNat / laxId / laxComp: coherence            │
          └────────────────────────────────────────────────┘
                      │                      │
                      │                      │
   praPolyEvalSourceOverI : Catᵒᵖ ⥤ Cat    praPolyEvalTargetOverI : Catᵒᵖ ⥤ Cat
   sends op I to                            constant at
     praPolyEvalAtISource I                 praPolyEvalTarget
```

The "outer base" is `Cat` (the I-base only).  The "inner base" (J) and
the data layers (P, Z) live inside the per-`I` Grothendieck
`praPolyEvalAtISource I` and are handled by the existing fixed-`I`
form's strict naturality.  The lax structure appears only at the I-layer.

When `f_I = 𝟙_I`, the forward whisker becomes identity; `laxApp`
reduces to `eqToHom`, and the bundle's I-component is exactly the
strict fixed-`I` form.

## New infrastructure: `LaxNatTransContraData`

Placement: new section in `GebLean/Utilities/Grothendieck.lean`,
immediately after the existing `OplaxFunctorCat` section (around line
7160).

Shape mirrors `OplaxNatTransContraData` (currently for `Cᵒᵖ' ⥤ Cat`)
but adapted to:

- `Cᵒᵖ ⥤ Cat` (unprimed opposite, matching standard mathlib +
  `grothendieckContraFunctor` conventions);

- the **lax** comparison direction (forward, target-side-pre-app
  through to source-side-after-app), opposite of oplax.

```lean
section LaxNatTransContraFunctor

universe vC uC vF uF

variable {C : Type uC} [Category.{vC} C]
variable (G F : Cᵒᵖ ⥤ Cat.{vF, uF})

abbrev LaxNatTransContraApp :=
  ∀ c : C, G.obj (Opposite.op c) ⥤ F.obj (Opposite.op c)

variable {G F} (app : LaxNatTransContraApp G F)

/-- Lax morphism for `α : G ⟹ F` between contra-functors.  For `f : c ⟶ c'`
    in C and `x : G.obj (op c')`, a morphism

      `(F.map f.op).obj ((app c').obj x) ⟶ (app c).obj ((G.map f.op).obj x)`

    encoding the comparison from "evaluate-then-pullback" to
    "pullback-then-evaluate". -/
abbrev LaxNatTransContraLaxApp :=
  ∀ {c c' : C} (f : c ⟶ c') (x : G.obj (Opposite.op c')),
    (F.map f.op).toFunctor.obj ((app c').obj x) ⟶
    (app c).obj ((G.map f.op).toFunctor.obj x)

variable (laxApp : LaxNatTransContraLaxApp app)

abbrev LaxNatTransContraLaxNat :=
  ∀ {c c' : C} (f : c ⟶ c')
    {x y : G.obj (Opposite.op c')} (φ : x ⟶ y),
    (F.map f.op).toFunctor.map ((app c').map φ) ≫ laxApp f y =
    laxApp f x ≫ (app c).map ((G.map f.op).toFunctor.map φ)

abbrev LaxNatTransContraIdEq :=
  ∀ (c : C) (x : G.obj (Opposite.op c)),
    (F.map (𝟙 c).op).toFunctor.obj ((app c).obj x) =
    (app c).obj ((G.map (𝟙 c).op).toFunctor.obj x)

lemma laxNatTransContraIdEqProof : LaxNatTransContraIdEq app := ...

abbrev LaxNatTransContraLaxId :=
  ∀ (c : C) (x : G.obj (Opposite.op c)),
    laxApp (𝟙 c) x = eqToHom (laxNatTransContraIdEqProof app c x)

abbrev LaxNatTransContraCompEq := ...
abbrev LaxNatTransContraCompEqRight := ...
lemma laxNatTransContraCompEqProof := ...
lemma laxNatTransContraCompEqRightProof := ...

abbrev LaxNatTransContraLaxComp :=
  ∀ {c c' c'' : C} (f : c ⟶ c') (g : c' ⟶ c'')
    (x : G.obj (Opposite.op c'')),
    laxApp (f ≫ g) x =
    eqToHom (laxNatTransContraCompEqProof app f g x) ≫
    (F.map f.op).toFunctor.map (laxApp g x) ≫
    laxApp f ((G.map g.op).toFunctor.obj x) ≫
    eqToHom (laxNatTransContraCompEqRightProof app f g x)

structure LaxNatTransContraData (G F : Cᵒᵖ ⥤ Cat.{vF, uF}) where
  app : LaxNatTransContraApp G F
  laxApp : LaxNatTransContraLaxApp app
  laxNat : LaxNatTransContraLaxNat app laxApp
  laxId : LaxNatTransContraLaxId app laxApp
  laxComp : LaxNatTransContraLaxComp app laxApp

/-- Identity lax nat trans. -/
def LaxNatTransContraData.id (G : Cᵒᵖ ⥤ Cat.{vF, uF}) :
    LaxNatTransContraData G G where
  app c := 𝟭 (G.obj (Opposite.op c))
  laxApp f x := eqToHom (by simp only [Functor.id_obj])
  laxNat _ _ := by simp [eqToHom_naturality]
  laxId _ _ := rfl
  laxComp _ _ _ := by simp [eqToHom_trans]

/-- Composition of lax nat transes. -/
def LaxNatTransContraData.comp ... := ...

/-- Promote a strict NatTrans to a lax bundle. -/
def LaxNatTransContraData.ofNatTrans {G H : Cᵒᵖ ⥤ Cat.{vF, uF}}
    (α : NatTrans G H) : LaxNatTransContraData G H := ...

end LaxNatTransContraFunctor
```

Key difference from `OplaxNatTransContraData`: the `laxApp` direction is
`(F.map f.op).(app c').x ⟶ (app c).(G.map f.op).x` (opposite of oplax),
and there is no `.toFunctor` extractor because the lift to a strict
functor between contraGrothendiecks does not exist for this direction
(see Background).

Length estimate: ~150 lines (smaller than oplax's ~250 because no
`.toFunctor` extractor and its supporting lemmas).

## The praEval-specific construction

Placement: new section `PresheafPRAEvalNat` in `GebLean/PresheafPRA.lean`
immediately after `PresheafPRAEvalAtINat` (currently ending at line
1705), before the closing `end GebLean`.

### Source over I: `praPolyEvalSourceOverI`

The (I, J)-bifunctor at the source-fibre level (combining
`presheafPRACatBifunctorUncurriedOp` with the `PSh(I)` projection)
already gives a `(Cat × Cat)ᵒᵖ ⥤ Cat`.  Currying over `I` then
composing with `grothendieckContraFunctor Cat` gives the desired
`Catᵒᵖ ⥤ Cat`.

```lean
/-- The `(Cat × Cat)ᵒᵖ ⥤ Cat` bifunctor: at op `(J, I)`, gives
    widened `PRACat I J × PSh(I)`.  PRA factor comes from
    `presheafPRACatBifunctorUncurriedOp`; PSh(I) factor from projecting
    op (J, I) → op I and applying `presheafCatFunctor`. -/
private def praPolyEvalSourceFibBif :
    (Cat.{v_J, u_J} × Cat.{v_I, u_I})ᵒᵖ ⥤ Cat.{...} :=
  -- LSP-discovered exact universe annotations and pairing
  ...

/-- Curry over the I component, then apply `grothendieckContraFunctor
    Cat` to get the I-indexed family of fixed-I sources as a functor. -/
def praPolyEvalSourceOverI :
    Cat.{v_I, u_I}ᵒᵖ ⥤ Cat.{...} :=
  -- LSP-discovered exact construction; conceptually:
  --   (op I) ↦ (grothendieckContraFunctor Cat).obj
  --              (praPolyEvalSourceFibBif curried at op I)
  ...
```

The action of `praPolyEvalSourceOverI` on a Cat-mor `f_I.op : I_tᵒᵖ →
I_sᵒᵖ` (from `f_I : I_s → I_t`) is the I-pullback functor on
`praPolyEvalAtISource`, sending `(J, (P_t, Z_t))` to `(J, (f_I^* P_t,
f_I^* Z_t))`.

Equivalence check: `praPolyEvalSourceOverI.obj (op I)` should be
definitionally equal to (or canonically isomorphic to)
`praPolyEvalAtISource I`.  If equal, no slice functor needed for the
strong bridge; if isomorphic, an `eqToHom` / `eqToIso` mediates.

### Target over I: `praPolyEvalTargetOverI`

```lean
/-- Outer-base target functor: constant at `praPolyEvalTarget`. -/
def praPolyEvalTargetOverI :
    Cat.{v_I, u_I}ᵒᵖ ⥤ Cat.{...} :=
  (Functor.const _).obj praPolyEvalTarget.{u_I, v_I, u_J, v_J, w_I, w'}
```

The action on Cat-mors is the identity functor on `praPolyEvalTarget`.

### The lax nat trans

```lean
/-- Per-I component: the existing fixed-I flat functor. -/
private def praPolyEvalLaxNatTrans_app (I : Cat.{v_I, u_I}) :
    praPolyEvalSourceOverI.{u_I, v_I, u_J, v_J, w_I, w'}.obj
        (Opposite.op I) ⥤
      praPolyEvalTargetOverI.{u_I, v_I, u_J, v_J, w_I, w'}.obj
        (Opposite.op I) :=
  -- Up to the source's curry-equivalence, this is praPolyEvalAtIFunctor I.
  praPolyEvalAtIFunctor.{u_I, v_I, u_J, v_J, w_I, w'} I

/-- Lax-comparison morphism: at `f_I : I_s ⟶ I_t` and
    `x : praPolyEvalAtISource I_t`, the morphism in
    `praPolyEvalTarget` from `(praPolyEvalAtIFunctor I_t).obj x` to
    `(praPolyEvalAtIFunctor I_s).obj((praPolyEvalSourceOverI.map f_I.op).obj x)`,
    given by the forward whisker on the J-fibre.

    Concretely, for `x = (J, (P_t, Z_t))`:
    base part: `𝟙_J` (no J change).
    fibre part: forward whisker, taking the widened presheaf
    `praEvalAt(P_t)(Z_t)` to the widened presheaf
    `praEvalAt(f_I^* P_t)(f_I^* Z_t)`. -/
private def praPolyEvalLaxNatTrans_laxApp
    {I I' : Cat.{v_I, u_I}} (f : I ⟶ I')
    (x : praPolyEvalSourceOverI.{u_I, v_I, u_J, v_J, w_I, w'}.obj
        (Opposite.op I')) :
    (praPolyEvalTargetOverI.{...}.map f.op).toFunctor.obj
      ((praPolyEvalLaxNatTrans_app.{...} I').obj x) ⟶
    (praPolyEvalLaxNatTrans_app.{...} I).obj
      ((praPolyEvalSourceOverI.{...}.map f.op).toFunctor.obj x) :=
  -- forward-whisker fibre, packaged via GrothendieckContraFunctor.mkHom
  ...

/-- The lax natural transformation bundle. -/
def praPolyEvalLaxNatTrans :
    LaxNatTransContraData
      praPolyEvalSourceOverI.{u_I, v_I, u_J, v_J, w_I, w'}
      praPolyEvalTargetOverI.{u_I, v_I, u_J, v_J, w_I, w'} where
  app I := praPolyEvalLaxNatTrans_app.{...} I
  laxApp f x := praPolyEvalLaxNatTrans_laxApp.{...} f x
  laxNat := by intros; ...    -- forward-whisker is functorial in the fibre data
  laxId := by intros; ...     -- f_I = 𝟙 reduces to eqToHom
  laxComp := by intros; ...   -- whisker-composition coherence
```

Coherence proofs:

- **`laxNat`** — forward whisker is natural in the fibre data
  (whiskering `g : F → Z` to `g ⋙ f_I.op` is natural in `g`).  Should
  be `rfl` or near-`rfl` — whiskering is functor-precomposition, which
  composes strictly.

- **`laxId`** — at `f_I = 𝟙_I`, the whisker by `f_I.op` is identity,
  so the comparison morphism is identity at the fibre and at the J-base.
  Reduces to `eqToHom` by the framework's
  `laxNatTransContraIdEqProof`.

- **`laxComp`** — at `f_I ≫ g_I`, the whiskers compose via
  `(f_I ≫ g_I).op = g_I.op ⋙ f_I.op` (functor-op functoriality).
  Reduces to the canonical `eqToHom`-bracketed expression via
  forward-whisker functoriality.

### Source-object helper

```lean
def praPolyEvalSourceOverIObj
    (I : Cat.{v_I, u_I}) (J : Cat.{v_J, u_J})
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
    (Z : ↑(presheafCat.{u_I, v_I, w_I} I)) :
    praPolyEvalSourceOverI.{u_I, v_I, u_J, v_J, w_I, w'}.obj
      (Opposite.op I) :=
  -- Up to the source's curry-equivalence:
  praPolyEvalAtISourceObj.{...} I J P Z
```

Public, mirrors `praPolyEvalAtISourceObj`.

### Strong bridge to fixed-`I`

The fixed-`I` form is the per-`I` component of the bundle.  This is
trivial by construction:

```lean
@[simp] theorem praPolyEvalAtIFunctor_eq_praPolyEvalLaxNatTrans_app
    (I : Cat.{v_I, u_I}) :
    praPolyEvalLaxNatTrans.{u_I, v_I, u_J, v_J, w_I, w'}.app I =
    praPolyEvalAtIFunctor.{u_I, v_I, u_J, v_J, w_I, w'} I := rfl
```

If the source's curry produces a Cat object that is definitionally
equal to `praPolyEvalAtISource I`, this is a true `rfl`.  If only
isomorphic, the theorem statement uses an `eqToHom` / equivalence on
the type signature.

### Weak per-component bridge

```lean
@[simp] theorem praEvalAtFunctor_via_praPolyEvalLaxNatTrans
    (I : Cat.{v_I, u_I}) (J : Cat.{v_J, u_J})
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
    (Z : ↑(presheafCat.{u_I, v_I, w_I} I)) :
    ((praEvalAtFunctor.{u_I, v_I, u_J, v_J, w_I, w'} I J).obj P).obj Z =
    -- unwidened fibre of the bundle's I-component applied to the
    -- source-object helper
    (ULift.down ... (ULiftHom.objDown ...
      (show ULiftHom (ULift (Jᵒᵖ ⥤ Type _)) from
        GrothendieckContraFunctor.objFiber
          ((praPolyEvalLaxNatTrans.{...}.app I).obj
            (praPolyEvalSourceOverIObj.{...} I J P Z))))) :=
  -- Composition of the strong bridge above with
  -- praEvalAtFunctor_via_praPolyEvalAtIFunctor
  by simp [praPolyEvalAtIFunctor_eq_praPolyEvalLaxNatTrans_app,
           praEvalAtFunctor_via_praPolyEvalAtIFunctor]
```

Gives downstream `simp` users a direct handle on the bundled form.

## Tests

New file `GebLeanTests/Utilities/PresheafPRAEvalNat.lean`, registered in
`GebLeanTests.lean`.  Six sections:

1. **Type-signature sanity** — `LaxNatTransContraData`,
   `praPolyEvalSourceOverI`, `praPolyEvalTargetOverI`,
   `praPolyEvalLaxNatTrans` exist with expected types at concrete
   universes.

2. **`LaxNatTransContraData` framework sanity** — small concrete
   construction (e.g., identity lax nat trans on a tiny `Cᵒᵖ ⥤ Cat`)
   compiles.  Verify `id`, `comp`, `ofNatTrans` constructors at
   concrete inputs.

3. **Bridge collapse** — the strong bridge
   `praPolyEvalAtIFunctor_eq_praPolyEvalLaxNatTrans_app` and the weak
   bridge `praEvalAtFunctor_via_praPolyEvalLaxNatTrans` hold at concrete
   inputs.

4. **Pointwise-accessor compatibility** — `praEvalAt`, `praEvalAt_index`,
   `praEvalAt_mor`, `praEvalAt_mk` still produce expected shapes.

5. **Lax coherence at concrete inputs** — verify the bundle's `laxNat`,
   `laxId`, `laxComp` hold at small concrete `(I_s, I_t, f_I, x)`
   triples.  In particular, `laxId` at the identity I-mor and a
   non-trivial source-object.

6. **Universe polymorphism** — works at mixed universes such as
   `{1, 0, 0, 0, 0, 0}`, `{0, 0, 1, 0, 0, 0}`, and the all-zero
   baseline.

## File placement

- `GebLean/Utilities/Grothendieck.lean`: new section
  `LaxNatTransContraFunctor` immediately after the existing
  `OplaxFunctorCat` section (around line 7160).

- `GebLean/PresheafPRA.lean`: new section `PresheafPRAEvalNat`
  immediately after the existing `PresheafPRAEvalAtINat` section
  (currently ending at line 1705), before the closing `end GebLean`.
  Section contents in this order: source-fibre bifunctor (private),
  `praPolyEvalSourceOverI`, `praPolyEvalTargetOverI`, lax nat trans
  (with private helper apps), source-object helper, strong bridge,
  weak bridge.

- `GebLeanTests/Utilities/PresheafPRAEvalNat.lean`: new file,
  registered in `GebLeanTests.lean`.

## Naming conventions

- `LaxNatTransContraData`, `LaxNatTransContraApp`,
  `LaxNatTransContraLaxApp`, `LaxNatTransContraLaxNat`,
  `LaxNatTransContraIdEq`, `LaxNatTransContraLaxId`,
  `LaxNatTransContraCompEq`, `LaxNatTransContraCompEqRight`,
  `LaxNatTransContraLaxComp`, `laxNatTransContraIdEqProof`,
  `laxNatTransContraCompEqProof`, `laxNatTransContraCompEqRightProof`
  — framework names parallel to the existing oplax section.

- `praPolyEvalSourceOverI`, `praPolyEvalTargetOverI` — outer-base
  bifunctors.  The `OverI` suffix indicates "as a functor over the
  I-base"; distinguishes from `praPolyEvalAtISource` (with `I` in name
  as a fixed parameter) and `praPolyEvalTarget` (J-only target).

- `praPolyEvalLaxNatTrans` — the lax natural transformation bundle,
  the central artifact of this workstream.

- `praPolyEvalSourceOverIObj` — source-object helper.

- `praPolyEvalAtIFunctor_eq_praPolyEvalLaxNatTrans_app` — strong bridge
  theorem.

- `praEvalAtFunctor_via_praPolyEvalLaxNatTrans` — weak per-component
  bridge theorem.

The `Lax` prefix on `praPolyEvalLaxNatTrans` reflects that the bundle
is genuinely a lax natural transformation, not a strict one.

## Risks and open questions

1. **Curry-then-grothendieck construction for `praPolyEvalSourceOverI`.**
   The source over I is built by currying the `(I, J)`-bifunctor over
   I and composing with `grothendieckContraFunctor Cat`.  Two questions:

   - Whether the resulting `praPolyEvalSourceOverI.obj (op I)` is
     **definitionally equal** to `praPolyEvalAtISource I`, or only
     isomorphic up to `eqToHom`.  Risk: medium.  Mitigation: if not
     definitional, use an `eqToIso` in the bridge theorems and live
     with mild `eqToHom` chasing.

   - Universe alignment: the curried bifunctor and its
     grothendieck'd composite live in specific Cat universes that may
     need explicit annotations.  Risk: small.  Mitigation: follow the
     universe-padding pattern from `praPolyEvalAtISourceFib`.

2. **`laxComp` proof complexity.**  Forward whiskers compose strictly
   (`f_I.op ⋙ g_I.op = (g_I ≫ f_I).op` in Cat-functor composition), so
   the coherence equation should reduce to the canonical
   `eqToHom`-bracketed form by functoriality.  Risk: medium —
   `eqToHom` alignment in the fibre may need explicit chasing through
   `Cat.opFunctor.map_comp` and forward-whisker associativity.
   Mitigation: factor into per-step lemmas if direct proof gets long.

3. **`laxApp` construction at the morphism level.**  The forward
   whisker is naturally a NatTrans of presheaves on J; lifting it to
   a morphism in `praPolyEvalTarget` (= contraGrothendieck over Cat
   of `praEvalTargetFibre`) requires packaging via
   `GrothendieckContraFunctor.mkHom` with the appropriate `eqToHom`
   for the J-base part.  Risk: small — well-trodden territory from
   the praDirections workstream.

4. **`LaxNatTransContraData.laxComp` direction.**  The composition
   coherence equation has a specific shape involving the order of
   `f.op` and `g.op` and corresponding `eqToHom` bookends.  Mirror of
   the oplax case but with the comparison direction reversed.  Risk:
   small — closely follow the oplax composition coherence shape.

## Future Work (out of scope here)

- Symmetric infrastructure: build `OplaxNatTransContraFunctorData`
  (unprimed, against `grothendieckContraFunctor`) parallel to the new
  `LaxNatTransContraData`, completing the four-corner table of
  oplax/lax × covariant-base/contra-base.

- Lax functor between Grothendiecks (general 2-categorical
  infrastructure): would let lax bundles like
  `praPolyEvalLaxNatTrans` be expressed as a single Cat-arrow in a
  bicategory of Grothendiecks.  Speculative without a concrete
  consumer.

- `praDirections` (I, J)-naturality at the directions level is already
  strict (built via `praPolyDirectionsFunctor`); no lax extension
  needed for that workstream.

- Eventually, the `praEval` (I, J, P, Z)-natural form will plug into
  the Phase 6 double-category structure as the cell action of the
  evaluation operator on PRAs, and into the type-checker for the
  programming language under development.
