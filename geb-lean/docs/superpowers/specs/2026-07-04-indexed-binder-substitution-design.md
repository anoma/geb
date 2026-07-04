# Indexed binder-substitution kit: design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [1. Scope and policy](#1-scope-and-policy)
  - [1.1 What this delivers](#11-what-this-delivers)
  - [1.2 Motivation and consumer](#12-motivation-and-consumer)
  - [1.3 Constraints (inherited)](#13-constraints-inherited)
  - [1.4 Transcription-only policy](#14-transcription-only-policy)
- [2. Background: the universal property (summary)](#2-background-the-universal-property-summary)
- [3. Design](#3-design)
  - [3.1 The binding signature](#31-the-binding-signature)
  - [3.2 The term type](#32-the-term-type)
  - [3.3 Thinnings (order-preserving embeddings)](#33-thinnings-order-preserving-embeddings)
  - [3.4 The generic traversal (the Kit)](#34-the-generic-traversal-the-kit)
  - [3.5 Renaming and substitution](#35-renaming-and-substitution)
  - [3.6 The law suite](#36-the-law-suite)
  - [3.7 The bundled universal property](#37-the-bundled-universal-property)
  - [3.8 Test calculus](#38-test-calculus)
- [4. Components and boundaries](#4-components-and-boundaries)
- [5. Interface consumed by Phase 6](#5-interface-consumed-by-phase-6)
- [6. File structure](#6-file-structure)
- [7. Transcription versus novel](#7-transcription-versus-novel)
- [8. Deferred and future work](#8-deferred-and-future-work)
- [9. Open questions](#9-open-questions)
- [10. References](#10-references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## 1. Scope and policy

### 1.1 What this delivers

A generic, reusable infrastructure kit for intrinsically-typed
(well-typed, well-scoped) syntax with binders, realized on the
repository's `PolyEndo` / `PolyFix` polynomial-functor stack. For any
signature declaring operations with binding, the kit supplies:

- the term type (a `PolyFix`, so decision 8 holds);
- a renaming action along context embeddings;
- capture-avoiding simultaneous substitution;
- the substitution-lemma suite (renaming functoriality, the four
  renaming/substitution fusion laws, and the substitution monoid laws),
  proved once, generic over the signature;
- a bundled universal-property abstraction: a `RelativeMonad` structure
  over the variables functor that the term type instantiates.

It is exercised on one small test calculus (the simply-typed lambda
calculus) and delivers no application-specific syntax.

### 1.2 Motivation and consumer

The kit is the L1 step of ramified-recurrence Phase 6 (soundness, route
L), broken out as an independent sub-project (user decision 2026-07-04).
Phase 6 transcribes Leivant III sections 4-5, which normalize a typed
lambda calculus with binders (`RlambdaMR-omega`, `RlambdaMR-omega_o`, and
the representation calculus `1lambda(A)`); those calculi are the kit's
downstream consumers. The kit itself is application-neutral: it knows
nothing of ramified recurrence.

The repository's existing term layer `Tm` (`GebLean/Ramified/Term.lean`)
handles multi-sorted syntax whose contexts are parameters and which has
no binders, with substitution as the free-monad `bind` (`polyFreeMBind`).
Binder syntax, where the context indexes the terms and a binder shifts
the context index, is the strictly richer setting this kit addresses.

### 1.3 Constraints (inherited)

- Decision 8: every recursive type is a `PolyFix` of a `PolyEndo`; no
  Lean-native recursive inductive types. The term type is a `PolyFix`.
- No `noncomputable`; axiom hygiene (`propext`, `Quot.sound`,
  `Classical.choice` only); `sorry` never in committed code; the
  pre-commit Lean triad for every `.lean` commit; markdownlint and
  doctoc for every `.md`; `jj` only, no push without user line-by-line
  review; commit-message format with the
  `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`
  trailer; generic user references; the project prose style; citation at
  point of use.

### 1.4 Transcription-only policy

The mathematics is standard programming-language metatheory; the
realization on the polynomial-functor substrate is this project's. The
transcription-versus-novel marking is section 7. The background
mathematics is documented, with citations, in the companion research
note `docs/superpowers/notes/2026-07-04-binder-substitution-research.md`;
this spec cites it rather than restating it.

## 2. Background: the universal property (summary)

Full detail and citations are in the research note (sections 2-4).
Capture-avoiding substitution for intrinsically-typed syntax is the
multiplication of a monoid in the substitution-monoidal presheaf
category `[Ctx, Set]` (Fiore-Plotkin-Turi), equivalently the Kleisli
extension of the free relative monad over the variables functor
(Altenkirch-Chapman-Uustalu). The ordinary free-monad `bind` on the
slice `Set^S` is the degeneration of this structure to a discrete
context category (no binders). The term carrier is an indexed W-type
plus a functorial renaming action; no presheaf-internal fixpoint
primitive is required (research note section 4). The constructive
realization is the generic traversal ("Kit") of Allais et al., from
which renaming and substitution both arise and the law suite is proved
once.

This design takes the constructive route: build the renaming action, the
substitution operator, and the law suite by a generic traversal on
`PolyFix`, and state the universal property (as the `RelativeMonad`
abstraction of section 3.7), without constructing the coend-based
substitution tensor.

## 3. Design

Throughout, `Ty` is an arbitrary type of object sorts and
`Ctx := List Ty` a context; the term type is indexed by `Ctx x Ty`. A
variable is a de Bruijn index into the context. It is `Type`-valued
positional data, not the `Prop` membership `s in Gamma` (which is
proof-irrelevant and would collapse distinct occurrences of the same
sort):

```lean
def Var (Γ : Ctx Ty) (s : Ty) : Type := { i : Fin Γ.length // Γ.get i = s }
```

`Var` is first-order indexing data, not recursive syntax, so decision 8
does not bear on it (as with `Thinning`, section 3.3). The kit appends a
binder's bound sorts at the end of the context (`Gamma ++ Xi`), so the
newest bound variables occupy the highest indices.

### 3.1 The binding signature

A `BinderSig Ty` describes operations with binding. Each operation has a
result sort and a list of arguments; each argument declares the sorts it
binds (a `Ctx` appended to the ambient context) and the argument's own
sort. This induces a polynomial endofunctor on the index `Ctx x Ty`:

```lean
structure BinderSig (Ty : Type u) where
  Op : Type u
  result : Op → Ty
  args : Op → List (Ctx Ty × Ty)   -- per argument: (bound sorts, sort)

-- the induced signature endofunctor: at output index (Γ, s),
-- positions are operations with result s (in any Γ), and the
-- argument at (Ξ, t) targets the extended index (Γ ++ Ξ, t).
def BinderSig.polyEndo (S : BinderSig Ty) : PolyEndo (Ctx Ty × Ty)
```

The context-extending direction targets `(Gamma ++ Xi, t)`; this is the
`identTarget` pattern already used by `RIdent`
(`GebLean/Ramified/HigherOrder.lean:262`), lifted to a reusable
signature abstraction. `BinderSig.polyEndo` and its evaluation carry a
`@[simp]` characterization.

### 3.2 The term type

Variables are the leaves of a free monad over the diagonal variable
family. Unlike the existing `Tm` idiom (`Term.lean:107,:113`), where the
context is a parameter and the leaf object is the per-context
`varOver Γ`, here the context is part of the index, so the leaf object
must be the single `Ctx x Ty`-indexed family whose fiber over `(Γ, s)`
is `Var Γ s` (a per-context leaf object would place the sub-terms under
a binder, at index `(Γ ++ Ξ, t)`, in a different free monad and break
the single-`PolyFix` structure):

```lean
-- diagonal variable family: total space Σ Γ, Fin Γ.length;
-- fiber over (Γ, s) is Var Γ s (positional, Type-valued)
def varOver : Over (Ctx Ty × Ty)
  := Over.mk (fun p : (Σ Γ : Ctx Ty, Fin Γ.length) => (p.1, p.1.get p.2))
def Tm (S : BinderSig Ty) (Γ : Ctx Ty) (s : Ty) : Type
  := PolyFreeM varOver S.polyEndo (Γ, s)
def Tm.var {S Γ s} (x : Var Γ s) : Tm S Γ s      -- = polyFreeMPure
def Tm.op  {S Γ s} (o) (args) : Tm S Γ s          -- = PolyFix.mk (Sum.inr …)
```

`Tm S Γ s` is a `PolyFix` (decision 8). Its recursor is `PolyFix.ind`; a
`@[simp]` characterization of `Tm.op`'s children by argument index is
provided. Under a binder that binds `Ξ`, a sub-term at index
`(Γ ++ Ξ, t)` has variable leaves `Var (Γ ++ Ξ) t` automatically, since
the diagonal leaf family's fiber there is exactly that.

### 3.3 Thinnings (order-preserving embeddings)

Context renamings are order-preserving embeddings (OPEs). Thinnings are
first-order data on `Ctx`, not recursive syntax, so decision 8 does not
bear on them. `Thinning` is the general OPE relation (each step keeps or
drops a context entry), so arbitrary embeddings — including the suffix
embedding `Δ ⊆ Δ ++ Ξ` that the under-binder weakening of the
append-at-end convention needs — are expressible:

```lean
def Thinning : Ctx Ty → Ctx Ty → Type              -- OPEs (keep/drop steps)
def Thinning.id {Γ} : Thinning Γ Γ
def Thinning.weak {Γ s} : Thinning Γ (s :: Γ)       -- drop one new head
def Thinning.lift {Γ Δ s} : Thinning Γ Δ → Thinning (s :: Γ) (s :: Δ)
def Thinning.weakAppend {Γ Ξ} : Thinning Γ (Γ ++ Ξ) -- suffix embedding
def Thinning.comp {Γ Δ Θ} : Thinning Γ Δ → Thinning Δ Θ → Thinning Γ Θ
def Thinning.app {Γ Δ s} : Thinning Γ Δ → Var Γ s → Var Δ s
```

with the category laws (`id`/`comp` unit and associativity) and `app`
functoriality. mathlib's `List.Sublist` is the OPE relation on lists
but is `Prop`-valued, so it cannot compute `Thinning.app` into `Type`; a
`Type`-valued thinning (as here, or a `Fin` order embedding with a
sort-preservation condition) is used. The plan confirms the exact
representation (section 9).

### 3.4 The generic traversal (the Kit)

One fold, defined by `PolyFix.ind`, parameterized by a `Kit`: a value
family `V : Ctx → Ty → Type`, a thinning action on values, a variable
injection, and an algebra interpreting each operation, with the
environment weakened across each binder's bound sorts.

```lean
structure Kit (S : BinderSig Ty) (V : Ctx Ty → Ty → Type) where
  var  : ∀ {Γ s}, Var Γ s → V Γ s
  toTm : ∀ {Γ s}, V Γ s → Tm S Γ s
  wk   : ∀ {Γ Δ s}, Thinning Γ Δ → V Γ s → V Δ s   -- thinnable values
def Env (V : Ctx Ty → Ty → Type) (Γ Δ : Ctx Ty) : Type
  := ∀ (s : Ty), Var Γ s → V Δ s
def traverse {S V} (K : Kit S V) {Γ Δ s}
    (ρ : Env V Γ Δ) (t : Tm S Γ s) : Tm S Δ s
```

At an operation, `traverse` recurses into each argument with the
environment weakened (via `K.wk` along the suffix embedding) across that
argument's bound sorts and extended by the freshly bound variables; at a
variable it applies `ρ` and injects through `K.toTm`. A `@[simp]`
equational characterization of `traverse` on `var`/`op` is provided.
`traverse` is defined by `PolyFix.ind` with the environment-abstracting
motive `motive {x} _ := ∀ Δ, Env V x.1 Δ → Tm S Δ x.2`.

### 3.5 Renaming and substitution

Two instances of `traverse`:

```lean
def ren {S Γ Δ s} (ρ : Thinning Γ Δ) (t : Tm S Γ s) : Tm S Δ s
  -- traverse with V = Var, K.wk = Thinning weakening of variables
def sub {S Γ Δ s} (σ : Env (Tm S) Γ Δ) (t : Tm S Γ s) : Tm S Δ s
  -- traverse with V = Tm S, K.wk = ren of terms
```

`ren` is the functorial renaming action (the presheaf structure of
section 2); `sub` is the context-changing substitution — the
relative-monad Kleisli extension `k*` — whose value-thinning instance is
`ren` (so `ren` is defined first). On the identity-context, renaming-free
fragment, `sub` agrees with `polyFreeMBind` (research note section 3).

### 3.6 The law suite

Proved once, generic over `S : BinderSig Ty`. The four Allais fusion
laws are ren-ren, ren-sub, sub-ren, sub-sub; ren-ren is renaming
functoriality and sub-sub is the substitution associativity, so they are
grouped with the functor and monoid laws respectively:

- renaming functoriality (ren-ren): `ren Thinning.id = id`,
  `ren (ρ.comp τ) = ren τ ∘ ren ρ`;
- the mixed fusion laws: ren-sub `sub σ (ren ρ t) = sub (fun s x => σ s
  (ρ.app x)) t`, and sub-ren `ren ρ (sub σ t) = sub (fun s x => ren ρ (σ
  s x)) t`;
- substitution monoid / relative-monad laws: left unit
  `sub σ (Tm.var x) = σ _ x`, right unit `sub (fun _ => Tm.var) t = t`,
  associativity (sub-sub) `sub τ (sub σ t) = sub (fun s x => sub τ (σ s
  x)) t`.

The laws live in the `Binding` namespace, avoiding collision with the
`Ramified` clone laws `Tm.subst_id` / `Tm.subst_subst`
(`Term.lean:139,:153`).

Following Fiore-Szamozvancev and Allais et al., substitution is defined
after renaming (the renaming action is the pointed strength that makes
substitution-under-a-binder well-defined), and the laws are propositional
equalities proved by `PolyFix.ind`.

### 3.7 The bundled universal property

mathlib has no relative-monad type and its monoid-object interface
`Mon_` requires the substitution tensor this design does not build, so a
minimal relative-monad structure is defined (the concept is
Altenkirch-Chapman-Uustalu, Definition 1) and instantiated:

```lean
-- A minimal relative monad (Altenkirch-Chapman-Uustalu, Definition 1):
-- an object map T, a unit, a Kleisli extension, and three laws.
structure RelativeMonad {J0 C} (J : J0 → C) (hom : C → C → Type)
    (T : J0 → C) where
  unit : ∀ X, hom (J X) (T X)
  ext  : ∀ {X Y}, hom (J X) (T Y) → hom (T X) (T Y)
  -- laws: ext k ∘ unit = k; ext unit = id; ext ℓ ∘ ext k = ext (ext ℓ ∘ k)
```

The kit provides the instance with ambient category `C = Set^Ty`
(`[Ty, Set]`, sorts discrete), index category `J0 = Ctx` carrying the
renamings, `J Γ = fun s => Var Γ s`, `hom X Y = ∀ s, X s → Y s`,
`T = Tm S`, `unit = Tm.var`, and `ext = sub`; its three laws are exactly
the section 3.6 monoid laws. This is the Altenkirch-Chapman-Uustalu
relative-monad framing (Examples 2-3), in which `hom` is the `Set^Ty`
family map that `sub` consumes (an `Env (Tm S)`); it is deliberately not
a `[Ctx, Set]` presheaf natural transformation — that is the
Fiore-Plotkin-Turi monoid framing, whose multiplication is a map out of
the coend tensor this design does not build. The module docstring
records that `(Tm S, Tm.var, sub)` is thereby the initial Sigma-monoid /
free relative monad over the variables presheaf (research note
section 2), whose discrete degeneration is `polyFreeMonad`. A future
`Mon_` instantiation in the substitution-monoidal `[Ctx, Set]` category
(once its coend tensor is built in the unified repository) is the
convergence target and is deferred (section 8).

### 3.8 Test calculus

The simply-typed lambda calculus instantiates the kit end to end: a base
type and function types (`Ty` = the STLC types), operations `app` and
`lam` (`lam` binds one argument sort), and worked `example`s exercising
`var`, `ren`, `sub`, and each law on concrete terms. This is the kit's
acceptance test; it is not a consumer API.

## 4. Components and boundaries

Each component has one responsibility, depends only on those below it,
and is testable independently:

| Component | Responsibility | Depends on |
| --- | --- | --- |
| `BinderSig` | signatures with binding; the induced `PolyEndo` | `PolyEndo`, `Polynomial` |
| `Tm` | the term type, `var`, `op`, recursor | `BinderSig`, `PolyFreeM` |
| `Thinning` | OPEs on contexts and their action on variables | `Ctx`, `Var` |
| `Kit` / `traverse` | the generic fold with binder-weakened environments | `Tm`, `Thinning`, `PolyFix.ind` |
| `ren` / laws | renaming as a `Kit` instance; functoriality | `Kit`, `Thinning` |
| `sub` / laws | substitution as a `Kit` instance; fusion + monoid laws | `ren`, `Kit` |
| `Env` helpers | `idEnv`, `extendEnv`, the append-variable eliminator, `instantiate`, `instantiate₁` | `Tm`, `Var`, `sub` |
| `RelativeMonad` + instance | the bundled universal property | `sub` and its laws |
| `Stlc` example | end-to-end instantiation and acceptance tests | the whole kit |

## 5. Interface consumed by Phase 6

Phase 6 instantiates `BinderSig` for each Leivant calculus and consumes:
`Tm`, `Tm.var`, `Tm.op`; `ren`, `sub`; the law suite (by name); the
`RelativeMonad` instance; and the environment helpers below. The
beta/eta/recurrence/flat reductions of the Leivant calculi are defined
by Phase 6 on top of `sub`. Each substitutes the bound variables while
fixing the ambient context: with the append-at-end convention a body
lives at `Γ ++ Ξ` and the reduct at `Γ`, so the substitution is the
identity environment on the `Γ`-part extended by the argument terms on
the `Ξ`-slots (an `Env (Tm S) (Γ ++ Ξ) Γ`), not an environment over a
one-element context. To build it the kit exports:

- `idEnv : Env (Tm S) Γ Γ` — the identity environment `Tm.var`;
- `extendEnv : Env (Tm S) Γ Δ → (∀ t, Var Ξ t → Tm S Δ t) →
  Env (Tm S) (Γ ++ Ξ) Δ` — environment extension over appended contexts;
- the append-variable eliminator `Var (Γ ++ Ξ) s → Var Γ s ⊕ Var Ξ s`;
- `instantiate : (∀ t, Var Ξ t → Tm S Γ t) → Tm S (Γ ++ Ξ) s → Tm S Γ s`
  — the derived multi-variable substitution (`sub` at
  `extendEnv idEnv _`);
- `instantiate₁ : Tm S Γ a → Tm S (Γ ++ [a]) s → Tm S Γ s` — its
  single-variable specialization (beta / destructor substitution),
  internalizing the singleton `Fin 1` / sort-proof transport once so
  every caller need not re-derive it.

The beta/recurrence/flat reductions themselves are not part of this kit.
The kit fixes the shapes of `Tm`, `ren`, `sub`, and these helpers that
Phase 6's reduction relations and normalization argument rely on.

## 6. File structure

New source under `GebLean/Binding/`; tests under `GebLeanTests/Binding/`.
The plan finalizes the split; the intended units are:

| File | Contents |
| --- | --- |
| `GebLean/Binding/Signature.lean` | `Ctx`, `Var`, `BinderSig`, `BinderSig.polyEndo` |
| `GebLean/Binding/Term.lean` | `varOver`, `Tm`, `Tm.var`, `Tm.op`, recursor simp lemmas |
| `GebLean/Binding/Thinning.lean` | `Thinning`, its category laws, `Thinning.app` |
| `GebLean/Binding/Kit.lean` | `Kit`, `Env`, `traverse`, traversal simp lemmas |
| `GebLean/Binding/Renaming.lean` | `ren`, functoriality laws |
| `GebLean/Binding/Substitution.lean` | `sub`, fusion and monoid laws |
| `GebLean/Binding/RelativeMonad.lean` | `RelativeMonad`, the `Tm` instance |
| `GebLean/Binding/Examples/Stlc.lean` | the STLC test calculus |
| `GebLean/Binding.lean` | directory index |
| `GebLeanTests/Binding/*.lean` | per-component tests (+ index imports) |

## 7. Transcription versus novel

| Element | Kind | Source / note |
| --- | --- | --- |
| The universal property (initial Sigma-monoid / free relative monad); substitution = monoid multiplication / Kleisli extension | transcription | Fiore-Plotkin-Turi LICS 1999; Altenkirch-Chapman-Uustalu FoSSaCS 2010 |
| `RelativeMonad` structure and its three laws | transcription | Altenkirch-Chapman-Uustalu Definition 1 (no mathlib type; new Lean formalization) |
| Renaming, substitution, the generic Kit traversal, the law suite (functor/fusion/monoid) | transcription | Allais et al. ICFP 2018; Fiore-Szamozvancev POPL 2022; Benton-Hur-Kennedy-McBride JAR 2012 |
| Realization on `PolyEndo`/`PolyFix`: `BinderSig.polyEndo`, `Tm` as `PolyFreeM` over `Ctx x Ty`, `traverse` via `PolyFix.ind` | novel packaging | this project's substrate; generalizes the `RIdent` context-shifting pattern (`HigherOrder.lean:262,:280`) |
| `Thinning` (OPEs) | transcription | standard de Bruijn thinnings (or a mathlib embedding type if applicable) |
| STLC test calculus | transcription | standard |

## 8. Deferred and future work

- `Mon_` instantiation in the substitution-monoidal (coend-tensor)
  category, once that tensor is built; the presheaf-native re-homing of
  the term type to the `PresheafPRA` / unified endo-slice-presheaf tier
  (research note sections 5-7). The construction here transports to that
  setting; the universal property stated here is its specification.
- Alpha-equivalence is not an issue (de Bruijn indices are intrinsically
  alpha-quotiented); no separate alpha layer is built.
- Metasubstitution (second-order variables, Fiore-Szamozvancev) is not
  needed by Phase 6 and is out of scope.

## 9. Open questions

- The `Thinning` representation. mathlib's `List.Sublist` is the OPE
  relation on lists but is `Prop`-valued, so it cannot compute
  `Thinning.app` into `Type`; a `Type`-valued thinning is expected. The
  plan confirms whether a mathlib `Type`-valued embedding (for example a
  `Fin` order embedding with a sort-preservation condition) is reused or
  `Thinning` is defined here; either way the external interface is
  unchanged.
- The precise universe placement of `BinderSig.Op` relative to `Ty`
  (resolved during Task 1 by elaboration; the interface is
  universe-polymorphic as far as compiles).

## 10. References

- Research note (background, citations, substrate map):
  `docs/superpowers/notes/2026-07-04-binder-substitution-research.md`.
- Ramified master plan (Phase 6, route L, the consumer):
  `docs/superpowers/plans/2026-07-02-ramified-recurrence-plan.md`.
- Gate record (decision 8):
  `docs/superpowers/notes/2026-07-02-ramified-gates-decisions.md`.
- Primary literature: see the research note section 9.
