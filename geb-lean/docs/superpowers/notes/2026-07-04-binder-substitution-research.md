# Binder substitution as a presheaf monad: research findings

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [1. Purpose and scope](#1-purpose-and-scope)
- [2. The universal property](#2-the-universal-property)
  - [2.1 Fiore-Plotkin-Turi: the initial substitution monoid](#21-fiore-plotkin-turi-the-initial-substitution-monoid)
  - [2.2 Altenkirch-Chapman-Uustalu: the free relative monad](#22-altenkirch-chapman-uustalu-the-free-relative-monad)
  - [2.3 Fiore-Szamozvancev: mechanized second-order metatheory](#23-fiore-szamozvancev-mechanized-second-order-metatheory)
  - [2.4 Allais-Atkey-Chapman-McBride-McKinna: the constructive Kit](#24-allais-atkey-chapman-mcbride-mckinna-the-constructive-kit)
- [3. Bind is the discrete-presheaf degeneration](#3-bind-is-the-discrete-presheaf-degeneration)
- [4. The carrier is a W-type plus a renaming action](#4-the-carrier-is-a-w-type-plus-a-renaming-action)
- [5. Repository substrate assets](#5-repository-substrate-assets)
  - [5.1 The `PolyEndo` / `PolyFix` stack (algebra-bearing)](#51-the-polyendo--polyfix-stack-algebra-bearing)
  - [5.2 `RIdent`: the context-shifting precedent](#52-rident-the-context-shifting-precedent)
  - [5.3 The `PresheafPRA` layer (functors and a discrete equivalence)](#53-the-presheafpra-layer-functors-and-a-discrete-equivalence)
- [6. The vendored `geb-mathlib` tower](#6-the-vendored-geb-mathlib-tower)
- [7. Substrate map (endo / slice / presheaf)](#7-substrate-map-endo--slice--presheaf)
- [8. Design implications and option space](#8-design-implications-and-option-space)
- [9. References](#9-references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

This note records the research pass for the indexed binder-substitution
infrastructure sub-project (broken out of ramified-recurrence Phase 6,
route L step L1). It documents the universal property of capture-avoiding
substitution for intrinsically-typed syntax, the reconciliation of that
property with the repository's existing free-monad `bind`, the map of
substrate assets in the repository and the vendored `geb-mathlib` tower,
and the resulting design option space. It is written to remain useful to
the future repository in which endofunctor, slice, and presheaf
polynomial functors are unified.

Companion documents: the ramified master plan
`docs/superpowers/plans/2026-07-02-ramified-recurrence-plan.md` (Phase 6,
route L); the gate record
`docs/superpowers/notes/2026-07-02-ramified-gates-decisions.md`
(decision 8: every recursive type is a `PolyFix` of a `PolyEndo`).

## 1. Purpose and scope

Ramified-recurrence Phase 6 (soundness) transcribes Leivant III
sections 4-5, which normalize a typed lambda calculus with binders. That
requires intrinsically-typed de Bruijn syntax with capture-avoiding
substitution. The repository's term layer `Tm`
(`GebLean/Ramified/Term.lean`) handles multi-sorted syntax whose contexts
are parameters and which has no binders; its substitution is the
free-monad `bind` (`polyFreeMBind`). Binder syntax, where contexts index
the terms and a binder shifts the context index, is a strictly richer
setting. This note pins the mathematics of that setting and inventories
what the repository already supplies toward it.

Constraint (decision 8): every recursive type in this development is a
`PolyFix` of a `PolyEndo`; Lean-native recursive inductive types are not
used. The design must therefore realize binder syntax and its
substitution on the `PolyFix` stack.

## 2. The universal property

The account below draws on four primary sources. Each states the same
object under a different presentation.

### 2.1 Fiore-Plotkin-Turi: the initial substitution monoid

M. Fiore, G. Plotkin, D. Turi, "Abstract Syntax and Variable Binding",
LICS 1999, pp. 193-202, DOI `10.1109/LICS.1999.782615`.

Let `F` be the category of finite cardinals and all functions
(renamings); `[F, Set]` the presheaf category. The presheaf of variables
`V(n) = F(1, n) = n` is the tensor unit. Context extension `delta` is
precomposition with `(-) + 1`: `(delta X)(n) = X(n + 1)`. A binding
signature induces a signature endofunctor `Sigma` on `[F, Set]`
(eq. (10)); the presheaf of terms modulo alpha-equivalence is the free
`Sigma`-algebra on `V`, i.e. the carrier of the initial
`(V + Sigma)`-algebra, `T_V = mu X. V + Sigma(X)` (Theorem 2.1).

The substitution monoidal structure has tensor

```text
(X . Y)(m) = integral^{n in F} X(n) x Y(m)^n
           = ( coproduct_{n} X(n) x Y(m)^n ) / ~
```

a coend, with unit `V`. A monoid `(X, mu, iota)` for `(., V)` is a
presheaf with unit `iota : V -> X` (variables-as-terms) and
multiplication `mu : X . X -> X` (simultaneous substitution). Clones are
equivalent to such monoids (Proposition 3.4). For any binding signature,
`(T_V, sigma, eta_V)` is a `Sigma`-monoid with `sigma` the substitution,
defined by structural recursion using the pointed strength of `delta`
(Corollary 3.6); and `T_V` is the initial `Sigma`-monoid (Theorem 4.1).
Initiality is the universal property: the unique homomorphism out of it
is compositional interpretation and satisfies the semantic substitution
lemma automatically.

### 2.2 Altenkirch-Chapman-Uustalu: the free relative monad

T. Altenkirch, J. Chapman, T. Uustalu, "Monads Need Not Be
Endofunctors", FoSSaCS 2010, LNCS 6014, pp. 297-311, DOI
`10.1007/978-3-642-12032-9_21`; LMCS 11(1:3) 2015, DOI
`10.2168/LMCS-11(1:3)2015`.

A relative monad on a functor `J : J0 -> C` is `T : |J0| -> |C|` with
units `eta_X : C(J X, T X)` and Kleisli extension
`(-)* : C(J X, T Y) -> C(T X, T Y)` satisfying the three monad laws with
`J` inserted for type-compatibility (Definition 1). Ordinary monads are
the case `J = Id_C`. Well-scoped lambda terms form the initial algebra of
`F G Gamma = J_f Gamma + G Gamma x G Gamma + G(1 + Gamma)` on
`[Fin, Set]` and are a relative monad over the variables functor
`J_f : Fin -> Set` (Example 2); substitution is precisely the Kleisli
extension `k*`. The typed case (Example 3) uses `J : Fin / Ty`,
`C = [Ty, Set]`. Sections 3-4 show relative monads are the monoids for a
left-Kan-extension tensor; when `Lan_J` is well-behaved this tensor
coincides with the Fiore-Plotkin-Turi `.`, so the two presentations name
one structure.

### 2.3 Fiore-Szamozvancev: mechanized second-order metatheory

M. Fiore, D. Szamozvancev, "Formal Metatheory of Second-Order Abstract
Syntax", POPL 2022, PACMPL 6(POPL) art. 53, DOI `10.1145/3498715`;
arXiv `2201.03504`. Agda artefact `agda-soas`.

Uses the Fiore-Plotkin-Turi universal property (initial `Sigma`-monoid)
in the multi-sorted second-order setting and mechanizes, generically from
a binding signature: the intrinsically-typed term type, then weakening,
renaming, simultaneous substitution, and metasubstitution, with all
correctness laws. The realization is two-staged: a renaming action first
(supplying the pointed strength), then substitution as the monoid
multiplication. Substitution cannot be defined before renaming.

### 2.4 Allais-Atkey-Chapman-McBride-McKinna: the constructive Kit

G. Allais, R. Atkey, J. Chapman, C. McBride, J. McKinna, "A Type- and
Scope-Safe Universe of Syntaxes with Binding", ICFP 2018, PACMPL 2(ICFP)
art. 90, DOI `10.1145/3236785`; JFP 31 e22, 2021, DOI
`10.1017/S0956796820000076`; arXiv `2001.11001`. Descends from McBride
"Type-preserving renaming and substitution" (2005) and Benton-Hur-
Kennedy-McBride "Strongly typed term representations in Coq", JAR 2012
(the original "Kit").

Intrinsically-typed terms are indexed families `List I -> I -> Set`
(context, result sort). A generic `Semantics` record with a `Thinnable`
value family, a `var` injection, and an `alg` using a Kripke function
space at binders yields one generic traversal (`semantics`, the fold).
Renaming is that traversal with values = variables; substitution is it
with values = terms, whose `Thinnable` instance is renaming (so renaming
precedes substitution, echoing the pointed strength). The generic
`Simulation` and `Fusion` frameworks prove the law suite (identity,
renaming functoriality, the four rename/substitution fusion laws, and the
monoid laws) once for every syntax in the universe. This is the
constructive, initial-algebra realization of the Fiore-Plotkin-Turi
universal property.

## 3. Bind is the discrete-presheaf degeneration

Take the context category discrete on a sort set `S` (objects are sorts,
only identity morphisms). This is exactly "syntax without binders": no
context to weaken, no non-trivial renamings. Then:

- `[Disc S, Set] = Set^S`, the slice `Type / S` up to the family/fibration
  equivalence. A presheaf is a bare `S`-indexed family; the renaming
  action `X(rho)` is trivial.
- In the tensor `(X . Y)(m) = integral^n X(n) x Y(m)^n` the only maps are
  identities, so the coend collapses to indexed-family composition
  `(X <> Y)_s = coproduct_{t in S} X_{t,s} x Y_t`, with unit the singleton
  family. Monoids are exactly `S`-sorted monads on `Set^S` with Kleisli
  bind.
- In the relative-monad view (ACU Definition 1) put `J = Id`; the three
  relative-monad laws become the three Kleisli monad laws verbatim, `eta`
  is `return`, `k*` is `bind`.

So the repository's `polyFreeMBind` (the Kleisli extension of the free
monad on the slice `Over X`, `GebLean/PolyAlg.lean:3980`) is precisely
this degeneration, and the repository's `Tm.subst`
(`GebLean/Ramified/Term.lean:130`) is capture-avoiding substitution for
the no-binder fragment. Nothing is lacking there. Binder substitution is
the non-degenerate case of the same universal property, in which
`delta != Id` and renamings are non-trivial; it is a context-changing
generalization of `bind`, not a replacement for it.

## 4. The carrier is a W-type plus a renaming action

Fiore-Plotkin-Turi Theorem 2.1 makes `T_V` an initial algebra in
`[F, Set]`. Because `[F, Set]` is a presheaf topos and `V + Sigma(-)` is
finitary, the initial algebra is computed pointwise by the Adamek
sequence: `T_V(n)` is an ordinary `Set`-level (indexed) inductive family,
and the presheaf structure is the additional functorial renaming action
`T_V(rho)`. Container-theoretically this is an indexed W-type:

- N. Gambino, M. Hyland, "Wellfounded Trees and Dependent Polynomial
  Functors", TYPES 2003, LNCS 3085, pp. 210-225: dependent polynomial
  functors have initial algebras (W-types) whenever the base has W-types.
- T. Altenkirch, N. Ghani, P. Hancock, C. McBride, P. Morris, "Indexed
  Containers", JFP 25 e5, 2015, DOI `10.1017/S095679681500009X`: indexed
  W-types reduce to ordinary W-types plus indexing.
- M. Fiore, "Discrete Generalised Polynomial Functors", ICALP 2012, LNCS
  7392, pp. 214-226, DOI `10.1007/978-3-642-31585-5_22`: the functor
  class tailored to variable binding.

Consequence: the term carrier is obtainable as a family of ordinary
indexed W-types; no presheaf-internal fixpoint primitive is required. The
presheaf level adds only the renaming action, coherent bookkeeping on top
of an inductive family. This is the determining fact for the substrate
choice.

## 5. Repository substrate assets

### 5.1 The `PolyEndo` / `PolyFix` stack (algebra-bearing)

`GebLean/PolyAlg.lean` and `GebLean/Polynomial.lean`:

- `PolyEndo X := PolyFunctorBetweenCat X X` (`PolyAlg.lean:55`) is a
  genuine dependent polynomial (indexed) endofunctor on the slice
  `Over X` for arbitrary index `X`; positions are indexed by the output
  index and each direction is assigned an arbitrary input index
  (`polyBetweenIndex`, `polyBetweenFamily`, `Polynomial.lean:970,:984`).
  A binder that shifts the context is a direction whose target index is
  the extended context.
- `PolyFix (P : PolyEndo X) : X -> Type` (`PolyAlg.lean:176`) is the
  indexed W-type; each child's index is whatever the family assigns, so
  children may live at extended indices. Dependent eliminator
  `PolyFix.ind` (`:206`); fold `polyFixFold` (`:359`); initiality
  `polyFixAlg_isInitial` (`:533`); Lambek iso `polyFixStr_iso` (`:635`).
- Free monad `PolyFreeM A P x := PolyFix (polyTranslate A P) x`
  (`:3344`), unit `polyFreeMPure` (`:3950`), bind `polyFreeMBind`
  (`:3980`) with the monad laws (`:3993-:4021`); monad on the slice
  `polyFreeMonad` (`:9615`) via `polyFreeForgetAdjunction` (`:8608`).
- The a-la-carte coproduct of polynomial endofunctors exists:
  `polyBetweenCoprod` (`GebLean/PolyUMorph.lean:420`), with injection and
  copairing, the colimit proof `polyBetweenIsColimitCofan` (`:605`), and a
  `HasCoproducts` instance (`:617`). (An earlier survey searched only
  `PolyAlg.lean` and missed this.)

### 5.2 `RIdent`: the context-shifting precedent

`GebLean/Ramified/HigherOrder.lean`:
`identEndo A : PolyEndo (List RType x RType)` (`:271`) indexes shapes by
`(context, result-sort)` and, for the recurrence-schema formers, assigns
directions a target context that is the parent's context extended
(`identTarget`, `:262`). `RIdent A Gamma tau := PolyFix (identEndo A)
(Gamma, tau)` (`:280`), folded by `PolyFix.ind` in `RIdent.interp`
(`:398`). This is a working instance of context-shifting directions on
`PolyFix` over a discrete `List RType x RType` index. It is closed (holes
are stored in shapes, no variable leaves), so it never needed a renaming
action or substitution; that layer is exactly what the binder-infra
sub-project adds.

### 5.3 The `PresheafPRA` layer (functors and a discrete equivalence)

`GebLean/PresheafPRA.lean`, `PresheafPRAUMorph.lean`,
`PresheafPRADiscrete.lean`:

- `PresheafPRACat I J` (`PresheafPRA.lean:139`) is the category of
  parametric right adjoints `PSh(I) -> PSh(J)`, evaluated faithfully by
  `praEvalAtFunctor` (`:1387`, fully faithful `:1423`).
- Universal constructions: arbitrary-indexed products `praHasProduct`
  (`PresheafPRAUMorph.lean:1742`) and coproducts `praHasCoproduct`
  (`:2297`); limits on the underlying `CoprodCovarRepCat`; a
  positions/directions round-trip `praReassemble` (`:1220`).
- Discrete equivalence `polyBetweenPresheafPRAEquiv`
  (`PresheafPRADiscrete.lean:257`): a two-way equivalence
  `PolyFunctorBetweenCat X Y ~= PresheafPRACat (Discrete X) (Discrete Y)`,
  evaluation-compatible (`evalCompatEquiv`, `:342`); `polyToPRA` (`:296`).
- Missing: no initial algebras / W-types / fold / induction at the
  `PresheafPRACat` level; no monad, free monad, bind, tensor, strength, or
  PRA composition; hence no renaming action and no substitution. The only
  route to a W-type is descending through the discrete equivalence into
  `PolyEndo` and using `PolyFix`.

Crucial limitation: the discrete equivalence covers only discrete index
categories, i.e. the no-binder case. For the non-discrete `[Ctx, Set]`
that binders require, there is no passage from `PresheafPRACat I J` down
to `PolyEndo`, so the presheaf layer supplies no W-type for binder syntax.

## 6. The vendored `geb-mathlib` tower

`vendor/geb-mathlib/Geb/Mathlib/Data/PFunctor/`:

- Tier 0: mathlib's univariate `PFunctor` (`Slice/Basic.lean:9`), which
  supplies W-types (`PFunctor.W`) but they are never used or lifted in
  this tree.
- Tier 1 (slice): `SliceDomPFunctor`/`SlicePFunctor extends PFunctor`
  (`Slice/Basic.lean:85-96`), a Gambino-Hyland dependent polynomial
  functor `Over dom -> Over cod` (`SlicePFunctor.functor`,
  `Slice/Functor.lean:104`).
- Tier 2 (presheaf): `PresheafPFunctor` (`Presheaf/Basic.lean:384`)
  `extends` the slice layer in a diamond and evaluates it at a presheaf's
  category of elements, cutting out natural elements, to give a Weber
  parametric-right-adjoint functor `PSh(I) -> PSh(J)`
  (`Presheaf/Functor.lean:123`).

The inter-layer passages are real but upward and one-directional
(`extends` plus evaluate-at-elements plus a naturality subtype); they
push functors up, not fixpoints, and are not packaged equivalences. There
are no initial algebras, folds, monads, bind, tensor, or strength at any
tier. This tower is the mathlib-aligned functor scaffolding
intended for the future unified repository; on the algebra side it is
currently bare.

## 7. Substrate map (endo / slice / presheaf)

```text
                 W-types / fold        renaming action   substitution
 PolyEndo/PolyFix   yes (PolyFix)         no (new)          no (new)
 (GebLean)          free monad: yes                         bind: discrete
                    (PolyFreeM)                             case only

 PresheafPRA        no                    no                no
 (GebLean)          (only via discrete    (presheaf =       (no monad
                    equiv -> PolyEndo)    functoriality,    on PRA)
                                          absent)

 geb-mathlib tower  no (PFunctor.W        no                no
 (vendored)         unused, not lifted)
```

Two-way passage `PolyEndo <-> PresheafPRA` exists only on discrete index
categories (`polyBetweenPresheafPRAEquiv`), i.e. the no-binder case. No
non-discrete passage exists anywhere. Therefore binder syntax cannot draw
a W-type from the presheaf layer; the W-type must come from `PolyFix`
over a discrete `Ctx x Ty` index, with the renaming action and
substitution built as folds on top. In presheaf terms, the renaming
action is exactly the data that upgrades the discrete-presheaf (slice)
object to a genuine `[Ctx, Set]`-presheaf; supplying it is the new
content.

## 8. Design implications and option space

Section 4 shows the term carrier is an indexed W-type plus a renaming
action; sections 5-7 show the only extant W-type substrate is `PolyFix`
over a discrete index (with `RIdent` as precedent), and that no
presheaf-level algebra machinery exists in either the repository PRA
layer or the vendored tower. Section 2.4 and the Fiore-Szamozvancev and
Allais lines give the constructive recipe: build (a) a renaming action,
(b) a context-changing substitution operator (the relative-monad Kleisli
extension), (c) the law suite, by a generic Kit-style traversal
(`PolyFix.ind`), and state the universal property (initial
`Sigma`-monoid / free relative monad) as the specification without
building the coend tensor.

Three approaches for how much presheaf-level structure to build now.

- Approach A (Kit on `PolyFix`, discrete index plus renaming action).
  Term type = `PolyFix` over discrete `Ctx x Ty` with variable leaves
  (generalizing `RIdent`, which has none). Renaming and substitution are
  one generic Kit traversal (`PolyFix.ind`); the law suite is proved once,
  generic over the binder signature. The presheaf / relative-monad
  universal property is stated as the specification the three operations
  satisfy, with its discrete degeneration identified with the existing
  free-monad `bind`. Decision-8-native, tractable now, reuses
  `PolyFix`/`PolyFreeM`; the presheaf story is the reusable specification
  for the future repository, and the construction transports directly.

- Approach B (native presheaf-level initial algebras). Build presheaf-
  level W-types (a `praFix`), fold, and monad structure at the
  `PresheafPRACat` level, so syntax lives natively in `[Ctx, Set]` with
  the renaming action inside the functoriality. Most presheaf-native and
  aligned with the unified vision, but requires building
  presheaf-internal fixpoint and monad machinery that exists in neither
  the repository PRA layer nor the
  vendored tower; section 4 shows this adds no capability over the fold
  (the carrier still reduces to an indexed W-type plus a renaming action).
  Highest implementation cost.

- Approach C (hybrid). Build the term type as `PolyFix` over a discrete
  index as in A, and additionally package the renaming action as explicit
  presheaf-PRA structure, connecting to `PresheafPRACat` through the
  discrete equivalence where it applies. More presheaf alignment than A;
  the non-discrete passage gap means the connection is partial, so the
  extra packaging yields limited benefit over A while adding
  infrastructure.

## 9. References

Primary literature:

- Fiore, Plotkin, Turi, "Abstract Syntax and Variable Binding", LICS
  1999, DOI `10.1109/LICS.1999.782615`.
- Altenkirch, Chapman, Uustalu, "Monads Need Not Be Endofunctors",
  FoSSaCS 2010 / LMCS 11(1:3) 2015, DOI `10.2168/LMCS-11(1:3)2015`.
- Fiore, Szamozvancev, "Formal Metatheory of Second-Order Abstract
  Syntax", POPL 2022, DOI `10.1145/3498715`, arXiv `2201.03504`.
- Allais, Atkey, Chapman, McBride, McKinna, "A Type- and Scope-Safe
  Universe of Syntaxes with Binding", ICFP 2018 / JFP 31 e22 2021, DOI
  `10.1017/S0956796820000076`, arXiv `2001.11001`.
- Benton, Hur, Kennedy, McBride, "Strongly Typed Term Representations in
  Coq", JAR 2012.
- Gambino, Hyland, "Wellfounded Trees and Dependent Polynomial Functors",
  TYPES 2003, LNCS 3085.
- Altenkirch, Ghani, Hancock, McBride, Morris, "Indexed Containers", JFP
  25 e5 2015, DOI `10.1017/S095679681500009X`.
- Fiore, "Discrete Generalised Polynomial Functors", ICALP 2012, DOI
  `10.1007/978-3-642-31585-5_22`.

Repository and vendored assets: file-and-line references appear inline in
sections 5-6.
