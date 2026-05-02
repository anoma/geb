# LawvereNatBT: Two-Sort Lawvere Theory Extending LawvereER

## Status

This design supersedes the earlier
`2026-04-15-lawvere-treeer-subproject-4g2-design.md`, which pursued
an on-the-nose categorical isomorphism between a single-sort
tree-native theory and LawvereER.  That goal was not attainable at
first-order with Szudzik encoding (see "Background" below).  The
present design substitutes a two-sort theory and targets categorical
equivalence, which is both mathematically correct and practically
preferable.

## Overview

`LawvereNatBT` is a two-sorted Lawvere theory with sorts ℕ and BT
(labeled binary trees).  It extends `LawvereER` (the existing ℕ-only
theory) by adding BT as a second sort, together with explicit
bridging morphisms between the two.  `LawvereNatBTLex` is its
finite-limit completion via decidable subobjects, paralleling
`LawvereERLexCat`.

The intended computational class is the elementary recursive
functions (E₃), captured by:

* `LawvereER`'s generators (`zero`, `succ`, `proj`, `sub`, `comp`,
  `bsum`, `bprod`) on the ℕ sort;
* structural generators (`leaf`, `node`, `proj`, `comp`, `foldBT`) on
  the BT sort;
* cross-sort bridge generators `encodeBT : BT → ℕ` and
  `decodeBT : ℕ → BT` interpreting as Szudzik's bijection.

The categorical relationship with `LawvereER` is an equivalence (not
an on-the-nose isomorphism): the inclusion
`I : LawvereER → LawvereNatBT` sending `n ↦ (n, 0)` is fully faithful,
and every object `(n, m)` is internally isomorphic to `(n + m, 0)`
via iterated `encodeBT`, making `I` essentially surjective.

## Background

### Why the two-sort design

Prior design work (spec
`2026-04-15-lawvere-treeer-subproject-4g2-design.md`) pursued an
on-the-nose isomorphism `LawvereERCat ≅ LawvereTreeERCat`, with
`LawvereTreeER` as a single-sort tree-only theory.  Implementation
analysis established:

1. First-order polyadic ramified recurrence (our `TreeMor1` at any
   depth K) captures polynomial time on tree size (per Leivant 1994
   and Bellantoni-Cook 1992; see Leivant 1999 Table 1).  Under any
   encoding of ℕ into BT, this is strictly smaller than E₃.
2. Routes to reach E₃ within a single-sort tree theory require
   substantial new framework: higher-order types (Leivant's main
   result: `RRec^ω = E₃`), the Beckmann-Weiermann 2000 fragment of
   Gödel's T with a ground-`N` recursor restriction, or LOOP-style
   imperative syntax with size- or value-iteration.
3. The on-the-nose iso goal was incorrectly attributed to
   Beckmann-Weiermann 2000 in the prior spec's design decision D2;
   the cited result (Leivant 1994 + Bellantoni-Cook 1992) is for
   polynomial time, not E₃.

The two-sort design sidesteps these obstructions entirely: ℕ
arithmetic lives on the ℕ sort (using `LawvereER`'s already-verified
E₃-generating set), BT structural operations live on the BT sort
(first-order poly-time on tree size, a subset of E₃), and explicit
bridges mediate between them.  The combined theory has class E₃ by
construction.

### Why equivalence rather than isomorphism

Categorical equivalence expresses "same computational power,
different representations" — which is exactly the structural content
we want.  A tree-enhanced theory with explicit encode/decode bridges
offers *more expressiveness* (tree data structures) with *equal
strength* (same function class as `LawvereER`).  Isomorphism would
require the two theories to have the same object set, which they do
not (`LawvereNatBT` has BT arities while `LawvereER` does not).

### Relation to Phase 4g.1 existing work

Phase 4g.1's `LawvereTreeERCat` built a single-sort unlabeled tree
theory using depth-bounded `TreeMor1` terms.  That work is preserved
as-is: it remains a parallel development, useful in its own right for
tree-structural algorithms whose class is polynomial time on tree
size.  This design adds a faithful embedding
`LawvereTreeER ↪ LawvereNatBT` identifying unlabeled trees with the
labeled trees whose every leaf label is 0 (a decidable subobject in
the lex completion).

## Scope

### In scope

* `LawvereNatBT` base theory: term type `NatBTMor`,
  extensional-equality quotient, category structure, finite products,
  interpretation functor into `Type`, faithfulness.
* Full faithful embedding `I : LawvereER ↪ LawvereNatBT` sending
  `n ↦ (n, 0)`.
* Bridge generators `encodeBT` and `decodeBT` as named morphisms,
  with equational proofs `encodeBT ∘ decodeBT = 1_ℕ` and
  `decodeBT ∘ encodeBT = 1_BT` in the quotient.
* Categorical equivalence `LawvereER ≃ LawvereNatBT`.
* Full faithful embedding `LawvereTreeER ↪ LawvereNatBT`.
* Lex completion `LawvereNatBTLex` mirroring `LawvereERLexCat`, with
  decidable subobjects.
* Specific decidable subobject constructions: unlabeled BT
  (label = 0), finite-alphabet BT (label ≤ k).
* Transport of Phase 4f results (Ackermann non-fullness, tetration
  non-elementary) to `LawvereNatBT`.

### Out of scope

* Higher-order types, function-typed recursors, or any extension
  beyond first-order Lawvere theory structure.
* Paramorphism or destructors as primitive generators (derivable
  from `foldBT` plus pairing).
* Re-implementing Phase 4g.1's `LawvereTreeER` as a restriction of
  the two-sort theory; the theories coexist.
* Any modification of `LawvereER` itself.

## Design decisions

### D1. Objects indexed by `ℕ × ℕ`

Objects of `LawvereNatBT` are pairs `(n, m) : ℕ × ℕ`, interpreted as
`ℕⁿ × BTᵐ`.  Morphisms `(n, m) → (n', m')` are dependent tuples
consisting of `n'` ℕ-valued terms and `m'` BT-valued terms, each with
arity `(n, m)` in the appropriate sort.

Rationale: minimum new framework.  A general multi-sorted
Lawvere-theory scaffolding is not required for two sorts.
Generalization to more sorts, if ever needed, follows a standard
pattern and does not affect the two-sort implementation.

### D2. Labeled trees: BT with `leaf : ℕ → BT`

The BT type in this theory carries ℕ labels at leaves:

```
inductive BT where
  | leaf : ℕ → BT
  | node : BT → BT → BT
```

Unlabeled BT (from `GebLean/LawvereBT.lean`, with `leaf : BT`)
remains available for Phase 4g.1.  The labeled BT is either a fresh
inductive definition or obtained via the existing polynomial-functor
machinery with `ℕ` in place of `PUnit` at the leaf fiber.  Choice
between the two is left to implementation.

Rationale: ℕ-labeled leaves make BT a W-type over the polynomial
functor `ℕ + X × X`, the natural type for ASTs, tagged unions, and
labeled data.  Unlabeled BT is recovered as the decidable subobject
with predicate "every leaf label is 0".  Finite-alphabet trees
(alphabet size `k+1`) are the decidable subobject with predicate
"every leaf label is ≤ k".

### D3. Explicit bridge generators in both directions

Named generators:

* `encodeBT : BT → ℕ` — interprets as Szudzik-based encoding, the
  elementary-recursive `encodeBT` already present in
  `GebLean/LawvereBTPrimrec.lean` (or its labeled-tree analogue).
* `decodeBT : ℕ → BT` — the inverse.

Both are generators of the two-sort theory.  The equations
`encodeBT ∘ decodeBT = 1_ℕ` and `decodeBT ∘ encodeBT = 1_BT` hold in
the extensional quotient.

Rationale: making the bijection explicit as named morphisms supports
direct manipulation.  The internal isomorphism
`(n, m) ≅ (n + m, 0)` is constructible within the theory's language
by composing `encodeBT`s componentwise.  Both directions are given
for symmetry and proof convenience.

### D4. BT structural generators: leaf, node, proj, comp, foldBT

The BT sort generators:

* `leaf : ℕ → BT` (takes a ℕ-sort term for the label).
* `node : BT × BT → BT`.
* `proj_BT` and `comp_BT` (standard Lawvere-theory structure).
* `foldBT : (ℕ → X) → (X × X → X) → BT → X` — catamorphism.  The
  result sort `X` ranges over ℕ and BT.

Paramorphism, destructors, and case analysis are not primitives.
They are derivable from `foldBT` plus pairing (paramorphism via
paired fold; case analysis via fold with step ignoring recursive
values).

Rationale: minimum generator set.  The paramorphism derivation via
paired fold is straightforward given the finite-product structure.
Case analysis is `foldBT (fun n => onLeaf n) (fun x => onNode) t`
with an appropriate shape.

### D5. ℕ arithmetic unchanged from LawvereER

The ℕ sort uses `LawvereER`'s existing generators: `zero`, `succ`,
`proj`, `sub`, `comp`, `bsum`, `bprod`.  No new ℕ-side generators.

Rationale: `LawvereER` already generates E₃ on ℕ; no addition
needed.  The non-fullness and non-elementary results (Phase 4f.1
Ackermann, Phase 4f.2 tetration) apply on the ℕ sort unchanged.

### D6. Three-stage factorization: `LawvereER ≅ LawvereNatBTPure ≃ LawvereNatBT0 ≃ LawvereNatBT`

The categorical equivalence `LawvereER ≃ LawvereNatBT` factors as
three separate stages, each of which is independently meaningful:

```
LawvereER  ≅  LawvereNatBTPure  ≃  LawvereNatBT0  ↪  LawvereNatBT
       (Stage 3              (Stage 2                 (Stage 1
        on-the-nose iso)      back-translation         FullSubcategory
                              via ER-Szudzik)          + Szudzik on objects)

                  LawvereER ≃ LawvereNatBT  (composed)
```

**Naming summary** (in this spec, in code, and in the workstream
tracker):

| Conceptual name | Lean type | Role |
|---|---|---|
| TreeER | `LawvereNatBTCat` | Two-sort base category |
| Tree0ER | `LawvereNatBT0Cat` | `FullSubcategory` on `m = 0` objects |
| TreeNatER | `LawvereNatBTPureCat` | Strict-ER fragment of Tree0ER's hom-sets |
| NatER | `LawvereERCat` | Existing ℕ-only theory |

#### Stage 1: `LawvereNatBT ≃ LawvereNatBT0` (Szudzik on objects)

`LawvereNatBT0Cat` is the `FullSubcategory` of `LawvereNatBTCat`
on the `ObjectProperty`

```
isNatBT0 : LawvereNatBTCat → Prop
isNatBT0 nm := nm.2 = 0
```

By mathlib's `FullSubcategory` infrastructure, the inclusion
`ι : LawvereNatBT0Cat ⥤ LawvereNatBTCat` is full and faithful
automatically.  Hom-sets `(n_1, 0) ⟶ (n_2, 0)` in
`LawvereNatBT0Cat` are inherited verbatim from `LawvereNatBTCat`
— including morphism classes whose representatives use
`encodeBT`/`foldBTNat`/etc. internally.

Essential surjectivity: every object `(n, m)` of `LawvereNatBTCat`
has an explicit isomorphism `(n, m) ≅ (n + m, 0)` via
componentwise `encodeBT` (forward) and `decodeBT` (backward),
relying on the round-trip equations
`encodeBT ∘ decodeBT = 1_ℕ` and `decodeBT ∘ encodeBT = 1_BT` in
the extensional quotient.  Both `encodeBT` and `decodeBT` are
NatBT-internal generators; no ER-side machinery is invoked for
this stage.

Combined: `ι` is an equivalence
`LawvereNatBT0Cat ≃ LawvereNatBTCat` via mathlib's
`Functor.asEquivalence` (or analogous constructor) on a
fully-faithful + essentially-surjective functor.

#### Stage 2: `LawvereNatBT0 ≃ LawvereNatBTPure` (back-translation via ER-Szudzik)

`LawvereNatBTPureCat` ("TreeNatER") is a category whose objects
match `LawvereNatBT0Cat` and whose morphisms `(n_1, 0) ⟶ (n_2,
0)` are quotient classes containing only **strict-ER
representatives** — `NatBTMorN (n_1, 0) (n_2, 0)` tuples whose
every component's every sub-term is in the strict-ER fragment.
The strict-ER fragment is defined by the recursive predicate

```
NatBTMor1.isStrictER : NatBTMor1 nm σ → Prop
```

which holds when:

* `nm.2 = 0` and `σ = .nat`, AND
* the constructor is one of `zero`/`succ`/`natProj`/`sub`/
  `compNat`/`bsum`/`bprod`, AND
* every sub-term recursively satisfies `isStrictER`.

This excludes `leafBT`/`nodeBT`/`btProj`/`compBT`/
`foldBTNat`/`foldBTBT`/`encodeBT`/`decodeBT`.  By induction,
every term satisfying `isStrictER` is in 1-1 syntactic
correspondence with an `ERMor1 n` term.  `LawvereNatBTPureCat`'s
hom-sets are thus in 1-1 quotient correspondence with
`ERMorNQuo n_1 n_2`.

Stage 2 establishes the equivalence `LawvereNatBT0Cat ≃
LawvereNatBTPureCat` via:

* **Forward functor `ι_pure : LawvereNatBTPureCat ⥤
  LawvereNatBT0Cat`**: the inclusion of strict-ER quotient
  classes into the broader `LawvereNatBT0Cat` hom-sets.  Faithful
  by construction.
* **Backward functor `K : LawvereNatBT0Cat ⥤ LawvereNatBTPureCat`**:
  the *back-translation* taking each `LawvereNatBT0Cat`
  morphism class to its strict-ER class via structural reduction
  of `encodeBT`/`decodeBT`/`foldBTNat`/etc. in terms of
  ER-derivable Szudzik arithmetic.

The back-translation requires an ER-side simulation of `BTL`
operations:

* `Nat.pair`/`Nat.unpair` (Szudzik's bijection
  `ℕ × ℕ → ℕ`) as derived `ERMor1` terms with computation
  theorems linking to mathlib's `Nat.pair`.
* `BTL.encode`/`BTL.decode` as derived `ERMor1` terms,
  built using ER-derived `Nat.pair`/`Nat.unpair` and arithmetic.
* `BTL.fold`-on-code: a course-of-values recursion over a
  Gödel code computing the same value as `BTL.fold` on the
  decoded tree.  This is an ER-derived term with bounded
  iteration via `bsum`/`bprod`.

The Phase 4g.2 artifacts in `GebLean/Utilities/SzudzikSeq.lean`
(`Nat.seqPack`, `Nat.seqAt`, `Nat.treeFoldOnCode`,
`Nat.mutuTreeFoldOnCode`) provide the Layer-1 functions needed
by these derived ER terms.  The packaging-as-`ERMor1`-terms is
new work, but the underlying ℕ-level functions and their
correctness theorems are already in place.

The 4g.2 obstruction (Szudzik-polynomial barrier when
packaging at TreeERMor1 depth 1) does not apply to ER:
`ERMor1` has full composition and unbounded `bsum`/`bprod`,
which makes the ER analogues of the Layer-1 functions
straightforward to construct.

After both functors and round-trip equations are in place,
mathlib's `Equivalence` constructor packages them into
`LawvereNatBT0Cat ≃ LawvereNatBTPureCat`.

#### Stage 3: `LawvereNatBTPure ≅ LawvereER` (on-the-nose iso)

`LawvereNatBTPureCat`'s morphisms are by construction in 1-1
correspondence with `ERMorNQuo` morphisms.  In Lean this can be
realized by defining `LawvereNatBTPureCat`'s hom-set carrier
directly as `ERMorNQuo n_1 n_2` (with the object set
appropriately wrapped), making the iso definitional.

The functors:

* `J : LawvereERCat ⥤ LawvereNatBTPureCat`: identity on
  morphisms (with object-side renaming `n ↦ ⟨(n, 0), rfl⟩`).
* `K' : LawvereNatBTPureCat ⥤ LawvereERCat`: the inverse,
  also identity on morphisms.

Compositions `K' ∘ J` and `J ∘ K'` are definitional identities.
The iso is `Iso.refl _` or a trivial `Equivalence` construction.

#### Composition into the final equivalence

Composing the three stages — Stage 3 (`LawvereERCat ≅
LawvereNatBTPureCat`), Stage 2 (`LawvereNatBTPureCat ≃
LawvereNatBT0Cat`), Stage 1 (`LawvereNatBT0Cat ≃
LawvereNatBTCat`) — gives the categorical equivalence
`LawvereERCat ≃ LawvereNatBTCat`.

Equivalence is stronger than the "embedding plus non-fullness"
relationship between `LawvereER` and `LawvereBTQuotCat`.  The
distinction: every `LawvereNatBT` morphism, modulo the
equivalence, arises from a `LawvereER` morphism — whereas
`LawvereBTQuotCat`'s morphism space genuinely extends
`LawvereER`'s to include primitive-recursive-but-not-elementary
functions.

#### Rationale

The three-stage factorization has several properties motivating
the design:

* **Each stage isolates one piece of the work.**  Stage 1
  handles object-level Szudzik; Stage 2 handles morphism-level
  back-translation (the substantive new work); Stage 3 is
  trivial syntactic re-packaging.  This separation makes each
  stage independently reviewable and lets each be implemented
  in isolation.
* **Szudzik on objects vs Szudzik on morphisms are clearly
  distinguished.**  Stage 1's essential-surjectivity uses
  NatBT-internal `encodeBT`/`decodeBT` only.  Stage 2's
  back-translation uses the new ER-derived Szudzik
  infrastructure.  No conflation.
* **`LawvereNatBT0Cat` is available as a sub-presentation of
  `LawvereNatBTCat`.**  Clients who want the ℕ-only fragment do
  not have to switch categories — they restrict to
  `LawvereNatBT0Cat` as a `FullSubcategory` of the very category
  they were already working in.  This makes `LawvereNatBT` the
  one client-facing presentation of elementary recursion: the
  ℕ-only viewpoint and the tree-enabled viewpoint coexist as
  one category and a full subcategory of it.
* **`LawvereER` becomes a Lean-internal verification artifact.**
  Its purpose is to confirm, within Lean, that the
  client-facing `LawvereNatBT` is equivalent — and that the
  internal `LawvereNatBT0` is back-translatable — to the
  standard mathematical formulation of elementary recursive
  functions.  The Phase 4f.1 Ackermann non-fullness and Phase
  4f.2 tetration non-elementarity results live on the
  `LawvereER` side and transport across the equivalence to
  `LawvereNatBT`.
* **Equivalence captures "same computational strength,
  different representations."**  `LawvereNatBT` does not
  strengthen the function class beyond E₃; the tree sort
  contributes expressiveness, not computational power.  The
  back-translation gives this guarantee its constructive
  content: every NatBT computation explicitly reduces to an ER
  computation (via Szudzik), with no appeal to choice or
  classical reasoning.

### D7. Faithful embedding of Phase 4g.1 `LawvereTreeER`

The functor `J : LawvereTreeER → LawvereNatBT` sends each unlabeled
BT morphism to the labeled BT morphism constructed by uniformly
substituting `leaf 0` at every leaf position.  This is faithful
(distinct unlabeled morphisms remain distinct once given leaf label
0) and lands in the decidable subobject "leaves have label 0".

Rationale: preserves Phase 4g.1's existing work and makes the
relationship to the labeled theory explicit.

### D8. Lex completion

`LawvereNatBTLex` is built by the same decidable-subobject pattern
as `LawvereERLexCat`: objects are pairs `((n, m), p)` with `p` a
decidable predicate on `ℕⁿ × BTᵐ`; morphisms respect the predicate.
Finite products come from predicate conjunction; equalizers come
from predicate refinement.

Specific decidable subobjects of interest, built in
`LawvereNatBTSubtypes.lean`:

* **Unlabeled trees**: predicate "every leaf label in the tree
  equals 0".  The embedding of Phase 4g.1's `LawvereTreeER` lands
  in this subobject.
* **Finite-alphabet trees of alphabet size `k+1`**: predicate "every
  leaf label is ≤ k".

Rationale: matches the existing lex infrastructure from
`GebLean/LawvereERLex.lean` and `GebLean/LawvereERLexCat.lean`.
The lex completion is where downstream specializations naturally
emerge.

## Module layout

New library modules (under `GebLean/`):

* `LawvereNatBT.lean` — inductive term type `NatBTMor` and
  structural lemmas; no equational quotient yet.
* `LawvereNatBTQuot.lean` — extensional-equality setoid,
  `NatBTMorQuo`, category structure, `HasChosenFiniteProducts`.
* `LawvereNatBTInterp.lean` — interpretation functor into `Type`
  with faithfulness.
* `LawvereNatBT0.lean` — `isNatBT0` predicate and the
  `FullSubcategory` `LawvereNatBT0Cat`, with restricted
  `HasChosenFiniteProducts` (Stage 1's subcategory).
* `Utilities/ERTreeArith.lean` — ER-derived Szudzik primitives:
  `ERMor1.natPair`, `ERMor1.natUnpair`, `ERMor1.btlEncode`,
  `ERMor1.btlDecode`, plus `ERMor1.foldBTLOnCode` (the ER
  simulation of `BTL.fold` over a Gödel code).  Each carries
  an `@[simp]`-marked correctness theorem linking its
  interpretation to the corresponding `Nat.*` or `BTL.*`
  function.  Builds on `Utilities/SzudzikSeq.lean`'s Layer-1
  infrastructure (Phase 4g.2 preserved artifacts).
* `LawvereNatBTBackTrans.lean` — `NatBTMor1.toER` (the
  back-translation from `NatBTMor1 (n, 0) σ` to `ERMor1`-or-
  encoding-thereof), with extensional-correctness theorem
  showing the back-translated term has the same interpretation
  as the input modulo a `Fin.elim0` BT context.
* `LawvereNatBTPure.lean` — `LawvereNatBTPureCat` (Stage 3's
  TreeNatER): a category whose objects are isomorphic to
  `LawvereNatBT0Cat`'s and whose hom-sets are `ERMorNQuo` (or
  a thin wrapper).  Provides the on-the-nose iso
  `LawvereERCat ≅ LawvereNatBTPureCat`.
* `LawvereNatBTEquiv.lean` — Stage 1 (Szudzik on objects giving
  `LawvereNatBT0Cat ≃ LawvereNatBTCat`), Stage 2 (back-
  translation giving `LawvereNatBTPureCat ≃ LawvereNatBT0Cat`),
  Stage 3 composition, and the final `LawvereERCat ≃
  LawvereNatBTCat`.
* `LawvereNatBTLex.lean` — lex completion via decidable subobjects;
  finite limits.
* `LawvereNatBTSubtypes.lean` — unlabeled and finite-alphabet
  subtypes; faithful embedding `LawvereTreeER ↪ LawvereNatBT`.
* `LawvereNatBTTransport.lean` — transport of Phase 4f.1 and 4f.2
  non-fullness and non-elementary results.

New test modules under `GebLeanTests/` mirror each library file.

Registration: each new module added to `GebLean.lean`; each test
module added to `GebLeanTests.lean`.

## Detailed content sketches

### Term type

The inductive `NatBTMor` is dependently indexed by an ambient
arity `(n, m) : ℕ × ℕ` (the domain) and a sort `σ : Sort` (either
`ℕ` or `BT`), producing morphisms of the corresponding codomain
shape.  Exact Lean encoding — two separate inductives for each sort,
or a single inductive indexed by the sort — is an implementation
decision resolved during Stage α.

The generators:

```
-- ℕ-sort generators (ported from LawvereER)
zero          : NatBTMor (n, m) .nat
succ          : NatBTMor (n, m) .nat → NatBTMor (n, m) .nat
natProj       : Fin n → NatBTMor (n, m) .nat
sub           : NatBTMor (n, m) .nat → NatBTMor (n, m) .nat
                → NatBTMor (n, m) .nat
compNat       : NatBTMor (k, l) .nat
                → (Fin k → NatBTMor (n, m) .nat)
                → (Fin l → NatBTMor (n, m) .bt)
                → NatBTMor (n, m) .nat
bsum, bprod   : NatBTMor (n + 1, m) .nat → NatBTMor (n + 1, m) .nat

-- BT-sort generators
leaf          : NatBTMor (n, m) .nat → NatBTMor (n, m) .bt
node          : NatBTMor (n, m) .bt → NatBTMor (n, m) .bt
                → NatBTMor (n, m) .bt
btProj        : Fin m → NatBTMor (n, m) .bt
compBT        : NatBTMor (k, l) .bt
                → (Fin k → NatBTMor (n, m) .nat)
                → (Fin l → NatBTMor (n, m) .bt)
                → NatBTMor (n, m) .bt
foldBT_nat    : NatBTMor (n + 1, m) .nat      -- base: label is extra ℕ slot
                → NatBTMor (n + 2, m) .nat    -- step: two ℕ-valued recurs
                → NatBTMor (n, m + 1) .nat    -- plus the BT input
foldBT_bt     : NatBTMor (n + 1, m) .bt       -- base: label is extra ℕ slot
                → NatBTMor (n, m + 2) .bt     -- step: two BT-valued recurs
                → NatBTMor (n, m + 1) .bt     -- plus the BT input

-- Bridge generators
encodeBT      : NatBTMor (n, m + 1) .nat     -- takes one BT, gives ℕ
decodeBT      : NatBTMor (n + 1, m) .bt      -- takes one ℕ, gives BT
```

(The two `foldBT_*` constructors handle the two result sorts; if a
single polymorphic constructor is preferred, the sort is a parameter
of the constructor.  The exact signature for composition is also a
design point resolved during Stage α.)

### Interpretation

Each morphism `f : NatBTMor (n, m) σ` interprets as a function
`(Fin n → ℕ) × (Fin m → BT) → ⟦σ⟧` where `⟦.nat⟧ = ℕ` and
`⟦.bt⟧ = BT`.  The interpretation is structural.  Faithfulness of
the interpretation is the claim that distinct morphism classes
produce distinct interpretations.

### Equivalence (three-stage)

#### Stage 1: `LawvereNatBT0Cat ≃ LawvereNatBTCat`

`LawvereNatBT0Cat` is the `FullSubcategory` of `LawvereNatBTCat`
on the `ObjectProperty` `isNatBT0 nm := nm.2 = 0`.  Mathlib's
`FullSubcategory` infrastructure provides:

* The full-and-faithful inclusion functor `natBT0Inclusion :=
  isNatBT0.ι : LawvereNatBT0Cat ⥤ LawvereNatBTCat`.
* `Full` and `Faithful` instances automatically.

Essential surjectivity: every object `(n, m)` of
`LawvereNatBTCat` carries an explicit isomorphism `(n, m) ≅
(n + m, 0)` constructed by `encodeBT` on each BT component
(forward) and `decodeBT` on each ℕ-component-that-was-a-tree
(backward), with the round-trip equations holding in the
extensional quotient.  Combined with full + faithful, this
makes `natBT0Inclusion` a categorical equivalence
(`Functor.asEquivalence` or analogous).

This stage uses only NatBT-internal machinery (the `encodeBT`
and `decodeBT` generators).  No ER-side Szudzik infrastructure
is needed.

#### Stage 2: `LawvereNatBTPureCat ≃ LawvereNatBT0Cat`

`LawvereNatBTPureCat` (TreeNatER) is the strict-ER fragment of
`LawvereNatBT0Cat`'s hom-sets.  Concretely, a morphism class
`(n_1, 0) ⟶ (n_2, 0)` in `LawvereNatBTPureCat` is a quotient
class containing some representative whose every `natComps`
component is in the strict-ER fragment.

Two functors:

* `naturalInclusion : LawvereNatBTPureCat ⥤ LawvereNatBT0Cat`:
  the inclusion of strict-ER quotient classes into the broader
  `LawvereNatBT0Cat` hom-sets.  Faithful by construction.
* `backTranslate : LawvereNatBT0Cat ⥤ LawvereNatBTPureCat`:
  the back-translation, sending a `LawvereNatBT0Cat` morphism
  class `[t]` (with `t : NatBTMor1 (n_1, 0) .nat`) to the
  strict-ER class `[NatBTMor1.toER t]` where `toER` reduces
  every `encodeBT` / `decodeBT` / `foldBTNat` / etc. to its
  ER-side simulation via the derived `ERMor1` Szudzik
  infrastructure.

The round-trip equations:

* `backTranslate ∘ naturalInclusion = 𝟙_LawvereNatBTPureCat`:
  back-translating a strict-ER term gives the same strict-ER
  term (modulo extensional equality, which collapses to
  syntactic equality on the strict-ER fragment).
* `naturalInclusion ∘ backTranslate ≅ 𝟙_LawvereNatBT0Cat`:
  the back-translated then re-included class is extensionally
  equal to the original, so the two are equal in the
  `LawvereNatBT0Cat` quotient.  Naturality holds in the
  quotient.

The substantial work is in `NatBTMor1.toER`'s definition and
its correctness theorem.  See D6's Stage 2 description and the
`LawvereNatBTBackTrans.lean` module entry below for details.

#### Stage 3: `LawvereERCat ≅ LawvereNatBTPureCat`

`LawvereNatBTPureCat`'s morphism carrier is by construction
1-1 with `ERMorNQuo`.  Realized by defining the hom-set
directly as `ERMorNQuo n_1 n_2` (with the object-set wrapping
each `n` as `⟨(n, 0), rfl⟩`), the on-the-nose iso between
`LawvereERCat` and `LawvereNatBTPureCat` is `Iso.refl _` (or a
trivial `Equivalence` whose unit and counit are identities).

#### Final composition

```
LawvereERCat
   ≅  LawvereNatBTPureCat   (Stage 3, on-the-nose)
   ≃  LawvereNatBT0Cat      (Stage 2, back-translation)
   ≃  LawvereNatBTCat       (Stage 1, Szudzik on objects)
```

The composed equivalence is `natBTEquivalence : LawvereERCat
≌ LawvereNatBTCat`.  No `noncomputable` annotation should be
needed: every component is constructive once the back-
translation infrastructure is in place.

### ER-derived Szudzik and primitive-recursion infrastructure

Stage 2's back-translation requires an ER-side primitive-
recursion combinator and ER-derived Szudzik primitives.
The detailed design is a separate spec:
`docs/superpowers/specs/2026-04-17-er-primrec-design.md`
(local, gitignored).  That mini-phase adds the
Wikipedia-literal derived term `ERMor1.natRec` via Gödel
β-function and bounded search, preserving the `ERMor1`
inductive unchanged (the 7 Wikipedia generators remain the
exclusive primitives), then builds `ERMor1.foldBTLOnCode` on
top of it.

Summary of what the mini-phase provides:

* `ERMor1.natPair (n m : ℕ) : ERMor1 2`: takes `(x, y)` and
  returns `Nat.pair x y`.  Built from arithmetic primitives;
  every ingredient (`+`, `*`, `min`, `max`, `isqrt`) is
  expressible via `bsum`/`bprod` and `sub`.  Correctness:
  `(ERMor1.natPair).interp ![x, y] = Nat.pair x y`.
* `ERMor1.natUnpairFst : ERMor1 1` and `ERMor1.natUnpairSnd :
  ERMor1 1`: the components of `Nat.unpair`.
* `ERMor1.btlEncode : ERMor1 1`: the ER simulation of
  `BTL.encode`.  Recursive on the input via tree-fold-on-code
  (since BTL is itself encoded as a ℕ).  Correctness:
  `(ERMor1.btlEncode).interp ![BTL.encode t] = BTL.encode t`.
* `ERMor1.btlDecodeFold (baseLeaf stepNode : ERMor1 (k+1)) :
  ERMor1 (k+1)`: the ER simulation of `BTL.fold baseLeaf
  stepNode (BTL.decode (ctx 0))`, closing the loop for
  `foldBTNat` back-translation.  Built using `Nat.treeFoldOnCode`
  packaged as an `ERMor1` term (the same Layer-1 function that
  `Utilities/SzudzikSeq.lean` already provides).

Phase 4g.2's preserved Layer-1 work (`Nat.seqPack`, `Nat.seqAt`,
`Nat.treeFoldOnCode`, `Nat.mutuTreeFoldOnCode`,
`Nat.tupleRecN`) lives in `GebLean/Utilities/SzudzikSeq.lean`
and provides the underlying ℕ-level functions.  The new work is
*packaging these as ER-derived `ERMor1` terms* with
`@[simp]`-marked correctness theorems.  The Phase 4g.2
obstruction (Szudzik-polynomial barrier when packaging at
`TreeERMor1` depth 1) does not apply to the unrestricted
`ERMor1`: full composition and unbounded `bsum`/`bprod` make
the ER analogues straightforward.

### Back-translation strategy

`NatBTMor1.toER` is defined by structural recursion on
`NatBTMor1 (n, 0) σ` terms.  The `.nat` cases:

* `zero`/`succ`/`natProj`/`sub`/`compNat` (with `gBT` empty,
  forced by `nm'.2 = 0` for the nested arity)/`bsum`/`bprod`:
  recurse trivially to ER constructors.
* `foldBTNat baseLeaf stepNode tree`: recurse on `baseLeaf`,
  `stepNode`, and `tree.toER_bt` (the encoded `BTL.encode`
  representation), then apply `ERMor1.btlDecodeFold` to wrap
  them.
* `encodeBT t`: recurse on `t` via `t.toER_bt`, returning the
  encoded ℕ representation directly.

The `.bt` cases (sub-terms of `foldBTNat`/`encodeBT`):

* `leafBT label`: returns `2 * label.toER` (matching
  `BTL.encode (BTL.leaf label_value) = 2 * label_value`).
* `nodeBT l r`: returns `2 * Nat.pair (l.toER_bt) (r.toER_bt)
  + 1`, with `Nat.pair` realized via `ERMor1.natPair`.
* `btProj`: impossible (range is `Fin 0`).
* `compBT`: similar to `compNat`, with empty `gBT`.
* `foldBTBT`: by inspection, has step at arity `(n, 2)` —
  excluded from `LawvereNatBT0Cat` morphisms because its
  step-arity is non-zero; cannot occur in `(n_1, 0) ⟶ (n_2, 0)`
  morphisms via direct sub-term occurrence.  Implementer
  verifies this is genuinely impossible or handles it via
  an absurd case.
* `decodeBT k`: returns `k.toER` (since `BTL.encode (BTL.decode
  k) = k` by round-trip).

The correctness theorem says: for every term `t` and every
context `(ctxN, Fin.elim0)`,

```
(t.toER).interp ctxN = t.interp ctxN Fin.elim0  (.nat case)
(t.toER_bt).interp ctxN = (t.interp ctxN Fin.elim0).encode  (.bt)
```

By induction on `t`, using the `@[simp]`-marked correctness
theorems for the ER-derived Szudzik primitives.

### Transport of Phase 4f results

Given the equivalence, every categorical property of `LawvereER`
transports: if a statement of the form "no morphism in `LawvereERCat`
computes function `f`" holds on the `LawvereER` side (Phase 4f.1
with Ackermann, Phase 4f.2 with tetration), the same statement holds
in `LawvereNatBT` for the evident analogue `f` composed with
component encoding / decoding at the domain / codomain.

## Build stages

### Stage α: base theory

Deliverables:

* `LawvereNatBT.lean` with term type and structural lemmas.
* `LawvereNatBTQuot.lean` with quotient, category structure,
  `HasChosenFiniteProducts`.
* `LawvereNatBTInterp.lean` with interpretation functor and
  faithfulness.
* Test module `GebLeanTests/LawvereNatBT.lean` with type-check
  examples and `#guard` computations.

### Stage β: three-stage equivalence with LawvereER

Deliverables:

* `LawvereNatBT0.lean` (Stage 1's subcategory; already complete
  as of session ending commit `4f806f6d`): `isNatBT0` predicate,
  `LawvereNatBT0Cat` `FullSubcategory`, restricted
  `HasChosenFiniteProducts`.
* `Utilities/ERTreeArith.lean`: ER-derived Szudzik primitives
  (`natPair`, `natUnpair`, `btlEncode`, `btlDecode`,
  `foldBTLOnCode`) packaging `Utilities/SzudzikSeq.lean`'s
  Layer-1 work as `ERMor1` terms with correctness theorems.
* `LawvereNatBTBackTrans.lean`: `NatBTMor1.toER` and
  `NatBTMor1.toER_bt`, with extensional-correctness theorems.
* `LawvereNatBTPure.lean` (Stage 3): `LawvereNatBTPureCat` whose
  hom-sets are 1-1 with `ERMorNQuo`, plus the on-the-nose
  iso `LawvereERCat ≅ LawvereNatBTPureCat`.
* `LawvereNatBTEquiv.lean`: assembles Stage 1 (essential
  surjectivity of `natBT0Inclusion` via Szudzik on objects),
  Stage 2 (back-translation equivalence
  `LawvereNatBTPureCat ≃ LawvereNatBT0Cat`), and the
  composition into `natBTEquivalence : LawvereERCat ≌
  LawvereNatBTCat`.
* `LawvereNatBTTransport.lean`: transport of Phase 4f.1
  Ackermann non-fullness and Phase 4f.2 tetration
  non-elementarity across the equivalence.
* Test modules exercising:
  * Each ER-derived Szudzik primitive against its ℕ-level
    counterpart.
  * The `NatBTMor1.toER` back-translation on representative
    terms involving `encodeBT`/`foldBTNat`/etc.
  * The three-stage composition typechecks and gives the
    expected functor types.
  * Transport regressions (Ackermann/tetration-non-fullness).

### Stage γ: lex completion and subtypes

Deliverables:

* `LawvereNatBTLex.lean` with decidable subobjects, finite limits,
  `HasChosenFiniteProducts`, `HasChosenEqualizers`,
  `HasChosenFiniteLimits`.
* `LawvereNatBTSubtypes.lean` with unlabeled BT and finite-alphabet
  BT subtypes; the faithful embedding
  `LawvereTreeER ↪ LawvereNatBT`.
* Test modules for each.

## Testing plan

Each stage contributes test files exercising:

* Type-check examples for each new constructor / functor / term.
* `#guard` interpretation computations on specific small inputs.
* `example` type-checks confirming the stated functorial / equivalence
  structure.
* Transport regressions: Ackermann non-representability on
  `LawvereNatBT` as a direct consequence of `LawvereER`
  non-fullness.

## Completion criteria

The sub-project completes when:

1. Every new module builds cleanly: zero warnings, zero `sorry`, zero
   `admit`.
2. `LawvereNatBT` base theory is defined with finite-product
   structure.
3. The equivalence `LawvereER ≃ LawvereNatBT` is formally proved:
   full-faithfulness of the inclusion and essential surjectivity.
4. Phase 4f results (Ackermann non-fullness, tetration
   non-elementary) transport to `LawvereNatBT` with explicit
   theorems.
5. `LawvereNatBTLex` supports unlabeled and finite-alphabet
   subtypes as specific decidable subobjects.
6. `LawvereTreeER ↪ LawvereNatBT` faithful embedding is proved.
7. All tests pass.
8. Workstream tracker updated to reflect the new sub-project
   structure.

## Literature references

* Leivant, D. "Ramified recurrence and computational complexity III:
  Higher type recurrence and elementary complexity." *Annals of Pure
  and Applied Logic* 96 (1999), 209–229.  Establishes `RMRec^ω = E₃`
  for higher-order ramified recurrence.  Table 1 contrasts first-
  order (poly-time) with higher-order (elementary).
* Bellantoni, S., Cook, S. "A new recursion-theoretic
  characterization of poly-time." 1992.  First-order polyadic
  ramified recurrence equals polynomial time.
* Leivant, D. "Ramified recurrence and computational complexity I:
  Word recurrence and poly-time." 1994.
* Beckmann, A., Weiermann, A. "Characterizing the elementary
  recursive functions by a fragment of Gödel's T." *Archive for
  Mathematical Logic* 39 (2000), 475–491.  The `T*` fragment of
  Gödel's T with ground-`N`-applied recursors captures E₃.
* Meyer, A., Ritchie, D. "The complexity of loop programs." *Proc.
  ACM 22nd National Conference* (1967).  LOOP-depth-k programs
  equal E_{k+1}.
* Szudzik, M. "An elegant pairing function." Source for the
  bijection interpreting `encodeBT` / `decodeBT`.

## Open questions and risks

### Labeled BT as new inductive vs. polynomial-functor parameterization

Two implementation routes for labeled BT: a direct inductive
definition with `leaf : ℕ → BT` and `node : BT → BT → BT`, or reuse
of the polynomial-functor machinery in `GebLean/LawvereBT.lean` with
ℕ in place of `PUnit` at the leaf fiber.  Both are viable.  The
choice is left to the Stage-α implementer; the polynomial-functor
route maximizes code reuse, the direct-inductive route maximizes
readability.

### Signature of `foldBT` at the Lawvere-theory level

Lawvere theories do not natively support polymorphic result types;
`foldBT` at different result sorts is presented as two generators
(one for ℕ result, one for BT result) or a single generator with a
sort parameter.  The sort-parameter route unifies the signature at
a minor cost in type-inference clarity.  Resolved during Stage α.

### Paramorphism risk

The design commits to deriving paramorphism from catamorphism plus
pairing.  The argument is straightforward given finite products.
If a specific E₃ operation on labeled trees proves genuinely
inexpressible via this derivation, paramorphism can be added as a
primitive generator without disrupting the surrounding framework.
This risk is flagged but not expected to materialize.

### Transport of Phase 4g.1's `LawvereTreeER`

The faithful embedding `LawvereTreeER ↪ LawvereNatBT` is natural,
but its exact realization as a decidable-subobject restriction
("every leaf label equals 0") requires verifying that the
resulting sub-theory's morphism set corresponds exactly to
`LawvereTreeER`'s.  This verification is part of Stage γ.

### Exact shape of `NatBTMorQuo`'s quotient on the equational theory

The equational theory includes the round-trip equations
`encodeBT ∘ decodeBT = 1_ℕ` and `decodeBT ∘ encodeBT = 1_BT`, plus
the usual interaction laws between the structural generators and the
bridges.  An explicit enumeration of the defining equations is part
of Stage α, informed by the interpretation.
