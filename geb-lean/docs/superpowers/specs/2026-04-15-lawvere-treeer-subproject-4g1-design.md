# Lawvere Tree-ER Sub-project 4g.1: Core Lawvere Theory — Design

## Overview

This spec covers the first of five sub-projects in the Phase 4g tree-native
parallel development of the Lawvere theory of elementary recursive functions.
Sub-project 4g.1 establishes the base category `LawvereTreeERCat` as a
standalone Lawvere theory, with `HasChosenFiniteProducts`, a faithful
interpretation functor into `Type`, and a faithful inclusion functor into
`LawvereBTQuotCat`.

The deliverable is a clean tree-native ER syntax layer that is immediately
usable for downstream Tree-ER development, ships with multi-slot fold as the
mutumorphism primitive, and bootstraps the transport-via-faithfulness
pattern that will be used throughout Sub-projects 4g.2 through 4g.4.

## Relation to the larger workstream

See `.session/workstreams/lawvere-elementary-recursive.md` section "Phase
4g" for the full five-sub-project structure and motivation.  Summary:

* **4g.1 (this spec):** Tree-ER core Lawvere theory.
* **4g.2:** Base-level isomorphism `LawvereTreeERCat ≅ LawvereERCat` plus
  Gödel arithmetic on trees (Szudzik pair/unpair, successor, subtraction,
  bounded sum/product as derived tree terms).
* **4g.3:** Transport of Phase 4f results (Primrec' translation, tower
  bound, Ackermann non-fullness, tetration non-elementarity) to the tree
  side.
* **4g.4:** Tree-ERLexCat finite-limit completion parity and Lex-level
  isomorphism to `LawvereERLexCat`.
* **4g.5:** Central documentation file `docs/tree-er-correspondence.md`.

## Scope

### In scope

* `BTMor1.foldDepth` function and its basic lemmas.
* Subtype types `TreeERMor1_0`, `TreeERMor1_1`, `TreeERMor1` keyed by
  fold-nesting depth bound.
* Widening lifts `TreeERMor1_0 → TreeERMor1_1 → TreeERMor1`.
* Tier-aware smart constructors for `leaf`, `branch`, `proj`, `comp` at
  each tier, plus `fold` constructors at depth-1 and depth-2 tiers.
* Mutumorphism helpers `fold1` (single recursion) and `mutuFold` (full
  m-slot output) at depth-1 and depth-2 tiers.
* Tuple type `TreeERMorN n m` and its interpretation.
* Setoid `treeErMorNSetoid` by extensional equality of interpretations.
* Quotient `TreeERMorNQuo` with identity and composition.
* `Category` instance on `LawvereTreeERCat := ℕ`.
* `HasChosenFiniteProducts LawvereTreeERCat` instance (terminal, binary
  product, projections, pairing, product laws).
* Interpretation functor `treeErInterpFunctor : LawvereTreeERCat ⥤
  Type` and its `Faithful` instance.
* Faithful inclusion functor `treeErInclusion : LawvereTreeERCat ⥤
  LawvereBTQuotCat` and its `Faithful` instance.
* Sanity tests demonstrating smart-constructor computation, mutumorphism
  worked example, category-law reductions, and functor-faithfulness
  type-checks.

### Out of scope (deferred)

* Gödel arithmetic on trees (Szudzik pair/unpair, successor, subtraction,
  bounded sum/product as derived TreeERMor1 terms) — Sub-project 4g.2.
* Isomorphism of categories between `LawvereTreeERCat` and
  `LawvereERCat` — Sub-project 4g.2.
* Transport of non-fullness and tower-bound results — Sub-project 4g.3.
* Equalizers, finite-limit completion, Δ-embedding to lex — Sub-project
  4g.4.
* Central correspondence document — Sub-project 4g.5.

## Design decisions

### D1: New inductive `TreeMor1` with explicit `comp` constructor

`TreeMor1 n` is a new 5-constructor inductive type paralleling
`BTMor1 n` but with an explicit composition constructor:

```lean
inductive TreeMor1 : ℕ → Type
  | leaf {n} : TreeMor1 n
  | branch {n} (l r : TreeMor1 n) : TreeMor1 n
  | proj {n} (i : Fin n) : TreeMor1 n
  | comp {n k} (f : TreeMor1 k)
      (g : Fin k → TreeMor1 n) : TreeMor1 n
  | fold {n m} (f : Fin m → TreeMor1 n)
      (g : Fin m → TreeMor1 (m + m))
      (tree : TreeMor1 n)
      (j : Fin m) : TreeMor1 n
```

`TreeERMor1 n` is the depth-≤-2 subtype:

```lean
def TreeERMor1 (n : ℕ) : Type :=
  { t : TreeMor1 n // t.foldDepth ≤ 2 }
```

Rationale: `BTMor1` lacks a `comp` constructor; composition is
via `BTMor1.subst`, which increases fold-nesting depth additively
(depth can double through substitution into fold base-children).
This makes a `BTMor1` subtype NOT closed under composition.
Adding `comp` as an explicit constructor whose `foldDepth` is
`max(f.depth, sup g_i.depth)` restores compositional closure at
every depth tier.

The `comp` constructor mirrors `ERMor1.comp` exactly — the same
structural design that makes `LawvereERCat` compositionally closed.
Interpretation maps `comp` to `(f.interp ∘ g_vec.interp) ctx`.
A translation function `TreeMor1.toBTMor1 : TreeMor1 n → BTMor1 n`
maps `comp` to `BTMor1.subst`, connecting the two representations
for the faithful inclusion into `LawvereBTQuotCat`.

Alternative considered: subtype `{ t : BTMor1 n // t.foldDepth ≤ 2 }`.
Rejected because `BTMor1.subst` increases depth additively, so
the subtype is not closed under composition.

### D2: Two-tier subtype aliases `TreeERMor1_0` and `TreeERMor1_1`

Three subtypes of `TreeMor1 n`, one per depth tier:

```lean
def TreeERMor1_0 (n : ℕ) : Type :=
  { t : TreeMor1 n // t.foldDepth = 0 }
def TreeERMor1_1 (n : ℕ) : Type :=
  { t : TreeMor1 n // t.foldDepth ≤ 1 }
def TreeERMor1   (n : ℕ) : Type :=
  { t : TreeMor1 n // t.foldDepth ≤ 2 }
```

Widening lifts `TreeERMor1_0 n → TreeERMor1_1 n → TreeERMor1 n` are
trivial subtype weakenings.

Rationale: `fold` increases depth by one; `comp` takes the max, not
the sum.  The tier aliases let the smart-constructor API statically
track depth so clients never need to supply `by decide` proofs
manually.  Because `TreeMor1` is a standard Lean inductive (not a
`PolyFix`), `foldDepth` reduces by `rfl` on every constructor and
depth proofs are trivially decidable.

### D3: Minimal-core generators, derived primitives deferred

Tree-ER's generators are exactly `BTMor1`'s: `leaf`, `branch`, `proj`,
`fold`, `comp`.  No arithmetic primitives.  Arithmetic primitives
(`zero`, `succ`, `sub`, `bsum`, `bprod`, `pair`, `unpair`, etc.) are
derived as specific `TreeERMor1` terms in Sub-project 4g.2, once Szudzik
encoding infrastructure is in place.

Rationale: this matches the Leivant 1999 / Beckmann-Weiermann 2000
characterization of E_3 over free algebras and follows the
"minimal-core-and-layered-conveniences" programming-language principle
adopted for this workstream.

### D4: Faithful inclusion into `LawvereBTQuotCat`

A dedicated functor `treeErInclusion : LawvereTreeERCat ⥤
LawvereBTQuotCat` is built and proved faithful as part of 4g.1.  This
bootstraps the transport-via-faithfulness pattern for all subsequent
sub-projects: equations proven in `LawvereBTQuotCat` (using full BT
machinery, or even native Lean computation on BT) lift to
`LawvereTreeERCat` via faithfulness of the inclusion.

### D5: Multi-slot fold exposed as the mutumorphism primitive

`BTMor1.fold`'s `m` parameter is the number of mutually-recurring
functions folded simultaneously.  `TreeERMor1.fold`'s smart constructor
exposes this directly; additionally, convenience wrappers `fold1`
(single-recursion, `m = 1`) and `mutuFold` (all-slots-at-once, returning
a `TreeERMorN`) are provided.

Rationale: tree-native mutumorphism is immediately available at depth 1
and depth 2 with no additional infrastructure.  This asymmetry with ℕ-ER
(where mutumorphism requires Szudzik pairing, deferred to 4g.2) reflects
the structural strength of trees as a mutually-recursive data type.

## Module layout

### Library modules

1. `GebLean/LawvereTreeER.lean` (~250–350 lines)

   Contents:
   * `BTMor1.foldDepth : {n : ℕ} → BTMor1 n → ℕ` and basic lemmas.
   * `TreeERMor1_0`, `TreeERMor1_1`, `TreeERMor1` subtype aliases.
   * Widening lift functions.
   * Smart constructors at each tier for `leaf`, `branch`, `proj`,
     `comp`; `fold` at depth-1 and depth-2 tiers.
   * Convenience wrappers `fold1` and `mutuFold` at each tier.
   * `TreeERMor1.interp` and `@[simp]` computation lemmas.
   * `TreeERMorN n m := Fin m → TreeERMor1 n` and its interpretation,
     identity, composition.

2. `GebLean/LawvereTreeERQuot.lean` (~200–300 lines)

   Contents:
   * `treeErMorNSetoid n m : Setoid (TreeERMorN n m)` — extensional
     equality of interpretations over `Fin n → BT.{0}`.
   * `TreeERMorNQuo n m := Quotient (treeErMorNSetoid n m)`.
   * `TreeERMorNQuo.id`, `.comp`; category laws.
   * `LawvereTreeERCat := ℕ` (abbrev).
   * `CategoryStruct` and `Category` instances.
   * `HasChosenFiniteProducts LawvereTreeERCat` instance.

3. `GebLean/LawvereTreeERInterp.lean` (~80–120 lines)

   Contents:
   * `treeErInterpFunctor : LawvereTreeERCat ⥤ Type` with
     `obj n := Fin n → BT` and `map := TreeERMorNQuo.interp`.
   * `treeErInterpFunctor.Faithful` instance.
   * `treeErInclusion : LawvereTreeERCat ⥤ LawvereBTQuotCat` with
     `obj n := n` and `map` via subtype `.val` unwrap on each tuple
     component.
   * `treeErInclusion.Faithful` instance.

### Test modules

1. `GebLeanTests/LawvereTreeER.lean`

   Contents:
   * `#guard` tests verifying `TreeERMor1.interp` computes correctly
     for each smart constructor.
   * A worked mutumorphism example: simultaneous computation of tree
     size and tree depth via `mutuFold` at depth-1, with `#guard`s
     confirming the two output slots.
   * Compile-time depth-tier type-checks (e.g., `#check` a `leaf` at
     each of the three tiers).

2. `GebLeanTests/LawvereTreeERQuot.lean`

   Contents:
   * Category-law sanity on specific small morphisms.
   * `HasChosenFiniteProducts` universal-property sanity (fst ∘ pair,
     snd ∘ pair, uniqueness on nose for small examples).

3. `GebLeanTests/LawvereTreeERInterp.lean`

   Contents:
   * `example` type-checks confirming `treeErInterpFunctor.Faithful`
     and `treeErInclusion.Faithful` are available.
   * `#guard` on a small morphism showing `treeErInterpFunctor.map`
     reduces to the expected underlying `BTMorNQuo.interpU` form.

### Dependencies

Existing modules:

* `GebLean/LawvereBT.lean` — `BT`, `BTMor1`, `BTMor1.interpU`
* `GebLean/LawvereBTQuot.lean` — quotient pattern + category + finite
  products
* `GebLean/LawvereBTInterp.lean` — interpretation functor pattern
* `GebLean/Utilities/ComputableLimits.lean` — `HasChosenFiniteProducts`
  class and related machinery

No new external Mathlib dependencies.

## Representation

### `BTMor1.foldDepth`

Structural recursion computing the maximum nesting depth of `fold`
constructors in a `BTMor1` term:

```lean
def BTMor1.foldDepth : ∀ {n : ℕ}, BTMor1 n → ℕ
  | _, .leaf => 0
  | _, .proj _ => 0
  | _, .branch l r => max l.foldDepth r.foldDepth
  | _, .comp f g =>
      max f.foldDepth
        ((Finset.univ : Finset (Fin _)).sup
          (fun i => (g i).foldDepth))
  | _, .fold _ f g tree _ =>
      1 + max (max
        ((Finset.univ : Finset (Fin _)).sup
          (fun i => (f i).foldDepth))
        ((Finset.univ : Finset (Fin _)).sup
          (fun i => (g i).foldDepth)))
        tree.foldDepth
```

Basic lemmas:

* `BTMor1.foldDepth_leaf`, `_proj`, `_branch`, `_comp`, `_fold` —
  `@[simp]` reductions for each constructor.
* `BTMor1.foldDepth_decidable` — `foldDepth` is a computable ℕ-valued
  function; `t.foldDepth ≤ k` is `Decidable` by `Nat.decLe` on a
  concrete term.

### Tier aliases and widening lifts

```lean
def TreeERMor1_0 (n : ℕ) : Type := { t : BTMor1 n // t.foldDepth = 0 }
def TreeERMor1_1 (n : ℕ) : Type := { t : BTMor1 n // t.foldDepth ≤ 1 }
def TreeERMor1   (n : ℕ) : Type := { t : BTMor1 n // t.foldDepth ≤ 2 }

def TreeERMor1_0.toDepth1 {n} (t : TreeERMor1_0 n) : TreeERMor1_1 n :=
  ⟨t.val, by have := t.property; omega⟩

def TreeERMor1_1.toDepth2 {n} (t : TreeERMor1_1 n) : TreeERMor1 n :=
  ⟨t.val, by have := t.property; omega⟩
```

The exact proof tactic may shift during implementation, but `omega`
after extracting `t.property` is expected to discharge each case.

### Smart constructors at depth-0 tier

```lean
def TreeERMor1_0.leaf {n : ℕ} : TreeERMor1_0 n :=
  ⟨BTMor1.leaf, by simp [BTMor1.foldDepth]⟩

def TreeERMor1_0.branch {n : ℕ}
    (l r : TreeERMor1_0 n) : TreeERMor1_0 n :=
  ⟨BTMor1.branch l.val r.val,
   by simp [BTMor1.foldDepth, l.property, r.property]⟩

def TreeERMor1_0.proj {n : ℕ} (i : Fin n) : TreeERMor1_0 n :=
  ⟨BTMor1.proj i, by simp [BTMor1.foldDepth]⟩

def TreeERMor1_0.comp {n k : ℕ}
    (f : TreeERMor1_0 k) (g : Fin k → TreeERMor1_0 n) :
    TreeERMor1_0 n :=
  ⟨BTMor1.comp f.val (fun i => (g i).val),
   by simp [BTMor1.foldDepth, f.property];
      intro i; exact (g i).property⟩
```

Analogous smart constructors at the depth-1 and depth-2 tiers, with
their underlying `BTMor1` terms identical but depth proofs using `≤ 1`
or `≤ 2` respectively.

### Fold smart constructors

Fold increases depth by one, so it is available at depth-1 taking
depth-0 arguments, and at depth-2 taking depth-1 arguments:

```lean
def TreeERMor1_1.fold {n m : ℕ}
    (f : Fin m → TreeERMor1_0 n)
    (g : Fin m → TreeERMor1_0 (m + m))
    (tree : TreeERMor1_0 n)
    (j : Fin m) : TreeERMor1_1 n :=
  ⟨BTMor1.fold m (fun i => (f i).val) (fun i => (g i).val)
    tree.val j,
   by simp [BTMor1.foldDepth];
      -- Using f i, g i, tree having foldDepth = 0,
      -- the fold's foldDepth is 1 + max 0 0 = 1.
      ...⟩

def TreeERMor1.fold {n m : ℕ}
    (f : Fin m → TreeERMor1_1 n)
    (g : Fin m → TreeERMor1_1 (m + m))
    (tree : TreeERMor1_1 n)
    (j : Fin m) : TreeERMor1 n :=
  ⟨BTMor1.fold m (fun i => (f i).val) (fun i => (g i).val)
    tree.val j,
   by simp [BTMor1.foldDepth];
      -- Using foldDepth ≤ 1 on f, g, tree, the fold's
      -- foldDepth is ≤ 1 + 1 = 2.
      ...⟩
```

### Convenience: `fold1` and `mutuFold`

`fold1` wraps the `m = 1` case of `fold`:

```lean
def TreeERMor1_1.fold1 {n : ℕ}
    (base : TreeERMor1_0 n)
    (step : TreeERMor1_0 2)
    (tree : TreeERMor1_0 n) : TreeERMor1_1 n :=
  TreeERMor1_1.fold
    (f := fun _ => base)
    (g := fun _ => step)
    tree 0

def TreeERMor1.fold1 {n : ℕ}
    (base : TreeERMor1_1 n)
    (step : TreeERMor1_1 2)
    (tree : TreeERMor1_1 n) : TreeERMor1 n :=
  TreeERMor1.fold
    (f := fun _ => base)
    (g := fun _ => step)
    tree 0
```

`mutuFold` exposes the full m-slot output as a `TreeERMorN`:

```lean
def TreeERMor1_1.mutuFold {n m : ℕ}
    (f : Fin m → TreeERMor1_0 n)
    (g : Fin m → TreeERMor1_0 (m + m))
    (tree : TreeERMor1_0 n) : TreeERMorN_1 n m :=
  fun j => TreeERMor1_1.fold f g tree j

def TreeERMor1.mutuFold {n m : ℕ}
    (f : Fin m → TreeERMor1_1 n)
    (g : Fin m → TreeERMor1_1 (m + m))
    (tree : TreeERMor1_1 n) : TreeERMorN n m :=
  fun j => TreeERMor1.fold f g tree j
```

(`TreeERMorN_1 n m := Fin m → TreeERMor1_1 n` as the corresponding tuple
type at the depth-1 tier.)

## Interpretation

### `TreeERMor1.interp`

Since `TreeERMor1 n ⊂ BTMor1 n`, interpretation is inherited:

```lean
def TreeERMor1.interp {n : ℕ}
    (t : TreeERMor1 n) (ctx : Fin n → BT.{u}) : BT.{u} :=
  t.val.interpU ctx
```

Analogous definitions at the depth-0 and depth-1 tiers.  `@[simp]`
lemmas link each to the underlying `BTMor1.interpU`.

### `TreeERMorN` and tuple interpretation

```lean
def TreeERMorN (n m : ℕ) : Type := Fin m → TreeERMor1 n

def TreeERMorN.interp {n m : ℕ}
    (f : TreeERMorN n m) (ctx : Fin n → BT.{u}) : Fin m → BT.{u} :=
  fun i => (f i).interp ctx

def TreeERMorN.id (n : ℕ) : TreeERMorN n n :=
  fun i => TreeERMor1.proj i

def TreeERMorN.comp {n m k : ℕ}
    (f : TreeERMorN n m) (g : TreeERMorN m k) : TreeERMorN n k :=
  fun i => TreeERMor1.comp (g i) f
```

Tuple-level `@[simp]` lemmas for `interp_id` and `interp_comp`.

## Quotient and category structure

### Setoid and quotient

```lean
def treeErMorNSetoid (n m : ℕ) : Setoid (TreeERMorN n m) where
  r f g := ∀ ctx : Fin n → BT.{0}, f.interp ctx = g.interp ctx
  iseqv := ⟨fun _ _ => rfl,
            fun h ctx => (h ctx).symm,
            fun h₁ h₂ ctx => (h₁ ctx).trans (h₂ ctx)⟩

def TreeERMorNQuo (n m : ℕ) : Type :=
  Quotient (treeErMorNSetoid n m)
```

Identity and composition lift to the quotient:

```lean
def TreeERMorNQuo.id (n : ℕ) : TreeERMorNQuo n n :=
  Quotient.mk _ (TreeERMorN.id n)

def TreeERMorNQuo.comp {n m k : ℕ}
    (f : TreeERMorNQuo n m) (g : TreeERMorNQuo m k) :
    TreeERMorNQuo n k :=
  Quotient.lift₂
    (fun f' g' => Quotient.mk _ (TreeERMorN.comp f' g'))
    (proof of well-definedness)
    f g
```

### Category instance

```lean
@[reducible] def LawvereTreeERCat : Type := ℕ

instance : CategoryStruct LawvereTreeERCat where
  Hom := TreeERMorNQuo
  id := TreeERMorNQuo.id
  comp := TreeERMorNQuo.comp

instance : Category LawvereTreeERCat where
  id_comp := (proof via extensional interp equality)
  comp_id := (proof via extensional interp equality)
  assoc := (proof via extensional interp equality)
```

All three laws reduce to `rfl` on extensional interpretation equalities.
Follow the pattern established in `GebLean/LawvereERQuot.lean` and
`GebLean/LawvereBTQuot.lean`.

### Chosen finite products

Mirror the `LawvereBTQuotCat` pattern.  Terminal object is `0`; binary
product is `n ⊗ m := n + m`; projections and pairing are built from
`TreeERMor1.proj` (which has depth 0 so lives in every tier).

```lean
def lawvereTreeERTerminal : ChosenTerminal LawvereTreeERCat := ...
def lawvereTreeERProduct (n m : LawvereTreeERCat) :
    ChosenBinaryProduct n m := ...
instance : HasChosenFiniteProducts LawvereTreeERCat := ...
```

Product laws (`fst ∘ pair = f`, `snd ∘ pair = g`, `pair fst snd = id`)
are proved by extensional interpretation equality.

## Interpretation functor

```lean
def TreeERMorNQuo.interp {n m : ℕ}
    (f : TreeERMorNQuo n m) :
    (Fin n → BT.{u}) → (Fin m → BT.{u}) :=
  Quotient.lift TreeERMorN.interp
    (fun _ _ h => funext h) f

def treeErInterpFunctor : LawvereTreeERCat ⥤ Type where
  obj n := Fin n → BT
  map := TreeERMorNQuo.interp
  map_id := (proof)
  map_comp := (proof)

instance : treeErInterpFunctor.Faithful where
  map_injective := (proof via Quotient.ind₂ and Quotient.sound)
```

## Faithful inclusion into `LawvereBTQuotCat`

```lean
def treeErInclusion : LawvereTreeERCat ⥤ LawvereBTQuotCat where
  obj n := n
  map := fun {n m} f =>
    Quotient.lift (fun (f' : TreeERMorN n m) =>
      Quotient.mk _ (fun i => (f' i).val))
      (proof of well-definedness on extensional equality)
      f
  map_id := (proof)
  map_comp := (proof)

instance : treeErInclusion.Faithful where
  map_injective := (proof)
```

**Why this matters for transport:** for morphisms `f g : Hom_{TreeER}(n, m)`,
proving `f = g` reduces to proving `treeErInclusion.map f = treeErInclusion.map g`
in `LawvereBTQuotCat` (by `map_injective` of the faithful functor).  This
means any equation provable on the BT side — using full BT machinery,
BT's category structure, BT's HasChosenFiniteProducts laws, or even
native Lean equalities on unwrapped `BTMor1` terms — lifts to
`LawvereTreeERCat` automatically.  Downstream sub-projects rely on this
pattern extensively.

## Testing plan

### `GebLeanTests/LawvereTreeER.lean`

* `#guard` that `TreeERMor1_0.leaf.interp (fun i => BT.leaf) = BT.leaf`.
* `#guard` that `TreeERMor1_0.branch` of two leaves interprets to the
  expected `BT.node BT.leaf BT.leaf`.
* `#guard` on `proj` at specific small arities.
* `#guard` on `comp` of a branch with two projections.
* Worked mutumorphism example: compute `treeSize` and `treeHeight`
  simultaneously via `mutuFold` at depth-1, `#guard` both slots on a
  specific small tree.
* `#check` that a `leaf` expression can be assigned to each of
  `TreeERMor1_0 n`, `TreeERMor1_1 n`, `TreeERMor1 n` via the widening
  lifts.

### `GebLeanTests/LawvereTreeERQuot.lean`

* `#check` that `Category LawvereTreeERCat` typeclass resolves.
* `#check` that `HasChosenFiniteProducts LawvereTreeERCat` resolves.
* `example` establishing `TreeERMorNQuo.id ∘ f = f` on a specific small
  `f`.
* `example` establishing `fst ∘ pair f g = f` for specific small `f, g`.

### `GebLeanTests/LawvereTreeERInterp.lean`

* `example : treeErInterpFunctor.Faithful := inferInstance`.
* `example : treeErInclusion.Faithful := inferInstance`.
* `#guard` on a specific morphism showing `treeErInterpFunctor.map f`
  reduces to the expected `BTMorNQuo.interpU (f.val)`-like form.

## Completion criteria

Sub-project 4g.1 is complete when:

1. All three library modules build cleanly, zero warnings, zero `sorry`,
   zero `admit`.
2. `LawvereTreeERCat : Type` has `Category` and `HasChosenFiniteProducts`
   instances.
3. `treeErInterpFunctor : LawvereTreeERCat ⥤ Type` is defined with a
   `Faithful` instance.
4. `treeErInclusion : LawvereTreeERCat ⥤ LawvereBTQuotCat` is defined
   with a `Faithful` instance.
5. Tier-aware smart constructors exist for `leaf`, `branch`, `proj`,
   `comp` at all three depth tiers.
6. `fold` smart constructors exist at depth-1 and depth-2 tiers.
7. `fold1` and `mutuFold` helpers exist at depth-1 and depth-2 tiers.
8. All tests pass; no `#guard` failures.
9. The workstream tracker is updated to mark 4g.1 complete.

## What's deferred to later sub-projects

* **4g.2:** Szudzik `pair` / `unpair` as `TreeERMor1` terms; derived
  arithmetic primitives (`zero`, `succ`, `sub`, `bsum`, `bprod`, `isqrt`);
  bidirectional translation functors between `LawvereERCat` and
  `LawvereTreeERCat`; proof of categorical isomorphism on the nose.
* **4g.3:** `ERMor1.toPrimrec'`-analog on tree-ER terms; tower bound
  transported; Ackermann non-fullness transported; tetration non-ER
  transported.  These are mostly corollaries of the 4g.2 isomorphism.
* **4g.4:** `TreeERBoolPred`, `TreeERBoolPredE` quotient, `TreeLexObj`,
  finite products and equalizers on `LawvereTreeERLexCat`, Δ-embedding,
  Lex-level isomorphism to `LawvereERLexCat`.
* **4g.5:** `docs/tree-er-correspondence.md` central reference document.

## Literature references

Each theorem in this sub-project will carry a one-line docstring citing
the relevant reference where applicable.  The full correspondence map
(including the theorems this sub-project builds on from the BT and ER
workstreams) will live in `docs/tree-er-correspondence.md` (Sub-project
4g.5).  Immediate references used in 4g.1:

* Leivant, D. "Ramified recurrence and computational complexity III."
  *APAL* 96 (1999): the depth-2 restriction characterizing E_3 over free
  algebras.
* Beckmann, A. & Weiermann, A. "Characterizing the elementary recursive
  functions by a fragment of Gödel's T."  *AML* 39 (2000): the
  syntactic Gödel's T fragment corresponding to depth-2 fold.

## Open questions

* **Universe polymorphism of the setoid:** `treeErMorNSetoid` as defined
  relates interpretations at `BT.{0}` specifically.  If a future need
  arises to relate universe-polymorphic interpretations, the setoid may
  need generalization.  No such need is anticipated in 4g.1 through
  4g.4.
* **Exact proof tactics for smart-constructor depth-well-definedness:**
  some `by simp [BTMor1.foldDepth, ...]` proofs in the smart constructors
  may need `omega` or specific inequality lemmas.  To be resolved during
  implementation; no structural impact on the design.
