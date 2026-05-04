# Copresheaves vs Presheaves on Twisted-Arrow Categories

## Overview

This document analyzes whether paranatural transformations between
arena-based profunctors can be characterized as natural transformations
between **copresheaves** on the twisted-arrow category, in addition to
the existing characterization via **presheaves**. The answer is that
copresheaf natural transformations correspond to a **proper subset** of
paranaturals -- those whose formula is independent of the "assignment"
morphism.

## Background

### Arena-based profunctors

An arena-based profunctor is given by an arena
`(ppos, pcontra, pcovar)` and interpreted as:

```text
InterpTypeProAr ar x y =
  (i : ppos ** (x -> pcontra i, pcovar i -> y))
```

### TypeDiNTar formula

A `TypeDiNTar` between arenas `p` and `q` consists of:

- `onpos : (i : ppos) -> (pcovar i -> pcontra i) -> qpos`
- `dcont : (i : ppos) -> (asn : pcovar i -> pcontra i) ->
  pcontra i -> qcontra (onpos i asn)`
- `dcov : (i : ppos) -> (asn : pcovar i -> pcontra i) ->
  qcovar (onpos i asn) -> pcovar i`

All three components depend on an **assignment**
`asn : pcovar i -> pcontra i`, which in the presheaf setting is
computed from the element and the twisted-arrow morphism.

### Twisted-arrow category

`Tw(C)` has:

- **Objects**: morphisms `m : x -> y` in `C`
- **Morphisms** from `(m : x -> y)` to `(n : a -> b)`:
  pairs `(s : a -> x, t : y -> b)` with `t . m . s = n`

### Key isomorphism

`Tw(C)` is isomorphic to `Tw(C^op)` (swapping source/target of objects,
swapping the two morphism components). However, `Tw(C)` is **not**
isomorphic to `Tw(C^op)^op`, and `Tw(C)^op` is **not** isomorphic to
`Tw(C^op)`.

## Existing results

The codebase proves two equivalences between paranaturals and presheaf
natural transformations:

1. **`TypeDiArAsPreshfNatTrans`** etc. -- presheaves on `Tw(Type)`
2. **`TypeDiArAsPreshfOpNatTrans`** etc. -- presheaves on `Tw(Type^op)`

Because `Tw(Type) ≅ Tw(Type^op)`, these are the **same equivalence**
viewed through the isomorphism, not two independent results. Presheaves
on `Tw(Type)` and presheaves on `Tw(Type^op)` are equivalent categories.

By the same isomorphism, copresheaves on `Tw(Type)` and copresheaves on
`Tw(Type^op)` are also equivalent. But since `Tw(C)^op` is different
from `Tw(C^op)`, presheaves and copresheaves on `Tw(Type)` are
genuinely different.

## Why the presheaf proof works

The presheaf embedding **flips** the profunctor arguments:

```text
TwArrPreshfEmbedProf f x y mxy = f y x
```

At twisted-arrow object `(m : x -> y)`, an element of `p(y, x)` is:

```text
(i ** (dcont : y -> pcontra i, dcov : pcovar i -> x))
```

The completeness proof (`TypeDiArFromPreshfNatTransComplete`) evaluates
presheaf naturality at:

```text
msa = dcov : pcovar i -> x
mbt = dcont : x -> pcontra i
```

This works because:

- `msa : s -> a` points **into** `x` -- same direction as `dcov`
- `mbt : b -> t` points **out of** `x` -- same direction as `dcont`

The element components **align with** the Tw-morphism parameters,
allowing the proof to recover any element from the identity element
`(pi ** (id, id))` via a single naturality square.

The assignment `asn = dcont . m . dcov : pcovar i -> pcontra i`
is naturally computable because the three maps compose:
`pcovar i -> x -> y -> pcontra i`.

## Why copresheaves are different

The copresheaf embedding does **not** flip:

```text
TwArrCoprEmbedProf p x y mxy = p x y
```

At twisted-arrow object `(m : x -> y)`, an element of `p(x, y)` is:

```text
(i ** (f : x -> pcontra i, g : pcovar i -> y))
```

### Direction mismatch

The copresheaf naturality parameters are:

- `mas : a -> s` -- points **into** `s`
- `mtb : t -> b` -- points **out of** `t`

But the element components point the **opposite** way:

- `f : x -> pcontra i` -- points **out of** `x`
- `g : pcovar i -> y` -- points **into** `y`

You cannot plug `f` or `g` into `mas` or `mtb`. The completeness
proof strategy used for presheaves does not apply.

### No natural assignment

To form `asn : pcovar i -> pcontra i`, you would need to compose
through `f`, some connecting morphism, and `g`. But:

- `g : pcovar i -> y` and `f : x -> pcontra i`
- Composing requires `y -> x`, but only `m : x -> y` is available

There is no canonical way to compute `asn` from copresheaf data.

## What copresheaf NTs correspond to

### Forward direction (asn-independent formula to copresheaf NT)

For a `TypeDiNTar` whose components are **independent of `asn`**:

```text
onpos(i)           -- no asn parameter
dcont(i) : pcontra i -> qcontra (onpos i)
dcov(i)  : qcovar (onpos i) -> pcovar i
```

The `m`-independent formula:

```text
gamma x y m (i ** (f, g)) = (onpos i ** (dcont i . f, g . dcov i))
```

satisfies copresheaf naturality (the proof is `Refl`, just as in the
presheaf case). The morphism `m` is unused.

### Backward direction (copresheaf NT to TypeDiNTar)

The existing extraction `TwArrCoprEmbeddingNTtoProfParaNT` evaluates
at `(a, a, id)`:

```text
gamma a a id : p a a -> q a a
```

This gives a `ProfDiNT`, which for arena-based profunctors yields a
`TypeDiNTar` by further evaluating at identity elements.

### Completeness fails for asn-dependent formulas

A paranatural whose formula genuinely depends on `asn` -- for example,
one that selects different output positions depending on
`dcont . m . dcov` -- cannot be expressed as a copresheaf NT. The
copresheaf embedding provides no way to compute `asn` from its data,
so there is no copresheaf NT whose diagonal restriction reproduces such
a paranatural.

## Summary

**Presheaf NTs on Tw(Type)**:

- Embedding: `f y x` (flip)
- Element components match Tw-morphism parameter directions
- Assignment `asn` computable: `dcont . m . dcov`
- Corresponds to: all paranaturals
- Completeness: proved (`TypeDiArFromPreshfNatTransComplete`)
- Naturality proof: `Refl`

**Copresheaf NTs on Tw(Type)**:

- Embedding: `p x y` (no flip)
- Element components oppose Tw-morphism parameter directions
- Assignment `asn` not computable from available data
- Corresponds to: proper subset (asn-independent paranaturals)
- Completeness: fails in general
- Naturality proof: `Refl` (for asn-independent formulas)

The two presheaf results (`TwArrPreshf` and `TwArrPreshfOp`) are
the same equivalence via `Tw(C) ≅ Tw(C^op)`. Copresheaf NTs are a
genuinely different and strictly smaller class.
