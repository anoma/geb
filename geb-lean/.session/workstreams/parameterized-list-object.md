# Workstream: Parameterized List Objects (PSO/PLO/PSTO/PLTO)

## Status

Active

## Context

Define parameterized snoclist objects (PSOs) and cons-list
objects (PLOs), their self-referential variants (PSTO/PLTO),
and establish the relationship with PBTOs.

A PSO for element type B is the parameterized initial algebra
of X -> 1 + X x B (left fold / snoclist).  A PLO is the
parameterized initial algebra of X -> 1 + B x X (right fold /
cons-list).

The correspondence with binary trees uses left-associative
structure: `branch(l, b) = snoc(l, b)`, making PSTO the
natural intermediary for PBTO conversions.  PLTO is then
obtained from PSTO by reversal.

Uses the Is/Has factoring pattern: `IsPSO B L` states the
universal property; `HasPSO B` bundles an object with it.
`IsPSTO T = IsPSO T T`; `IsPLTO T = IsPLO T T`.

See `docs/parameterized-list-object.md` for the mathematical
background and
`docs/superpowers/plans/2026-04-06-parameterized-list-object.md`
for the implementation plan.

## Tasks

### Phase 1: PSO and PSTO

- [x] Define `cfpLiftRecElem` helper in `PSO.lean`
- [x] Define `IsPSO B L` class
- [x] Define `HasPSO B`, `IsPSTO T`, `HasPSTO`
- [x] Show PSO(1) corresponds to PNNO

### Phase 2: PBTO <-> PSTO

- [x] PBTO -> PSTO: enriched-carrier components
- [x] PBTO -> PSTO: projection lemma
- [x] PBTO -> PSTO: main instance (`HasPBTO -> HasPSTO`)
- [ ] Investigate PSTO -> PBTO direction

### Phase 3: PLO and PLTO

- [x] Define `cfpLiftElemRec` helper in `PLO.lean`
- [x] Define `IsPLO B L` class
- [x] Define `HasPLO B`, `IsPLTO T`, `HasPLTO`

### Phase 4: PSTO <-> PLTO

- [x] Show PSTO -> PLTO (via argument swap)
- [x] Show PLTO -> PSTO (via argument swap)
- [x] `HasPSTO.toHasPLTO`, `HasPLTO.toHasPSTO`

### Phase 4.5: Paramorphisms

- [x] PLO paramorphism (carrier, base, step, elimination)
- [x] PLO paramorphism base equation (`ploParaElim_nil`)
- [x] PLO paramorphism step equation (`ploParaElim_cons`)
- [x] PLO paramorphism uniqueness (`ploParaElim_uniq`)
- [x] PSO paramorphism (carrier, base, step, elimination)
- [x] PSO paramorphism base equation (`psoParaElim_nil`)
- [x] PSO paramorphism step equation (`psoParaElim_snoc`)
- [x] PSO paramorphism uniqueness (`psoParaElim_uniq`)

### Phase 5: Register and test

- [x] Register modules in root imports, full build

### Phase 6: PSTO -> PBTO

- [x] Investigate direct construction approaches
- [x] Document findings in `GebLean/PSTOtoPBTO.lean`

## Notes

### PBTO -> PSTO strategy

The construction uses the PBTO catamorphism on enriched carrier
`T x X`.  The base morphism maps `a` to `(leaf, f(a))`.  The
step morphism maps `((t1, x1), (t2, x2))` to
`(branch(t1, t2), g(x1, t2))`: `x1` is the recursive result
on the left subtree (accumulated snoclist), and `t2` is the
right subtree (latest element, passed as data).

Uniqueness: given any `psi` satisfying PSO equations, the pair
`(cfpSnd A T, psi)` satisfies the PBTO catamorphism equations
on `T x X`, so by PBTO uniqueness it equals the enriched
catamorphism.

### PSTO -> PBTO investigation

The PSO fold recurses only on the left subtree (the accumulated
snoclist), passing the right subtree (the latest element) as
data.  To simulate the PBTO catamorphism, we also need the
recursive result on the right subtree.

The PSO paramorphism (now fully proved with step equation and
uniqueness) gives the step function access to:
`(a : A, l : T, b : T, phi(a, l) : X)`.

Both `l` and `b` are of type `T` (since B = T in PSTO). The
paramorphism provides `phi(a, l)` (recursive result on tail)
but NOT `phi(a, b)` (recursive result on element).

The question is whether the B = T identification provides
enough structure to derive the PBTO catamorphism. The Idris
code at `.claude/docs/TreeCalculus.idr` shows the mutual
recursion pattern:

```text
f(nil) = nil
f(snoc(rest, elem)) = snoc(f(rest), f(elem))
```

This recurses on both `rest` and `elem`, which Idris accepts
because both are strict sub-expressions and both have type T.
The recursion principle this uses IS the PBTO catamorphism.
The question is whether it can be derived from the PSO fold.

The fixed-point equation: if we set
`h(x, b) = g(x, PSO.elim z h (a, b))`, then
`psi = PSO.elim z h` satisfies the PBTO equations.
This requires finding `h` such that `h = Phi(h)`.

All five approaches attempted in `GebLean/PSTOtoPBTO.lean`
fail for the same structural reason: the PSO/PSTO fold
processes a snoclist by recursing on the accumulated
prefix and passing each element as raw data.  The PBTO
catamorphism requires recursion into both components.

1. Direct enriched carrier `T x X`: cannot fill the
   second argument of `g` (needs recursive result on
   the element, which is unavailable).
2. PSO paramorphism: provides `(a, l, b, phi(a,l))` but
   not `phi(a, b)`.  Same structural gap.
3. Fixed-point equation: self-referential definition
   rejected by Lean (no termination argument in the
   abstract categorical setting).
4. Double PSO fold (nested folds): inner fold faces the
   same problem recursively ad infinitum.
5. Product carrier `X x X`: no choice of second
   component resolves the gap.

A direct PSTO -> PBTO construction likely requires
additional structure (internal fixed-point operator,
parameterized NNO, or exponential objects).
