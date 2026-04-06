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
- [ ] Show PLO(1) corresponds to PNNO

### Phase 4: PSTO <-> PLTO

- [x] Show PSTO -> PLTO (via argument swap)
- [x] Show PLTO -> PSTO (via argument swap)
- [x] `HasPSTO.toHasPLTO`, `HasPLTO.toHasPSTO`

### Phase 4.5: Paramorphisms

- [x] PLO paramorphism: carrier, base, step, elimination
- [x] PLO paramorphism base equation (`ploParaElim_nil`)
- [ ] PLO paramorphism step equation (`ploParaElim_cons`)
- [ ] PLO paramorphism uniqueness
- [x] PSO paramorphism: carrier, base, step, elimination
- [x] PSO paramorphism base equation (`psoParaElim_nil`)
- [ ] PSO paramorphism step equation (`psoParaElim_snoc`)
- [ ] PSO paramorphism uniqueness

### Phase 5: Register and test

- [ ] Register modules in root imports, full build

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

### PSTO -> PBTO approaches

The PSO fold recurses only on the left subtree (the accumulated
snoclist), passing the right subtree (the latest element) as
data.  To simulate the PBTO catamorphism, we also need the
recursive result on the right subtree.

Approaches (in priority order):

1. Direct enriched carrier using T itself as a stack.
   Since T is a snoclist of T's, use carrier `X x T`
   where the T component accumulates pending right
   subtrees.  Process the accumulated stack with a
   second PSO fold.  Try this first.
2. Bauer's mutual-recursion trick
   (<https://cs.stackexchange.com/a/144184>): use the
   parameter as a "slice" to encode mutual recursion
   as a single parameterized fold.
3. Via PNNO: PSTO implies PSO(1) implies PNNO; use
   PNNO iteration to process the right subtree.
   Existing `iterNat` infrastructure may help.

### PLO/PSO paramorphisms

The paramorphisms follow the same pattern as the PBTO
paramorphism in TreeLogic.lean.  The carrier is
`A x (L x X)`, threading the parameter, the current
raw list, and the recursive result.

For PLO: the step function `g` sees
`(a, b, l, phi(a,l))` where `b` is the element and
`l` is the raw tail.  The carrier step takes
`(b, (a, (l, x)))` and produces
`(a, (cons(b,l), g(a,b,l,x)))`.

For PSO: the step function `g` sees
`(a, l, b, phi(a,l))` where `l` is the raw init and
`b` is the element.  The carrier step takes
`((a, (l, x)), b)` and produces
`(a, (snoc(l,b), g(a,l,b,x)))`.

The base equations follow by applying `elim_nil`,
then projecting out the X component via two
applications of `cfpLift_snd`.

The step equations and uniqueness proofs are deferred
as of 2026-04-06.

### PSTO <-> PLTO via argument swap

Since PSTO has `snoc : T x T -> T` and PLTO has
`cons : T x T -> T` (same object for both components),
the conversion uses `cons = cfpSwap T T >> snoc` (and
vice versa).  The elimination is converted by swapping
the step morphism's argument order:
PLO `elim f g` = PSO `elim f (cfpSwap X T >> g)`.

Proving the step equations requires the swap lemmas
`swap_liftRecElem_swap` and `swap_liftElemRec_swap`,
which show that swapping input components, applying
cfpLiftRecElem/cfpLiftElemRec, then swapping the output,
yields the dual helper.  Uniqueness is derived by
precomposing with the involution `cfpMap id (cfpSwap T T)`
to cancel `cfpSwap T T >> cfpSwap T T = id`.
