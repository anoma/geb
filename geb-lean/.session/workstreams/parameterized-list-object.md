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

- [ ] PBTO -> PSTO: enriched-carrier components
- [ ] PBTO -> PSTO: projection lemma
- [ ] PBTO -> PSTO: main instance (`HasPBTO -> HasPSTO`)
- [ ] Investigate PSTO -> PBTO direction

### Phase 3: PLO and PLTO

- [ ] Define `cfpLiftElemRec` helper in `PLO.lean`
- [ ] Define `IsPLO B L` class
- [ ] Define `HasPLO B`, `IsPLTO T`, `HasPLTO`
- [ ] Show PLO(1) corresponds to PNNO

### Phase 4: PSTO <-> PLTO

- [ ] Define `rev` using PSO elimination
- [ ] Show PSTO -> PLTO (via reversal)
- [ ] Show PLTO -> PSTO (via reversal)

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

### PSTO <-> PLTO strategy

Snoclist and cons-list are related by reversal.  For
snoclist-of-trees / list-of-trees (B = L), reversal operates
recursively at every level, since elements are themselves
trees.

The `rev` operation can be defined using the PSO (or PLO)
elimination, requiring no additional assumptions.
