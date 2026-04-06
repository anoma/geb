# Workstream: Tree PER Finite Limits

## Status

Active

## Context

Constructing finite limits in the category of partial equivalence
relations (PERs) on the binary tree type T.

## Completed

- Terminal PER (`terminalPERObj`): relation = constant leaf.
  All four fields proved (Boolean, symmetry, transitivity).
- Terminal morphism (`terminalPERPreMor`, `terminalPERMor`):
  map = identity, uses `boolAnd_const_leaf_right`.
- Terminal uniqueness (`terminalPERPreMor_unique`,
  `terminalPERMor_unique`): any two morphisms to terminal are
  equivalent.
- `terminalPERObj_isTerminal`: uses `Limits.IsTerminal.ofUniqueHom`.
- `treePER_hasTerminal`: `Limits.HasTerminal` instance.
- Product PER definition (`prodPERRel`), all axioms, projections,
  pairing, beta laws, eta/uniqueness law.
- `prodPERFst_comp_pair`, `prodPERSnd_comp_pair`: beta laws in
  the quotient category.
- `prodPER_pair_unique`: uniqueness of pairing in the quotient.
- `prodPERFan`, `prodPERFan_isLimit`: `BinaryFan` and `IsLimit`.
- `treePER_hasLimitPair`, `treePER_hasBinaryProducts`:
  `HasBinaryProducts` (parameterized by `hSep`, `hBD`).
- `boolAnd_comm`: unconditional commutativity of `boolAnd`,
  proved via `boolAnd_eq_elim` and `boolAnd_swap_eq_elim`
  showing both sides equal the same `p.elim` catamorphism.
- `boolAnd_fst_proj`: first-projection absorption
  `boolAnd(boolAnd(A, B), A) = boolAnd(A, B)`, proved via
  `boolAnd_swap_eq_elim` by factoring both sides through
  `cfpLift B A` and reducing to an elim_uniq argument.
  These simplifications removed the `IsSeparator` +
  `HasBoolDichotomy` hypotheses from both theorems.
- Equalizer PER definition (`eqPERRel`):
  `boolAnd(X.rel(x,y), boolAnd(eqCheck(x), eqCheck(y)))` where
  `eqCheck(x) = Y.rel(f(x), g(x))`.
- `eqPERRel_bool`, `eqPERRel_symm` (using `boolAnd_comm`,
  no separator/dichotomy assumption).
- `eqPERRel_quantTransitive`, `eqPERRel_eqTransitive`.
- `eqPERObj`: equalizer PER object assembly.
- `eqPERInclPreMor`, `eqPERIncl`: inclusion pre-morphism and
  quotient morphism from `eqPERObj` to `X`.
- `eqPER_equalizes`, `eqPER_equalizes_quot`: equalizing
  condition `incl ≫ f = incl ≫ g` in both pre-morphism
  equivalence and quotient equality.

## Tasks

- [ ] Equalizer lift pre-morphism (`eqPERLiftPreMor`): map = `m.map`,
  `map_rel` proof needs `boolAnd_assoc`, `boolAnd_idem`, and the
  equalizing condition to show
  `boolAnd(Z.rel, cfpMap m m ≫ eqPERRel) = Z.rel`.
  After reducing via `boolAnd_assoc` and `m.map_rel`, the remaining
  goal is `boolAnd(Z.rel, m ≫ eqCheck) = Z.rel`, which follows from
  the equalizing condition.  The equational form requires separator +
  dichotomy or a direct `boolAnd_implies_trans`-style argument.
- [ ] Equalizer lift quotient morphism.
- [ ] Equalizer factorization: `lift ≫ incl = m`.
- [ ] Equalizer uniqueness: if `k ≫ incl = m`, then `k = lift`.
- [ ] Fork and IsLimit assembly.
- [ ] `HasEqualizers` instance.
- [ ] `HasFiniteLimits` via
  `hasFiniteLimits_of_hasEqualizers_and_finite_products`.

## Notes

The `eqPERRel` definition uses `boolAnd(X.rel, boolAnd(eqCheck(fst),
eqCheck(snd)))` rather than `boolAnd(X.rel, Y.rel(f, g))` to achieve
equational symmetry.  The symmetry proof uses `boolAnd_comm_bool`
(commutativity for Boolean-valued arguments) to swap the two
`eqCheck` terms.

The `include hSep hBD in` directive is needed before theorems whose
types don't mention the separator/dichotomy but whose proofs use them,
since Lean 4 only auto-includes section variables that appear in the
type signature.

## `HasTreeEq LawvereBTQuotCat` construction

Status: not started, requires new infrastructure.

The `HasTreeEq` structure in `GebLean/TreePER.lean` asks for a morphism
`treeEq : cfpProd T T ⟶ T` satisfying Boolean-valued output, reflexivity,
symmetry, equational transitivity, and the four computation rules
(`ℓℓ`, `ℓβ`, `βℓ`, `ββ`).  The recursive `ββ` rule
`treeEq(β(a₁, a₂), β(b₁, b₂)) = boolAnd(treeEq(a₁, b₁), treeEq(a₂, b₂))`
is simultaneous (double) structural recursion on two trees.

The `TypePBTO.treeEqBT` construction for `Type u` uses a `BT.fold` with
carrier type `BT → BT` (function type), applied at the end to the second
argument.  This works in any cartesian closed category.  `LawvereBTQuotCat`
is cartesian monoidal only (its objects are the finite products `n : ℕ`
of the generator), so this approach does not transfer directly.

A single `BTMor1.fold` or `HasPBTO.elim` application cannot express
`treeEq`.  The step function `g : Fin m → BTMor1 (m + m)` only sees the
recursive results from the left and right children, not the original
parameter context.  Even with an enhanced variant that exposes the
context (e.g. a syntactic analogue of `btFoldEnhanced`), the recursive
results compare each sub-tree of the folded argument against the FULL
other argument, not against the corresponding sub-tree.  Multi-output
and state-tracking variants do not help because all recursive calls
receive the same parameter context.

Viable routes (all require new infrastructure):

- Build a constructive primitive-recursive completeness theorem for
  `LawvereBTQuotCat` (inverse of `interpU_primrec_of_ctx` in
  `LawvereBTPrimrec.lean`).  Every primitive recursive `BT × BT → BT`
  function would then lift to a `BTMor1 2` term, including the
  semantically-defined `TypePBTO.treeEqBT`.
- Simulate a Goedel encoding `BT ↔ Nat` within the Lawvere theory,
  implement natural-number equality as a `BTMor1`, and compose.  Nat
  equality on a unary encoding has the same double-recursion obstacle,
  so this likely reduces to the same problem.
- Add a primitive to `HasPBTO` or a new typeclass supporting double
  structural recursion directly (equivalent to exponentials or a
  case-analysis primitive combined with recursion).

The `HasTreeEq LawvereBTQuotCat` instance is a prerequisite for
downstream `LawvereBTPER`-specific results that depend on decidable
tree equality.  Work is blocked pending one of the routes above.

## Generic `treeEq` via bounded iteration (Phase 3a status)

A generic `treeEq : cfpProd p.T p.T ⟶ p.T` has been defined in
`GebLean/TreeLogic.lean` for any `HasPBTO C`, using a worklist-based
algorithm:

- State encoding: `branch(result, worklist)`.
- `compareStep` processes one worklist item: match (leaf, leaf) pops,
  mismatch sets result to `treeFalse`, expand (branch, branch) pushes
  children pairs.
- `treeEq := cfpLift initState (β ≫ treeSize) ≫ iterNat compareStep ≫
  treeLeftEndo ≫ isLeafEndo`.

The computation rules for `compareStep` are all proved
(`compareStep_leaf_wl`, `compareStep_match`, `compareStep_mismatch_left`,
`compareStep_mismatch_right`, `compareStep_expand`), as is the sanity
check `treeEq_ℓℓ`.

Proved in Phase 3a:

- `treeEq_bool : treeEq ≫ isLeafEndo = treeEq`.  One-liner via
  `Category.assoc` and `isLeafEndo_idem`.

Blocked in Phase 3a:

- `treeEq_refl : cfpLift (𝟙 p.T) (𝟙 p.T) ≫ treeEq =
  cfpTerminalFrom p.T ≫ p.ℓ`.

Obstacle analysis for `treeEq_refl`:

The natural strategy is `elim_uniq` on the morphism
`Φ := cfpLift (𝟙 p.T) (𝟙 p.T) ≫ treeEq`, showing it equals
`reflLeaf := p.elim p.ℓ (cfpTerminalFrom _ ≫ p.ℓ)` (the constant-leaf
morphism via `elim`).  By `elim_uniq` this reduces to two equations:

1. `p.ℓ ≫ Φ = p.ℓ` — immediate from `treeEq_ℓℓ`.
2. `p.β ≫ Φ = cfpMap Φ Φ ≫ (cfpTerminalFrom _ ≫ p.ℓ)`, which
   simplifies to `cfpLift p.β p.β ≫ treeEq =
   cfpTerminalFrom (cfpProd p.T p.T) ≫ p.ℓ`.

Equation (2) is "reflexivity on branches": `treeEq(branch(a,b),
branch(a,b)) = leaf` as a morphism equation.  Unfolding `treeEq` and
applying `compareStep_expand` once reduces the state to `(ℓ,
[(a,a), (b,b)])` with one fewer iteration, but the remaining
convergence requires reflexivity on the sub-pairs — the same
problem recursively.

The obstacle is that `treeEq`'s iteration count is bounded by
`treeSize`, and the correctness of this bound requires a tree-shape-
dependent invariant that cannot be verified by pointwise
computation rules alone.  Proving it would require:

- A general invariant lemma about `iterNat compareStep` converging
  from a "reflexive worklist" state, stated parametrically over
  `f : D ⟶ p.T` and with a suitable iteration count.
- Induction on the shape of `f` via `elim_uniq`, which in turn
  requires expressing the "converged state" as an output of a
  fold over `f`.

This machinery is a substantial standalone development.  An
alternative that would make `treeEq_refl` a direct `elim_uniq`
argument: define `treeEq` via a nested `p.elim` that takes the
recursive `treeEq` results as input at the branch case (the
double-recursion pattern described above for `LawvereBTQuotCat`).
This runs into the same obstacle that single-fold `elim` cannot
express double structural recursion without CCC/exponentials.

Next steps (to be decided):

- Attempt the full convergence invariant lemma for
  `iterNat compareStep` (estimated: a new sub-module worth of
  work).
- Or: restrict `HasTreeEq` instances to categories with additional
  structure (e.g. cartesian closed) where `treeEq` can be defined
  via a fold returning a function.
- Or: add `treeEq` to the axiomatic interface (`HasPBTO` or a
  sibling class), treating it as primitive in categories that lack
  CCC structure.

## `treeEq_ββ` obstacle analysis (Phase 3b, resolved)

Phase 3a established the iteration-infrastructure lemmas
`iterNat_cfpLift_succ`, `iterNat_plus`, and
`iterNat_cfpLift_fixed` (stability on fixed points).

The `compareStep` definition was changed so that mismatch
rules clear the worklist to `leafConst D` (rather than
preserving `rest`).  This makes the post-mismatch state a
fixed point of `compareStep` via `compareStep_leaf_wl`, so
subsequent iterations are no-ops.  Consequences:

- `treeEq_ℓℓ`, `treeEq_ℓβ`, `treeEq_βℓ`, `treeEq_bool` are
  all proved from iteration infrastructure alone.
- `treeEq_ℓβ` uses the peel-shift-stabilize pattern:
  `iterNat_cfpLift_succ` to peel one iteration,
  `elim_algebra_morphism` to commute `compareStep` past
  `p.elim`, `compareStep_mismatch_left` to reach the fixed
  point, then `iterNat_cfpLift_fixed` to collapse all
  remaining iterations.
- `treeEq_βℓ` is a direct adaptation using
  `compareStep_mismatch_right`.

`treeEq_ββ` and `treeEq_refl`, `treeEq_symm`, `treeEq_trans`
remain more difficult in the fully generic PBTO setting
because the branch-branch case requires decomposing a single
iteration of length `1 + S(branch(f1,f2)) + S(branch(g1,g2))`
into two sub-iterations whose intermediate states depend on
the outcome of the first pair's comparison.  This requires
case analysis, which at the morphism level is available
under `IsSeparator cfpTerminal` + `HasBoolDichotomy C` — the
same assumptions used throughout `TreePERLimits.lean`.

The path forward: parameterize the harder theorems
(`treeEq_ββ`, `refl`, `symm`, `trans`) by these two
assumptions.  They follow for `LawvereBTQuotCat`
(`lawvereBTQuotCat_isSeparator` + `lawvereBTQuotCat_hasBoolDichotomy`)
and for `Type u`, which covers both existing downstream uses.

## `treeEq_leaf_left` and `paraElim` experiment

`treeEq_leaf_left` (line ~6059 of `TreeLogic.lean`) characterizes
`treeEq` with a leaf first argument as `isLeafEndo`.  The proof
lifts to `cfpProd cfpTerminal p.T` and uses `p.elim_uniq` with
the leaf case from `treeEq_ℓℓ` and the branch case from
`treeEq_ℓβ`.

An attempt to characterize `treeEq` as a `paraElim` and derive
`treeEq_ββ` from `paraElim_β` was explored.  The analysis
confirms that `paraElim_uniq` does not bypass the `treeEq_ββ`
obstacle: the step verification for `paraElim_uniq` IS
`treeEq_branch_left` (Theorem 2 in the experiment), which itself
requires `treeEq_ββ` in its branch-case.  The circularity is
inherent to the approach.

Direct iteration tracing for `treeEq_ββ` reaches the state
after one `compareStep_expand`:

```lean
mkBranch (leafConst D)
  (mkBranch (mkBranch f1 g1)
    (mkBranch (mkBranch f2 g2) (leafConst D)))
```

with remaining count `inner_count`.  Decomposing this two-pair
worklist iteration into two sequential single-pair iterations
requires `iterNat_plus` combined with a proof that
`inner_count` equals a `natPlus` of the two individual counts.
This in turn requires commutativity and associativity of
`natPlus`, which are not yet proved, plus a worklist-carries
lemma showing that processing pair `(f1, g1)` with extra pairs
on the rest of the worklist still gives the same result as
`treeEq(f1, g1)`.

The documented path via `IsSeparator` + `HasBoolDichotomy`
remains the recommended approach for `treeEq_ββ`.

## `natTri_natSucc` (proved)

The triangular number recurrence `natTri_natSucc` is proved in
`NatArith.lean`. The proof uses:

- `natTriStep_cfpFst`, `natTriStep_cfpFst_comm`:
  step morphism composed with first projection.
- `natTriHelper_cfpFst`: first projection of
  `natTriHelper` equals `p.elim p.ℓ (cfpSnd ≫ natSucc)`,
  via `elim_algebra_morphism`.
- `natTriStepSingle_cfpSnd`: second projection of
  `natTriStepSingle`.
- `natTriHelper_natSucc`: evaluating `natTriHelper` at
  `(*, succ(n))` equals evaluating at `(*, n)` then
  applying `natTriStepSingle`. Factors through
  `cfpMap (𝟙) p.β` and uses `natTriHelper_β_factor`
  plus a cancellation lemma.
- `natTri_natSucc` itself: derives from
  `natTriHelper_natSucc` and `natTriStepSingle_cfpSnd`.

The statement:
`natSucc ≫ natTri = cfpLift
  (cfpLift (cfpTerminalFrom T) (𝟙 T) ≫
    natTriHelper ≫ cfpFst ≫ natSucc)
  natTri ≫ natPlus`

This says `tri(succ(n)) = natPlus(natSucc(index_n), tri(n))`
where `index_n` is the first projection of `natTriHelper` at
`(*, n)`.

## `cantorPair_injective` and `treeEqG_ββ` (not yet proved)

`cantorPair_injective` states:
`natEq(cantorPair(a,b), cantorPair(c,d)) =
  boolAnd(natEq(a,c), natEq(b,d))`

This requires a full number-theoretic argument about
the triangular number function:

1. `cantorPair(m,n) = tri(m+n) + m`. Equal pairs
   implies equal diagonals (`m+n = c+d`) by the gap
   property of triangular numbers.
2. Equal diagonals plus equal Cantor values implies
   `m = c` (by `natPlus_cancel_right`).
3. `m = c` and `m+n = c+d` implies `n = d`.

Step 1 requires proving that `natTri` is "injective
enough": if `tri(s) + a = tri(t) + c` with `a ≤ s`
and `c ≤ t`, then `s = t`. The standard argument uses
`tri(k+1) - tri(k) = k+1 > k ≥ a`, which in the
categorical setting requires:

- Order/comparison on right-spine naturals
- Properties of truncated subtraction with `natTri`
- Case analysis (possibly via `IsSeparator` +
  `HasBoolDichotomy`)

`treeEqG_ββ` depends on `cantorPair_injective`.
The existing `treeEqG_ββ_reduce` already reduces the
LHS to comparing Cantor-paired values via `natEq`.
