# Sub-stage delta.4.5 — BracketGap monotonicity infrastructure

**Date**: 2026-04-27.
**Workstream**: Lawvere Theory of Elementary Recursive Functions
(`.session/workstreams/lawvere-elementary-recursive.md`).
**Implementation plan**: `docs/superpowers/plans/2026-04-25-lawvere-godelt-typed-rebuild.md`.
**Strategy doc**: `docs/superpowers/notes/2026-04-27-redS-proof-strategy.md`.
**Branch**: `terence/syntax`.

## Goal

Add the infrastructure required to close `majorizes_redS` (B-W
Lemma 11, the S-combinator strict-decrease majorization) and to
generalize `majorizes_redTreeIter_node` from `sigma.level = 0` to
arbitrary `sigma`.  Five prior attempts at `majorizes_redS`
reduced to a single inequality (KI3) plus two related coefficient
inequalities, all of which are tractable once the right level of
abstraction is available.

This sub-stage produces three deliverables, in build order:

1. A reusable `dominates` predicate plus its propagation through
   `.app` (Ingredient A): non-strict and strict-preserving forms.
2. A redS-specific level-1 arithmetic toolkit (Ingredient B):
   three inequalities packaged as separate lemmas.
3. The two outstanding majorization theorems built on top:
   `majorizes_redS` and the general-`sigma`
   `majorizes_redTreeIter_node`.

## Motivation

The redS strict-at-0 inequality, when expanded term-by-term via
`bracketLevel_app_eq`, decomposes into three coefficient
comparisons (one per `[f]_0`, `[g]_0`, `[x]_0`) plus a slack
contribution from `[S_comb]_0 = 1`.  The three coefficient
comparisons reduce to inequalities at level 1:

* `[LHS]_1 + [appSfg]_1 + [appSf]_1 >= [RHS]_1 + [appfx]_1` (for
  the `[f]_0` coefficient).
* `[LHS]_1 + [appSfg]_1 >= [RHS]_1 + [appgx]_1` (for the `[g]_0`
  coefficient).
* `[LHS]_1 >= [RHS]_1 + max([appfx]_1, [appgx]_1) + 1` (KI3, for
  the `[x]_0` coefficient).

Each is a finite case-split on `(rho.level >= 1, sigma.level >= 1)`
that resolves to elementary arithmetic over `2^k` factors and a
few `[f]_i`, `[g]_i`, `[x]_i` values.  The "unbounded `tau.level`"
objection in the prior dispatch is incorrect: `tau` enters only
through `[S_comb]_i = 1` for `i <= S_comb.type.level`, and
the relevant comparisons stay at levels 0-2 throughout.

The strict slack arises automatically once these three are
cleared: the literal `1` inside the LHS factor `(1 + [f]_0)` (from
`[S_comb]_0 = 1`) gets multiplied by `2^([LHS]_1 + [appSfg]_1 +
[appSf]_1)` and has no RHS counterpart.

The `dominates` predicate (Ingredient A) is independently useful:

* The `redApp_left` and `redApp_right` cases of the eventual
  `Reduces.bracketLevel_strict` main theorem reduce to it.
* The `majorizes_redTreeIter_node` generalization to arbitrary
  `sigma` requires monotone bracket comparison at each level
  `1 <= i <= sigma.level`, which is what `dominates_app` provides.
* Stages `epsilon` (strong normalization) and `zeta`
  (Tait-Martin-Loef confluence) will likely consume the same
  predicate when proving congruence properties of reduction.

## Components

### A1. `dominates` predicate

```lean
def GodelTTerm.dominates {S : Set GodelTBase} {n : Nat}
    {sigma : GodelTType S} (t s : GodelTTerm S n sigma) : Prop :=
  forall i, s.bracketLevel i <= t.bracketLevel i
```

No notation introduced; use the qualified name.  Quantification
over `i` is unrestricted because brackets vanish for `i >
sigma.level` (`bracketLevel_high_zero`), so the unrestricted form
is equivalent to the restricted form `forall i, i <= sigma.level
-> [s]_i <= [t]_i`.

### A2. Routine structural lemmas

* `dominates_refl : forall t, t.dominates t`.
* `dominates_trans : t.dominates s -> s.dominates u -> t.dominates u`.
* `majorizes_imp_dominates : t.majorizes s -> t.dominates s` (just
  the conjunctive `.2` projection extended below `sigma.level` via
  `bracketLevel_high_zero`).

### A3. `dominates_app` (binary monotonicity)

```lean
theorem GodelTTerm.dominates_app
    {S : Set GodelTBase} {n : Nat} {sigma tau : GodelTType S}
    (f f' : GodelTTerm S n (.arrow sigma tau))
    (a a' : GodelTTerm S n sigma)
    (hf : f.isIterHead = false) (hf' : f'.isIterHead = false)
    (hF : f'.dominates f) (hA : a'.dominates a) :
    (GodelTTerm.app f' a').dominates (GodelTTerm.app f a)
```

Proof structure: downward induction on `i`, descending from a
sufficiently large bound (the maximum of the two terms' bracket-
vanishing levels via `G_ge_level` plus `bracketLevel_high_zero`).
The inductive step case-splits on `i <= sigma.level` (multiplicative
form via `bracketLevel_app_eq`) versus `i > sigma.level` (pass-
through via `bracketLevel_app_high`).  Multiplicative case factors:

* `2^[.app f a]_(i+1) <= 2^[.app f' a']_(i+1)` from the IH at
  level `i + 1` plus monotonicity of `2^k`.
* `[f]_i + [a]_i <= [f']_i + [a']_i` from `hF` and `hA`.
* Combined via `Nat.mul_le_mul`.

Pass-through case: directly from `hF`.

Estimated 60 lines.

### A4. `majorizes_app_left`

```lean
theorem GodelTTerm.majorizes_app_left
    (f f' : GodelTTerm S n (.arrow sigma tau))
    (a : GodelTTerm S n sigma)
    (hf : f.isIterHead = false) (hf' : f'.isIterHead = false)
    (h : f'.majorizes f) :
    (GodelTTerm.app f' a).majorizes (GodelTTerm.app f a)
```

Strict-at-0: from `bracketLevel_app_eq` at `i = 0` plus the strict
factor `[f']_0 > [f]_0`.  Monotone-at-i for
`1 <= i <= (.arrow sigma tau).level`: from `dominates_app` with
`a' = a` plus `dominates_refl a`.

Estimated 30 lines.

### A5. `majorizes_app_right`

```lean
theorem GodelTTerm.majorizes_app_right
    (f : GodelTTerm S n (.arrow sigma tau))
    (a a' : GodelTTerm S n sigma)
    (hf : f.isIterHead = false)
    (h : a'.majorizes a) :
    (GodelTTerm.app f a').majorizes (GodelTTerm.app f a)
```

Symmetric to A4.  Estimated 30 lines.

### B1. `redS_f_coef_bound`

```lean
theorem GodelTTerm.redS_f_coef_bound
    {S : Set GodelTBase} {n : Nat}
    (rho sigma tau : GodelTType S)
    (f : GodelTTerm S n (.arrow rho (.arrow sigma tau)))
    (g : GodelTTerm S n (.arrow rho sigma))
    (x : GodelTTerm S n rho) :
    let Sat   := GodelTTerm.S_comb (S := S) (n := n) rho sigma tau
    let appSf := GodelTTerm.app Sat f
    let appSfg := GodelTTerm.app appSf g
    let LHS   := GodelTTerm.app appSfg x
    let appfx := GodelTTerm.app f x
    let appgx := GodelTTerm.app g x
    let RHS   := GodelTTerm.app appfx appgx
    LHS.bracketLevel 1 + appSfg.bracketLevel 1
        + appSf.bracketLevel 1
      >= RHS.bracketLevel 1 + appfx.bracketLevel 1
```

Proof: 4-case split on `(rho.level >= 1, sigma.level >= 1)`.  Each
case unfolds the relevant brackets via `bracketLevel_app_eq` /
`bracketLevel_app_high` and discharges via `omega` (with help from
`Nat.pow_le_pow_left` for the `2^k` comparison when needed).
Estimated 50 lines (including the case-split scaffolding shared
with B2 and B3).

### B2. `redS_g_coef_bound`

Same shape as B1, with conclusion

```text
LHS.bracketLevel 1 + appSfg.bracketLevel 1
  >= RHS.bracketLevel 1 + appgx.bracketLevel 1
```

Estimated 30 lines (reusing the case-split scaffolding via shared
`have` bindings, or via a private helper definition).

### B3. `redS_x_coef_bound` (KI3)

Same shape as B1, with conclusion

```text
LHS.bracketLevel 1
  >= RHS.bracketLevel 1
       + max appfx.bracketLevel 1 appgx.bracketLevel 1 + 1
```

Estimated 50 lines (the strict `+1` requires an explicit argument
isolating the `[Sat]_1 = 1` contribution at level 2).

### Final theorem 1: `majorizes_redS`

```lean
theorem GodelTTerm.majorizes_redS {S : Set GodelTBase}
    {n : Nat} (rho sigma tau : GodelTType S)
    (f : GodelTTerm S n (.arrow rho (.arrow sigma tau)))
    (g : GodelTTerm S n (.arrow rho sigma))
    (x : GodelTTerm S n rho) :
    GodelTTerm.majorizes
      (.app (.app (.app (.S_comb (n := n) rho sigma tau) f) g) x)
      (.app (.app f x) (.app g x))
```

Strict-at-0: expand `[LHS]_0` and `[RHS]_0` once each via
`bracketLevel_app_eq`.  The `[f]_0`, `[g]_0`, `[x]_0` coefficients
of LHS dominate those of RHS by B1, B2, B3 respectively.  The
slack from `[Sat]_0 = 1` provides the strict gap.

Monotone-at-i for `1 <= i <= tau.level`: at each such level, the
LHS chain remains multiplicative via `bracketLevel_app_eq` (since
`i <= rho.level` requires `rho.level >= 1`, and otherwise pass-
through), and similarly for RHS.  Comparisons at higher levels
follow from `dominates_app` (A3) applied along the LHS chain
versus the RHS chain, with the same B1/B2/B3 inequalities serving
as level-1 comparison points.  This part may need a small
case-split on `tau.level`.

Estimated 60 lines.

### Final theorem 2: `majorizes_redTreeIter_node` generalized

The current proof at line ~2032 of `LawvereGodelTLemma16.lean`
restricts to `sigma.level = 0`.  Generalization replaces the
`omega`-finish at `i > 0` with an A3 / A4-based argument lifting
sub-term dominance through the redex.  The strict-at-0 part is
unchanged.

Estimated 150 lines (replacing the existing partial proof).

## File placement

All new lemmas land in `GebLean/LawvereGodelTLemma16.lean`.  The
new section header `-- BracketGap monotonicity infrastructure
(delta.4.5)` appears between the existing
`majorizes_redTreeIter_leaf` (line ~870) and the existing
`bracketLevel_zero_pos_combined` (line ~927), so that the
infrastructure is available to all subsequent majorization lemmas.

The redS-specific lemmas B1-B3 and `majorizes_redS` are appended
in a separate section after `majorizes_redTreeIter_node`.

The generalization of `majorizes_redTreeIter_node` revises the
existing definition in place (preserving its name and signature
modulo the dropped `hsigma : sigma.level = 0` hypothesis).

`Utilities/Tower.lean` is not modified.  No new utility files are
created.  The factoring of `bracketLevel` itself out of
`LawvereGodelTLemma16.lean` (into a hypothetical
`Utilities/GodelTBracket.lean`) is deferred as a separate refactor
not in this sub-stage's scope.

## Estimated total

* A1-A5: ~250 lines.
* B1-B3: ~130 lines.
* `majorizes_redS`: ~60 lines.
* `majorizes_redTreeIter_node` (general `sigma`): ~150 lines
  (replacing existing).

Approximately 590 lines total, in line with the strategy doc's
400-700 estimate.

## Build order

A1 -> A2 -> A3 -> A4 -> A5 -> B1 -> B2 -> B3 -> `majorizes_redS`
-> `majorizes_redTreeIter_node` (general).

Each step builds cleanly with `lake build` (zero warnings) and
`lake test` before the next step begins.  Where a proof step
gets stuck, factor out a smaller lemma per CLAUDE.md's
factoring-out-lemmas guidance.

## After delta.4.5

`Reduces.bracketLevel_le_at` (helper) and
`Reduces.bracketLevel_strict` (the main theorem of stage delta.5)
become tractable: each base reduction case delegates to the
corresponding `majorizes_red*` lemma's `.1` (strict) or `.2`
(monotone) projection; the two congruence cases (`redApp_left`,
`redApp_right`) delegate to A4 (`majorizes_app_left`) and A5
(`majorizes_app_right`).

## Risk assessment

The five-attempt failure pattern was diagnosed as missing the
abstraction A3 (dominance through `.app`).  With A3 in hand, the
KI3 inequality and its two siblings B1, B2 reduce to finite
case-split arithmetic.  The risk has shifted from "no path
forward" to "verify the case-split arithmetic".

Remaining sources of risk:

* The 4-case split in B1-B3 may turn out to need 8 cases
  (additional split on `tau.level`); the case scaffolding is
  designed to absorb this without restructuring.
* The `monotone-at-i` portion of `majorizes_redS` may need
  level-aware case-splits for `i > rho.level` versus
  `i <= rho.level` etc.  These follow from `bracketLevel_app_high`
  pass-through plus IH.

If a case unexpectedly does not close, the standard response
(per CLAUDE.md) is to factor out a smaller intermediate lemma
and recurse.  No interface change to the existing primitives
should be required.
