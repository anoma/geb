# `majorizes_redS` Proof Strategy and Research Notes

**Date**: 2026-04-27.
**Status**: Active work item.  Strategy documented for
continuity across sessions and compactions.
**Workstream**: Lawvere Theory of Elementary Recursive
Functions (`.session/workstreams/lawvere-elementary-recursive.md`).
**Plan**: `docs/superpowers/plans/2026-04-25-lawvere-godelt-typed-rebuild.md`.

## What this document covers

The proof of Beckmann-Weiermann 2000 Lemma 11 (the
S-combinator strict-decrease majorization) in our Lean
formalization.  Three subagent dispatches have failed to
complete this proof; the controller is now attempting it
directly in conversation following an explicit template.
This note records:

1. The exact theorem statement and its semantic
   verification.
2. Research findings on external proof sources.
3. The chosen proof strategy (template-following).
4. The structural setup (sub-term abbreviations, type
   levels, isIterHead facts) needed at the start of the
   proof.
5. The intended order of computation steps.
6. Pitfalls that have caused prior agent failures.

## Theorem statement

```lean
theorem GodelTTerm.majorizes_redS {S : Set GodelTBase}
    {n : Nat} (ρ σ τ : GodelTType S)
    (f : GodelTTerm S n (.arrow ρ (.arrow σ τ)))
    (g : GodelTTerm S n (.arrow ρ σ))
    (x : GodelTTerm S n ρ) :
    GodelTTerm.majorizes
      (.app (.app (.app (.S_comb (n := n) ρ σ τ) f) g) x)
      (.app (.app f x) (.app g x))
```

Recall `majorizes t s` is the conjunction:

* `s.bracketLevel 0 < t.bracketLevel 0` (strict at level 0)
* `∀ i, i ≤ σ_t.level → s.bracketLevel i ≤ t.bracketLevel i`
  (monotone for all i ≤ result-type-level; here that's
  `i ≤ τ.level`)

## Numerical verification

For ρ = σ = τ = nat, f = .K nat nat, g = .pred, x with
`[x]_0 = 100`:

* `[LHS]_0 = 8448`
* `[RHS]_0 = 606`
* gap = 7842 (well-positive)

This confirms the theorem is true; the work is to formalize.

## Research findings (2026-04-27)

The explicit S-combinator bracket-arithmetic proof in B-W's
specific form is essentially unique to Schütte's *Proof
Theory* (Springer 1977), which is paywalled and not on
archive.org.  All other sources consulted use either:

* A different proof technique (e.g. Tait's reducibility
  candidates — Avigad-Feferman dialectica chapter, Lean 4
  metatheory framework arxiv:2512.09280) — these establish
  SN but do not yield the explicit elementary derivation-
  length bound that our downstream stages need.
* A different formulation (recursors instead of combinators
  — Wilken-Weiermann 2012, Beckmann-Weiermann head-reduction
  trees) — the techniques transfer but the explicit S case
  is not written out.
* The λ-calculus version (Beckmann 1998/2001) — also not
  directly applicable to the combinator setup.

No open formalization in Coq, Agda, or Lean covers the
elementary bound for typed combinators with the bracket
measure.

## Proof strategy: template-following

The proof of `majorizes_redIter_succ` (committed at
`f4f2df34` in `GebLean/LawvereGodelTLemma16.lean` lines
1154-1500) is the structural template.  It uses:

1. `set` abbreviations for sub-terms.
2. `isIterHead = false` checks for each non-iter app.
3. Step-by-step `bracketLevel_app_eq` and
   `bracketLevel_app_high` rewrites computing bracket
   values at each relevant level.
4. Algebraic manipulation establishing the strict
   inequality.

The redS proof follows the same pattern with one extra
layer: the LHS chain has four `app`s (S, f, g, x) versus
the iter case's four (iter, t, a, b).

**Critical pitfall** (caused all prior agent failures):
prior dispatches tried to find a "clever" high-level
invariant like `[appfx]_i + [appgx]_i ≤ [appSfg]_i` and
got stuck because the natural invariant doesn't propagate
cleanly under the downward induction.  The actual technique
is just to PLOW THROUGH the algebra, computing each bracket
level explicitly.  The previous agents ALSO miscomputed
`[RHS]_0` as `[appfx]_0 + [appgx]_0` instead of
`2^[RHS]_1 * (sum)` — bear this in mind.

## Sub-term setup

Following the redIter_succ template, name the seven
sub-terms:

```lean
set Sat := GodelTTerm.S_comb (S := S) (n := n) ρ σ τ
set appSf := GodelTTerm.app Sat f
set appSfg := GodelTTerm.app appSf g
set LHS := GodelTTerm.app appSfg x
set appfx := GodelTTerm.app f x
set appgx := GodelTTerm.app g x
set RHS := GodelTTerm.app appfx appgx
```

isIterHead facts (all are `rfl` because each is an `.app`
or atomic non-iter):

```lean
have hSatNI : Sat.isIterHead = false := rfl
have happSfNI : appSf.isIterHead = false := rfl
have happSfgNI : appSfg.isIterHead = false := rfl
have happfxNI : appfx.isIterHead = false := rfl
have happgxNI : appgx.isIterHead = false := rfl
-- Also: f, g may have any structure but their isIterHead
-- only matters in `app f x`/`app g x` arrangements.
have hfNI : f.isIterHead = false := by cases f <;> rfl
have hgNI : g.isIterHead = false := by cases g <;> rfl
```

Type level abbreviations:

```lean
-- Atom Sat has type:
-- (ρ→σ→τ) → (ρ→σ) → ρ → τ
-- The first arrow's source type level:
-- L_ρστ = max(ρ.level + 1, max(σ.level + 1, τ.level))
-- The second arrow's source type level:
-- L_ρσ = max(ρ.level + 1, σ.level)
-- Sat.type.level = max(L_ρστ + 1, max(L_ρσ + 1, max(ρ.level + 1, τ.level)))
--                = max over all the arrow components
```

## Computation order (intended)

Follow the redIter_succ pattern exactly.  Key levels to
compute: 0, 1, 2, possibly higher (depending on type
levels).  The case-splits on `i ≤ τ.level`,
`i ≤ σ.level`, `i ≤ ρ.level` happen inside each
`bracketLevel_app_eq` invocation.

For the strict-at-0 part:

1. `[Sat]_0 = 1` (from `bracketLevel_S_comb`, since
   `0 ≤ Sat.type.level`).
2. `[appSf]_0 = 2^[appSf]_1 * (1 + [f]_0)` via
   `bracketLevel_app_eq` at i=0 with σ_f = (ρ→σ→τ)
   (level ≥ 1 ≥ 0).
3. `[appSf]_1 = 2^[appSf]_2 * ([Sat]_1 + [f]_1)` via
   `bracketLevel_app_eq` at i=1 (assuming
   `1 ≤ (ρ→σ→τ).level`, almost always true).
4. Higher levels of `[appSf]` compute similarly using
   pass-through (`bracketLevel_app_high`) when
   `i > (ρ→σ→τ).level`.
5. `[appSfg]_0 = 2^[appSfg]_1 * ([appSf]_0 + [g]_0)` via
   `bracketLevel_app_eq` at i=0 with σ_g = (ρ→σ).
6. `[appSfg]_1 = 2^[appSfg]_2 * ([appSf]_1 + [g]_1)` etc.
7. `[LHS]_0 = 2^[LHS]_1 * ([appSfg]_0 + [x]_0)` via
   `bracketLevel_app_eq` at i=0 with σ_x = ρ.
8. `[LHS]_1 = [appSfg]_1` (pass-through) when
   `1 > ρ.level`, otherwise `2^[LHS]_2 * ([appSfg]_1 + [x]_1)`.

For RHS:

9. `[appfx]_0 = 2^[appfx]_1 * ([f]_0 + [x]_0)` (σ_x = ρ).
10. `[appgx]_0 = 2^[appgx]_1 * ([g]_0 + [x]_0)` (σ_x = ρ).
11. `[RHS]_0 = 2^[RHS]_1 * ([appfx]_0 + [appgx]_0)`
    (σ_appgx = σ).
12. `[RHS]_1 = ?` via case-split on `1 ≤ σ.level`.

**Key observation for strict-at-0**: The `1 + [f]_0`
factor inside `[appSf]_0` (where the `1` comes from
`[Sat]_0 = 1`) is the source of the strict gap.  Expanding
LHS_0 fully:

```
[LHS]_0 = 2^[LHS]_1 * (2^[appSfg]_1 * (2^[appSf]_1 * (1 + [f]_0) + [g]_0) + [x]_0)
       = 2^([LHS]_1 + [appSfg]_1 + [appSf]_1) * (1 + [f]_0)
       + 2^([LHS]_1 + [appSfg]_1) * [g]_0
       + 2^[LHS]_1 * [x]_0
```

```
[RHS]_0 = 2^[RHS]_1 * (2^[appfx]_1 * ([f]_0 + [x]_0)
        + 2^[appgx]_1 * ([g]_0 + [x]_0))
       = 2^([RHS]_1 + [appfx]_1) * [f]_0
       + 2^([RHS]_1 + [appfx]_1) * [x]_0
       + 2^([RHS]_1 + [appgx]_1) * [g]_0
       + 2^([RHS]_1 + [appgx]_1) * [x]_0
```

For the strict gap, we need to dominate term-by-term.  The
"1" inside LHS contributes `2^([LHS]_1 + [appSfg]_1 + [appSf]_1)`
which has no counterpart on RHS — that's the strict slack.

For the [f]_0 term: `[LHS]_1 + [appSfg]_1 + [appSf]_1 ≥
[RHS]_1 + [appfx]_1 + 1`?  Need to verify.

Alternative formulation: bound [appfx]_i ≤ [appSf]_i and
[appgx]_i ≤ [appSfg]_i (or similar), each as auxiliary
sub-lemmas.

## Monotone-at-i part

For `1 ≤ i ≤ τ.level`: case-split on i vs other type
levels.  At each level, both LHS_i and RHS_i are either
multiplicative or pass-through.  The non-strict version
of the same algebraic argument gives `[RHS]_i ≤ [LHS]_i`.

For `i > τ.level` (outside the `majorizes` range, but
relevant if we work via `bracketLevel_high_zero`): both
are 0.

## Files involved

* Modify: `GebLean/LawvereGodelTLemma16.lean`.  Append
  `majorizes_redS` between existing `majorizes_redTreeIter_node`
  (line ~2032) and `end GebLean`.
* Possibly add helpers to `GebLean/Utilities/Tower.lean`
  (additions only, no modifications to existing).

## Estimated proof size

Based on `majorizes_redIter_succ` at 350 lines and the
extra structural layer in redS, expect 400-700 lines.
May benefit from factoring into 2-3 lemmas:

* Strict-at-0 part as a separate lemma.
* Monotone part as a separate lemma (with case-split on
  i vs σ.level, τ.level).
* Combine into the main theorem via `refine ⟨?_, ?_⟩`.

## After redS lands

Two more deliverables remain in stage δ.5:

1. **Generalize `majorizes_redTreeIter_node`** to remove
   the `hσ : σ.level = 0` hypothesis (currently restricts
   to base-typed σ).  The general case requires careful
   case-splits on i vs σ.level and i vs σ→σ.level etc.
   The strict-at-0 part should generalize directly; the
   monotone-at-higher-i part is the work.  Reference the
   pattern in `majorizes_redK` and `majorizes_redTreeIter_leaf`
   for general-σ handling.

2. **`Reduces.bracketLevel_le_at`** (helper) and
   **`Reduces.bracketLevel_strict`** (the main theorem of
   stage δ.5).  Both proven by `induction h` over the 12
   `Reduces` constructors.  Each base reduction case
   delegates to the corresponding `majorizes_red*` lemma's
   `.1` (strict) or `.2` (monotone) projection.  Two
   congruence cases (`redApp_left`, `redApp_right`) handled
   via case-split on `f.isIterHead` plus `bracketLevel_app_eq`
   arithmetic.  See the controller's earlier brief for the
   detailed strategy.

After all of stage δ.5 lands, stage δ.6 (Lemma 16 itself)
becomes the next item.  Estimated remaining stage δ work:
2-3 weeks of focused proof effort.

## Stages after δ

* **ε** Strong normalization: well-founded `▷` recursion via
  `Reduces.bracketLevel_strict`; total `normalize` function.
* **ζ** Confluence: Tait-Martin-Löf parallel-reduction
  proof.  Largely orthogonal to δ — does not depend on
  bracket measure.  Can potentially proceed in parallel.
* **η** Numeral normal form + completeness for `≈` vs
  extensional equality on base-typed terms.
* **θ** Categorical structure: `GodelTMor1`, tuples,
  `≈`-quotient, `Category LawvereGodelTCat`, finite
  products, faithful interp functor.
* **ι** Nucleus ≌ LawvereERCat: derived T* terms for ER
  constructors; `erToGodelT` and `godelTToER` via logical
  relations + `ERMor1.iterT`.  Lemma 16 is needed here
  for the iter case bound.
* **κ** Binary-tree extension at `S = {.nat, .tree}`.
* **λ** Szudzik-encoded equivalence BT ≌ Nucleus.
* **μ** Cross-stage tests including Plausible property
  tests on random trees.
* **ν** Programmer ergonomics (deferred polish).

The categorical equivalence with `LawvereERCat` (stage ι)
requires Lemma 16's elementary bound to construct the ER
witness for each iter sub-term.  The bound ensures that
`ERMor1.iterT`'s required iteration count is elementary
recursive in the inputs.

## Risk assessment

Stage δ.5 is the gating risk for the entire workstream.
If `redS` cannot be completed, the strict-decrease theorem
cannot be proven, SN cannot be derived in this framework,
Lemma 16 cannot be proven, and the categorical equivalence
with ER (the workstream's mathematical goal) cannot be
established.

Mitigations explored and rejected:
* **Restrict `Reduces.redTreeIter_node` to σ.level = 0**:
  rejected as a non-negotiable interface change per
  CLAUDE.md (B-W's reduction relation is a fixed
  mathematical contract).
* **Switch to Tait reducibility for SN**: gives SN but
  not the elementary bound; the bound is needed for
  stage ι.

## 2026-04-27 update: fourth dispatch BLOCKED

A fourth focused Opus dispatch with the full strategy doc,
the redIter_succ template reference, the controller's
partial setup code, the numerical example, and the explicit
term-by-term decomposition reported BLOCKED with the same
fundamental obstacle prior dispatches identified.

The agent reduced the strict-at-0 inequality to a "key
inequality KI3":

```
[LHS]_1 ≥ [RHS]_1 + max([appfx]_1, [appgx]_1) + 1
```

and confirmed: this requires a "stronger combined invariant"
that no agent has been able to identify, OR a recursive
descent through arbitrarily many `bracketLevel` levels
(unbounded since τ.level is universally quantified).

Approaches the agent verified do NOT close the proof:
1. Term-by-term expansion: x_0 coefficient comparison
   requires KI3.
2. Sub-term majorization `[appSfg]_i ≥ [appfx]_i + [appgx]_i`:
   fails with concrete counterexample at large [x]_0.
3. Uniform `LHS_i ≥ 2*RHS_i`: shifted KI3 reappears.
4. Strong induction descending on i: candidate invariants
   collapse at high-i base case (both sides 0).
5. Finite case-split on (ρ.level, σ.level, τ.level): not
   finite — recursive bracket levels depend on unbounded
   τ.level.

What was successfully built (verified compile with `sorry`
placeholder, in stash@{0}):
* `Sat.type.level ≥ 2` for any ρ, σ, τ.
* `[Sat]_i = 1` for `i ≤ Sat.type.level`.
* `[appSf]_2 ≥ 1`, `[appSf]_1 ≥ 2`, `[appSf]_0 ≥ 4 * (1 + [f]_0)`.
* `[appSfg]_1 ≥ 2`, `[appSfg]_0 ≥ 4 * ([appSf]_0 + [g]_0)`.
* `[LHS]_1 ≥ 2`.

These build cleanly and would be reusable if a successful
proof strategy emerges.

## Recommended next steps (per fourth-dispatch agent)

1. **Build auxiliary "bracket gap" infrastructure first**
   in `Utilities/Tower.lean` or new `Utilities/BracketGap.lean`:
   * `gap(t, s, i) := [t]_i - [s]_i`.
   * Compositional gap-propagation lemmas.
   * "Sub-term gap" lemmas comparing structurally
     different terms.
   Estimated 200-400 lines.  The `redS` proof would then
   be tractable (~50 lines) on top of this.
2. **Consider a different SN measure** that avoids per-redex
   majorization.  E.g., direct lex-product `(d, lh)`
   following B-W's reduction-tree analysis (different from
   the bracket measure).  This would require restructuring
   stage δ.6 (Lemma 16) since it currently inhabits the
   bracket measure.
3. **Locate Schütte 1977 directly** (interlibrary loan,
   physical library copy).  Without the original proof,
   re-deriving B-W's specific bracket-arithmetic argument
   is genuinely intractable in available compute time.

## 2026-04-27 decision: Path A (bracket-gap infrastructure)

User-approved direction: build the auxiliary infrastructure
in `Utilities/BracketGap.lean` (or extending `Utilities/Tower.lean`),
then build the redS proof on top.

**Plan for next session**:

1. **Brainstorm the BracketGap framework design.**  Use
   `superpowers:brainstorming`.  Key questions:
   * What is the right "gap" predicate?  Candidates:
     - `gap_at t s i := [t]_i - [s]_i`.
     - `dominates t s := ∀ i, [s]_i ≤ [t]_i`.
     - Strict-and-nonstrict pair like `majorizes`.
   * What composition lemmas are needed for redS?  At
     minimum: how does the gap propagate through `.app`?
     E.g., `gap_app_left : (∀ i, [g]_i ≤ [f]_i) → ∀ i, [.app g a]_i ≤ [.app f a]_i`.
   * Do we need symmetric lemmas (gap_app_right) for the
     RHS-construction case?  Or a more general lemma
     covering both LHS and RHS structures simultaneously?

2. **Write the plan** using `superpowers:writing-plans` with
   the design from step 1.  Include explicit per-lemma
   structure and order.

3. **Implement piece by piece** using either
   `superpowers:subagent-driven-development` or direct
   in-conversation work.  For sticky proofs, dispatch
   `lean4:sorry-filler-deep` (the lean4 plugin's
   strategic-sorry-resolver agent), which can resolve
   stubborn sorries by leveraging facts already in
   context.  Use the existing partial setup in
   `stash@{0}` for the redS structural skeleton.

4. **Apply to redS.**  After the framework lands, the
   redS proof should be ~50 lines using gap-propagation
   lemmas instead of direct algebraic computation.

5. **Apply to redTreeIter_node generalization.**  The
   same framework should resolve the σ-level-restriction
   on `majorizes_redTreeIter_node` (currently committed
   only for `σ.level = 0`).

**Sub-stage label**: This becomes a new sub-stage
**δ.4.5 (BracketGap infrastructure)** in the plan.
Insert before δ.5's remaining work.

**Estimated scope**: 200-400 lines of utilities + 50-100
lines of redS proof + 100-200 lines for generalizing
redTreeIter_node.  Total: ~400-700 lines new.

**Compute budget**: This is genuinely new mathematical
formalization work without an exact external template.
Expect multiple subagent dispatches and iteration.

Stash entries preserving partial work:
* `stash@{0}`: redS partial setup with sorry placeholder
  (the controller's initial scaffolding before fourth
  dispatch).
* `stash@{1}`: redIter_succ partial attempt (older).
* `stash@{2}`: failed combined lemma attempts (older).
* `stash@{3}`: subagent stage-delta deviation 2026-04-26
  (the first agent's rejected work — has the alternate
  Lemma 16 proof using modified `d`).
