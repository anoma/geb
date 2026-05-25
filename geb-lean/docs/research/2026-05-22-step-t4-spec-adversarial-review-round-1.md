# T4 spec adversarial review — round 1

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary](#summary)
- [Blockers](#blockers)
  - [B1. `comp` recipe wrong: nested tower not absorbed by `max`](#b1-comp-recipe-wrong-nested-tower-not-absorbed-by-max)
  - [B2. `vMax` is `private`; not reusable](#b2-vmax-is-private-not-reusable)
  - [B3. bsum identity is false in the relevant range](#b3-bsum-identity-is-false-in-the-relevant-range)
- [Serious](#serious)
  - [S1. `Finset.univ.sup` likely breaks axiom budget](#s1-finsetunivsup-likely-breaks-axiom-budget)
  - [S2. §6.1 `if i = 0` on `Fin 2` not idiomatic Lean](#s2-61-if-i--0-on-fin-2-not-idiomatic-lean)
  - [S3. §7.1 `numInputs = a` is a type identity, not a T2 invariant](#s3-71-numinputs--a-is-a-type-identity-not-a-t2-invariant)
  - [S4. Proof outline elides `comp`-recursion structural issue](#s4-proof-outline-elides-comp-recursion-structural-issue)
  - [S5. bsum/bprod side condition does not discharge the identity](#s5-bsumbprod-side-condition-does-not-discharge-the-identity)
  - [S6. §6.2 rejection of augmented-arity is mathematically wrong](#s6-62-rejection-of-augmented-arity-is-mathematically-wrong)
  - [S7. AXIOM\_ALLOW deferral defeats the spec gate](#s7-axiom_allow-deferral-defeats-the-spec-gate)
  - [S8. `comp` `v_total = Σ v i` is not absorbed by `vMax`](#s8-comp-v_total--σ-v-i-is-not-absorbed-by-vmax)
- [Minor](#minor)
  - [M1. Page-citation precision](#m1-page-citation-precision)
  - [M2. §5.2 `maxOver 0` left "or whatever"](#m2-52-maxover-0-left-or-whatever)
  - [M3. §3 `natK'` arity is implicit](#m3-3-natk-arity-is-implicit)
  - [M4. `boundExprK_params` mixes camelCase and snake\_case](#m4-boundexprk_params-mixes-camelcase-and-snake_case)
  - [M5. Module docstring contents not pre-specified](#m5-module-docstring-contents-not-pre-specified)
  - [M6. §15 references — page citations not uniform](#m6-15-references--page-citations-not-uniform)
  - [M7. §4.2 "small constant" has no numeric ceiling](#m7-42-small-constant-has-no-numeric-ceiling)
  - [M8. §10 dependency DAG ASCII layout misleading](#m8-10-dependency-dag-ascii-layout-misleading)
- [Methodology](#methodology)

<!-- END doctoc -->

## Summary

3 blockers, 8 serious, 8 minor.

## Blockers

### B1. `comp` recipe wrong: nested tower not absorbed by `max`

§4.2 table, line 215:

> `comp f gs` | … | `Nat.max r_f (Fin.maxOfNat (fun i => r_{gs i}))` |
> folded offset (Nat.max + small constant) |

`compileER_runtime` for `comp f gs` is at
`GebLean/LawvereERKSim/Compiler.lean:1728-1737`:

```text
| a, .comp (k := k) f gs, v =>
    let inner : Fin k → ℕ := fun i => (gs i).interp v
    …
    glue + compileER_runtime f inner + 2
```

The body contains `compileER_runtime f inner`, where
`inner i = (gs i).interp v`. The runtime of `f` is being
evaluated at the **ER-interpreted outputs** of the `gs`, not at
`v` itself. By the inductive hypothesis on `gs i`,
`(gs i).interp v` is itself only bounded by some `tower r_i' x`
shape (separately from the runtime of `gs i`), but more
critically: the runtime of `f` at this `inner` vector is
bounded by `tower r_f (vMax inner + offset_f)`, and
`vMax inner ≤ max_i (gs i).interp v`, which is bounded by some
`tower R x` shape where `R` depends on what bound ER carries
for `(gs i).interp v` (not on `r_{gs i}`, which is a runtime
exponent — distinct from a value exponent).

So the spec conflates two different quantities:

1. `r_{gs i}` — the tower height needed for the *runtime* of
   `gs i`.
2. The tower height needed for the *value* `(gs i).interp v`.

These are not the same. Tourlakis 2018 §0.1.0.27 bounds
`f ∈ E^n` by `A_n^r(max v)` for some `r`; that is a
*value* bound. §0.1.0.42 furnishes a runtime `t_f ∈ E^n`,
which by §0.1.0.27 has its own value bound — but the spec's
recipe collapses both into a single `r_e` field.

Concretely the compositional bound is

```text
compileER_runtime f inner
  ≤ tower r_f (vMax inner + offset_f)
  ≤ tower r_f (tower r_{gs}^{val} (vMax v + …) + offset_f)
  ≤ tower (r_f + r_{gs}^{val}) (vMax v + …) (by Tower.tower_comp)
```

Even granting the spec's identification of `r_{gs i}` with
`r_{gs i}^{val}`, the result is `r_f + max_i r_{gs i}`, not
`max(r_f, max_i r_{gs i})`. The `kToER` mirror
(`LawvereKSimMajorization.lean:643`) does this correctly:

```text
| _, .comp f gs, h =>
    …
    (p_f.1 + r_g, p_f.2 + o_g)
```

It uses `p_f.1 + r_g` (addition), not `max`. The spec's `Nat.max`
recipe at comp is wrong; `compileER_runtime` for `comp` is not a
"composition adds (no iteration)" case — the inner `f` sits over
a tower-bounded value, and you must pay the additive cost in
tower height.

This is a blocker: the recipe as written will not discharge
`boundExprK_params_dominates`'s comp case under structural
induction.

### B2. `vMax` is `private`; not reusable

§5.2 reads:

> `vMax : (Fin a → ℕ) → ℕ` is already defined in
> `GebLean/LawvereKSimMajorization.lean`; this composite
> realises that exact Nat function in K^sim — reuse, not a
> fresh `maxOfVec`.

The actual definition at
`GebLean/LawvereKSimMajorization.lean:43-44` is:

```lean
private abbrev vMax {a : ℕ} (v : Fin a → ℕ) : ℕ :=
  (Finset.univ : Finset (Fin a)).sup v
```

The `private` keyword makes `vMax` inaccessible from any other
file. `RuntimeBound.lean` cannot reference it; §4.3, §6.1, §6.3
all do so by name.

This is a blocker for the spec's reuse claim. Resolution options:

1. Promote `vMax` to a `public` definition (remove `private`,
   move to a more central file).
2. Define a fresh `RuntimeBound.vMax` (which is what the spec
   appears to actually require, regardless of language).
3. Use `Finset.univ.sup v` directly throughout, never naming the
   abstraction.

Option 1 conflicts with S1 below (axiom budget). The spec must
choose, and at present has chosen incoherently.

### B3. bsum identity is false in the relevant range

§4.2 line 230 and §4.3 claim the constructive identity
`v 0 · tower r x ≤ tower (r+1) x` (when `v 0 ≤ x`) is enough
for the bsum case.

Counterexample at `r = 1`, `x = v 0 = 3`:

```text
v 0 · tower 1 x = 3 · 2^3 = 3 · 8 = 24
tower 2 x      = 2^(2^3) = 2^8 = 256
```

OK at `r = 1, x = 3` (24 ≤ 256). But at `r = 1, x = 2, v 0 = 2`:

```text
v 0 · tower 1 x = 2 · 4 = 8
tower 2 x      = 2^4 = 16
```

OK. Now try `r = 0, x = v 0 = 3`:

```text
v 0 · tower 0 x = 3 · 3 = 9
tower 1 x      = 2^3 = 8
```

**9 > 8.** The identity fails at `r = 0` for `x = v 0 = 3`.

The existing lemma in `GebLean/Utilities/Tower.lean:101-117`
discharges a related but **`+ 2`** form:

```text
theorem mul_tower_le_tower_add_two {k m : ℕ} (hm : 2 ≤ m) :
    m * tower k m ≤ tower (k + 2) m
```

This says `m · tower k m ≤ tower (k + 2) m` (under `m ≥ 2`),
not `tower (k + 1) m`. So the increment that the proof
infrastructure already supports is `+ 2`, not `+ 1`.

The spec's `r_f + 1` recipe at bsum is in conflict with the
only known Tower-level lemma that has a chance of discharging
it. Either:

1. The bsum increment must be `r_f + 2` (matching
   `mul_tower_le_tower_add_two`), in which case the table is
   wrong by 1.
2. A new Tower-level lemma `m · tower k m ≤ tower (k + 1) m`
   under stronger conditions must be proved, but per the
   counterexample at `r = 0` this is false in general.

Either way the spec table as written cannot be discharged. The
prompt explicitly flags this with: "Does the Nat identity
`v 0 · tower r x ≤ tower (r+1) x` actually hold for the relevant
range?" — the answer is no.

This is a blocker: the recipe at bsum (and downstream at bprod,
which inherits one level of this load) is mis-stated by at least
one tower level.

## Serious

### S1. `Finset.univ.sup` likely breaks axiom budget

§11 anticipates `[propext, Quot.sound]` for `maxOver`, its
interp lemma, and `boundExprK_interp`. But `vMax` is
`(Finset.univ : Finset (Fin a)).sup v` — `Finset` and
`Finset.sup` are built on `Multiset`, which is `Quot` over
`List.Perm` and uses lattice infrastructure that frequently
pulls `Classical.choice` transitively in non-decidable lattices,
or for set-theoretic existence in `Finset.fold`.

§4.3, §6.1, §6.3 all chain `boundExprK_interp` /
`boundExprK_dominates` through `vMax`. The axiom audit will
likely surface `Classical.choice` at every theorem that touches
`vMax` after `simp` normalisation hits `Finset.sup_le` or
`Finset.le_sup`.

The spec must either:

1. Verify (now, not later) that `Finset.univ.sup` on `Fin a → ℕ`
   stays `[propext, Quot.sound]`-only after `simp` exposure —
   evidence required.
2. Substitute the project's constructive `Fin.maxOfNat` (defined
   at `GebLean/LawvereKSim.lean:106`) and accept that `vMax`
   is *not* reused; T4 introduces its own constructive maximum.

The spec at present punts on this. Given the project's
constructive-only rule, the burden is on the spec to demonstrate
the budget holds.

### S2. §6.1 `if i = 0` on `Fin 2` not idiomatic Lean

§6.1 lines 369-378:

```lean
def boundExprK : {a : ℕ} → ERMor1 a → KMor1 a := fun e =>
  let p := boundExprK_params e   -- (r_e, offset_e)
  KMor1.comp
    (KMor1.pow2_iter p.1)
    (fun _ : Fin 1 =>
      KMor1.comp KMor1.add
        (fun i : Fin 2 =>
          if i = 0 then KMor1.maxOver a
                   else KMor1.natK' a p.2))
```

`if i = 0` on `i : Fin 2` requires `DecidableEq (Fin 2)`, which
exists in Lean core, but the test `i = 0` with `0 : Fin 2`
introduces a `DecidableEq` instance lookup and produces a less
ergonomic elaboration than the standard `match i with | 0 => …
| 1 => …` form used elsewhere in the codebase (e.g., `branches_j`
in `KSimURMSimulator.lean:399` uses `if i.val = j.val` — the
`.val` lift). The codebase pattern is `match` over `Fin n` for
small `n`, or `if i.val = c` if a numeric comparison is needed.

Worse: `if i = 0` where `0 : Fin 2` elaborates against
`DecidableEq (Fin 2)`, which (at least in older mathlib) pulls
through `Nat.decEq` and is constructive — but in some mathlib
states the instance was replaced with one routing through
`Fintype.decidableEq`, which is `Classical`-tainted. This needs
verification.

The recommendation is to rewrite to `Fin.cases` /
`Fin.lastCases` or a `match`, matching the rest of the codebase.

### S3. §7.1 `numInputs = a` is a type identity, not a T2 invariant

§7.1 lines 436-437:

> `simulate (compileER e) : KMor1 ((compileER e).numInputs + 1)`,
> and `(compileER e).numInputs = a` by T2's compiler
> invariants.

`compileER` has signature (Compiler.lean:1590):

```lean
def compileER {a : ℕ} (e : ERMor1 a) : URMProgram a
```

i.e., `URMProgram a`. The structure `URMProgram` is
arity-indexed (`URMProgram (numInputs : ℕ)`, see
`ZeroTestURM.lean:122`), so `(compileER e).numInputs = a`
holds **definitionally by type**, not via a separate "T2
invariant" theorem. The spec's phrasing implies the existence of
a theorem to invoke at proof time; there is none, and none is
needed.

This is a minor mathematical mis-statement but a serious one
for plan-writing: a downstream task that says "invoke T2's
`numInputs` invariant" will not find such a lemma. The wording
must be tightened to "by the type signature of `compileER`".

### S4. Proof outline elides `comp`-recursion structural issue

§4.3 says:

> Proof: structural induction on `e`. Atom cases (...) close via
> `omega` … Inductive cases close via `Nat.tower_mono`-style
> lemmas …

Structural induction on `ERMor1` produces, in the `comp f gs`
case, two inductive hypotheses:

1. `IH_f : compileER_runtime f w ≤ tower r_f (vMax w + offset_f)`
   for *every* `w`.
2. `IH_gs i : compileER_runtime (gs i) v ≤ tower r_{gs i} (vMax v + offset_{gs i})`.

To conclude
`compileER_runtime (comp f gs) v ≤ tower r_e (vMax v + offset_e)`,
the proof must bound

```text
glue + compileER_runtime f inner + 2
```

where `inner i = (gs i).interp v`. The `glue` part is a sum
over `compileER_runtime gs_i v` (covered by IH_gs); the
`compileER_runtime f inner` part requires IH_f at the
**non-trivially-bounded** vector `inner`. Bounding `vMax inner`
requires a *separate* bound on `(gs i).interp v` — an ER value
bound. The spec carries no such bound and no plan to introduce
one. The only available value bound in the codebase is
`KMor1.majorize_by_A_two_iter` (for K-side, not ER-side), and
on the ER side the bound family is `A_two_iter` / `tower` via
`ERAMajorants.lean` — but the spec does not state how to invoke
it.

This is a serious gap in the proof outline (and is linked to
B1: the recipe needs to include the value-side tower height
contribution, not just the runtime-side).

### S5. bsum/bprod side condition does not discharge the identity

§4.2 line 230:

> `v 0 · tower r x ≤ tower (r+1) x`
> (valid when `v 0 ≤ x = vMax v + offset`)

`bsum f` has type `ERMor1 (k+1) → ERMor1 (k+1)` (from
`LawvereER.lean:53-54`). The `v 0` here is the iteration bound
extracted from the **first slot** of `v : Fin (k+1) → ℕ`. The
constraint `v 0 ≤ vMax v + offset` is *always* true since
`v 0 ≤ vMax v ≤ vMax v + offset`. So as a *side condition* on the
inequality, this is trivial.

But that is not what the spec needs. As B3 shows, the identity
is *false* — the side condition `v 0 ≤ x` is insufficient. The
spec presents the side condition as if it discharged the
identity; it does not. This is a serious mis-statement
masquerading as a proof sketch.

### S6. §6.2 rejection of augmented-arity is mathematically wrong

§6.2 lines 387-391:

> **Augmented-arity** (`pow2_iter r ∘ maxOver (a+1) ∘
> Fin.cons (natK' 0 offset) projections`): would compute
> `Nat.max offset (vMax v)` rather than `vMax v + offset`;
> loses tightness and breaks the bound table when offset >
> vMax v.

The claim that this "breaks the bound table when offset >
vMax v" is wrong. We have

```text
Nat.max offset (vMax v) ≥ vMax v   (always)
Nat.max offset (vMax v) ≥ offset    (always)
Nat.max offset (vMax v) ≤ vMax v + offset (always)
```

Therefore
`tower r (Nat.max offset (vMax v)) ≤ tower r (vMax v + offset)`
(by `tower_mono_right` from `Tower.lean:42`). The
augmented-arity form is *strictly tighter or equal* — never
larger. If the table is discharged by `tower r (vMax v +
offset)`, it is *a fortiori* discharged by the smaller value
`tower r (max offset (vMax v))`.

The spec's claim that the augmented-arity form "breaks the
bound table" is the opposite of what holds. The legitimate
reason to prefer `vMax v + offset` over `max(offset, vMax v)`
might be *cosmetic mirroring of the kToER side* (the comp /
simrec offset of `KMor1.majorize` adds offsets too), or a
desire to keep the proof shape symmetric — but it is not
"tightness".

Either the spec's stated reason is wrong (and a correct one
needs to be substituted), or the alternative was rejected on
sound grounds that the spec does not articulate.

### S7. AXIOM\_ALLOW deferral defeats the spec gate

§11:

> `[propext, Classical.choice, Quot.sound]` with AXIOM\_ALLOW
> comments per `.claude/rules/lean-coding.md` § Accepted
> exceptions, anticipated at: `boundExprK_params_dominates`
> (bsum/bprod cases, via `Fin.lastCases_castSucc` reached
> through `compileER_runtime`'s `Fin.cons`/`Fin.tail`
> manipulation) …

The spec gates implementation but defers a key axiom-profile
question to implementation. Per the project's adversarial-review
process (CLAUDE.md § Phase-driven workflow), specs are
adversarially reviewed *before* the plan begins; the spec is
expected to be definite about what `Classical.choice` is paid
for and where. Deferring "to be confirmed at implementation time"
is a process violation — discovered axiom dependencies during
implementation are too-late information for the adversarial
review.

The spec must either:

1. Sketch the exact `simp` chains that would surface
   `Fin.lastCases_castSucc` and demonstrate (by code excerpt)
   that the chain is unavoidable.
2. Commit to no Classical exposure and propose a path (e.g.,
   pattern-match avoidance of `Fin.cons`) to honour that
   commitment.

The current shape is "we might need an exception, we'll see" —
not an acceptable spec position under project rules.

### S8. `comp` `v_total = Σ v i` is not absorbed by `vMax`

§4.2 table at line 215 abbreviates the `comp` shape as
"`Σ_i (compileER_runtime gs_i + …) + …`". Examining
`Compiler.lean:1729-1737`, the actual shape is:

```text
let v_total : ℕ := ((List.finRange a).map v).foldl (· + ·) 0
let glue : ℕ :=
  ((List.finRange k).map
    (fun i => compileER_runtime (gs i) v
      + 4 + 5 * inner i + 9 * v_total + 2 * a)).foldl (· + ·) 0
```

`v_total = Σ_{i:Fin a} v i ≤ a · vMax v`. This is not
absorbed by `vMax v + offset`: a sum of `a` slots is `a` times
the max in the worst case. To absorb `a · vMax v` into
`tower r_e (vMax v + offset)`, you need a multiplicative-by-`a`
step, which itself uses something like
`mul_tower_le_tower_add_two`, costing another `+ 2` in tower
height.

The spec's recipe table does not address `v_total`. Even if B1
were resolved (additive tower-height composition), the `comp`
case still has a multiplicative-by-`a` factor that is not
mentioned in either the table or the rationale bullets.

## Minor

### M1. Page-citation precision

§2.4 attributes "Tourlakis 0.1.0.9" for `A_2^r ∈ K^sim_2` — the
PDF shows §0.1.0.9 at page references in the index; verify the
exact page (the table uses page numbers in §2.1 — "pp. 18–22" —
but not in §2.4).

§2.1 says "Lemma 0.1.0.42 — per-constructor URM runtime". The
PDF (p. 18) lists this as a Lemma, but the spec also describes
"For `n ≥ 2`, every `f ∈ E^n` is URM-computable within time
`t_f ∈ E^n`. Proof by induction over E^n", which is the
*statement* of 0.1.0.42, not the per-constructor URM runtime
table — there is no such table in 0.1.0.42; the URM
constructions are sketched in pp. 19–21 (initial functions on
p. 19, substitution on p. 20, bounded recursion on p. 21). The
heading is slightly misleading.

### M2. §5.2 `maxOver 0` left "or whatever"

§5.2 line 313:

> `maxOver 0 = KMor1.natK 0` (or whatever the arity-0
> constant-0 surface is in KArith; matches
> `vMax (v : Fin 0 → ℕ) = 0`).

`KArith.lean` exposes `KMor1.natK n` (`KArith.lean:310`-ish)
which gives a constant `c` at arity `n`; the spec should commit
to the actual surface (`KMor1.natK 0 0` or `KMor1.zero` of
arity 0?). The "or whatever" wording is fuzzy for a spec.

### M3. §3 `natK'` arity is implicit

§3 item 3 line 165:

> **`boundExprK : ERMor1 a → KMor1 a`** assembled from
> `pow2_iter`, `maxOver`, `natK'`, and `add`

`KMor1.natK' n c : KMor1 n` (from `KArith.lean:310`) — accepts
arity `n` and produces a constant `c` morphism at that arity.
§6.1's pseudocode uses `KMor1.natK' a p.2` — consistent. No issue
once read in context. M3 is just to flag that §3's bullet leaves
the arity implicit, where being explicit would aid the plan.

### M4. `boundExprK_params` mixes camelCase and snake\_case

The mathlib naming guide (`naming.html`) prescribes
`lowerCamelCase` for `def` and `snake_case` for `Prop`-valued
`theorem`/`lemma`. `boundExprK_params` is a `def` (returns
`ℕ × ℕ`) but uses a `snake_case` underscore separator.
`boundExprKParams` would be the conforming form. The spec uses
the snake form throughout; the plan will inherit this and a
later golf step will be required to bring it into line.

`boundExprK` similarly: `def boundExprK` is fine (camel), but
its mixed-case successor `boundExprK_dominates` (a `theorem`,
snake_case) is fine, and `boundExprK_params` (a `def`,
snake_case) is not. Either rename the `def` or accept the
deviation; the spec should state which.

### M5. Module docstring contents not pre-specified

The three new files (`RuntimeBound.lean`, `ErToK.lean`,
`ErToKFunctor.lean`) per §9 do not list their required
module-docstring contents. `lean-coding.md` requires
`/-! ... -/` with sections (title, summary, main definitions,
main statements, references, tags). Spec convention elsewhere
(e.g., the T3 spec) pre-specifies these so the plan can
verify them. Not blocking but should be added to §9.

### M6. §15 references — page citations not uniform

§15 lists §0.1.0.27, §0.1.0.37, §0.1.0.42, §0.1.0.43, §0.1.0.44
but does not include page numbers in the reference list.
Elsewhere (§2.1) page numbers are given. Make the citation
form uniform.

### M7. §4.2 "small constant" has no numeric ceiling

§4.2 uses "small constant" for the offset on succ, proj, sub.
The literature contract per the spec is the "recipe shape"; the
concrete constants are "implementation-flexible". This is fine,
but a small constant is mathematically vacuous as a number — it
should be at least bounded (e.g., "≤ 100" or "single-digit
multiple of the additive constant in the per-template
shape"). Otherwise an implementer who chooses
`offset_succ = 2^32` is still within the spec's letter.

### M8. §10 dependency DAG ASCII layout misleading

§10 lines 553-559:

```text
              RuntimeBound.lean (new)
                          │
                          ▼   ← T3 KSimURMSimulator.lean
                  ErToK.lean (new)
                          │
                          ▼   ← T2 Compiler.lean
              ErToKFunctor.lean (new)
```

The arrows indicate import direction (downward), and the
side-arrows indicate "this also imports". `ErToK.lean` imports
T2's `Compiler.lean` — but the side-arrow appears under
`ErToK.lean` pointing to `ErToKFunctor.lean`, which is confusing
ASCII layout. The DAG would read more clearly if all imports of
each file were grouped on its own row.

## Methodology

Sources consulted:

- Spec under review:
  `docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`.
- Tourlakis 2018,
  `.claude/docs/arithmetic-hierarchies/PR-complexity-topics.pdf`,
  pp. 15–22 (§0.1.0.36–§0.1.0.44).
- T2 compiler runtime:
  `GebLean/LawvereERKSim/Compiler.lean` lines 1722–1770
  (`compileER_runtime`) and line 1590 (`compileER`).
- T3 simulator surface:
  `GebLean/Utilities/KSimURMSimulator.lean` (full file).
- kToER majorization template:
  `GebLean/LawvereKSimMajorization.lean` lines 40–80
  (`vMax` definition and private API), 614–671
  (`KMor1.majorize`).
- Tower lemmas:
  `GebLean/Utilities/Tower.lean` (full file: confirmed
  `mul_tower_le_tower_add_two` increments by 2, not 1;
  `tower_comp` for nested-tower absorption).
- ER constructors and value semantics:
  `GebLean/LawvereER.lean` (constructors at lines 38–56,
  `natBSum`/`natBProd` at 61–67).
- URMProgram structure:
  `GebLean/Utilities/ZeroTestURM.lean` line 122
  (`URMProgram` is arity-indexed; `numInputs = a` is a
  type-level identity).
- KArith primitives:
  `GebLean/Utilities/KArith.lean` lines 44–561
  (`add`, `cond`, `monus`, `eq`, `pow2`, `natK'`).
- Constructive `Fin.maxOfNat`:
  `GebLean/LawvereKSim.lean` line 106.
- Markdownlint:
  `markdownlint-cli2` against the spec — 0 errors at review
  time (cf. project rule
  `.claude/rules/markdown-writing.md`).
- Mathlib upstream guides (re-fetched per CLAUDE.md):
  style.html, naming.html, doc.html, commit.html.

Tactics used:

- Cross-reference of the spec's per-constructor recipe table
  against the actual `compileER_runtime` body, term by term.
- Hand-computation of the bsum identity at small `(r, x, v 0)`
  values to find counterexamples (B3).
- Re-reading of `Tower.lean` to identify the available
  Nat-level lemma family and the increment they actually
  support (`+2`, not `+1`).
- Searched for `vMax` declarations to confirm scope (B2).
- Searched for `Finset.sup` exposure in `vMax`'s definition
  (S1).
- Checked `compileER`'s type signature to verify whether
  `(compileER e).numInputs = a` is a type-level identity or a
  theorem (S3).
- Compared `KMor1.majorize`'s comp recipe (uses `+`) against
  the spec's `Nat.max` recipe (B1).
