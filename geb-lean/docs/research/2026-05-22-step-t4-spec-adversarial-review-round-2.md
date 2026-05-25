# T4 spec adversarial review — round 2

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary](#summary)
- [Round-1 fix verifications](#round-1-fix-verifications)
  - [B1 fix verification](#b1-fix-verification)
  - [B2 fix verification](#b2-fix-verification)
  - [B3 fix verification](#b3-fix-verification)
  - [S1 through S8 fix verification](#s1-through-s8-fix-verification)
- [Residual blockers](#residual-blockers)
  - [B1'. §8 functor lift omits the multi-output passage](#b1-8-functor-lift-omits-the-multi-output-passage)
  - [B2'. `bprod` increment `+ 3` is too tight for the runtime](#b2-bprod-increment--3-is-too-tight-for-the-runtime)
  - [B3'. `Fin.maxOfNat` signature mismatch with all call sites](#b3-finmaxofnat-signature-mismatch-with-all-call-sites)
- [Residual serious](#residual-serious)
  - [S1'. `tower_comp` does not absorb the inner `+ offset_f` term](#s1-tower_comp-does-not-absorb-the-inner--offset_f-term)
  - [S2'. `comp` `+ 2` extra increment rationale (b) is not a concrete lemma](#s2-comp--2-extra-increment-rationale-b-is-not-a-concrete-lemma)
  - [S3'. Atom rationale claims "two applications" where one suffices](#s3-atom-rationale-claims-two-applications-where-one-suffices)
  - [S4'. `Fin.maxOfNat_i` is an undefined notation](#s4-finmaxofnat_i-is-an-undefined-notation)
  - [S5'. `tower_pow_le_tower_add_three` not cited where applicable](#s5-tower_pow_le_tower_add_three-not-cited-where-applicable)
- [New issues introduced by round-1 fixes](#new-issues-introduced-by-round-1-fixes)
  - [N1. §6.1 `match | 0 => … | 1 => …` deviates from project pattern](#n1-61-match--0----1---deviates-from-project-pattern)
  - [N2. Conjunctive bound theorem name](#n2-conjunctive-bound-theorem-name)
- [Minor](#minor)
  - [M1. §8.1 `obj n := n` is the wrong target type](#m1-81-obj-n--n-is-the-wrong-target-type)
  - [M2. §11 AXIOM_ALLOW underscore-escapes inconsistent](#m2-11-axiom_allow-underscore-escapes-inconsistent)
  - [M3. §4.2 table column 3 mis-labels `value shape` for `proj`](#m3-42-table-column-3-mis-labels-value-shape-for-proj)
  - [M4. Round-1 M1, M2, M3, M5, M6, M7, M8 deferral](#m4-round-1-m1-m2-m3-m5-m6-m7-m8-deferral)
- [Methodology](#methodology)

<!-- END doctoc -->

## Summary

3 blockers, 5 serious, 2 new, 4 minor.

## Round-1 fix verifications

### B1 fix verification

Round-1 B1 reported that the `comp` recipe used `Nat.max` over the
gs-runtime exponents, which is incorrect because the nested tower
substitution requires *additive* exponents
(`tower_comp` gives an additive composition law).

The revised §4.2 table line 233 now reads

> `comp f gs` | … | `mu_f + Fin.maxOfNat (fun i => mu_{gs i}) + 2`

— additive in `mu_f` and the gs-max, consistent with the
direction `KMor1.majorize` takes
(`LawvereKSimMajorization.lean:643`).
**Direction-of-recursion**: fixed.

**Quantitative correctness — the `+ 2`**: this is not adequately
justified. The spec's rationale at §4.2 lines 264–272 cites
(a) `mul_tower_le_tower_add_two` (one application for the
`v_total ≤ a · Fin.maxOfNat v` factor — accepting this) and
(b) an unspecified "additional level above the value bound",
which is not a concrete Tower lemma and does not correspond to
any lemma in `GebLean/Utilities/Tower.lean`. The +2 may or may
not suffice; the spec presents no proof. **Quantitative
rationale**: partially fixed (rationale (a) discharges, (b)
hand-wavey). Status: **partially fixed**.

See **S2'** for the (b) issue and **S1'** for a separate
obstruction in the `tower_comp` argument that the rationale
elides.

### B2 fix verification

Round-1 B2 reported that `vMax` is `private` in
`LawvereKSimMajorization.lean` (`:43-44`) and cannot be reused
from a new file. The fix replaces `vMax` with `Fin.maxOfNat`
(introduced in T3 at `GebLean/LawvereKSim.lean:106`), which is
public and constructive.

`Fin.maxOfNat` is confirmed to exist at the cited site:

```lean
def Fin.maxOfNat (n : ℕ) (f : Fin n → ℕ) : ℕ :=
  Fin.foldr n (fun i acc => max acc (f i)) 0
```

Public, no `private` modifier, depends only on `Fin.foldr`
(Lean-core, axiom-clean). Companion lemmas
`Fin.le_maxOfNat` and `Fin.maxOfNat_le` are also public and
land at lines 115 / 131. The `Fin 0 → ℕ` case gives 0 (foldr
base case is `0`). **Reusability**: fixed.

But: see **B3'** below — the spec's claimed type signature is
**wrong** about which arguments are implicit, and every call
site in the spec is therefore mistyped.

### B3 fix verification

Round-1 B3 reported that the bsum recipe's `+ 1` increment is
underspecified: the only available Tower lemma is
`mul_tower_le_tower_add_two` (`+ 2`).

The revised §4.2 table now uses `+ 2` for bsum and `+ 3` for
bprod. The rationale at lines 282–296 cites
`mul_tower_le_tower_add_two` directly for the bsum sum.

**bsum**: `+ 2`. The argument is `v 0 · tower mu_f m ≤ m ·
tower mu_f m ≤ tower (mu_f + 2) m` via
`mul_tower_le_tower_add_two` and `v 0 ≤ m`. The hypothesis
`m ≥ 2` of `mul_tower_le_tower_add_two` is dischargeable
because all spec offsets are `≥ 3`. **bsum increment**:
verified correct.

**bprod**: `+ 3`. See **B2'** below. The `+ 3` increment
covers the *value* bound (via `tower_pow_le_tower_add_three`,
which the spec does not cite but which is available at
`Tower.lean:120`), but **not the runtime**: the runtime
contains `Σ_{i<v 0} 9·A_i·B_i` where `A_i · B_i ≤
natBProd (i+1) (...) ≤ tower (mu_f + 3) m`. Summing over `i`
gives a multiplicative factor of `v 0 ≤ m`, so the sum is
`≤ m · tower (mu_f + 3) m ≤ tower (mu_f + 5) m`. The `+ 3`
increment does **not** dominate the sum-of-products. Status:
**partially fixed (value OK; runtime under-counted)**.

### S1 through S8 fix verification

- **S1** (`Finset.univ.sup` axiom budget): fixed. The
  switch to `Fin.maxOfNat` removes any `Finset`/`Multiset`
  exposure on the T4 surface.
- **S2** (§6.1 `if i = 0` on `Fin 2`): fixed (now `match i
  with | 0 => … | 1 => …`). But the new form has its own
  small issue — see **N1**.
- **S3** (`numInputs = a` as a type identity): fixed. §7.1
  lines 565–569 now says "holds *definitionally by type*,
  not by a separate invariant theorem".
- **S4** (proof outline elides comp recursion): partially
  fixed. The conjunctive `boundExprKParams_dominates` at
  §4.3 addresses *why* a joint runtime + value bound is
  needed. But the proof outline at §4.3 still elides the
  `tower_comp` mechanics (see **S1'**).
- **S5** (bsum side condition does not discharge identity):
  fixed via the move to `+ 2` and explicit
  `mul_tower_le_tower_add_two` citation. The hypothesis
  `m ≥ 2` is now traceable to the offsets `≥ 3` in the table.
- **S6** (§6.2 augmented-arity rejection wrong): the
  revised §6.2 (lines 503–525) presents a different
  rationale — "the kToER-side `KMor1.majorize` carries an
  explicit `(r, offset)` pair whose offset is *added* to
  the max in the bound shape; the bsum/bprod increment
  proofs in §4 rely on `mul_tower_le_tower_add_two`, which
  is stated in terms of `m = Fin.maxOfNat v + offset` (an
  additive form)." This is a defensible reason (kToER-mirror
  pattern + Tower-lemma shape compatibility), not the
  earlier false "tightness" claim. **Fixed**.
- **S7** (AXIOM_ALLOW deferral defeats spec gate):
  partially fixed. §11 now lists three specific sites
  (`boundExprKParams_dominates` bsum + bprod cases;
  `erToK_interp`) and gives a concrete reason
  (`Fin.lastCases_castSucc` via simp on `Fin.cons`/`Fin.tail`).
  The reachability claim is plausible given T3's existing
  use of the same exception, but the spec does not
  *demonstrate* (excerpt of the chain) that the simp will
  reach that lemma at exactly those three sites. **Status:
  fix is acceptable but not airtight.**
- **S8** (`v_total = Σ v i` not absorbed by vMax): partially
  fixed. The revised §4.2 rationale (line 266) names
  `v_total = Σ v i ≤ a · Fin.maxOfNat v` and claims one
  application of `mul_tower_le_tower_add_two` absorbs it
  (using `a ≤ tower 0 a`). The concrete step is:
  `a · m ≤ m · m = m · tower 0 m ≤ tower 2 m` (when
  `a ≤ m`). The spec offsets give `offset_e ≥ 4·a + 8`, so
  `m = Fin.maxOfNat v + offset_e ≥ a`. Mechanism is sound;
  one application of `mul_tower_le_tower_add_two`. **Fixed.**

## Residual blockers

### B1'. §8 functor lift omits the multi-output passage

The spec's §8.1 (lines 622–627) defines

```lean
def erToKFunctor : LawvereERCat ⥤ LawvereKSimDCat 2 where
  obj n   := n
  map ⟦e⟧ := ⟦⟨erToK e, erToK_level e⟩⟧
```

The morphism component is presented as a quotient lift
of `erToK : ERMor1 a → KMor1 a`. But:

- `Hom n m` in `LawvereERCat` is `ERMorNQuo n m`
  (`LawvereERQuot.lean:153`), an equivalence class of
  multi-output `ERMorN n m` tuples — **not** a single
  `ERMor1`.
- `Hom n m` in `LawvereKSimDCat 2` is `KSimMor 2 n m`
  (`LawvereKSimQuot.lean:445-447`), a structure with
  `hom : KMorNQuo n m` and a depth-2 witness — **not** a
  single `KMor1`.

The existing reverse functor `kToERFunctor`
(`LawvereKSimER.lean:474`) handles this by operating
through `kToERN` (the multi-output variant), with
explicit `Quotient.liftOn` and `Quotient.sound` machinery
spanning ~95 lines (`kToERFunctor_map` at lines 384–402
plus the law proofs). The T4 spec contains no analogous
construction:

- No `erToKN : ERMorN n m → KMorN n m` is mentioned.
- The spec text never uses `ERMorN`, `KMorN`, `ERMorNQuo`,
  `KMorNQuo`, or `KSimMor` (verified via grep of the spec).
- The depth-witness component
  (`KMorNQuo.atDepth 2 (erToKN e)`) is alluded to as
  `erToK_level e`, but `erToK_level` is a level lemma on
  a *single* `KMor1`, not a depth witness on the
  multi-output `KMorNQuo`.

The spec's pseudo-Lean at §8.1 elides every interesting
type. The recipe of "via `erToK_interp` and quotient
`sound`" (line 644–648) does not describe how to traverse
the two quotient layers (ERMorN → ERMorNQuo and KMorN →
KMorNQuo) plus the depth structure on the K side.

This was not raised in round 1; on closer inspection it
is a residual blocker that round 1 missed.

### B2'. `bprod` increment `+ 3` is too tight for the runtime

The revised §4.2 sets `mu_e = mu_f + 3` for `bprod`. The
rationale at lines 290–296 covers the **value bound**:

```text
(tower mu_f m)^{v_0} ≤ 2^(v_0 · tower mu_f m)
                    ≤ 2^(tower (mu_f + 2) m)
                    = tower (mu_f + 3) m.
```

(Aside: this composite argument is reproducible by the
single lemma `tower_pow_le_tower_add_three`
(`Tower.lean:120`), which the spec does not cite.) But the
**runtime** for `bprod` (Compiler.lean:1753–1770) is

```text
40 + 10 * bound + Σ_{i < v 0} (perIter_f(i) + 9·A_i·B_i +
                                  4·A_i + 9·B_i + nRegs_f)
```

where `A_i := natBProd i (...)`, `B_i := f.interp ctx_f`.
Each `A_i · B_i ≤ Π_{j ≤ i} f.interp_j ≤ natBProd (v 0)
(...) ≤ tower (mu_f + 3) m` (by the value identity above).
Summing over `i < v 0`:

```text
Σ_{i < v 0} 9 · A_i · B_i ≤ v 0 · 9 · tower (mu_f + 3) m
                          ≤ m · tower (mu_f + 3) m
                          ≤ tower (mu_f + 5) m
```

by `mul_tower_le_tower_add_two`. The total runtime is
therefore `≤ tower (mu_f + 5) m`, not `tower (mu_f + 3) m`.
The recipe `mu_e = mu_f + 3` does **not** dominate the
runtime.

The same issue applies, more weakly, to `bsum`: the spec's
`+ 2` for bsum covers both runtime and value because each
`perIter(i) ≤ tower mu_f m` directly and the outer
`v 0`-sum costs one `+ 2`. For `bprod`, the *interior*
contains an *additional* `Π`-factor whose value sits at
`mu_f + 3`, and then the outer `v 0`-sum costs another
`+ 2`, giving `mu_f + 5`.

The conjunctive proof `boundExprKParams_dominates` at §4.3
will not close under structural induction on `bprod` with
`mu_e = mu_f + 3`.

(Note: if the spec intends `mu_f + 5`, the bsum/bprod
literature-fixed contract at line 304 lists `+ 2` and
`+ 3` as the literature-fixed shapes — making this fix
non-trivial, since changing the increment is what the spec
explicitly forbids.)

### B3'. `Fin.maxOfNat` signature mismatch with all call sites

The actual signature
(`GebLean/LawvereKSim.lean:106`) is

```lean
def Fin.maxOfNat (n : ℕ) (f : Fin n → ℕ) : ℕ
```

with `n` **explicit**, not implicit. The spec at line 424
states:

> `Fin.maxOfNat : {n : ℕ} → (Fin n → ℕ) → ℕ`

— with `{n : ℕ}` (implicit). This is **wrong**: the actual
definition takes `n` as an explicit positional argument.

Every spec call site uses the implicit form:

- Line 158: `Fin.maxOfNat v`
- Line 225: `Fin.maxOfNat v`
- Line 233: `Fin.maxOfNat (fun i => mu_{gs i})` (also
  missing the index bound)
- Line 240–243: `Fin.maxOfNat v`
- Line 266: `a · Fin.maxOfNat v`
- Line 320: `Fin.maxOfNat : (Fin n → ℕ) → ℕ` — uses an
  ambiguous form
- Lines 421, 506–509: `Fin.maxOfNat v`

Every call site as written would fail elaboration; each
needs an explicit `n` argument
(`Fin.maxOfNat _ v` or `Fin.maxOfNat a v`).

This is a documentation-level blocker: the spec presents
an interface that does not exist as stated, and every
type-signature-bearing pseudo-Lean block in §4 would not
compile.

The existing `simulate_level` at
`KSimURMSimulator.lean:978` confirms the call shape used
elsewhere:

```lean
change max (Fin.maxOfNat _ (fun i => (baseFamily P i).level))
           (Fin.maxOfNat _ (fun i => (stepFamily P i).level))
```

— with the explicit `_` placeholder.

## Residual serious

### S1'. `tower_comp` does not absorb the inner `+ offset_f` term

The spec at line 263 claims:

> `tower mu_f (tower mu_{gs} m + offset_f) ≤ tower (mu_f +
> mu_{gs}) m` (via `tower_comp` in `Tower.lean`)

`Tower.tower_comp` (`Tower.lean:51`) states:

```lean
theorem tower_comp (j k x : ℕ) :
    tower j (tower k x) = tower (j + k) x
```

An **equality**, requiring the form `tower j (tower k x)`
exactly — with **no additive term inside** (`+ offset_f`).
The spec's purported chain has `tower mu_f (tower mu_{gs}
m + offset_f)`; this does *not* match the lemma's
left-hand side. To use `tower_comp` you must first absorb
the `+ offset_f` into the inner tower
(e.g., `tower mu_{gs} m + offset_f ≤ tower (mu_{gs} + 1) m`
when `offset_f ≤ tower mu_{gs} m`, which needs another
sub-argument and another tower-level increment).

The spec's `comp` proof outline does not describe this
absorption. The `+ 2` increment in the recipe might
absorb this in principle, but the spec does not say so,
and the rationale (b) at line 269–272 names an unrelated
"runtime needs additional level above value bound" reason
instead.

### S2'. `comp` `+ 2` extra increment rationale (b) is not a concrete lemma

§4.2 rationale (b) at lines 269–272:

> (b) the value bound's own composition, already captured
> by `mu_f + mu_{gs}`, but the runtime needs an additional
> level above the value bound.

This sentence is not a proof step. It does not name a
Tower lemma. It does not state what the "additional level"
arithmetic discharges. Read literally, it says "we add 1
because the runtime is greater than the value", but the
runtime is *not* a function of the value at a single
point; the runtime accounts for `compileER_runtime f
inner` (which IH bounds against the *value* bound), and
the value `f.interp inner` (also against the value bound),
plus glue. There is no clean "runtime vs. value gap" that
takes exactly one tower level.

If the `+ 2` for comp is really discharging two distinct
multiplicative factors (`v_total` factor at +2 *and*
`tower_comp` absorption at +1, totalling +3), then the
recipe is **under-stating by one**. If it is discharging
only the `v_total` factor (+2) and the `tower_comp`
absorption is folded into `mu_{gs}` somehow, the spec
should say so explicitly.

This is the same kind of hand-wavey rationale that S5
(round 1) was supposed to eradicate.

### S3'. Atom rationale claims "two applications" where one suffices

§4.2 lines 245–247:

> `10 · (Fin.maxOfNat v + offset) ≤ tower 2 (Fin.maxOfNat
> v + offset)` via two applications of
> `mul_tower_le_tower_add_two` from `Tower.lean:101` (each
> application costs `+ 2` per the lemma; one would suffice
> for the value side but two are needed for the runtime).

`mul_tower_le_tower_add_two` gives `m · tower k m ≤ tower
(k + 2) m`. With `k = 0` and `m ≥ 10` (the spec offsets
ensure `m ≥ 16`), one application gives
`m · m ≤ tower 2 m` (since `tower 0 m = m`). Then
`10 · m ≤ m · m ≤ tower 2 m`. **One application**, not
two. The spec's "two applications … one for the value, two
for the runtime" is incorrect arithmetic; the asymmetry is
unmotivated.

This is minor in mathematical impact (the right answer is
still `mu = 2` for atoms) but worrying as a calibration
signal: the spec's rationale paragraphs are not careful
about which Tower lemma application is needed.

### S4'. `Fin.maxOfNat_i` is an undefined notation

§4.2 line 260–261:

> `mu_g := Fin.maxOfNat_i mu_{gs i}` and
> `offset_g := Fin.maxOfNat_i offset_{gs i}`

§4.2 line 310–311:

> `Fin.maxOfNat_i` denotes constructive folding of a
> finite family of `ℕ` via `Fin.maxOfNat`-style induction

The introduced notation `Fin.maxOfNat_i` is not a Lean
identifier; it appears nowhere in the codebase. This is
the spec's informal shorthand for "fold via
`Fin.maxOfNat`", but the spec uses it inside what reads
like a recipe (line 260) and a table cell (line 233).

The intended Lean form, based on `KMor1.majorize`'s use
(line 637–642), is:

```lean
let r_g := Fin.foldr _ (fun i acc =>
             max acc (boundExprKParams (gs i)).1) 0
```

— a `Fin.foldr` chain, not a `Fin.maxOfNat` application
(since `Fin.maxOfNat` does not accept a folder argument).
This is the right idiom, and the spec should be explicit:
it is *defining* a new operation, not reusing
`Fin.maxOfNat`. Either:

1. Introduce a separate `def boundExprKMaxFamily` (or
   similar) and reference it.
2. Inline the `Fin.foldr` directly.
3. Generalise `Fin.maxOfNat` to fold any
   `Fin n → α`-shaped argument.

Pick one. The current text is informal in a way that the
implementer cannot translate.

### S5'. `tower_pow_le_tower_add_three` not cited where applicable

§4.2 line 290–294 describes the bprod value bound by
composing a Nat identity `T^k ≤ 2^(k · T)` with
`mul_tower_le_tower_add_two`. But the codebase already has
`Tower.tower_pow_le_tower_add_three`
(`Tower.lean:120-132`), proved with the same arithmetic,
that gives exactly `(tower k m)^m ≤ tower (k + 3) m` for
`m ≥ 2`.

The spec should cite this lemma directly and discharge
the value identity via a single named lemma application,
rather than open-coding the composite argument. The spec
also forgets that the project pre-supplies this lemma.

Note: this strengthens **B2'** above — the value bound
*is* clean (`tower_pow_le_tower_add_three` is right
there), but the spec's separate argument for the runtime
multiplied by another `v 0`-sum is what under-counts.

## New issues introduced by round-1 fixes

### N1. §6.1 `match | 0 => … | 1 => …` deviates from project pattern

The fix for round-1 S2 replaces `if i = 0` with

```lean
match i with
| 0 => KMor1.maxOver a
| 1 => KMor1.natK' a p.2
```

The existing codebase consistently uses the explicit-proof
form `match i with | ⟨0, _⟩ => … | ⟨1, _⟩ => …`:

- `KArith.lean:537-543` (`KMor1.condEq` over `Fin 4`),
- `KArith.lean:508-510` (`KMor1.eq` over `Fin 2`),
- `KSimURMSimulator.lean:128-133` (`KMor1.cond` over `Fin
  3`).

The `| 0 =>` form **may** elaborate (Lean's pattern
matcher recognises numeric literals against `Fin n`), but
it diverges from the established project pattern. The
plan-side cost is small (mechanical search-and-replace if
elaboration fails). Flag as a project-consistency
deviation, not a logic error.

### N2. Conjunctive bound theorem name

The spec at §4.3 (line 340) names the conjunctive theorem
`boundExprKParams_dominates`. This is a single
**theorem** whose conclusion is a Prop-valued conjunction
of two ≤ inequalities. Mathlib's naming conventions
(`naming.html`) suggest `_and_` or two separate theorems
joined later (e.g., `boundExprKParams_runtime_dominates`
plus `boundExprKParams_value_dominates`, both proved by
mutual induction). Either form is OK, but a single
conjunctive Prop is less reusable downstream than a pair
of named lemmas. Plan can reuse the conjunctive form
internally, then expose the two halves.

## Minor

### M1. §8.1 `obj n := n` is the wrong target type

§8.1 line 624:

```lean
  obj n   := n
```

`LawvereERCat = ℕ` and `LawvereKSimDCat 2 = ℕ` (by
`def`); both unfold to `ℕ`, so `obj n := n` typechecks by
definitional unfolding. But `n` on the left is bound at
`LawvereERCat` and on the right at `LawvereKSimDCat 2` —
there should be a cast (`OfNat`-based, e.g.,
`(n : LawvereKSimDCat 2)`) to make the dependence
explicit. Compare `kToERFunctor`'s `obj n := n`
(`LawvereKSimER.lean:476`) — same pattern, also relying
on def-unfolding. So spec is consistent with existing
code, but the practice is borderline; not strictly a bug.

### M2. §11 AXIOM_ALLOW underscore-escapes inconsistent

§11 uses `AXIOM\_ALLOW` (with escaped underscore) in some
places (lines 380, 712, 735, 742) and `AXIOM_ALLOW` (no
escape) in others. Probably stale escapes from a
markdownlint workaround. Project-wide convention should
be one or the other.

### M3. §4.2 table column 3 mis-labels `value shape` for `proj`

Table line 232: `proj i | 11 + 10·v i | v i | 2 | ≤ 16`.

For `proj i`, the value `e.interp v = v i ≤ Fin.maxOfNat
v`. The "value shape" column gives `v i`, which is
correct as a literal value but does not show that it is
bounded by `Fin.maxOfNat v` for the bound to discharge.
Trivial in the proof (any `v i ≤ Fin.maxOfNat v`); flag
for the plan-stage spelling.

### M4. Round-1 M1, M2, M3, M5, M6, M7, M8 deferral

Round-1's minor items M1 (page citations), M2
(`maxOver 0` definite-ness, "or whatever"), M3 (`natK'`
arity in §3), M5 (module docstring contents
pre-specification), M6 (uniform page citations in §15),
M7 ("small constant" numeric ceiling), M8 (§10 dependency
DAG ASCII layout) — the revised spec only partially
addressed these:

- M2 (`maxOver 0` definite-ness): fixed (now
  `maxOver 0 = KMor1.zero` definitely; §5.2 line 415).
- M3 (`natK'` arity): de facto handled by §6.1 pseudocode
  showing `KMor1.natK' a p.2`. **OK.**
- M7 (offset ceilings): fixed in the spec table
  (`≤ 16`, `≤ 24`, `4·a + 8`, `+ 32`, `+ 44`); concrete
  numeric ceilings.
- M1 (page-citation precision): not visibly changed.
- M5 (module docstring contents pre-specification): not
  visibly changed.
- M6 (uniform page citations): not visibly changed.
- M8 (§10 DAG ASCII layout): not visibly changed.

Flag for the plan stage; none of these block.

## Methodology

Sources consulted:

- Spec under review:
  `docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`,
  jj revision `88aa28bf`.
- Round-1 review:
  `docs/research/2026-05-22-step-t4-spec-adversarial-review-round-1.md`.
- T2 compiler runtime:
  `GebLean/LawvereERKSim/Compiler.lean`, lines 1590
  (`compileER`), 1716–1770 (`compileER_runtime`).
- T2 top-level correctness:
  `GebLean/LawvereERKSim/Top.lean`, lines 89–97
  (`compileER_runFor`).
- T3 simulator surface:
  `GebLean/Utilities/KSimURMSimulator.lean`, lines
  548 (`simulate`), 958–964 (`simulate_interp`),
  975–984 (`simulate_level`).
- Tower lemmas:
  `GebLean/Utilities/Tower.lean`, full file: confirmed
  `tower_comp` (line 51, equality form, no offset
  absorption), `mul_tower_le_tower_add_two` (line 101,
  `m · tower k m ≤ tower (k + 2) m`, requires `m ≥ 2`),
  `tower_pow_le_tower_add_three` (line 120,
  `(tower k m)^m ≤ tower (k + 3) m`, requires `m ≥ 2`),
  `tower_mono_right` (line 42), `self_le_tower`
  (line 27).
- kToER majorize template:
  `GebLean/LawvereKSimMajorization.lean`, lines 614–671
  (`KMor1.majorize`).
- ER inductive:
  `GebLean/LawvereER.lean`, lines 36–57
  (`ERMor1` constructors); `comp` at line 47–48 takes
  `{k n : ℕ}` plus `f : ERMor1 k` and
  `g : Fin k → ERMor1 n`, producing `ERMor1 n` —
  consistent with spec's notation up to argument naming.
- Constructive `Fin.maxOfNat`:
  `GebLean/LawvereKSim.lean`, lines 106–141; **`n`
  explicit** in the signature.
- LawvereERCat quotient:
  `GebLean/LawvereERQuot.lean`, lines 139–160 (`Hom n
  m := ERMorNQuo n m`, multi-output).
- LawvereKSimDCat quotient:
  `GebLean/LawvereKSimQuot.lean`, lines 442–493
  (`KSimMor` structure and category instance).
- kToERFunctor (the reference pattern):
  `GebLean/LawvereKSimER.lean`, lines 384–479
  (`kToERFunctor_map`, `kToERFunctor`).
- KArith primitives:
  `GebLean/Utilities/KArith.lean`, lines 44–561
  (`KMor1.add` at 111, `KMor1.cond` at 222,
  `KMor1.natK'` at 310, `KMor1.monus` at 464,
  `KMor1.eq` at 506, `KMor1.pow2` at 561) — confirmed
  arities, level facts (`add.level = 1`,
  `monus.level = 2`, `pow2.level = 2`,
  `natK'.level = 0`).
- Markdownlint:
  `markdownlint-cli2` on the spec — 0 errors at review
  time.
- Mathlib upstream guides (re-fetched per CLAUDE.md):
  `style.html`, `naming.html`, `doc.html`,
  `commit.html`.

Tactics used:

- Quantitative verification of B3 fix: re-derived bsum
  identity (verified `+ 2` correct) and bprod identity
  (found `+ 3` correct for value, **insufficient for
  runtime sum of products**, requiring `+ 5`).
- Signature-of-`Fin.maxOfNat` check: read the actual
  definition at `LawvereKSim.lean:106`, compared
  against the spec's claimed signature at line 424 —
  **mismatch** (spec says implicit `{n}`, code has
  explicit `n`).
- Functor type-check: traced `Hom n m` through
  `LawvereERCat` (`ERMorNQuo n m`) and
  `LawvereKSimDCat 2` (`KSimMor 2 n m` with depth
  witness); confirmed the spec's §8.1 pseudocode skips
  every quotient layer.
- Tower lemma re-check: confirmed that `tower_comp`'s
  statement is an equality with no offset inside, so
  the spec's `+ offset_f` term does not directly fit.
- Cross-reference of round-1 findings: each S1–S8
  verified against the revised spec text and
  classified as fixed / partially-fixed / not-fixed.
- Grep of spec text for multi-output references
  (`ERMorN`, `KMorN`, `ERMorNQuo`, `KMorNQuo`,
  `KSimMor`): **zero hits**, confirming §8 lifts only
  single-output `erToK` and elides the multi-output
  passage.
