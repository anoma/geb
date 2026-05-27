# T4 spec adversarial review — round 3

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary](#summary)
- [Round-2 fix verifications](#round-2-fix-verifications)
  - [B1' (multi-output functor) — fixed](#b1-multi-output-functor--fixed)
  - [B2' (bprod increment) — not fixed](#b2-bprod-increment--not-fixed)
  - [B3' (Fin.maxOfNat call sites) — fixed](#b3-finmaxofnat-call-sites--fixed)
  - [S1' (tower_comp absorption) — fixed](#s1-tower_comp-absorption--fixed)
  - [S2' (rationale b) — fixed](#s2-rationale-b--fixed)
  - [S3' (atom one application) — fixed](#s3-atom-one-application--fixed)
  - [S4' (Fin.maxOfNat_i undefined) — fixed](#s4-finmaxofnat_i-undefined--fixed)
  - [S5' (tower_pow_le_tower_add_three citation) — fixed](#s5-tower_pow_le_tower_add_three-citation--fixed)
  - [N1 (explicit-witness Fin match) — fixed](#n1-explicit-witness-fin-match--fixed)
- [Residual blockers](#residual-blockers)
  - [B2'(r3). bprod runtime increment `+ 5` still under-counts the constant 9](#b2r3-bprod-runtime-increment--5-still-under-counts-the-constant-9)
- [Residual serious](#residual-serious)
- [New issues](#new-issues)
  - [N1(r3). §8.2 pseudo-Lean contains a literal `sorry` and bracket-comment placeholders](#n1r3-82-pseudo-lean-contains-a-literal-sorry-and-bracket-comment-placeholders)
  - [N2(r3). comp `9·v_total` term needs explicit constant-absorption step](#n2r3-comp-9v_total-term-needs-explicit-constant-absorption-step)
- [Minor](#minor)
  - [M1(r3). AXIOM_ALLOW underscore-escape still inconsistent](#m1r3-axiom_allow-underscore-escape-still-inconsistent)
  - [M2(r3). §5.2 line 444 informal `Fin.maxOfNat (v : Fin 0 → ℕ) = 0` is ill-typed](#m2r3-52-line-444-informal-finmaxofnat-v--fin-0-%E2%86%92-%E2%84%95--0-is-ill-typed)
  - [M3(r3). erToKN_compat_extEq precondition shape vs setoid relation](#m3r3-ertokn_compat_exteq-precondition-shape-vs-setoid-relation)
- [Methodology](#methodology)

<!-- END doctoc -->

## Summary

1 blocker, 0 serious, 2 new (minor in severity), 3 minor. **NOT
CONVERGED.**

## Round-2 fix verifications

### B1' (multi-output functor) — fixed

The revised §8 (lines 652–770) now provides the full multi-output
passage:

- `erToKN : ERMorN n m → KMorN n m` (line 668) as componentwise
  application of `erToK`, with `ERMorN n m = Fin m → ERMor1 n`
  (LawvereER.lean:151) and `KMorN n m = Fin m → KMor1 n`
  (LawvereKSim.lean:65). Types match.
- `erToKN_interp` (line 671) and `erToKN_level` (line 676) are
  componentwise wrappers — type-correct.
- `erToKN_compat_extEq` (line 680) provides the well-definedness
  hypothesis for the quotient lift. The conclusion shape
  `∀ v j, (erToKN e₁ j).interp v = (erToKN e₂ j).interp v`
  matches what `kMorNSetoid` (LawvereKSimQuot.lean:21) requires
  for `Quotient.sound`.
- `erToKFunctor_map` (line 699) uses `Quotient.liftOn e` over
  `e : ERMorNQuo n m` and produces a `KSimMor 2 n m`.
- The depth-2 witness construction is indicated as
  `/- depth-2 witness via erToKN_level -/` — a placeholder. The
  intended construction is
  `Quotient.mk (kMorNQuoAtDepthSetoid 2 _) { rep := erToKN rec,
  rep_level := erToKN_level rec, rep_eq := rfl }`, which
  produces a `KMorNQuo.atDepth 2 (Quotient.mk _ (erToKN rec))`
  (LawvereKSimQuot.lean:372–397). The construction is feasible.
- `erToKFunctor_map_id` (line 726) and `erToKFunctor_map_comp`
  (line 734) mirror `kToERFunctor_map_id`/`_comp` shape from
  LawvereKSimER.lean:410–479. The proof obligations are
  discharged componentwise by `erToK_interp` (via
  `erToKN_compat_extEq` post-`congr_fun`).
- `erToKFunctor` (line 760) assembles into a
  `CategoryTheory.Functor LawvereERCat (LawvereKSimDCat 2)`.

Sanity-check on the lift: given `e₁ ≈ e₂` in `erMorNSetoid n m`
(`∀ ctx, e₁.interp ctx = e₂.interp ctx`), the two
`KSimMor 2 n m` values differ only in their `hom` field
(`depth_witness` is `Subsingleton` per
LawvereKSimQuot.lean:402–407). `KSimMor.ext`
(LawvereKSimQuot.lean:475) reduces equality to `hom`-equality,
i.e., `Quotient.mk _ (erToKN e₁) = Quotient.mk _ (erToKN e₂)`,
which `Quotient.sound` reduces to extensional K^sim equality of
the families, discharged by `erToKN_compat_extEq` after a
`congr_fun` (or `funext`) on the setoid relation's per-ctx
equality.

Status: **fixed** structurally. See N1(r3) for a minor
spec-form concern about the literal `sorry` placeholder.

### B2' (bprod increment) — not fixed

Round-2 reported `mu_f + 3` insufficient for bprod's runtime
sum `Σ_{i < v 0} 9·A_i·B_i` (Compiler.lean:1762–1769) and
suggested `mu_f + 5`. The revised §4.2 (line 241) now uses
`mu_f + 5`, with rationale at lines 308–321.

The new rationale (line 314–320) claims:

> The runtime, however, contains `Σ_{i<v 0} 9·A_i·B_i` where
> `A_i · B_i ≤ natBProd (i+1) (f.interp ∘ …) ≤ tower (mu_f + 3)
> m`; the outer sum introduces a `v 0 ≤ m` multiplicative
> factor, costing another `+ 2` by
> `mul_tower_le_tower_add_two`. Total runtime increment: `+ 5`.

This argument elides the constant factor `9` (and the additional
`4·A_i + 9·B_i` terms in Compiler.lean:1767). With the constant
included, the available Tower lemmas do not close the bound at
`tower (mu_f + 5) m`. See B2'(r3) below for the residual
analysis.

Status: **not fixed.** The fix as applied (the change from
`+ 3` to `+ 5`) is the same arithmetic error round-2's review
itself made — both elided the factor 9. The correct increment
is `+ 7` (see B2'(r3)).

### B3' (Fin.maxOfNat call sites) — fixed

The actual signature
`def Fin.maxOfNat (n : ℕ) (f : Fin n → ℕ) : ℕ`
(LawvereKSim.lean:106) has `n` **explicit**. The revised spec at
line 453 now correctly states
`Fin.maxOfNat : (n : ℕ) → (Fin n → ℕ) → ℕ`.

Call sites use `Fin.maxOfNat _ v` (e.g., lines 160, 231, 246–267,
283, 533) or `Fin.maxOfNat k (fun i => …)` (lines 233, 239, 266,
267). The `_` form lets Lean infer `n` from `v`'s type
(`Fin n → ℕ`), and the explicit `k` form supplies the arity.
Both forms compile.

Status: **fixed.**

### S1' (tower_comp absorption) — fixed

The revised §4.2 rationale for `comp` (lines 269–289) now spells
out the inner-offset absorption explicitly as a three-step
argument:

- Step (i): inner-offset absorption via
  `mul_tower_le_tower_add_two` on `X = tower mu_g m`, giving
  `X + offset_f ≤ tower (mu_g + 2) m` (after composing through
  `tower_comp` to fold back to base m).
- Step (ii): `tower_comp` gives
  `tower mu_f (tower (mu_g + 2) m) = tower (mu_f + mu_g + 2) m`.
- Step (iii): outer glue `9 · v_total ≤ m · m ≤ tower 2 m`,
  absorbed by margin into `tower (mu_f + mu_g + 4) m`.

`tower_comp` is invoked at exactly the place it applies (an
equality, no offset inside). Status: **fixed.** See N2(r3) for
a related sub-finding about the factor `9` in step (iii).

### S2' (rationale b) — fixed

The hand-wavey "additional level above value" wording from
round 2 is gone. The new rationale concretely names
`mul_tower_le_tower_add_two` for the `v_total ≤ a · Fin.maxOfNat
_ v` absorption (line 282–284, 391). Status: **fixed.**

### S3' (atom one application) — fixed

The revised §4.2 atom rationale (lines 252–253) now reads
"by a single application of `mul_tower_le_tower_add_two`",
correctly stating the chain
`10 · m ≤ m · m = m · tower 0 m ≤ tower 2 m`. Status: **fixed.**

### S4' (Fin.maxOfNat_i undefined) — fixed

The notation `Fin.maxOfNat_i` from round 2 is gone. Call sites
now use the explicit form `Fin.maxOfNat k (fun i => …)`
(lines 233, 239, 266, 267). Status: **fixed.**

### S5' (tower_pow_le_tower_add_three citation) — fixed

`tower_pow_le_tower_add_three` is now cited in the bprod
rationale (lines 309–313). Status: **fixed.**

### N1 (explicit-witness Fin match) — fixed

§6.1 (lines 516–518) now uses
`match i with | ⟨0, _⟩ => … | ⟨1, _⟩ => …`, matching the
explicit-witness pattern at KArith.lean:537–543 and
KSimURMSimulator.lean:128–133. Status: **fixed.**

## Residual blockers

### B2'(r3). bprod runtime increment `+ 5` still under-counts the constant 9

Compiler.lean:1753–1770 gives bprod's runtime as

```text
40 + 10 * bound + Σ_{i < bound} (perIter_f(i)
                                  + 9·A_i·B_i + 4·A_i + 9·B_i
                                  + nRegs_f)
```

where `bound = v 0`, `A_i = natBProd i (f.interp ∘ ctx_f)`,
`B_i = f.interp ctx_f`.

By IH on `f` (value bound), `B_i = f.interp ctx_f ≤ tower mu_f m`
(where `m = Fin.maxOfNat _ v + offset`). By
`tower_pow_le_tower_add_three`, `A_i = Π_{j < i} B_j ≤
(tower mu_f m)^m ≤ tower (mu_f + 3) m`. So
`A_i · B_i ≤ natBProd (i+1) ≤ tower (mu_f + 3) m`.

For the sum, set `T := tower (mu_f + 3) m`. Then

```text
Σ_{i < v 0} 9 · A_i · B_i ≤ 9 · v 0 · T ≤ 9 · m · T
```

(using `v 0 ≤ m`). To bound `9 · m · T` by some
`tower (mu_f + k) m`, the available Tower lemmas
(`Tower.lean:51, 101, 120`) give:

- `mul_tower_le_tower_add_two`: `m · tower j m ≤ tower (j + 2) m`
  (requires `m ≥ 2`).
- `tower_pow_le_tower_add_three`: `(tower j m)^m ≤ tower (j + 3) m`
  (requires `m ≥ 2`).
- `tower_comp`: `tower j (tower k x) = tower (j + k) x`
  (equality; inner argument is itself a tower).

To absorb the factor `9 · m`:
`9 · m · T ≤ m · m · T = m · (m · T) ≤ m · tower (mu_f + 5) m
≤ tower (mu_f + 7) m` (requires `m ≥ 9`, which the offset
≥ 44 ensures).

The spec's argument (line 314–320) elides the factor `9`,
treating `9 · v 0 · T ≤ m · T` directly. This step is
quantitatively invalid: it requires `9 · v 0 ≤ m`, i.e.,
`9 · (m − offset) ≤ m`, i.e., `8m ≤ 9·offset`. For arbitrary
`Fin.maxOfNat _ v`, this fails because `m` can be arbitrarily
large while `offset` is a fixed constant.

Concretely: take `v 0 = m − offset`. The required inequality
`9 · v 0 ≤ m` becomes `9(m − offset) ≤ m`, i.e.,
`m ≤ (9 · offset)/8`. With `offset = 44`, this gives
`m ≤ 49.5`. But there is no upper bound on `Fin.maxOfNat _ v`,
so `m` can exceed 49.5 freely.

Therefore the conclusion `Σ_{i < v 0} 9 · A_i · B_i ≤
tower (mu_f + 5) m` does not hold for arbitrary `v`; the
correct bound is `tower (mu_f + 7) m`.

The same constant-absorption issue affects the `4·A_i + 9·B_i`
sub-terms in Compiler.lean:1767, but those are dominated by the
`9·A_i·B_i` term (since `4·A_i ≤ 4·A_i·B_i + 4` when `B_i ≥ 1`,
and `B_i = 0` case is trivial; similarly for `9·B_i`).

**Resolution options:**

1. **Increase the increment to `+ 7`.** This is the smallest
   value the available Tower lemmas can certify.

2. **Add a `const_mul_tower_le_tower_add_two` (or similar)
   helper lemma** absorbing a constant factor `c ≤ m` with
   the same `+ 2` cost (`c · tower k m ≤ tower (k + 2) m`
   when `c ≤ m`). With offset ≥ 9 (which holds), this would
   keep `+ 5` viable. The lemma is provable from
   `mul_tower_le_tower_add_two` plus `c · T ≤ m · T`, but it
   does not currently exist in `Tower.lean`. Adding it would
   keep the spec's increment but expand the Tower-lemma
   surface T4 depends on (and requires updating §15 references
   and §4.2 rationale).

3. **Tighten the runtime bound differently** — e.g., absorbing
   the constant `9` into a different intermediate. Several
   approaches were checked (folding `9` into the `tower_pow`
   step, bounding via `(tower k m)^2`, etc.); all give `+ 6`
   or worse, so `+ 5` is unreachable without a new Tower
   lemma.

The blocker is quantitative-mathematical, not structural: the
fix is mechanical once the right increment (or supporting
lemma) is chosen.

Status: **residual blocker.** This is the same arithmetic
error round-2's review made; the author applied the requested
`+ 5` faithfully, but the request itself was incorrect.

## Residual serious

(none)

## New issues

### N1(r3). §8.2 pseudo-Lean contains a literal `sorry` and bracket-comment placeholders

§8.2 (line 707–708) presents the `Quotient.sound` step as

```lean
    (fun e₁ e₂ h => by
      /- KSimMor equality via depth-witness Quotient.sound +
         erToKN_compat_extEq -/
      sorry)
```

For a spec, illustrative pseudo-Lean is acceptable, but a
literal `sorry` in committed spec text reads as either
(a) a placeholder the implementer must replace, or (b) a
deferred-proof indicator. The companion forward functor
(`kToERFunctor_map` at LawvereKSimER.lean:384–402) provides
the analogous proof without `sorry`, in 19 lines. The spec
could either:

- Omit the proof body entirely (use `… proof …` ellipsis), or
- Include a concrete proof sketch mirroring the kToERFunctor
  shape (`apply Quotient.sound; intro v; funext i; apply
  erToKN_compat_extEq (...); exact congr_fun (h v) i` or
  similar).

The `/- depth-2 witness via erToKN_level -/` placeholder at
line 704 is the same kind of stub. Both are bracket-comment
elisions of constructions that are mechanically feasible but
not spelled out.

Severity: spec-form, not a logic error. Flag for the plan
stage. Not a blocker.

### N2(r3). comp `9·v_total` term needs explicit constant-absorption step

The comp rationale step (iii) (lines 283–289):

> Outer glue: `glue` includes `9 · v_total` where
> `v_total = Σ_i v i ≤ a · Fin.maxOfNat _ v ≤ m · m` (for
> `offset_e ≥ a`). One more application of
> `mul_tower_le_tower_add_two` gives `m · m ≤ tower 2 m ≤
> tower (mu_f + mu_g + 4) m`.

The chain elides the factor `9` (same elision pattern as
B2'(r3), but at a smaller scale). To bound `9 · v_total`:
`9 · v_total ≤ 9 · a · Fin.maxOfNat _ v ≤ 9 · m · m`. With
`9 ≤ m` (offset ≥ 9, which `4·a + 8` gives only for
`a ≥ ⌈1/4⌉ = 1` or with the `+ 8` term), `9 · m · m ≤
m · m · m`. Then `m · m · m = m · (m · m) ≤ m · tower 2 m ≤
tower 4 m`. So `9 · v_total ≤ tower 4 m`.

The spec's `+ 4` (the `mu_f + mu_g + 4` recipe at line 239)
absorbs this in the sense `tower 4 m ≤ tower (mu_f + mu_g + 4) m`
by `tower_mono_left`, and then the sum `glue + rt(f)` adds
one more `mul_tower_le_tower_add_two` (the spec's "final
mul_tower_le_tower_add_two on the outer side, absorbed by the
`+ 4` margin"). With slack accounting:
`tower 4 m + tower (mu_f + mu_g + 2) m
≤ 2 · tower (mu_f + mu_g + 4) m
≤ m · tower (mu_f + mu_g + 4) m
≤ tower (mu_f + mu_g + 6) m`.
This gives `+ 6`, not `+ 4`.

But the spec's `+ 4` is the *increment relative to*
`mu_f + mu_g`, not relative to `0`. The base after step (ii)
is `tower (mu_f + mu_g + 2) m`. To get the sum
`9·v_total + rt(f) + const ≤ tower (mu_f + mu_g + 4) m`, we
need each summand `≤ tower (mu_f + mu_g + 3) m` (then
sum-of-two costs one `+ 1`, absorbed by
`mul_tower_le_tower_add_two` into `+ 2` cleanly when summing
pairs).

`rt(f) ≤ tower (mu_f + mu_g + 2) m` from step (ii). The other
summand: `9 · v_total ≤ 9 · m · m`. Is
`9 · m · m ≤ tower (mu_f + mu_g + 3) m`?
For `mu_f + mu_g ≥ 1`: `9 m² ≤ m³ ≤ m · tower 2 m ≤ tower 4 m ≤
tower (mu_f + mu_g + 3) m` when `mu_f + mu_g ≥ 1`.
For `mu_f + mu_g = 0` (both atoms with mu = 0, i.e., zero
constants only): `9 m² ≤ tower 3 m = 2^(2^(2^m))`, true for
m ≥ 3 (huge).

So the comp `+ 4` is provable for the *common* cases but the
mu_f = mu_g = 0 boundary depends on `m ≥ 3` (i.e., offset ≥ 3,
which `4·a + 8 ≥ 8 ≥ 3` ensures). OK, the bound closes — but
the spec's rationale at lines 283–289 doesn't show the
constant-9 absorption explicitly, and the reader cannot
reconstruct it without the auxiliary `9 m² ≤ tower 3 m` step.

**Resolution:** Either (a) state the constant-9 absorption
step explicitly in the rationale, or (b) increase the
increment to `+ 6` so that an extra
`mul_tower_le_tower_add_two` discharges the constant
without bookkeeping.

This is the same kind of elided-constant issue as B2'(r3) but
the math here actually closes for comp (with margin to spare)
because the `9 · v_total` term is dominated by `m²` whereas
bprod's `9 · A_i · B_i` is dominated by `m · tower (mu_f + 3)
m` (which has the tower buying back the constant cost).

Severity: rationale-completeness issue, not a logic
error. Flag for the plan stage. Not a blocker.

## Minor

### M1(r3). AXIOM_ALLOW underscore-escape still inconsistent

Round-2 M2 flagged inconsistent escaping of `AXIOM_ALLOW`.
Spec still uses `AXIOM_ALLOW` (lines 399, 830) and
`AXIOM\_ALLOW` (lines 409, 840, 853, 860). markdownlint
passes both forms; project-wide convention should be one or
the other. Recommendation: drop the escape (use
`AXIOM_ALLOW` uniformly), matching the existing
`KSimURMSimulator.lean` annotation style.

### M2(r3). §5.2 line 444 informal `Fin.maxOfNat (v : Fin 0 → ℕ) = 0` is ill-typed

Line 444:

> `maxOver 0 = KMor1.zero` (arity-0 constant 0; matches
> `Fin.maxOfNat (v : Fin 0 → ℕ) = 0`).

The notation `Fin.maxOfNat (v : Fin 0 → ℕ)` is ill-typed:
`Fin.maxOfNat` takes two arguments `(n : ℕ) (f : Fin n → ℕ)`,
and `(v : Fin 0 → ℕ)` is a type ascription, not an
application. The intended form is `Fin.maxOfNat 0 v = 0` (or
`Fin.maxOfNat _ v = 0` with the type forcing `n = 0`). Trivial
to fix; flag for plan stage.

### M3(r3). erToKN_compat_extEq precondition shape vs setoid relation

§8.1 (line 680–688) defines `erToKN_compat_extEq` with
hypothesis `he : ∀ v j, (e₁ j).interp v = (e₂ j).interp v`. The
ERMorN setoid (`erMorNSetoid` at LawvereERQuot.lean:23–32)
relates `e₁ ≈ e₂` by `∀ ctx, e₁.interp ctx = e₂.interp ctx`,
where `e₁.interp ctx : Fin m → ℕ` (a function). The two shapes
are connected by `funext` / `congr_fun`:

```text
∀ ctx, e₁.interp ctx = e₂.interp ctx   (setoid)
∀ ctx, ∀ j, e₁.interp ctx j = e₂.interp ctx j   (after congr_fun)
∀ ctx, ∀ j, (e₁ j).interp ctx = (e₂ j).interp ctx   (by ERMorN.interp def)
```

The lift at §8.2 elides this step. The kToERFunctor analog at
LawvereKSimER.lean:384–402 uses `Quotient.exact h_eq` and
`congr_fun (hrel v') i'` to bridge; the T4 spec should
indicate the same bridging step (one line in the proof, but
not currently mentioned).

Severity: spec-completeness, not logic. Flag for plan stage.

## Methodology

Sources consulted:

- Spec under review:
  `docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`,
  jj revision `ba267073` on bookmark
  `feat/ertok-runtime-bound`.
- Round-2 review:
  `docs/research/2026-05-22-step-t4-spec-adversarial-review-round-2.md`.
- T2 compiler runtime:
  `GebLean/LawvereERKSim/Compiler.lean`, lines 1590, 1722–1770
  (bprod runtime confirmed to contain `9 * A_i * B_i`,
  `4 * A_i`, `9 * B_i` summands at lines 1762–1769).
- T3 simulator:
  `GebLean/Utilities/KSimURMSimulator.lean` (consumed; unchanged
  from round-2 review).
- Tower lemmas:
  `GebLean/Utilities/Tower.lean`, lines 51 (`tower_comp`),
  101 (`mul_tower_le_tower_add_two`),
  120 (`tower_pow_le_tower_add_three`),
  65 (`tower_mono_left`). Full file re-checked for any
  constant-absorbing lemma that would let `+ 5` close
  bprod's runtime; none found.
- `Fin.maxOfNat` signature:
  `GebLean/LawvereKSim.lean:106` — confirmed `n` explicit.
- kToER multi-output passage:
  `GebLean/LawvereKSimER.lean:336–479` —
  `kToERN`, `kToERN_interp`, `kToERN_compat_extEq`,
  `kToERFunctor_map`, `kToERFunctor_map_id`,
  `kToERFunctor_map_comp`, `kToERFunctor`. The T4 spec's §8
  closely mirrors this pattern.
- Quotient categories:
  `GebLean/LawvereERQuot.lean` (lines 23–32: `erMorNSetoid`,
  lines 37–38: `ERMorNQuo`).
  `GebLean/LawvereKSimQuot.lean` (lines 21: `kMorNSetoid`,
  lines 372–397: `KMorNQuo.AtDepthRaw`,
  `kMorNQuoAtDepthSetoid`, `KMorNQuo.atDepth`;
  lines 402–407: `Subsingleton` instance;
  lines 411–417, 420–440: identity and composition depth
  witnesses; lines 445–447: `KSimMor` structure; lines 475–481:
  `KSimMor.ext`).
- Markdownlint:
  `markdownlint-cli2` on the spec — 0 errors at review time.
- Mathlib upstream guides (re-fetched per CLAUDE.md):
  `style.html`, `naming.html`, `doc.html`, `commit.html` —
  spec's `def`/`theorem` casing, section structure, and
  reference format all consistent.

Tactics used:

- B2'(r3) quantitative recheck: re-derived the bound chain
  `Σ_{i < v 0} 9 · A_i · B_i ≤ ?`, comparing the
  spec's `+ 5` claim against the available Tower lemmas. The
  constant factor `9` requires either an additional
  `mul_tower_le_tower_add_two` application (yielding `+ 7`) or
  a new "constant times tower" lemma. The round-2 review's
  derivation made the same elision and was therefore not a
  valid prescription. Confirmed via direct algebraic
  inspection: `9 · v 0 ≤ m` requires `9 · (Fin.maxOfNat _ v) ≤
  Fin.maxOfNat _ v + offset`, which for `Fin.maxOfNat _ v →
  ∞` cannot hold with fixed offset.
- §8 type-check: traced `Quotient.liftOn e` over `e :
  ERMorNQuo n m`, confirmed `ERMorN n m = Fin m → ERMor1 n`
  (LawvereER.lean:151) and `KMorN n m = Fin m → KMor1 n`
  (LawvereKSim.lean:65), confirmed the `KSimMor 2 n m`
  structure has `hom : KMorNQuo n m` and `depth_witness :
  KMorNQuo.atDepth 2 hom` (LawvereKSimQuot.lean:445–447), and
  confirmed `KMorNQuo.atDepth d q` is constructible from
  `KMorNQuo.AtDepthRaw` via the always-true setoid (lines
  372–397), so the `/- depth-2 witness via erToKN_level -/`
  placeholder is realisable as
  `Quotient.mk (kMorNQuoAtDepthSetoid 2 _) { rep := erToKN
  rec, rep_level := erToKN_level rec, rep_eq := rfl }`.
- Setoid-relation chase: verified that the lift's
  `Quotient.sound` obligation reduces to
  `(kMorNSetoid n m).r (erToKN e₁) (erToKN e₂)`, discharged
  by `erToKN_compat_extEq` post-`congr_fun` over the ERMorN
  setoid's per-ctx equality.
- Round-2 fix verification: each round-2 finding (B1', B2',
  B3', S1', S2', S3', S4', S5', N1) re-checked against the
  revised spec text and classified.
- Markdownlint: ran on the spec, 0 errors.
