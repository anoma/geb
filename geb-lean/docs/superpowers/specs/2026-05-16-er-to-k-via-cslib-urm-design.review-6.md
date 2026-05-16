# Round-6 adversarial review — erToK via Tourlakis URM simulation

Reviewer: fresh-context `general-purpose` Agent (round 6).
Artefact under review:
[`2026-05-16-er-to-k-via-cslib-urm-design.md`](2026-05-16-er-to-k-via-cslib-urm-design.md).
Prior rounds:
[`.review-1.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-1.md),
[`.review-2.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-2.md),
[`.review-3.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-3.md),
[`.review-4.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-4.md),
[`.review-5.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-5.md).

## Citation verification log

All external Tourlakis citations verified at PDF. All
internal `File.lean:line` references verified. PASS.

## Other verification log

- **Constructive discipline.** Mathlib's `Fin.find`
  signature is `(p : Fin n → Prop) [DecidablePred p]
  (h : ∃ k, p k) : Fin n` — not `Option`-valued. Spec's
  `match Fin.find … with | some i => …` will not
  type-check. See S4.
- **Level claims.** §6.2 step level 1 → simrec level 2 ✓.
  §7.1 `boundExprK e` level 2 ✓.
- **§5.1 walkthrough `comp succ [proj 0]` at `[5] → 6`.**
  Walks through *only* after introducing implicit
  register-wiring conventions the spec does not state.
  See S1.
- **§5.1.1 cross-references `tower h_e (max(x⃗) + p_e)`
  runtime bound** that does not exist in §7 (which uses
  `pow2_iter r_e ∘ maxOver a`). Stale leftover. See S2.
- **§9.1 imports `GebLean.Utilities.Tower`** that no
  load-bearing construction uses. Phantom dependency.
  See S3.

## Findings

### Blocker

(None.)

### Serious

#### S1. §5.1 `comp f gs` template under-specifies g-to-f wiring

Spec says only "Sequential composition (Tourlakis p. 21
'concatenate M_g and M_f')". For `comp f gs` with
multi-input `f`, this leaves implicit: which register
holds `gs[i]`'s output, which register `f`'s slot-i
reads from, whether a transfer is emitted at the seam.
The pre-clone-at-prelude discipline (§5.1 prelude
construction) only handles outermost inputs, not the
g→f seam. Implementing `comp` as written admits
multiple inequivalent realisations.

**Response:** fix. Add to §5.1: each `compileER e'`
allocates a fresh output register `V_out_{e'}` on
entry and writes its result there; `compileER (comp f
gs)` allocates `V_out_{gs i}` for each `gs i`, runs
each `compileER (gs i)` sequentially, then for each
`i : Fin (arity f)` emits a destructive transfer
`V_out_{gs i} → V_in_{f, i}` (via the M-template),
then runs `compileER f` reading from `V_in_{f, i}`
slots. `f`'s internal `proj` constructors are
compiled (recursively) to read from its slot
registers, applying the pre-clone-at-prelude
discipline locally if a slot is read more than once.

#### S2. §5.1.1 stale runtime-bound reference

Line 453 references `tower h_e (max(x⃗) + p_e)` as the
runtime bound containing the per-iteration overhead.
§7.1 defines the bound as `pow2_iter r_e ∘ maxOver a`.
The §5.1.1 reference is to a prior revision's bound
expression.

**Response:** fix. Replace "absorbed into the `tower
h_e (max(x⃗) + p_e)` runtime bound (§7.3)" with
"absorbed into the `boundExprK e` runtime bound (§7)".

#### S3. §9.1 phantom dependency on `Tower`

`GebLean.Utilities.Tower` listed as an import; no
section uses any Tower symbol. Likely co-residual with
S2.

**Response:** fix. Remove `GebLean.Utilities.Tower`
from §9.1's `LawvereERKSim` dependency list.

#### S4. §4.3 `URMState.init` `Fin.find` API mismatch

Mathlib's `Fin.find` returns `Fin n` (with an
existence proof required), not `Option (Fin n)`. The
spec's `match Fin.find … with | some _ | none` will
not compile.

**Response:** fix. Replace with `List.find?` over
`List.finRange P.numInputs`:

```lean
def URMState.init (P : URMProgram)
    (v : Fin P.numInputs → ℕ) : URMState P where
  pc := 0  -- Tourlakis's I(0) = 1 mapped to 0
  regs := fun r =>
    match (List.finRange P.numInputs).find?
        (fun i => decide (P.inputRegs i = r)) with
    | some i => v i
    | none   => 0
```

`List.find?` is in Lean core (`List.find?` at `Init.Data.List.Basic`),
returns `Option (Fin P.numInputs)`. `P.inputRegs_inj`
ensures the `some i` value is unique when it exists.

#### S5. §9.1 `URMTourlakis.lean` dependency framing

Round-5 prose described `URMTourlakis.lean` as
depending on "Lean core and basic Fin / Array
machinery only". With `Fin.find` (mathlib) the
framing was already inaccurate; with the S4 fix
(`List.find?`, Lean core) the framing becomes
accurate.

**Response:** fix. Reword §9.1 to "depends on Lean
core; uses `List.find?`, `Function.update`, and
basic `Fin`/`Array` machinery; no mathlib reach
required."

### Minor

#### M1. §5.2 "Atoms: constant (≤ 3 instructions)"

`succ`, `proj i`, `sub` expand to ~7+ instructions
each via the M-template. "≤ 3" only fits `ERMor1.zero`.

**Response:** fix. Rephrase to "Atoms: bounded by a
small constant times input value (M-template loops
run `≤ vMax v` times); `ERMor1.zero` is the only
constant-instruction-count atom".

#### M2. §6.2 base case "level 0" wording

The case-split `if j ∈ inputRegs.range then ...` is
meta-level (compile-time), so each component reduces
to `proj k` or `zero`, both level 0. Wording could be
sharper.

**Response:** fix. Reword to clarify the case-split is
resolved at compile time.

#### M3. §7.2 handwave on concrete constants

Tourlakis §0.1.0.42 proof on p. 21 gives a more
delicate bound `t_h(⃗y) + O(Σ_{i<x} t_g(i, ⃗y, f(i, ⃗y)))`
than the spec's "additive bump at bsum/bprod" shape.

**Response:** fix. Acknowledge in §7.2 that the
recursion shape is the Tourlakis-p. 21 shape, not a
flat additive bump; the implementation's `r_e` must
dominate this shape.

#### M4. §3.1 `maxK` level reasoning wording

"comp taking the max of monus and add" reads as
"max(level monus, level add)". Clarify with the family
form.

**Response:** fix. Reword to "`KMor1.comp add [monus,
proj 1]` has level `max(level add, max(level monus,
level (proj 1))) = max(1, max(2, 0)) = 2`".

#### M5. §2.2 redundancy with §5.1

"V_z is the project's formal encoding of Tourlakis's
informal `goto l` shorthand" appears in both §2.2 and
§5.1.

**Response:** reject-as-cosmetic-taste (the §2.2
mention is a heads-up in the URM-correspondence
narrative; §5.1's is the load-bearing specification.
Both serve different readers).

#### M6. §13.1 missing pointer to §0.1.0.38

§0.1.0.38 (p. 16, "Example") gives the worked
simulating equations for a small URM, useful as a
cross-check on §6.1.

**Response:** fix. Add §0.1.0.38 to §13.1.

### Cosmetic-taste

#### C1. §5.1.1 step 3 dangling convention

"Reset `f`'s output-register scratch to 0 (or to the
accumulator value, depending on …)" — pick one.

**Response:** fix. Commit to: reset to 0; the
accumulator is a separate register that the outer
`bsum`/`bprod` template adds/multiplies into.

#### C2. §6.2 font mixing

`v_i_prev` (programmer style) vs `v_i(y, x⃗)`
(Tourlakis style) in adjacent paragraphs.

**Response:** fix. Use Tourlakis style throughout
§6.1–§6.2, since these sections transcribe Tourlakis.

#### C3. §11 SLOC ranges uncalibrated

400–600 for T2 hints at under-specification.

**Response:** reject-as-cosmetic-taste (these are
estimates, not contracts).

#### C4. §2.2 / §5.1 V_z explanation duplication

Subsumed by M5.

**Response:** subsumed.

## Convergence assessment

Round does NOT converge: 0 blocker(s), 5 serious
finding(s).

Convergence is close. S1 (`comp` wiring) is the
substantive remaining gap; S2/S3 (stale `tower`
reference + phantom `Tower` dep) are one-edit fixes;
S4/S5 (`Fin.find` API + framing) are one structural
edit each. After round 7 verifies these, the spec is
plausibly convergent.
