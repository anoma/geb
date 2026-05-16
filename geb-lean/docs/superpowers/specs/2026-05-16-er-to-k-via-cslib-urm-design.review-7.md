# Round-7 adversarial review — erToK via Tourlakis URM simulation

**Convergence record.** This round meets the
convergence criterion of
[`docs/process.md`](../../process.md) § Adversarial
review (zero blocker, zero serious findings).

Reviewer: fresh-context `general-purpose` Agent
(round 7). Artefact under review:
[`2026-05-16-er-to-k-via-cslib-urm-design.md`](2026-05-16-er-to-k-via-cslib-urm-design.md).
Prior rounds:
[`.review-1.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-1.md),
[`.review-2.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-2.md),
[`.review-3.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-3.md),
[`.review-4.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-4.md),
[`.review-5.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-5.md),
[`.review-6.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-6.md).

## Citation verification log

All external Tourlakis citations verified at PDF
(§0.1.0.2, .4, .7, .9, .17 subitems, .20, .27, .36, .37,
.42, .43, .44; pp. 15–22 and pp. 19–21 worked examples).
All internal `File.lean:line` references verified. PASS.

Spot checks performed:

- §0.1.0.36 (p. 15) runtime majorisation definition: ✓.
- §0.1.0.37 (pp. 15–16) base + step cases: ✓ line-by-line
  against Tourlakis's four `v_i(y+1, …)` clauses and four
  `I(y+1, …)` clauses.
- §0.1.0.37 conclusion ("all simulating functions are in
  K^sim_2"): ✓ verbatim p. 16.
- §0.1.0.42 (p. 18) URM-computability within
  `t ∈ E^n`: ✓.
- §0.1.0.43 (p. 21) Ritchie–Cobham: ✓.
- §0.1.0.44 (p. 22) `f = λx⃗. v_1(A^r_n(max x⃗), x⃗)`: ✓.
- p. 19 M URM (λx.x), N URM (λx.x+1) — both destructive
  in source variable: ✓.
- p. 20 Loop-to-URM template with scratch register B per
  Loop scope: ✓.
- p. 21 bounded-recursion URM template (separate index
  `i` and count `x`): ✓.

## Other verification log

- **§5.1.2 walkthrough — `compileER (comp succ [proj 0])`
  arity 1 input `[5]`.**
  - Outer prelude: 1 consumer of slot 0; emit one
    preserving-transfer `V_input_0 → V_src_{0,0}`.
    V_input_0 = 5; V_src_{0,0} = 5 after prelude.
  - Allocate `V_out_{gs 0}` for `proj 0`'s output.
  - `compileER (proj 0)`: M-template — loop V_src_{0,0}
    times incrementing V_out_{gs 0}. V_out_{gs 0} = 5.
  - Allocate `V_in_{succ, 0}`; transfer V_out_{gs 0} →
    V_in_{succ, 0}. V_in_{succ, 0} = 5.
  - `compileER succ` — loop V_in_{succ, 0} times plus
    extra inc. V_out_succ = 6. ✓ Matches
    `(comp succ [proj 0]).interp ![5] = 6`.

- **Level claims.** §6.2 step level 1 (PC-dispatch via
  nested `cond` chain with `pred^k` discriminators);
  simrec adds 1 → level 2. §7.1 `boundExprK e` level 2.
  `erToK e` level 2 by `comp`'s max rule. ✓ No
  `KMor1.eq` (level 2) appears on the load-bearing
  path.

- **§6.1 vs Tourlakis p. 16.** Line-by-line under the
  0/1 PC-indexing shift. ✓

- **§8.1 vs Tourlakis p. 22.** Substitution
  `v_1 ↔ simulate (compileER e)`,
  `A^r_n(max x⃗) ↔ boundExprK e`,
  `x⃗ ↔ proj_i` is exact. ✓

- **§9.1 dependency graph.** All cited modules exist;
  `Tower` correctly removed; no phantom deps. ✓

- **Constructive discipline.** §4.3 uses
  `(List.finRange P.numInputs).find?` (Lean core,
  constructive, `Option`-valued). No `Classical.choose`
  / `noncomputable`. ✓ (See M1 for §10's naming
  inconsistency.)

- **Round-1 leftover names.** Confined to §2.1 / §12.11
  / §14 narrative; `V_z` is now distinguished from
  forbidden `Z0` in §12.11. ✓

## Findings

### Blocker

None.

### Serious

None.

### Minor

1. **§10 vs §4.3 name inconsistency** (`Fin.find` vs
   `List.find?`). §10 prose says "uses `Fin.find`"; §4.3
   actually shows `(List.finRange P.numInputs).find? …`.
   Both are constructive. Align the wording.

   **Response:** fix. §10 wording updated to
   `List.find?`.

2. **§11 critical-path graph omits T3 → T4 edge.** T4
   (`boundExprK_dominates`) depends on T3's K^sim
   composites (`pow2_iter`, `maxOver`) as well as T2's
   `compileER_runtime`. Restate as "T1 → T2 → T4 → T5;
   T3 parallels T2 but precedes T4".

   **Response:** fix.

3. **`succ`/`proj` template redundant `V_out ← 0`
   instruction.** Fresh registers initialise to 0 per
   `URMState.init`; the explicit zero-assignment is
   harmless but redundant.

   **Response:** fix. Drop the redundant `V_out ← 0`
   from §5.1 succ and proj templates; note the
   convention in §5.1 prelude prose.

4. **§3.1 `natK` lift type ascription.** `Fin.elim0`
   needs an explicit ascription `(Fin.elim0 : Fin 0 →
   KMor1 n)` to disambiguate the target type.

   **Response:** fix.

5. **§3 inventory `KMor1.signum` not on load-bearing
   path.** Listed for completeness.

   **Response:** fix. Annotate the row to mark it
   "listed for completeness; not used in §3.1–§8".

6. **§5.2 §0.1.0.42 `n ≥ 2` applicability for our
   `n = 3` case.** Brief exposition note would
   clarify.

   **Response:** fix. Add one-line note that our case
   ER = E^3 corresponds to Tourlakis's `n = 3` (within
   the `n ≥ 2` range covered by §0.1.0.42).

7. **File naming `LawvereERKSim.lean` vs existing
   `LawvereKSimER.lean`.** Trivially confusable;
   document the convention.

   **Response:** fix. Add a one-line note in §9 module
   layout: `LawvereERKSim.lean` (ER → K direction) is
   distinct from `LawvereKSimER.lean` (K → ER
   direction, already landed).

### Cosmetic-taste

1. **§3.1 phrasing "load-bearing".** Borderline
   colloquialism per project style guide.

   **Response:** reject-as-cosmetic-taste (structural
   sense, not value-laden adjective).

2. **§7.2 "Concrete values are computed by the
   implementation."** Awkward deferral phrasing.

   **Response:** fix. Tighten to "Concrete constants
   are determined during implementation."

3. **§3 inventory column hybrid labels** ("(standard)",
   "(project-internal)").

   **Response:** reject-as-cosmetic-taste (single
   column suffices; splitting into "Source" + "Status"
   inflates table width without clarity gain).

4. **§2.2 `stop` table entry specifies PC only;** §4.2
   `step` correctly returns `s` (whole state). Minor
   exposition.

   **Response:** fix. Reword the §2.2 row to "`pc :=
   pc`; registers unchanged".

## Convergence assessment

**Round converges: zero blocker, zero serious.**

Per [`docs/process.md`](../../process.md) §
Adversarial review § Convergence criterion: "A round
**converges** when its reviewer reports zero blocker and
zero serious findings. Minor and cosmetic-taste findings
are not a barrier to convergence and may remain open at
termination."

This round-7 review file is the convergence record.

The seven minor and four cosmetic findings have author
responses applied in this file's response lines; they
do not block convergence. The author may apply the
minor fixes inline to the spec at termination but is
not required to re-dispatch a fresh reviewer.

**Status: spec ready for the writing-plans phase
(`superpowers:writing-plans`).**
