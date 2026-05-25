# T4 plan adversarial review — round 3

Round-3 adversarial review of
[`docs/superpowers/plans/2026-05-22-step-t4-runtime-bound-plan.md`](../superpowers/plans/2026-05-22-step-t4-runtime-bound-plan.md)
at jj revision `3c011fe0` on `feat/ertok-runtime-bound`,
against
[`docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`](../superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md),
the round-1 review at
[`2026-05-22-step-t4-plan-adversarial-review-round-1.md`](2026-05-22-step-t4-plan-adversarial-review-round-1.md),
the round-2 review at
[`2026-05-22-step-t4-plan-adversarial-review-round-2.md`](2026-05-22-step-t4-plan-adversarial-review-round-2.md),
and the authoritative project sources cited inline.

## Summary

- Residual blockers: 0
- Residual serious: 2 (S4 fragile packaging; R-S3 comp `+ 6`
  obligation deferred to implementer)
- New issues from round-2 fixes: 0
- Minor: 4

Round-2 verifications: all four claimed round-2 fixes (R-B1,
N1, N2, R-S2) check out against the revised plan text. Of the
four deferred items, S3 is verified as a non-defect (Lean 4
handles the pattern; the codebase uses an identical form);
R-S1 is now best classified as a documentation niggle (the
spec and plan chains agree numerically); S4 and R-S3 remain
serious. The plan has not yet converged.

## Round-2 fix verifications

### R-B1 (Tasks 5–8 `compileER_runtime` namespace): ADDRESSED via workflow note

Plan lines 111–120 (workflow note "Namespace qualification for
T2 surface") instruct the implementer to qualify every use of
`compileER_runtime`, `compileER_runFor`, `compileER_numRegs`,
`URMState.init`, `URMState.runFor` as
`LawvereERKSim.compileER_runtime`, etc., at every site,
overriding the pseudo-Lean's bare references in Tasks 4–10.

The unqualified references at plan lines 746, 782, 807, 819,
857, 880, 936, 1002, 1010, 1061, 1085, 1155, 1171, 1275, 1352,
1447, 1529 remain in the pseudo-Lean, but the workflow note
binds the implementer to qualify them all on first transcription.
This is the same fix shape applied for the existing T2 surface
in T3's plan (which built and passed). The workflow-note
approach is sufficient.

Confirmed: the qualified `LawvereERKSim.compileER_runFor`
reference still appears at line 1696 (Task 10 Step 6), which
exemplifies the qualified form the implementer mirrors
elsewhere.

### N1 (Task 10 `Fin.cons` lambda-family normalisation): ADDRESSED

Plan lines 1671–1697 (Task 10 Step 6 body) replace the broken
`simp only [Fin.cons_zero, Fin.cons_succ]` with an explicit
`have h_fam : (fun i : Fin _ => ...) = Fin.cons ((boundExprK
e).interp v) v` proved by `funext i; induction i using
Fin.cases with | zero => simp ... | succ j => simp ...`, then
`rw [h_fam]` before `rw [KSimURMSimulator.simulate_interp]`.
This matches the round-2 reviewer's prescribed fix. The
explanatory comment at lines 1664–1670 documents why the
`simp` approach failed (lambda binder hides the discriminand).

The closing line
`exact LawvereERKSim.compileER_runFor e v _ (boundExprK_dominates
e v)` follows correctly from the post-rewrite goal shape, with
the implementer-adjustment caveat documented at lines 1700–1704.

### N2 (AXIOM_ALLOW does not auto-propagate): ADDRESSED via workflow note

Plan lines 122–135 (workflow note "AXIOM\_ALLOW annotation
placement") spell out that "Inheritance does not auto-propagate
to callers; theorems that consume an AXIOM\_ALLOW'd lemma carry
their own annotation," then enumerate the three primary sites
*and* the inherited sites (`boundExprK_dominates`,
`erToKN_interp`, `erToKFunctor_map_id`, `erToKFunctor_map_comp`,
`erToKFunctor`), saying each needs an explicit annotation line.

The per-task pseudo-Lean for Tasks 9, 11, 13, 14 does not show
the AXIOM_ALLOW lines at the inherited declarations, but the
workflow note binds the implementer to add them. This is a
documentation-only deferral and is acceptable for an SDD-driven
plan, on par with round 2's other workflow-note fixes (Tasks
5–8 namespace qualification). See M1 below for a residual
minor concerning whether Task 13's pseudo-Lean should mention
this for emphasis.

### R-S2 (Task 3 `interp_pow2_iter` signature mismatch): ADDRESSED

Plan lines 556–576 (Task 3 Step 3) now state the lemma as

```text
@[simp] theorem KMor1.interp_pow2_iter :
    ∀ (r : ℕ) (v : Fin 1 → ℕ),
      (KMor1.pow2_iter r).interp v = tower r (v 0) := by
  ...
```

(generalised `Fin 1 → ℕ` form), matching Task 9 Step 3's
prerequisite at lines 1471–1479. The proof body at lines
559–575 follows correctly: `induction r`, `zero` case closes by
`simp [KMor1.pow2_iter, KMor1.interp_proj, tower]`; `succ n
ih` case reshapes via `have h_inner : (fun _ : Fin 1 => ...) =
(fun _ : Fin 1 => ...)` plus `funext _; exact ih v`, then
`simp [tower]`.

Note the round-2 reviewer's note that the lemma name remains
`KMor1.interp_pow2_iter` (no rename required); only the
quantifier shape changed.

## Residual blockers

None.

## Residual serious

### S4: Task 12 `KMorNQuo.atDepth` packaging — anonymous constructor remains

(Deferred from rounds 1 and 2.) Plan Task 12 Step 2 (lines
1900–1906) still writes:

```text
private def erToKN_atDepth {n m : ℕ}
    (e : ERMorN n m) :
    KMorNQuo.atDepth 2
      (Quotient.mk (kMorNSetoid n m) (erToKN e)) :=
  Quotient.mk _ ⟨erToKN e, erToKN_level e, rfl⟩
```

Verified against `GebLean/LawvereKSimQuot.lean:372-417`:

- `KMorNQuo.AtDepthRaw d q` is a 3-field structure with fields
  `rep : KMorN n m`, `rep_level : ∀ i : Fin m, (rep i).level ≤ d`,
  `rep_eq : Quotient.mk (kMorNSetoid n m) rep = q`
  (lines 373–376).
- The canonical builder `KMorNQuo.id_atDepth` (lines 411–417)
  uses NAMED fields:

  ```text
  Quotient.mk _
    { rep        := KMorN.id n
      rep_level  := fun _ => by simp [KMorN.id, KMor1.level]
      rep_eq     := rfl }
  ```

- `KMorNQuo.comp_atDepth` (lines 420–440) likewise uses named
  fields.

The plan's anonymous constructor `⟨erToKN e, erToKN_level e,
rfl⟩` faces two issues:

1. `erToKN_level e : (j : Fin m) → (erToKN e j).level ≤ 2`
   (per Task 11 Step 5 lines 1837–1839), i.e., a function of
   `j` whose target is the level inequality at a fixed `j`.
   The field `rep_level` expects `∀ i : Fin m, (rep i).level ≤
   2`. These are definitionally interconvertible (Lean's `∀`
   and `→` over `Fin m → ℕ`-targets coincide when the codomain
   is the proposition); Lean's anonymous-constructor elaborator
   typically handles the eta-reduction. But the plan's note at
   lines 1908–1910 ("Adjust the `kMorNQuoAtDepthSetoid` argument
   shape to match `LawvereKSimQuot.lean`'s actual surface;
   consult `KMorNQuo.atDepth`'s definition.") flags the surface
   may need adjustment without prescribing the named-field
   form.
2. The codebase's only two extant builders both use named
   fields; using anonymous-constructor matching here diverges
   from the codebase convention and increases the risk of
   silent matching to a wrong constructor in case
   `AtDepthRaw`'s field order shifts in future maintenance.

Fix: rewrite Task 12 Step 2's pseudo-Lean to use named fields:

```text
private def erToKN_atDepth {n m : ℕ}
    (e : ERMorN n m) :
    KMorNQuo.atDepth 2
      (Quotient.mk (kMorNSetoid n m) (erToKN e)) :=
  Quotient.mk _
    { rep        := erToKN e
      rep_level  := fun j => erToKN_level e j
      rep_eq     := rfl }
```

This mirrors `KMorNQuo.id_atDepth` exactly and is robust to
field-order shifts.

Severity: serious (codebase-convention mismatch + fragile
elaboration; the kToER analogue uses named fields).

### R-S3: comp `+ 6` recipe may not absorb the `k · 9 · v_total` outer fold

(Deferred from rounds 1's S6 and 2's R-S3.) The
`compileER_runtime` definition at
`GebLean/LawvereERKSim/Compiler.lean:1728-1737` is:

```text
| a, .comp (k := k) f gs, v =>
    let inner : Fin k → ℕ := fun i => (gs i).interp v
    let v_total : ℕ :=
      ((List.finRange a).map v).foldl (· + ·) 0
    let glue : ℕ :=
      ((List.finRange k).map
        (fun i => compileER_runtime (gs i) v
          + 4 + 5 * inner i
          + 9 * v_total + 2 * a)).foldl (· + ·) 0
    glue + compileER_runtime f inner + 2
```

The `9 * v_total` term sits inside the per-`i` lambda mapped
over `List.finRange k`, so the outer fold contributes
`Σ_{i<k} 9 * v_total = k · 9 * v_total` (plus the other
per-`i` constants `4 + 5·inner i + 2·a` summed `k` times).

The spec's §4.2 comp rationale (lines 282–302) describes only
one `9 · v_total` absorption (lines 282–293) and a separate
"sum-of-two-tower-bounded-terms" absorption (lines 293–299).
The spec does not analyse the per-`i` factor `k`. The final
spec step at line 296 reads

> `2 · tower (mu_f + mu_g + 6) m ≤ m · tower (mu_f + mu_g + 6) m`
> `≤ tower (mu_f + mu_g + 6) m`

The last inequality is mathematically false in general (it
should be `≤ tower (mu_f + mu_g + 8) m` if a further
`mul_tower_le_tower_add_two` is applied); the spec's argument
here is sloppy.

The plan's Task 6 acknowledges this risk explicitly. Plan Step
5 (lines 1057–1073) leaves the `h_glue` proof as a `sorry`
described as "~40-60 lines"; Plan Step 6 (lines 1080–1100)
includes the note:

> The implementer must check whether the bound discharges at
> +6 (via tighter absorption chains) or whether the recipe
> needs to be revised to +7.

This is a deferred verification: if the implementer cannot
discharge `+ 6`, the recipe needs to be revised to `+ 7`
(or `+ 8`), which propagates through Task 9 (`boundExprK_dominates`),
Task 10 (`erToK`), Task 12 (`erToKFunctor_map`), and the
overall T4 deliverable, including spec §4.2's table and §6.

The plan's note at line 1098–1100 instructs the implementer
to escalate to user review before revising the recipe. This
is the right escalation path, but the residual obligation
remains: a project-gate convergence requires either resolving
the recipe value within the plan or explicitly documenting the
alternative recipe values that the bound might need.

Severity: serious — open recipe value contradicts the
"zero blockers / zero serious" convergence gate.

Possible resolutions: (a) verify in detail that `+ 6` discharges
under the chain `k · 9 · v_total ≤ k · 9 · m · m ≤ m · m · m ·
m ≤ tower 4 m ≤ tower (mu_f + mu_g + 6) m` (uses `k ≤ m` and
`9 ≤ m`, both of which follow from `m ≥ Fin.maxOfNat _ v + (
offset_f + offset_g + 4·a + 8)` with `k ≤ a + offset_f`, but
the relation between `k` and the offset components needs to be
spelled out); or (b) revise the recipe to `+ 7` or `+ 8`,
updating the spec and downstream tasks; or (c) annotate the
plan with the precise chain that closes at `+ 6` so the
implementer has a deterministic discharge path.

## New issues introduced by round-2 fixes

None. All four round-2 fixes (R-B1 workflow note, N1 `have
h_fam` construction, N2 inheritance-annotation workflow note,
R-S2 generalised `interp_pow2_iter` signature) are well-formed
and do not introduce new defects.

## Minor

### M1: Task 13 pseudo-Lean does not show AXIOM_ALLOW lines (workflow-note coverage)

Plan workflow note at lines 122–135 binds the implementer to
add AXIOM_ALLOW lines on inherited sites
(`erToKFunctor_map_id`, `erToKFunctor_map_comp`,
`erToKFunctor`). Task 13 Steps 1 and 3 (plan lines 1974–2034)
display the `theorem` declarations without the `--
AXIOM_ALLOW:` comment immediately above them. Per the workflow
note this is acceptable (the note overrides). For maximum
clarity, the pseudo-Lean could be amended to display the
annotation line; this is a minor documentation-completeness
nit, not a defect.

### M2: spec atom rationale phrasing carry-over (R-S1 downgrade)

(Downgraded from R-S1 serious.) Spec §4.2 atom paragraph
(lines 245–255) describes the absorption as "a single
application of `mul_tower_le_tower_add_two`" while expanding
the chain as `10·m ≤ m·m = m · tower 0 m ≤ tower 2 m`. The
plan's atom-case proofs (Task 5 Steps 4–6, lines 818–900) use
a calc chain with a `nlinarith` preparation followed by one
`apply Tower.mul_tower_le_tower_add_two`. Numerically the spec
and plan agree: the spec's `10·m ≤ m·m` is Nat-arithmetic, and
the spec's "single application" refers to the single
invocation of the named Tower lemma at the end.

The wording mismatch ("a single application" implying nothing
prior, while in practice a Nat-arithmetic `nlinarith` precedes
it) is a documentation niggle. The plan and spec are
consistent in substance.

Severity: minor (documentation niggle, not a defect of
elaboration or correctness).

### M3: residual `Fin.maxOfNat_succ` fallback reference (R1 M1 carry)

Plan Task 2 Step 5 lines 452–454 still mentions the
non-existent `Fin.maxOfNat_succ` as a TDD-recovery fallback if
`simp [Fin.maxOfNat, Fin.foldr_succ]` does not close. The
primary chain via `Fin.foldr_succ` is the recommended path;
the fallback is offered as a last resort with the instruction
"introduce it locally as a helper lemma in `LawvereKSim.lean`
if not already present". Acceptable. No fix required.

### M4: closeout LOC estimate carry-over from round 1's M5

Plan closeout line 2216 (per Task 15 Step 8 commit message)
gives "~1480 LOC. Comparable to T3." T3 actual at PR `db059ef4`
is ~1000 LOC; T4 estimate ~1480 is ~48% larger. The "comparable
to T3" phrasing carries forward from the spec; rephrasing to
"larger than T3 due to the recipe machinery in
`boundExprKParams_dominates`" would be more accurate. Minor.

## Convergence assessment

Zero blockers; two serious (S4, R-S3). The plan has not yet
converged to the project gate of zero blockers and zero
serious. S4 (anonymous-constructor packaging in Task 12) is
a mechanical fix; R-S3 (`comp` recipe `+ 6` discharge
obligation) requires substantive arithmetic verification or a
recipe revision.

Recommended next-round disposition:

- S4: apply the named-field rewrite verbatim (5 lines of plan
  edit).
- R-S3: either (a) provide a detailed discharge chain inside
  Task 6 Step 5 of the plan showing how `k · 9 · v_total`
  absorbs into `+ 6`, or (b) revise the spec and plan to
  `+ 7` (or `+ 8`) with the downstream propagation. Path (b)
  is the safer choice given that the spec's own chain at
  lines 296–297 contains a mathematical slip (`m · tower (X) m
  ≤ tower (X) m` is false in general).

## Methodology

Each round-1 and round-2 finding was located in the revised
plan (jj `3c011fe0`) by line number; each round-2 fix-claim
was verified by reading the cited line range and comparing
against the prior plan's shape.

The deferred items S3, S4, R-S1, R-S3 were re-investigated
against authoritative codebase sources:

- S3 (`_, .zero` dependent pattern): verified against
  `GebLean/LawvereERKSim/Compiler.lean:1722-1727`, which
  defines `compileER_runtime` using the identical underscore-
  on-implicit pattern (`| _, .zero, _ => 3` etc.) and
  elaborates successfully in committed code. Pattern is
  Lean-4-supported; not a defect.
- S4 (`KMorNQuo.atDepth` packaging): verified against
  `GebLean/LawvereKSimQuot.lean:372-440`, specifically the
  `AtDepthRaw` structure definition (lines 373–376) and the
  canonical builders `id_atDepth` (411–417) and
  `comp_atDepth` (420–440). The codebase uses named-field
  syntax; the plan's anonymous-constructor sketch is fragile.
- R-S1 (atoms `nlinarith` vs spec "single application"):
  spec §4.2 lines 245–255 expand the chain explicitly with
  `10·m ≤ m·m = m · tower 0 m`, so the Nat-arithmetic step is
  inside the spec's own description even though the prose
  reads "a single application of `mul_tower_le_tower_add_two`".
  The mismatch is documentation only; downgraded to minor M2.
- R-S3 (comp `9·v_total` per-`i`): verified against
  `Compiler.lean:1728-1737`, which confirms `9 * v_total`
  sits inside the per-`i` mapped lambda (line 1735), giving
  `k · 9 · v_total` over the outer fold. The spec's §4.2
  rationale (lines 282–302) does not analyse this `k` factor
  explicitly and contains a mathematical slip at lines
  296–297. The plan's Task 6 Step 6 (lines 1080–1100)
  acknowledges the open obligation. Serious.

The cited Lean declarations and lemma signatures were verified
against:

- `GebLean/Utilities/Tower.lean` (lines 17, 27, 42, 51, 65,
  101, 120 for the actual Tower surface).
- `GebLean/LawvereER.lean` (lines 30–58 for `ERMor1`'s
  constructors and arities).
- `GebLean/LawvereKSimQuot.lean` (lines 33–48, 372–476 for
  `KMorNQuo`, `AtDepthRaw`, `atDepth`, `id_atDepth`,
  `comp_atDepth`, `KSimMor`).
- `GebLean/LawvereERKSim/Compiler.lean` (lines 1722–1770 for
  `compileER_runtime`'s closed form per constructor).
- The spec at
  `docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`
  (lines 219–340 for §4 recipe and rationale).

Mathlib upstream guides
(`https://leanprover-community.github.io/contribute/{naming,style,doc,commit}.html`)
were not re-pulled in this round; the
`.claude/rules/lean-coding.md` local digest sufficed for
style / naming / commit-message checks. No new commit-message
defects detected beyond round-1 M3 (fixed in round 2 via the
`$'...\n...'` form at plan line 1548).

The plan is markdownlint-clean per the standard
`.markdownlint-cli2.jsonc` configuration.
