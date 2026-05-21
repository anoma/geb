# T2 plan adversarial review — round 2

## Author responses

- **S1** (literal-`Fin`-pattern match exhaustiveness in
  `compileFrag_sub`): **fix.** Rewrote `inputRegs` using
  `Fin.cases ⟨2, by decide⟩ (Fin.cases ⟨3, by decide⟩
  Fin.elim0)` and the three invariant proofs using
  `fin_cases p <;> ...` (mathlib tactic available via
  the transitive `Mathlib` import chain from
  `Mathlib.Data.List.FinRange`). If `fin_cases` is
  unavailable in the local mathlib pin, the
  implementer's fallback is explicit
  `match (p.val, p.isLt) with | (0, _) => ... | (1, _)
  => ... | (n+2, h) => absurd h (by omega)`.
- **M1** (coverage table inconsistency with Divergence
  subsection): **fix.** Coverage table row for "§5.1
  prelude" rewritten to "localised variant adopted; see
  Divergence subsection" with cross-references to all
  four affected tasks (5.3, 6.3, 7.1, 8.1).
- **M2 / N3** ("three combinator bodies" mismatch with
  four declarations): **fix.** Subsection renamed to
  "Plan-style note: sketches in four declaration bodies".
  TOC regenerated.
- **N1** ("more elaborate" prose usage): **fix.**
  Rewrote as "emits a nested loop, in contrast to bsum's
  single transferLoop addition". The remaining
  occurrence at line 1017 is the Lean-vernacular sense
  of "elaborate" (the elaborator phase), retained.
- **N2** (Tasks 2-12 indicative-tense commit bodies):
  **fix.** Rewrote each of the 11 remaining task commit
  bodies in imperative present (mirror/introduce/encode/
  realize/glue/emit/mirror/dispatch/define/prove/verify).

## Summary

Round 2 verifies the fixes claimed in round 1's "Author
responses" against the current plan. Of the round-1 items
marked `fix`, all are present and substantively address the
flagged defect; three carry minor incompleteness. The two
items marked `defer-with-rationale` (B3, M3) are evaluated
below; B3's rationale is recorded transparently in the new
"Plan-style note" subsection and is acceptable for the
plan's single-cycle commitment, but the heading wording and
the coverage-table interaction remain inconsistent. New
Lean-code blocks introduced by the round-1 fixes
(`compileER_runtime`, `compileFrag_succ`,
`compileFrag_zero`, `URMRaw.preservingTransfer`,
`compileFrag_sub`) type-check on inspection with one
exception worth flagging: the `compileFrag_sub` and
`compileFrag_succ` bodies use literal-`Fin`-pattern matching
(`match i with | ⟨0, _⟩ => …`) whose exhaustiveness Lean
does not in general recognise automatically.

Counts: 0 blockers, 1 serious, 2 minor, 3 nits.

The plan is not yet converged; the serious finding S1
(literal-`Fin`-pattern exhaustiveness in `compileFrag_sub`)
is a concrete implementability risk that the implementer
will hit at build time. The remaining findings are minor
documentation/style items. Recommend a round-3 review after
S1 is addressed (a one-line edit replacing the `match` with
`Fin.cases` or equivalent).

## Round-1 fix verification

For each round-1 finding marked `fix`, the table below
records: location of the fix; whether the fix is present;
whether new defects were introduced.

| Round-1 ID | Status | Notes |
| --- | --- | --- |
| B1 (`compileER_runtime` body type error) | fix present | Rewritten with `(k := k)` constructor patterns, `Fin.tail v`, explicit `ctx_f : Fin (k+1) → ℕ` annotation. Type-checks on inspection. |
| B2 (silent mathlib imports) | fix present | Body now uses `List.finRange` / `List.range` / `List.foldl` from imports already in T1. No new mathlib imports. |
| B3 (five `sorry` placeholders) | defer-with-rationale; recorded but heading wording inconsistent | See § B3 deferral below. |
| S1 (duplicate `preservingTransfer` definitions) | fix present | Only the corrected 9-instruction body remains (Step 4.4). |
| S2 (`mTemplate` miscites Tourlakis M) | fix present | Renamed to `transferLoop`; helper `transferLoopLen`; all callsites updated; citation reworded. |
| S3 (spec §5.1 prelude discipline) | fix present | "Divergence from spec §5.1's global prelude discipline" subsection added. Caveat: the coverage table at line 2247 still claims Tasks 5.3/6.3 *cover* the prelude discipline — see § minor M1. |
| S4 (`runFor_succ` peeling) | fix present | Task 11.2 strategy leads with `URMState.runFor_add`; slack `s := t' - compileER_runtime e v` and halt-state self-loop absorption added. |
| S5 (`compileFrag_succ` `inputRegs_inj` type mismatch) | fix present | Tactic-mode rewrite `by intro i j _; exact Subsingleton.elim _ _`. Closes the goal `i = j` since `Fin 1` is a `Subsingleton`. |
| S6 (PC offset arithmetic in `compileFrag_sub`) | fix present | Parenthesised as `(.assignR 0 0) :: ((pT 1 2 1 4) ++ (tL 10 3 5) ++ [...])`. |
| S7 (`compileER_runtime` proj branch arity binder) | fix present | Pattern now `\| _, .proj i, v => 11 + 10 * v i`. |
| S8 (spec §12 coverage table miss) | fix present | Table expanded with §12.2–§12.6 marked out of T2 scope. |
| M1 (inert `let _ := rawList`) | fix present | Removed. |
| M2 (`compileFrag_zero` `Fin.elim0` proofs) | fix present | Rewritten with `intro a _ _; exact Fin.elim0 a` and `intro i _; exact Fin.elim0 i`. Closes the right goals (see § Lean-correctness spot-checks). |
| M3 (redundant double citations) | defer-with-rationale; sound | Rationale is sound — spec citations carry implementation-specific information; the Divergence subsection (round-1 S3 fix) is a concrete example. |
| M4 (`runFor_succ` primacy) | fix present | Same as S4. |
| M5 ("Wait, that's 15" filler) | fix present | Rewritten without the filler. |
| M6 (`check-axioms.sh` followup) | fix present | Step 12.2 names the followup as "the project's general infrastructure backlog". |
| N1 ("elaborate", "straightforward") | partial fix | Two occurrences of "elaborate" remain in the plan; see § Nits. |
| N2 (indicative-tense commit messages) | partial fix | Only Task 1's commit was rewritten; Tasks 2–12 still carry indicative-tense bodies. See § Nits. |
| N3 (markdownlint cleanliness) | fix present | `markdownlint-cli2` on the plan reports 0 errors. |

## B3 deferral evaluation

The deferral records that Tasks 6, 7, 8, 11 each leave one
public-declaration body as a `sorry` plus Lean-syntax
skeleton, with the body filled in by the implementer
subagent during execution. Three evaluation axes:

1. **Transparency.** The new "Plan-style note: sketches in
   three combinator bodies" subsection (lines 233–262)
   explicitly flags the deviation, names the four affected
   declarations, and ties the structure to the
   subagent-driven-development workflow. The deferral is
   transparently recorded. However the subsection's
   heading says "three combinator bodies" while the body
   prose mentions four declarations (the three combinators
   plus `compileER_runFor`). Reader sees a mismatch between
   the subsection name and its content. See § Nits N3.

2. **Sketch density.** Tasks 6.3, 7.1, 8.1 sketches give
   block-by-block PC offsets and register layouts in
   pseudo-code, plus prose enumeration of the four
   structural-invariant obligations. Task 11's sketch
   gives a five-step proof outline plus an inner-induction
   strategy for `bsum`/`bprod`. Each sketch is concrete
   enough that an implementer with the plan in hand can
   reach the correct shape; the implementer still has to
   discharge several distinct concerns (register
   injections, PC arithmetic, invariant proofs) that
   require independent thought. The sketches are dense but
   not so dense that they pre-empt design work.

3. **Rationale soundness.** "One plan-execute cycle per
   contract boundary" is a defensible position: splitting
   T2 into four cycles to drive the sorries to zero in the
   plan would invert the plan-vs-implementation ratio
   (more plan iterations than implementer commits) and
   fragment a spec commitment that the spec itself treats
   as a single step. The trade-off is recorded.

Conclusion: the B3 deferral is acceptable. The implementer
subagent has enough scaffolding to make progress; the
plan-style note tells future readers that this is a
deliberate choice. The heading wording (Nit N3) is the
only follow-up.

## New defects introduced by round-1 fixes

### S1 (new). Literal-`Fin`-pattern match in `compileFrag_sub`'s `inputRegs`

Exhaustiveness on `Fin 2` is not recognised by Lean
automatically.

`compileFrag_sub`'s `inputRegs` (Step 5.4, lines 1184–1187):

```lean
inputRegs := fun i =>
  match i with
  | ⟨0, _⟩ => ⟨2, by decide⟩
  | ⟨1, _⟩ => ⟨3, by decide⟩
```

The same literal-`Fin`-pattern style appears at lines
1195–1201 (`inputRegs_inj`), 1203–1210
(`outputReg_not_input`), and 1212–1219 (`zeroReg_not_input`).
The match patterns `⟨0, _⟩` and `⟨1, _⟩` constrain
`i.val = 0` and `i.val = 1` respectively; covering both
requires Lean's pattern compiler to recognise that
`i : Fin 2` has `i.val < 2` and that `Fin` is defined by
val/isLt projection. In Lean 4 / mathlib current, pattern
matching on `Fin n` with literal numeric patterns is *not*
exhaustiveness-checked from `val < n`; the compiler treats
`Fin` as a generic structure with no special handling.
The implementer is likely to hit a "missing cases: (i :
Fin 2)" warning or error at build time.

Two workarounds available:

- Use `Fin.cases` / `Fin.succRecOn`:

  ```lean
  inputRegs := Fin.cases ⟨2, by decide⟩
    (Fin.cases ⟨3, by decide⟩ Fin.elim0)
  ```

- Use a conditional on `i.val`:

  ```lean
  inputRegs := fun i =>
    if h : i.val = 0 then ⟨2, by decide⟩
    else ⟨3, by decide⟩
  ```

This is implementability-risk-level: the implementer will
hit it on the first build attempt for Task 5.4. Same
caveat applies to `compileFrag_succ`'s
`outputReg_not_input` style (lines 989–998) if Lean's
pattern compiler treats `i : Fin 1` consistently
(probably fine since `Fin 1` is a `Subsingleton`, but the
proof writes `intro i h; have hv : ⟨2,…⟩ = ⟨1,…⟩ := h; …`
which is structurally OK because no pattern match is
performed on `i`).

Recommend rewriting `compileFrag_sub`'s `inputRegs` and
the associated invariant proofs using `Fin.cases` or
explicit `if h : i.val = 0` analysis before
implementation begins.

### Other Lean-correctness spot-checks

- **Step 10.1 `compileER_runtime` body.** The expression
  `((List.finRange k).map (Fin.tail v)).foldl (· + ·) 0`
  in the `bsum`/`bprod` branches: `Fin.tail v : Fin k → ℕ`
  when `v : Fin (k+1) → ℕ`; `List.finRange k : List (Fin k)`;
  `List.map (Fin.tail v) (List.finRange k) : List ℕ` —
  type-checks. Semantics: `((List.finRange k).map (Fin.tail
  v))` enumerates `Fin.tail v ⟨0, _⟩, Fin.tail v ⟨1, _⟩,
  …, Fin.tail v ⟨k-1, _⟩` = `v ⟨1, _⟩, v ⟨2, _⟩, …, v ⟨k,
  _⟩` (since `Fin.tail v j = v j.succ`). The fold sums
  these to `Σ_{j=1}^{k} v j`. Matches the spec semantics.

- **Step 5.1 `compileFrag_zero`.** `inputRegs_inj := by
  intro a _ _; exact Fin.elim0 a`. After `intro a _ _`,
  goal is `a = _` where `a : Fin 0`. `Fin.elim0 a` produces
  any type. Closes. `outputReg_not_input := by intro i _;
  exact Fin.elim0 i`: goal is `False` (from `≠`); same
  pattern. Closes.

- **Step 5.2 `compileFrag_succ`.** `inputRegs_inj := by
  intro i j _; exact Subsingleton.elim _ _`. After
  `intro i j _`, goal is `i = j` with `i j : Fin 1`.
  `Subsingleton.elim _ _` produces `_ = _`; Lean
  elaborates the underscores to `i`, `j`. Closes.

- **Step 4.4 `URMRaw.preservingTransfer`.** Two-loop
  structure with explicit per-PC commentary. The exit
  PC is `pcBase + 9`. The loops' goto targets jump back
  to `pcBase` (for loop 1) and `pcBase + 5` (for loop 2);
  the `jumpZR` exit targets jump to `pcBase + 5` (loop
  1's exit) and `pcBase + 9` (loop 2's exit). Layout
  consistent with the architecture-overview docstring.

- **Step 5.4 `compileFrag_sub`.** Register layout 0..5
  (six registers); `inputRegs i.val + 2` for i ∈ {0, 1}
  maps to registers 2 and 3; output at register 1;
  zero-reg at register 0; tmp_pT at register 4; scratch
  B at register 5. Instruction list: `assignR 0 0 ::
  (pT 1 2 1 4 ++ tL 10 3 5 ++ [jumpZR 5 18 15, decR 5,
  decR 1, goto 14, stopR])`. Lengths: 1 + 9 + 4 + 5 = 19
  instructions, PCs 0..18. PC 14 jumpZR exits to PC 18
  (stop) and bodies to PC 15. PCs match. (Apart from
  the `Fin`-pattern-exhaustiveness concern at S1, the
  body is consistent.)

## Remaining defects from round 1

Re-evaluating the four B3-deferred bodies' sketch density:

- **Step 6.3 `compileFrag_comp` sketch (lines 1336–1430).**
  The sketch enumerates: numRegs formula; per-`gs i` and
  per-`f` register injections; PC offset arithmetic;
  instruction-block concatenation; the four structural
  invariants. The sketch does not specify how to construct
  the register-injection functions concretely (e.g., as
  case-splits on `i.val < zero-reg-position`, or as
  arithmetic) — the implementer must invent the indexing
  arithmetic. Sufficient density given the scaffold.

- **Step 7.1 `compileFrag_bsum` sketch (lines 1498–1592).**
  Detailed register layout (registers 0 through
  `7 + 2k` + `f`'s internals); per-iteration prologue
  structure; loop-counter handling; accumulator update.
  The sketch references "register `7+2k`: scratch tmp
  for preserving-transfer of outer params (one shared
  tmp; reused after each preserving-transfer leaves it
  zero)" — the implementer must verify that the
  shared-tmp re-use does not collide with the inner
  `f` block's register indices. Sufficient density,
  with one implementability hint: a sub-invariant
  "shared tmp leaves V_tmp = 0 after each preserving
  transfer" should be proved as a small intermediate
  lemma before being relied on.

- **Step 8.1 `compileFrag_bprod` sketch (lines
  1638–1687).** "Copy `compileFrag_bsum`'s implementation;
  substitute the addition update with the R^XY_Z
  multiplication update; widen the numRegs by 2 to fit
  the additional scratch registers; adjust PC offsets
  accordingly." Plus a schematic for the R^XY_Z update.
  Density adequate.

- **Step 11 `compileER_runFor` (lines 1962–2063).**
  Theorem statement is concrete; proof skeleton names
  `runFor_add` primary, `runFor_succ` for innermost
  peeling, slack absorption via halt-state self-loop,
  inner induction on `v 0` for `bsum`/`bprod`. Strategy
  cites concrete lemmas
  (`URMState.runFor_add`, `Function.update_apply`) and
  hints at intermediate lemmas (`transferLoop_correct`).
  Adequate.

The four sketches are dense enough that an
implementer-subagent can produce the bodies without
additional design work. The deferral is acceptable.

## Lean-correctness spot-checks

Five new code blocks (the ones the author rewrote in
response to round 1):

1. `compileER_runtime` (Step 10.1) — type-checks and
   matches spec semantics, with reservation about whether
   Lean's elaboration of `Fin.cons i (Fin.tail v)` against
   `f : ERMor1 (k+1)` infers `k+1` cleanly. The `(k := k)`
   constructor pattern in the `bsum`/`bprod` branch
   addresses this explicitly.

2. `compileFrag_succ` (Step 5.2) — body closes goals
   (verified above).

3. `compileFrag_zero` (Step 5.1) — body closes goals
   (verified above).

4. `URMRaw.preservingTransfer` (Step 4.4) — body is a
   single 9-instruction list literal; layout matches the
   architecture-overview description.

5. `compileFrag_sub` (Step 5.4) — body fundamentally OK
   modulo the `Fin`-pattern-exhaustiveness concern (S1).

## Style and discipline conformance

### Banned style words

Two remaining occurrences of "elaborate" (round-1 N1's
"fix" was incomplete):

- Line 1017: "does not elaborate (because `simp` does
  not fully unfold the goal)" — this is the Lean-vernacular
  meaning of "elaborate" (the elaborator phase), not the
  prose meaning. Acceptable in technical commentary about
  Lean.
- Line 1646: "This is more elaborate than `bsum`'s single
  M-template addition" — this is the prose meaning
  (= complex, intricate), which CLAUDE.md style list
  excludes. Should be rewritten (e.g., "This update is
  larger than `bsum`'s single M-template addition" or
  "This update emits a nested loop, in contrast to
  `bsum`'s single M-template addition"). See Nit N1.

### Commit-message tense

The N2 round-1 fix only rewrote Task 1's commit body. The
other 11 task commits (Tasks 2–12) still use indicative-
tense bodies: "URMInstrRaw mirrors URMInstr" (Task 2),
"CompiledFragment a packages numRegs" (Task 3),
"URMRaw.goto encodes unconditional jump" (Task 4),
"compileFrag_zero, …" (Task 5), "compileFrag_comp glues
sub-fragments" (Task 6), "compileFrag_bsum emits …"
(Task 7), "compileFrag_bprod mirrors compileFrag_bsum"
(Task 8), "compileERFrag dispatches" (Task 9),
"compileER_runtime e v: ℕ-valued runtime witness defined"
(Task 10; note: this body is non-verb-led; OK), …. The
Mathlib commit guide mandates **imperative present**
("mirror", "package", "encode", "dispatch", not
"mirrors", "packages", "encodes", "dispatches"). See
Nit N2.

### Markdownlint cleanliness

`markdownlint-cli2` on the plan file reports zero errors.
Round-1 N3 fix is present.

## Blockers

None.

## Serious findings

### S1. Literal-`Fin`-pattern match in `compileFrag_sub`

Exhaustiveness on `Fin 2` is not recognised by Lean
automatically.

Plan Step 5.4, lines 1184–1187 (`inputRegs`), 1195–1201
(`inputRegs_inj`), 1203–1210 (`outputReg_not_input`),
1212–1219 (`zeroReg_not_input`). The pattern
`fun i : Fin 2 => match i with | ⟨0, _⟩ => … | ⟨1, _⟩ => …`
covers both numeric values but relies on Lean's pattern
compiler recognising `Fin 2`-exhaustiveness from
`val < 2`. Lean does *not* perform this automatically;
the implementer will see a missing-cases warning at
build time. Recommend rewriting `inputRegs` using
`Fin.cases ⟨2, by decide⟩ (Fin.cases ⟨3, by decide⟩
Fin.elim0)` or `if h : i.val = 0 then ⟨2, by decide⟩
else ⟨3, by decide⟩`, and rewriting the three invariant
proofs in tactic mode using `Fin.cases` / `fin_cases`.

This is a concrete implementability defect that the
plan must fix before execution; otherwise Task 5's
build step will fail.

## Minor findings

### M1. Spec coverage table still claims Tasks 5.3/6.3 cover the §5.1 prelude discipline

Plan line 2247: "| §5.1 prelude (pre-clone-at-prelude
discipline) | Tasks 5.3 (proj), 6.3 (comp) |". The new
"Divergence from spec §5.1's global prelude discipline"
subsection (lines 303–328) explicitly says the plan
adopts a *localised variant* that does *not* implement
the spec's pre-clone-at-prelude discipline. The coverage
table is inconsistent with the Divergence subsection.
Recommend updating the table row to "§5.1 prelude — see
Divergence subsection; localised variant adopted
(Tasks 5.3, 6.3, 7.1, 8.1 all employ the localised
preserving-transfer idiom)".

### M2. "Plan-style note" heading mismatches its body content

The heading says "three combinator bodies" but the body
discusses four declarations.

The subsection heading at line 233 reads "Plan-style note:
sketches in three combinator bodies", but the body
enumerates `compileFrag_comp`, `compileFrag_bsum`,
`compileFrag_bprod`, and `compileER_runFor` (four
declarations across Tasks 6, 7, 8, 11). The heading
undersells the scope. Recommend renaming to "Plan-style
note: sketches in four declaration bodies" or "…in three
combinator bodies and one correctness theorem".

## Nits

### N1. Two remaining occurrences of "elaborate"

- Line 1017: "does not elaborate (because `simp` does not
  fully unfold the goal)" — Lean-vernacular usage,
  acceptable.
- Line 1646: "This is more elaborate than `bsum`'s single
  M-template addition" — prose usage of a banned
  adjective; rewrite (e.g., "is larger than", "emits a
  nested loop in contrast to").

### N2. Tasks 2–12 commit-message bodies remain in indicative-tense

Round-1 N2's `fix` only touched Task 1's commit. Tasks
2–12 carry bodies like "URMInstrRaw mirrors URMInstr"
(Task 2), "CompiledFragment a packages numRegs" (Task 3),
"URMRaw.goto encodes …" (Task 4), "compileFrag_comp glues
sub-fragments" (Task 6), "compileFrag_bsum emits …"
(Task 7), "compileFrag_bprod mirrors …" (Task 8),
"compileERFrag dispatches …" (Task 9). Mathlib commit
guide mandates imperative present
("mirror"/"package"/"encode"/"dispatch", not
"mirrors"/"packages"/"encodes"/"dispatches"). The
implementer following the plan top-down will copy these
verbs verbatim into commits, propagating the style
violation. Recommend rewriting each task's `jj describe`
body in imperative present.

### N3. "Plan-style note" heading count mismatches its content

See § Minor M2.

## Sign-off

Plan has 0 blockers, 1 serious, 2 minor, 3 nits;
not yet converged on round 2. The single serious finding
(S1: `Fin`-pattern exhaustiveness in `compileFrag_sub`) is
a concrete implementability risk that the implementer will
hit at the first build attempt of Task 5; recommend a
round-3 review after the author rewrites
`compileFrag_sub`'s `inputRegs` and the three associated
invariant proofs using `Fin.cases` or an explicit
val-decision. The remaining minor/nit findings are
documentation tightenings.
