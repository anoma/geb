# T2 plan adversarial review — round 1

## Author responses

- **B1** (`compileER_runtime` body type error): **fix.**
  Rewrote `compileER_runtime` with explicit arity binders
  via constructor-pattern `(k := k)`, `Fin.tail v` in
  place of `fun j => v ⟨1 + j.val, by omega⟩`, and explicit
  `ctx_f : Fin (k + 1) → ℕ` annotation. See plan
  Step 10.1.
- **B2** (silent mathlib imports): **fix.** Replaced
  `Finset.sum` / `Finset.range` / `Finset.univ` with
  `List.finRange` / `List.range` / `List.foldl` from Lean
  core + the existing `Mathlib.Data.List.FinRange` import.
  No new mathlib imports. See plan Step 10.1 and Tech
  Stack section.
- **B3** (five `sorry` placeholders): **defer-with-rationale.**
  Tasks 6, 7, 8, 11 each cover one *contract boundary*
  (one public declaration) whose body is structurally
  larger than other tasks' bodies. Splitting T2 into four
  plan-execute cycles would fragment the spec's
  single-step T2 commitment. The plan now flags this
  decision explicitly under "Plan-style note: sketches in
  three combinator bodies" in the Architecture overview,
  and the per-task verification step still requires the
  `sorry` to be removed before commit. The
  subagent-driven-development workflow's
  implementer-subagent fills in each body during
  execution.
- **S1** (duplicate `preservingTransfer` definitions):
  **fix.** Removed the first (buggy) definition; kept
  only the corrected 9-instruction version.
- **S2** (`mTemplate` miscites Tourlakis's M): **fix.**
  Renamed to `URMRaw.transferLoop` (with helper
  `transferLoopLen`); updated all 12 callsites; clarified
  citation as "body of Tourlakis 2018 p. 19's M program,
  generalised to arbitrary src/dst and omitting trailing
  stop".
- **S3** (spec §5.1 prelude discipline replaced):
  **fix.** Added "Divergence from spec §5.1's global
  prelude discipline" subsection under Architecture
  overview, explicitly flagging the localised variant as
  a deliberate deviation from the spec's prelude-walk
  discipline (with externally-equivalent semantics).
- **S4** (`runFor_succ` peeling on bound `t'`): **fix.**
  Task 11.2 strategy now leads with `URMState.runFor_add`
  as the primary tool for splitting `t' = m + n`; cites
  `runFor_succ` only for innermost peeling. Added slack
  `s := t' - compileER_runtime e v` and halt-state
  self-loop absorption to the proof skeleton.
- **S5** (`compileFrag_succ` `inputRegs_inj` type
  mismatch): **fix.** Rewrote in tactic mode (`by intro
  i j _ ; exact Subsingleton.elim _ _`).
- **S6** (PC offset arithmetic fragile in
  `compileFrag_sub`): **fix.** Added explicit
  parenthesisation: `(.assignR 0 0) :: (pt ++ tl ++ [...])`.
- **S7** (`compileER_runtime` proj branch arity binder):
  **fix.** Changed `| k, .proj i, v` to `| _, .proj i, v`
  for pattern consistency.
- **S8** (spec §12.2–§12.6 coverage table miss):
  **fix.** Expanded coverage table to list §12.2 (T1),
  §12.3 (T3), §12.4 (T5), §12.5 (T3), §12.6 (T4) as
  out-of-T2-scope explicitly.
- **M1** (inert `let _ := rawList`): **fix.** Removed
  the inert binding from `compileFrag_succ`.
- **M2** (`compileFrag_zero` `Fin.elim0` proofs): **fix.**
  Rewrote with explicit `intro a _ _ ; exact Fin.elim0 a`
  pattern for `Function.Injective`-shape goals and `intro
  i _ ; exact Fin.elim0 i` for the disjointness goals.
- **M3** (redundant double Tourlakis + spec citations):
  **defer-with-rationale.** The two citations serve
  different purposes: the Tourlakis citation grounds the
  mathematical content; the spec citation grounds the
  implementation choice (which often diverges from
  Tourlakis's informal text, e.g., the localised
  preserving-transfer discipline of S3). Removing one
  loses information. Where both citations refer to
  exactly the same fact with no implementation diff, the
  spec citation can be dropped — but the plan's current
  citations are not in that category.
- **M4** (`runFor_succ` primacy): **fix.** Same as S4.
- **M5** ("Wait, that's 15" filler): **fix.** Rewrote
  paragraph as "The plan defines fifteen public
  declarations … Additional emission/internal helpers
  introduced by this plan … support the public
  declarations but are not part of the spec's named set."
- **M6** (no `check-axioms.sh` followup pointer):
  **fix.** Step 12.2 now identifies the followup as
  "patch the vendored script under `scripts/` or report
  upstream to the `lean4-skills` repository; that task
  lives outside the erToK workstream and is tracked in
  the project's general infrastructure backlog".
- **N1** ("elaborate", "straightforward"): **fix.** Both
  instances rewritten without value-laden adjectives.
- **N2** ("Sets up", indicative tense): **fix.** Task 1
  commit message rewrote to imperative present ("Set up
  …", "Register …").
- **N3** (markdownlint-cli2 discipline on plan):
  **fix.** Plan verified `markdownlint-cli2`-clean after
  every Edit. Convention documented in the plan's
  "Style and discipline reminders" section.

## Summary

The plan is structurally complete (12 tasks, covering Tasks 1
through 12, mapping spec §5/§5.1/§5.1.1/§5.1.2/§5.2/§9/§10/§12
sections to tasks). However it has several concrete defects:
the `sorry` placeholders in Tasks 6, 7, 8, 11 hide ~80 % of
the actual Lean work behind English sketches with no
guarantee that the sketches type-check, and Task 10's
`compileER_runtime` body is internally inconsistent
(`outerInputs` indexed by `Fin k` but `compileER_runtime f
ctx_f` recurses with a `Fin (k+1)` context that crosses arity
boundaries) and silently introduces two new mathlib imports
not declared in the plan's file-structure section.

Counts: 3 blockers, 8 serious, 6 minor, 3 nits.

## Blockers

### B1. `compileER_runtime` body is a type error as written

Plan lines 1798–1838. The branch

```lean
| _, .bsum f, v =>
    let bound := v 0
    let outerInputs := fun j => v ⟨1 + j.val, by omega⟩
    30 + 10 * bound +
      (Finset.range bound).sum (fun i =>
        let ctx_f : Fin _ → ℕ :=
          Fin.cons i outerInputs
        compileER_runtime f ctx_f
        + 50 + 10 * (i + (Finset.univ.sum
            (fun j => outerInputs j)))
        + 5 * f.interp ctx_f)
```

has multiple defects:

1. `outerInputs := fun j => v ⟨1 + j.val, by omega⟩` does
   not match the spec semantics. `ERMor1.bsum f`'s
   interpretation (`LawvereER.lean:90–92`) uses `Fin.cons i
   (Fin.tail ctx)`, not `fun j => v ⟨1 + j.val, _⟩`. While
   these denote the same function pointwise, `Fin.tail` is
   the upstream-defined form and is what every later proof
   step in Task 11.2 will need to manipulate. Using a hand-
   rolled `1 + j.val` indexing creates an unnecessary
   coercion gap.

2. The pattern `| _, .bsum f, v =>` binds the implicit arity
   to `_`. But `outerInputs` then needs the type `Fin k →
   ℕ` for the recursive call `compileER_runtime f ctx_f` to
   type-check (since `f : ERMor1 (k+1)`). Lean must infer
   `k` from `v : Fin (k+1) → ℕ`; this works, but the
   `outerInputs` definition's `Fin _` and `1 + j.val` are
   ambiguous without explicit `(j : Fin k)` annotation. The
   plan provides no such annotation.

3. The runtime depends recursively on `f.interp ctx_f`,
   i.e., evaluates the ER expression to compute the runtime
   bound. This is *not in itself* an error, but the recursive
   `compileER_runtime` definition does not type-check
   straightforwardly because Lean cannot unify `Fin _` for
   the codomain of `outerInputs` against the implicit `k+1`
   needed in `ctx_f : Fin (k+1) → ℕ`. The `Fin.cons i
   outerInputs` expression needs `i : ℕ` (the head's value
   type) and `outerInputs : Fin k → ℕ`; producing `Fin (k+1)
   → ℕ`. That works only when the implicit `_` in `Fin _ →
   ℕ` resolves to `k+1`, which Lean may or may not infer
   without explicit annotation.

4. Likewise for the `bprod` branch.

The plan must rewrite the body using `Fin.tail v` directly:

```lean
| k, .bsum f, v =>
    let bound := v 0
    30 + 10 * bound +
      (Finset.range bound).sum (fun i =>
        let ctx_f : Fin (k + 1) → ℕ :=
          Fin.cons i (Fin.tail v)
        compileER_runtime f ctx_f + 50 + ...)
```

with the arity bound explicit (replace `_,` with `k,` in the
pattern).

### B2. Task 10 silently adds mathlib imports not declared in the plan

Plan line 1850: "`Finset` and `Finset.range`/`Finset.univ`/sums
require `Mathlib.Algebra.BigOperators.Basic` (for
`Finset.sum`) and `Mathlib.Data.Finset.Range` (for
`Finset.range`). Add these imports to the module's header in
this task if not already present from a transitive resolution."

But the plan's `File structure` (line 137) says:

> No new mathlib helpers beyond what `ZeroTestURM.lean`
> already imports (`Mathlib.Data.List.FinRange`,
> `Mathlib.Logic.Function.Basic`).

Also Tech Stack (line 36): "No new mathlib helpers beyond
what `ZeroTestURM.lean` already imports".

If the plan in fact requires `Mathlib.Algebra.BigOperators.Basic`
and `Mathlib.Data.Finset.Range`, those imports must be
declared at the top of the plan in `File structure` and in
the Task 1 skeleton (Step 1.1), not buried in Task 10. The
two statements are inconsistent. An implementer following
the plan top-down will plant the wrong imports.

Either:

- declare the new imports up-front and remove the "no new
  mathlib helpers" claim; or
- rewrite the runtime using `List.foldl` / `List.finRange`
  (`Mathlib.Data.List.FinRange` is already imported) to
  avoid `Finset.sum` and `Finset.range`.

The plan picks neither path.

### B3. Five `sorry` placeholders in committed code path

Plan Steps 6.3, 7.1, 8.1, 11.1, 11.2 each contain a `sorry`
placeholder in the displayed Lean code. The surrounding
text explicitly tells the implementer "Replace the `sorry`
placeholder with the full implementation in this step"
(lines 1354, 1497, 1641, 1972–1980, 1989). CLAUDE.md §
`sorry`, `admit`, and underscores forbids `sorry` in
committed code; the project's writing-plans skill expects
each task's final state to be commit-clean.

Reviewer judgement: the plan as written *does* require the
implementer to remove the `sorry`s before committing each
task (Step 6.4, 7.2, 8.2, 11.3 verification steps demand a
clean build with no warnings, and `sorry` triggers a
warning). So the *commits* should be clean — but the *plan
itself* presents un-implemented code under the heading
"Define `compileFrag_comp`" / "Define `compileFrag_bsum`"
etc. without giving the actual definition. Each of these
five steps is, in effect, "write the function" with a
sketch attached, not a step of the plan.

Specifically:

- Step 6.3 (`compileFrag_comp`) gives a `sorry` body plus a
  5-bullet construction sketch (lines 1297–1356). The
  sketch references "the implementer's task is to: (1)
  define one fresh-block-allocation helper… (2) compose
  them… (3) concatenate…  (4) discharge the four structural
  invariants by case analysis". This is not a plan step; it
  is a description of the work the plan is supposed to
  define.

- Step 7.1 (`compileFrag_bsum`) likewise: `sorry` plus a
  construction sketch (lines 1442–1537). The actual
  fragment construction is delegated entirely to the
  implementer.

- Step 8.1 (`compileFrag_bprod`) gives a `sorry` plus
  "copy `compileFrag_bsum`'s implementation; substitute
  the addition update with the R^XY_Z multiplication
  update; widen the numRegs by 2…" — but the multiplication
  update itself is a schematic with PC labels written in
  prose, not Lean.

- Step 11.1 + 11.2 (`compileER_runFor`) gives `sorry` for
  every case (zero/succ/proj/sub/comp/bsum/bprod) with
  prose paragraphs around them; the plan estimates 200–400
  lines of proof.

These five steps total an estimated ≥1000 Lean lines that
the plan has not actually drafted. The plan's "12 tasks"
structure is therefore misleading: the bulk of T2's Lean
work is in those five steps, and the plan provides only
prose for them. Compare T1's plan, where each declaration
is given as a complete, type-checking Lean block before the
verification step.

Recommendation: either decompose each of Tasks 6, 7, 8, 11
into multiple subtasks (e.g., Task 6.1 — register
injection helpers; Task 6.2 — instruction-array assembly;
Task 6.3 — invariant discharge; Task 6.4 — type-check the
final definition), or accept that the plan delegates the
hard work to the implementing subagent and rename those
tasks as "drafting" tasks.

## Serious findings

### S1. `URMRaw.preservingTransfer` markdown contains two contradictory definitions

Plan Steps 4.4 (lines 763–785) gives a 9-instruction
`preservingTransfer` with one body, then immediately
("Adjust the definition to emit 9 instructions and set the
exit PC to `pcBase + 9`. The corrected definition is:" line
797) gives a different body for the same name (lines
800–815). An implementer copying the first block will get
the wrong definition; the plan must delete the first
(buggy) block and keep only the corrected version. As
written, the duplication is a defect.

### S2. Plan's M-template signature does not match Tourlakis's M

Plan Step 4.2 (lines 711–746) calls a 4-instruction
destructive transfer the "M-template" and cites "Tourlakis
2018 p. 19 M-template". But Tourlakis's M (p. 19) is a
5-instruction *URM program* for λx.x:

```text
1 : if V_2 = 0 goto 5 else goto 2
2 : V_1 ← V_1 + 1
3 : V_2 ← V_2 ∸ 1
4 : goto 1
5 : stop
```

The plan's `URMRaw.mTemplate` omits the trailing `stop`, since
it is a reusable fragment. That is reasonable. But the plan
calls this 4-instruction fragment "M template" and asserts
"Tourlakis 2018 p. 19 M-template, destructive form. Emits
exactly 4 raw instructions" (line 733). Tourlakis's M is 5
instructions; the plan is citing a re-derived idiom and
calling it M. Either rename to e.g. `transferLoop` and say
"derived from Tourlakis p. 19 M", or amend the citation to
"adapted from Tourlakis p. 19 M, omitting trailing stop".

### S3. Spec §5.1 prelude discipline replaced by per-proj preservation

Spec §5.1 (lines 365–414 of spec) prescribes a *global
prelude* that walks the ER tree, counts `k_i` consumers per
input slot, and emits per-consumer preserving-transfer
clones at PC 0. Per-template `proj i` then reads
*destructively* from its pre-allocated scratch. Plan instead
makes `compileFrag_proj` always preserving (Step 5.3 lines
1014–1051), eliminating the need for a prelude walk but
diverging from spec §5.1's chosen discipline.

This is a legitimate design choice (and arguably simpler),
but it must either be flagged as a deliberate deviation
from the spec or the spec must be amended. Currently the
plan silently inverts the spec's discipline. Spec §5.1.2
also references "the pre-clone-at-prelude discipline
(§5.1 prelude construction) locally to the sub-URM" —
plan's `compileFrag_comp` (Step 6.3) does not implement
such a sub-prelude walk.

The plan's spec-coverage table (line 2159) cites Tasks
"5.3 (proj), 6.3 (comp)" as covering "§5.1 prelude
(pre-clone-at-prelude discipline)" — but neither task
implements a prelude walk. Either the table is wrong, the
plan deviates from spec without flagging, or the discipline
is satisfied by other means.

### S4. `runFor_succ` peeling may not engage when `t'` is a bound, not a literal

Plan Task 11 (lines 1936–1944): "use the `runFor_succ`
simp lemma to peel one step at a time". `URMState.runFor_succ`
(ZeroTestURM.lean:182–185) is

```lean
@[simp] theorem URMState.runFor_succ
    (P : URMProgram) (s : URMState P) (n : ℕ) :
    URMState.runFor P s (n + 1)
      = URMState.runFor P (URMState.step P s) n := rfl
```

For `t' ≥ compileER_runtime e v`, the proof needs to
unfold `runFor t'` step by step. But `t'` is a *bound*, not
a concrete `Nat`; the simp lemma needs `t' = n + 1` to
fire. The proofs will need to use `runFor_add` and
case-split on `t' = runtime + extra`, or peel via `Nat.succ`
matching after substituting a concrete runtime value.
Plan does not address how the structural step-peeling will
interact with the inequality `compileER_runtime e v ≤ t'`.

### S5. Plan's `compileFrag_succ` `inputRegs_inj` proof is type-mismatched

Plan Step 5.2 (lines 941–944):

```lean
inputRegs_inj := fun i j _ => by
  have : i = j := Subsingleton.elim _ _
  exact this
```

`Function.Injective` in mathlib unfolds to
`∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂`. The lambda binder
`fun i j _ =>` does not directly match this curried form
(implicit arguments must be matched with `⦃⦄` or the
function used as `intro`). The likely-working version is:

```lean
inputRegs_inj := by
  intro i j _
  exact Subsingleton.elim _ _
```

The plan's `fun … => by …` style is fragile across
mathlib versions; recommend tactic-mode throughout for
consistency.

### S6. PC offset arithmetic for `compileFrag_sub` is fragile

Plan Step 5.4 lines 1100–1108:

```text
PC 0:   assign V_z 0
PC 1-9: preservingTransfer 1 2 1 4
PC 10-13: mTemplate 10 src=3 dst=5
PC 14:  jumpZR V_5 PC_exit PC_body
PC 15:  dec V_5
PC 16:  dec V_1
PC 17:  goto PC=14
PC 18:  stop
```

The PC 14 jumpZR uses `PC_exit = 18` and `PC_body = 15`.
But the Lean body (lines 1121–1130) writes the literals as
`.jumpZR 5 18 15` — and exit at 18 is the `stopR`.
Currently fine *if* the M-template at PC 10–13 emits
exactly 4 instructions, the preservingTransfer at PC 1–9
emits exactly 9, and PC 0 emits 1: 1 + 9 + 4 + 4 (the inner
loop) + 1 (stop) = 19 instructions, PCs 0–18. Consistent.

However the constructed `rawList` is

```lean
.assignR 0 0 ::
URMRaw.preservingTransfer 1 2 1 4 ++
URMRaw.mTemplate 10 3 5 ++
[ .jumpZR 5 18 15, .decR 5, .decR 1, URMRaw.goto 14, .stopR ]
```

The list-cons / list-append associativity is fragile:
`(.assignR 0 0) :: pt9 ++ mT4 ++ [.jumpZR…]` parses as
`(.assignR 0 0) :: (pt9 ++ (mT4 ++ […]))` per Lean's `::`
right-associativity and `++`'s standard precedence — which
gives `[assign] ++ pt9 ++ mT4 ++ inner5` = 1 + 9 + 4 + 5 =
19. Plan should make this parenthesisation explicit or use
a `List.concat` chain to make the implementer's reading
unambiguous.

### S7. `compileER_runtime`'s arity pattern for `proj` is wrong

Plan Step 10.1 line 1809: `| k, .proj i, v => 11 + 10 * v i`.

But this is structurally wrong as a pattern: the implicit
argument syntax is `{a : ℕ}`, so the pattern should be
`| _, .proj i, v` or `| _ + 1, .proj i, v` if `i : Fin (k+1)`.
The user-named `k` here binds the arity, but the `proj` constructor
in `ERMor1` is `proj {k : ℕ} (i : Fin k) : ERMor1 k`, so the
arity `a` *equals* `k`. Lean will likely accept `| k, .proj i, v`
since the implicit arity for `proj` can unify with the
outer `a`. But the inconsistent naming (`_` everywhere else,
`k` here) is at minimum a style defect; it may also
genuinely confuse Lean's pattern compiler. Use `| _,
.proj i, v => 11 + 10 * v i` for consistency.

### S8. Spec §12.5 / §12.7 / §12.9 coverage misses

Plan's spec-coverage table (lines 2155–2173) maps spec §12
items 1, 7, 8, 9, 10, 11. But spec §12 has items 12.1
through 12.21+ (per spec lines 952–1074, only partly read).
Plan does not cover §12.2–§12.6 (URM correspondence,
simulation lemma transcription, §0.1.0.44 proof, level
claim, runtime bound). Most of these are T3/T4/T5 scope,
not T2 — but the plan should explicitly say so. Instead
the plan's table silently truncates spec §12. Either
expand the table to mark T2-out-of-scope items, or note
that the §12 punch list spans T2–T5.

## Minor findings

### M1. The `let _ := rawList` pattern in `compileFrag_succ` is suspicious

Plan Step 5.2 line 932: `let _ := rawList  -- inert binding
so the let-block parses`. This is a code smell — Lean's
parser handles `let X := …; { ... }` without inert
bindings. Either the code is broken (in which case the
fix is wrong) or the binding is unneeded. Recommend
removing it and verifying the build.

### M2. `compileFrag_zero` `Fin 0` proofs may not close the right goals

Plan Step 5.1 lines 892–897:

```lean
inputRegs_inj := by
  intro a; exact a.elim0
outputReg_not_input := by
  intro i; exact i.elim0
```

`Fin 0` has `Fin.elim0 : Fin 0 → α`, but the goals here
are `_ = _` and `_ ≠ _`, which take `i : Fin 0` as an
argument. The expressions `a.elim0` and `i.elim0` will
work if Lean can infer the goal type from context.
Recommend writing `exact Fin.elim0 a` / `exact Fin.elim0 i`
or `exact (a : Fin 0).elim0`. Plan's `a.elim0` syntax
depends on dot-notation finding `Fin.elim0` from `a`'s
type, which is reliable but worth double-checking by
running the build.

Also: `inputRegs_inj` is `Function.Injective inputRegs`
which is `∀ ⦃a₁ a₂⦄, inputRegs a₁ = inputRegs a₂ → a₁ = a₂`.
Plan's `intro a; exact a.elim0` introduces only one of the
three arguments (the first implicit). Use `intro a _ _;
exact a.elim0` or rely on `Fin.elim0`'s ability to close
any goal under a `Fin 0` hypothesis.

### M3. Docstring text repeats "Tourlakis 2018" cite redundantly

Many declarations carry `Tourlakis 2018 §X p. Y; spec §Z`
where the two citations refer to the same fact. CLAUDE.md
docstring rules (`.claude/rules/lean-coding.md` § Comment
and docstring rules) recommend one literature reference per
declaration. Consolidate: choose either the external
Tourlakis cite or the spec cite — not both — except where
the spec adds genuinely independent content
(implementation-specific choices not in Tourlakis).

### M4. `runFor_succ` peels at the front; correctness proofs more often need `runFor_add`

Plan Task 11 says "use the `runFor_succ` simp lemma to peel
one step at a time". T1's `runFor_succ` peels the front:
`runFor (n+1) = runFor (step s) n`. For correctness proofs
that need to apply IH on a sub-fragment's run-count, the
helper that peels at the *back* is `runFor_add`. The plan
mentions `runFor_add` later (line 1947) but underplays its
centrality. Recommend leading with `runFor_add` and citing
`runFor_succ` only as a special case.

### M5. Step 12.4 mis-counts spec-named declarations

Plan line 2112: "Wait, that's 15." The "Wait" is a banned
conversational filler per CLAUDE.md style rules
(line 180). The lapse into stream-of-consciousness "Wait,
that's 15" is also unprofessional in a checked-in plan.
Rewrite without the filler ("Spec §9 lists 15 declarations
(plus internal helpers introduced by this plan); each must
be present.").

### M6. Step 12.2 references a `check-axioms.sh` bug without filing a follow-up

Plan lines 2065–2070: "The cross-workstream defect that
`scripts/check-axioms.sh` does not handle nested namespaces
is documented in the user's handoff message; it remains
out of scope for T2 and is to be fixed in a separate
remediation cycle (file is vendored from `lean4-skills`;
patch locally or report upstream)." The plan should at
minimum name the remediation branch / issue. As written,
the bug is acknowledged but the trail to its fix is left
implicit.

## Nits

### N1. Capitalised "Wait" and other banned style words

In addition to M5's "Wait", scan plan for: "elaborate"
(line 1239 "most structurally elaborate"), "straightforward"
(line 839), and "load-bearing"-adjacent phrasing. CLAUDE.md
style list forbids "elegant", "clever", "neat", "powerful",
"interesting" — "elaborate" is borderline.

### N2. Commit messages mix "Sets up" and other indicative-tense phrasings

Plan's draft commit messages: line 459 ("Sets up the new
module"), line 464 ("registers the T2 tranche's planned
main definitions"). The Mathlib commit guide (CLAUDE.md
linked: `https://leanprover-community.github.io/contribute/commit.html`)
mandates **imperative present tense** ("set up", not "sets
up"). Plan should rewrite each `jj describe -m` body in
imperative form. Compare T1 plan's commit drafts for the
same drift.

### N3. Plan-line-width compliance not explicitly verified

CLAUDE.md and markdown-writing.md mandate `markdownlint-cli2`
clean. The plan-author's auto-memory
(`feedback_adversarial_review_markdownlint`) says the
review file must also be lint-clean. The plan does not
mention running `markdownlint-cli2` on itself; recommend
adding a final step "verify plan and review markdown is
markdownlint-cli2 clean".

## Sign-off

Plan has 3 blockers, 8 serious, 6 minor, and 3 nits;
not yet converged. The blockers (B1 `compileER_runtime`
type error; B2 missing import declarations;
B3 five `sorry` placeholders representing ~80 % of the
actual Lean code) require structural changes before the
plan is implementable. Recommend a second adversarial round
after the author addresses B1–B3 and S1–S3.
