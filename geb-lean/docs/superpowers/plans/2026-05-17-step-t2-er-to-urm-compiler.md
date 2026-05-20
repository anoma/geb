# Step T2 — ER → URM compiler — Implementation Plan

> **Status (2026-05-20). T2 complete.** All thirteen tasks
> (T2.0 through T2.12 plus the Final holistic review) landed
> across several execution sessions. The climactic theorem
> `compileER_runFor` lives at
> `GebLean/LawvereERKSim/Top.lean`. Every public declaration
> in `GebLean/LawvereERKSim/*.lean` is
> `[propext, Quot.sound]`-only. `lake build` clean.
>
> Plan checkboxes (`- [ ]`) below were not updated incrementally;
> task-level progress was tracked via the live task list and via
> the per-phase handoff documents
> (`docs/superpowers/plans/2026-05-18-step-t2-t11-handoff.md` and
> the per-session execution handoffs under
> `docs/superpowers/plans/2026-05-20-step-t2-t11-*.md`). A
> post-T2 followup branch tracking deferred cleanups (naming
> sweeps, structural extraction, `_pre_stop_correct_*` private
> re-evaluation) is enumerated in the Task 11 handoff doc's
> § "Followup branch (post-T2)".
>
> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Land the ER → URM compiler `compileER : ERMor1 a
→ URMProgram`, its runtime witness `compileER_runtime :
ERMor1 a → (Fin a → ℕ) → ℕ`, and the correctness theorem
`compileER_runFor` stating that running the compiled URM
for `t' ≥ compileER_runtime e v` steps leaves
`(compileER e).outputReg` holding `e.interp v`.
Spec §5 (per-ER-constructor templates) and §5.2
(compiler correctness).

**Architecture:** Compositional fragment-based compiler.
A `CompiledFragment a` is a self-contained URM-like value
parameterised by ER arity `a`, carrying an instruction
array, register count, output register, input register
assignment, plus structural invariants matching
`URMProgram` and one additional reserved-zero register
(used to encode unconditional `goto` via `jumpZ`
self-jump). Per-ER-constructor combinators
(`compileFrag_zero`, …, `compileFrag_bprod`) glue
sub-fragments together by register-index injection and
PC-shifting. The top-level `compileER` is the recursive
driver over `ERMor1 a` dispatching to each combinator.
`compileER_runtime` mirrors the structural recursion to
compute the URM step count; `compileER_runFor` proves
correctness by induction on `e`.

**Tech Stack:** Lean 4 + mathlib4 (transitive). Build via
`lake build`. The lakefile sets `warningAsError = true`;
every Lean linter warning fails the build. No new mathlib
helpers beyond what `ZeroTestURM.lean` already imports
(`Mathlib.Data.List.FinRange`,
`Mathlib.Logic.Function.Basic`).

**Spec:**
[`docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`](../specs/2026-05-16-er-to-k-via-cslib-urm-design.md)
§5 (ER → URM compiler), §5.1 (per-ER-constructor
templates), §5.1.1 (per-iteration prologue for
`bsum`/`bprod`), §5.1.2 (`comp f gs` g-to-f wiring),
§5.2 (`compileER_runtime`, `compileER_runFor`), §9
(module layout: `GebLean/LawvereERKSim.lean`), §10
(constructive discipline), §12 (adversarial-review punch
list).

**T1 artefact (prerequisite):**
[`GebLean/Utilities/ZeroTestURM.lean`](../../../GebLean/Utilities/ZeroTestURM.lean)
— `URMInstr r`, `URMProgram`, `URMState`,
`URMState.step`, `URMState.runFor` with
`runFor_zero`/`runFor_succ`/`runFor_add`, `URMState.init`.

**ER constructor source:**
[`GebLean/LawvereER.lean`](../../../GebLean/LawvereER.lean)
— `ERMor1` inductive (`zero`, `succ`, `proj`, `sub`,
`comp`, `bsum`, `bprod`), `ERMor1.interp`, plus
`@[simp]` reduction lemmas `interp_zero` …
`interp_bprod`.

**Tourlakis citations:** Tourlakis 2018
`PR-complexity-topics.pdf`:

- §0.1.0.37 (pp. 15–16): formal URM semantics; instruction
  set; halt-self-loop convention.
- p. 19 worked example M for `λx.x` and N for `λx.x+1`
  (single-loop destructive transfer of V_2 into V_1, plus
  trailing increment for N).
- p. 19 worked example `R^XY_Z` for `λxy.xy` (nested-loop
  multiplication template).
- p. 20 Loop-to-URM translation template with per-Loop
  scratch register B (the cited per-loop bookkeeping).
- p. 21 bounded-recursion URM template (basis `z ← h(y⃗)`;
  iterator `z ← g(i, y⃗, z)`; decrement of bound register
  per iteration; iteration-index register stepped through
  `0, 1, …`).
- §0.1.0.42 (p. 18): for any `f ∈ E^n` there exists a URM
  computing `f` within time bound in `E^n`; this Lemma
  grounds the existence of `compileER_runtime` as the
  per-template recursive runtime witness.

---

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [File structure](#file-structure)
- [Style and discipline reminders](#style-and-discipline-reminders)
  - [Verifying a clean build](#verifying-a-clean-build)
  - [Test discipline](#test-discipline)
- [Architecture overview](#architecture-overview)
  - [Plan-style note: sketches in four declaration bodies](#plan-style-note-sketches-in-four-declaration-bodies)
  - [Fragment-based compositional compilation](#fragment-based-compositional-compilation)
  - [Divergence from spec §4.1's `URMProgram` field shape](#divergence-from-spec-41s-urmprogram-field-shape)
  - [Divergence from spec §5.1's global prelude discipline](#divergence-from-spec-51s-global-prelude-discipline)
  - [Reserved registers](#reserved-registers)
  - [Goto encoding](#goto-encoding)
  - [Destructive vs preserving transfers](#destructive-vs-preserving-transfers)
- [Task 0 — T1 prerequisite refactor: arity-index `URMProgram`](#task-0--t1-prerequisite-refactor-arity-index-urmprogram)
- [Task 1 — Module skeleton](#task-1--module-skeleton)
- [Task 2 — Raw-instruction intermediate and conversion](#task-2--raw-instruction-intermediate-and-conversion)
- [Task 3 — `CompiledFragment` structure](#task-3--compiledfragment-structure)
- [Task 4 — Emission helpers (M-template, preserving-transfer, goto)](#task-4--emission-helpers-m-template-preserving-transfer-goto)
- [Task 5 — Atom fragment compilers (`zero`, `succ`, `proj`, `sub`)](#task-5--atom-fragment-compilers-zero-succ-proj-sub)
- [Task 6 — `comp` fragment compiler](#task-6--comp-fragment-compiler)
  - [Construction](#construction)
- [Task 7 — `bsum` fragment compiler](#task-7--bsum-fragment-compiler)
  - [Construction sketch](#construction-sketch)
- [Task 8 — `bprod` fragment compiler](#task-8--bprod-fragment-compiler)
- [Task 9 — Top-level `compileER`](#task-9--top-level-compileer)
- [Task 10 — `compileER_runtime`](#task-10--compileer_runtime)
- [Task 11 — `compileER_runFor` correctness theorem](#task-11--compileer_runfor-correctness-theorem)
- [Task 12 — Axiom audit and final verification](#task-12--axiom-audit-and-final-verification)
- [Spec coverage check](#spec-coverage-check)
- [Out of scope](#out-of-scope)

<!-- END doctoc -->

## File structure

**Created:**

- `GebLean/LawvereERKSim.lean` — primary module. Public
  declarations: `URMInstrRaw`, `URMInstrRaw.toBounded`,
  `CompiledFragment`, `compileFrag_zero`,
  `compileFrag_succ`, `compileFrag_proj`,
  `compileFrag_sub`, `compileFrag_comp`,
  `compileFrag_bsum`, `compileFrag_bprod`, `compileER`,
  `compileER_runtime`, `compileER_runFor`. The same module
  is extended in T3–T5 with `simulate`, `boundExprK`,
  `erToK`, `erToKN`, `erToKFunctor`; this plan covers the
  T2-tranche of declarations only.

**Modified:**

- `GebLean/Utilities/ZeroTestURM.lean` (T1 module) — Task
  0 prerequisite refactor lifts `URMProgram`'s
  `numInputs` field into a type parameter so T2's
  `CompiledFragment a` can `extends URMProgram a`
  cleanly. Refactor is mathematically vacuous; touches
  `URMProgram`, `URMState`, `URMState.step`,
  `URMState.runFor` (with reduction lemmas), and
  `URMState.init` signatures only.

No umbrella import in `GebLean.lean` is added at T2 (the
umbrella import lands at T5 when the public-facing
`erToK` is in place).

**Tests:** no separate `GebLeanTests/` module is created
at T2. The universal correctness theorem
`compileER_runFor` is T2's verification surface;
program-specific tests over `compileER`-emitted URMs are
covered by `compileER_runFor` at the universal level. Per
the auto-memory note `feedback_godel_interp_not_decidable_in_tests`,
`#guard` over `URMState.runFor` of compiled URMs is
infeasible: kernel reduction over a destructive-transfer
loop fans out exponentially. T2 confines verification to
the universally-quantified correctness theorem; concrete
end-to-end tests on compiled URMs are out of scope at
both T1 and T2.

## Style and discipline reminders

Each task's code must follow `CLAUDE.md` and
`.claude/rules/lean-coding.md`:

- Lines ≤ 100 characters.
- Spaces around binary operators in source.
- Every implemented function/definition/structure/theorem
  carries a literature reference in its docstring
  (Tourlakis 2018 §0.1.0.37 pp. 15–16, pp. 19–21 templates,
  or §0.1.0.42 p. 18; alternatively, spec §5.1/§5.2).
- Module docstring with required sections (title, summary,
  main definitions, main statements, references, tags) is
  established in Task 1 and extended at each task per
  CLAUDE.md's "Document only the persistent" rule
  (additions describe the declaration as it stands, not
  the iteration that produced it).
- Use `simp only [...]` not bare `simp [...]` per the
  flexible-tactic linter.
- No `sorry`, no `admit`, no warnings
  (`warningAsError = true`).
- No banned words from `CLAUDE.md`'s style list
  ("load-bearing", "key", "important", "elegant",
  "crucial", "beautiful", "clever", "neat", "powerful",
  "interesting", state-judgment words "blocked", "issue",
  "challenge", conversational fillers "yes", "wait",
  "hmm", "careful", "actually").
- No `noncomputable`, no `Classical.*` on any declaration.
  Spec §10 forbids `Classical.choose`, `Classical.choice`,
  `Classical.em` anywhere.
- `markdownlint-cli2` clean if any docs are touched (this
  plan and the spec's doctoc-maintained TOCs are the only
  Markdown touched in T2).
- Two structural invariants of `URMProgram`
  (`inputRegs_inj` and `outputReg_not_input`) are
  inherited by `CompiledFragment`; the additional
  reserved-zero register adds three independent invariants
  (zero-reg disjoint from inputs, zero-reg disjoint from
  output, zero-reg index < numRegs which is automatic from
  the `Fin numRegs` typing).

### Verifying a clean build

To force re-elaboration of a single module:

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereERKSim.olean
lake build GebLean.LawvereERKSim
```

After each task, before committing, run this command.
Inspect the full output for `error:` lines and for warning
lines (any warning fails the build under
`warningAsError = true`).

### Test discipline

`URMState.runFor (compileER e) v t` over any compiled URM
with a destructive-transfer loop runs Tourlakis's
M-template instruction sequence: each iteration unfolds
`Function.update` plus a pattern match on
`URMInstr`. Kernel reduction is exponential in the
instruction count times the input value. The auto-memory
note `feedback_godel_interp_not_decidable_in_tests`
documents the same pathology for `ER` interpretation
unfolding.

T2 therefore relies solely on the universally-quantified
correctness theorem `compileER_runFor`. No `#guard` over
compiled URMs is added. The structure of `compileER_runFor`
(structural induction on `e`, per-constructor case
matching the template structure) is what makes T2's
correctness verifiable in finite proof effort, in contrast
to running concrete URMs at kernel speed.

## Architecture overview

### Plan-style note: sketches in four declaration bodies

Three combinator bodies are out of reach for a single
plan task to fully prescribe in verbatim Lean:
`compileFrag_comp` (Task 6.3), `compileFrag_bsum`
(Task 7.1), `compileFrag_bprod` (Task 8.1). Each
involves register-space injection, PC-shifting, and
discharging four structural invariants on a numRegs
formula that depends on sub-fragment sizes — together
~150–200 Lean lines each. Similarly, the
`compileER_runFor` correctness theorem (Task 11)
estimates ~200–400 lines of proof.

Rather than splitting T2 across four plan-execute cycles
(one per combinator), this plan keeps T2 as one cycle
with these four bodies stubbed via `sorry` plus a
Lean-syntax skeleton (block-by-block guidance with
explicit Lean tokens, not English prose). The
`subagent-driven-development` workflow's
implementer-subagent fills in each body during execution;
the per-task verification step requires the `sorry` to
be removed before the task commits.

The plan's task structure (13 tasks: Task 0 prerequisite
plus 12 T2 tasks) therefore reflects the *contract*
boundaries (one task per public declaration plus one
verification task), not the *Lean line count*. Tasks 6, 7, 8, 11 each cover one
declaration whose body is structurally larger than other
tasks' bodies. The per-task subagent allocates effort
proportionally.

### Fragment-based compositional compilation

The compiler is fragment-based, not state-monadic.
A `CompiledFragment a` is an immutable record `extends
URMProgram a` (after T1's arity-indexing refactor in
Task 0) carrying:

- All fields of `URMProgram a` (`numRegs`, `instrs`,
  `outputReg`, `inputRegs`, `inputRegs_inj`,
  `outputReg_not_input`) — inherited via `extends`.
- `numRegs_pos : 0 < numRegs` (so the reserved-zero
  register `⟨0, _⟩` fits).
- `zeroReg_not_input : ∀ i, inputRegs i ≠ ⟨0, _⟩`.
- `zeroReg_not_output : ⟨0, _⟩ ≠ outputReg`.

The reserved-zero register is conventionally `⟨0,
numRegs_pos⟩` in every fragment. The fragment's first
instruction is `assign ⟨0, _⟩ 0`, defensively zeroing the
reserved register at the start of execution (also serving
as the no-op anchor for the `goto` encoding).

The `extends` relationship auto-generates the forgetful
projection `CompiledFragment.toURMProgram : {a : ℕ} →
CompiledFragment a → URMProgram a`, eliminating the need
for a hand-written conversion. Top-level `compileER`
returns a `URMProgram a` directly by composing
`compileERFrag` with `.toURMProgram`.

### Divergence from spec §4.1's `URMProgram` field shape

The T1-landed `URMProgram` carries `numInputs : ℕ` as a
field; T2's `CompiledFragment a` has the arity `a` as a
type parameter. To `extends` cleanly, T1's `URMProgram`
is refactored at the beginning of T2 execution (Task 0)
to be arity-indexed:

```lean
-- Before (T1 as landed):
structure URMProgram where
  numRegs    : ℕ
  numInputs  : ℕ
  instrs     : Array (URMInstr numRegs)
  ...

-- After (Task 0 refactor):
structure URMProgram (numInputs : ℕ) where
  numRegs : ℕ
  instrs  : Array (URMInstr numRegs)
  ...
```

`URMState`, `URMState.step`, `URMState.runFor`,
`URMState.init` are updated to add an implicit `{a : ℕ}`
binder and replace `P.numInputs` with `a`. The mechanical
edits are detailed in Task 0; Lean's elaborator infers
the implicit `a` at every callsite from `P`'s type.

The refactor is mathematically vacuous (field-form and
parameter-form representations of `(numInputs, numRegs,
…)` carry identical semantic content) but enables the
`extends` factoring that this plan adopts.

Per-ER-constructor combinators glue sub-fragments by:

1. Choosing a register-space injection
   `inj : Fin sub.numRegs → Fin outer.numRegs` that maps
   `sub`'s reserved-zero to `outer`'s reserved-zero,
   `sub`'s inputs to fresh `outer` registers, and `sub`'s
   other registers (including output) to fresh `outer`
   registers.
2. Re-indexing each instruction in `sub.instrs` via
   `URMInstr_reindex inj`, defined task-by-task as needed.
3. PC-shifting `sub`'s instructions: every `jumpZ i l₁ l₂`
   target in `sub.instrs` is shifted by the cumulative
   offset of `sub`'s instruction block within
   `outer.instrs`.
4. Appending the re-indexed, PC-shifted instructions to
   the outer instruction array, plus any glue
   instructions (`transferLoop` transfers, prelude
   pre-clones).

### Divergence from spec §5.1's global prelude discipline

Spec §5.1 prescribes a *global prelude walk*: at compile
time, `compileER` walks the entire ER tree, counts `k_i`
(number of `proj i` consumers per input slot), and emits
per-consumer preserving-transfer clones at PC 0; then
`proj i` reads destructively from its pre-allocated
scratch. This plan adopts a localised variant:
`compileFrag_proj` always emits a preserving-transfer at
the proj site (so every `proj` read is non-destructive of
the input register), and `compileFrag_comp` /
`compileFrag_bsum` / `compileFrag_bprod` clone outer
parameters into `f`'s slot-scratch registers via
preserving-transfer at the appropriate composition or
per-iteration point.

The two disciplines are externally equivalent: both
produce a compiled URM in which every input register is
preserved through any `proj` read. The localised variant
avoids the global-prelude walk and its per-input
`k_i`-counting, at the cost of a constant-factor overhead
per `proj` consumer (one extra preserving-transfer per
read). Spec §5.1's prelude-walk is preserved as an
alternative implementation; this plan deviates
deliberately for simpler combinator boundaries and
records the deviation here.

### Reserved registers

Convention enforced by every `CompiledFragment`:

- Register `⟨0, _⟩` is the reserved-zero register `V_z`.
  Initialised by the first instruction (`assign 0 0`);
  not written by any later instruction. Used as the
  zero-comparand for `goto l ≡ jumpZ V_z l l`.
- The `outputReg` field designates the output register.
- The `inputRegs` function designates input registers.

The injectivity of `inputRegs` and the disjointness of
`outputReg` and the reserved-zero from inputs are
structural invariants enforced at construction time.
These match `URMProgram`'s invariants exactly
(reserved-zero is the only addition).

### Goto encoding

Tourlakis's worked examples (p. 19) use `goto l` as
informal shorthand. The five-instruction URM (§0.1.0.37
p. 16) has no `goto`. Formal encoding:

```text
goto l   ≡   jumpZ V_z l l
```

where `V_z` is the reserved-zero register `⟨0, _⟩` (its
value is always 0 by the reserved-zero invariant, so the
jump always takes the `l₁` branch which equals `l₂` so
the destination is unconditional).

### Destructive vs preserving transfers

Tourlakis's M-template (p. 19) is a destructive transfer:
the source register is zeroed by the inner loop, the
destination accumulates the source's value. Formally,
this is:

```text
-- Destructive transfer V_src → V_dst  (zeroes V_src):
M(src, dst, top_loop, exit):
  top_loop:  jumpZ V_src exit body
  body:      dec V_src
             inc V_dst
             jumpZ V_z top_loop top_loop  -- unconditional goto top_loop
  exit:      ...
```

To copy V_src to V_dst while preserving V_src, the
preserving-transfer idiom uses a tmp register:

```text
-- Preserving transfer V_src → V_dst (V_src unchanged):
PT(src, dst, tmp, top, exit, top2, exit2):
  top:    jumpZ V_src exit body
  body:   dec V_src
          inc V_dst
          inc V_tmp
          jumpZ V_z top top
  exit:   -- Now V_src = 0, V_dst = original, V_tmp = original.
  top2:   jumpZ V_tmp exit2 body2
  body2:  dec V_tmp
          inc V_src
          jumpZ V_z top2 top2
  exit2:  -- Now V_src = original, V_tmp = 0, V_dst = original.
```

This requires one fresh tmp register per preserving
transfer. The combinator `compileFrag_proj` and the
prelude construction inside `compileFrag_comp` (§5.1) and
the per-iteration prologue inside `compileFrag_bsum`,
`compileFrag_bprod` (§5.1.1) all rely on this idiom.

---

## Task 0 — T1 prerequisite refactor: arity-index `URMProgram`

**Files:**

- Modify: `GebLean/Utilities/ZeroTestURM.lean` (T1 module).

Refactor T1's `URMProgram` to be parameterised by
`numInputs : ℕ` rather than carrying it as a field, and
propagate through `URMState`, `URMState.step`,
`URMState.runFor`, the runFor reduction lemmas, and
`URMState.init`. The refactor is mathematically vacuous;
its purpose is to enable T2's `CompiledFragment a extends
URMProgram a` factoring.

- [ ] **Step 0.1: Refactor `URMProgram`**

Change the structure declaration:

```lean
-- Replace this:
@[ext] structure URMProgram where
  numRegs : ℕ
  numInputs : ℕ
  instrs : Array (URMInstr numRegs)
  outputReg : Fin numRegs
  inputRegs : Fin numInputs → Fin numRegs
  inputRegs_inj : Function.Injective inputRegs
  outputReg_not_input : ∀ i, inputRegs i ≠ outputReg

-- With this:
@[ext] structure URMProgram (numInputs : ℕ) where
  /-- Number of registers. -/
  numRegs : ℕ
  /-- Program instructions, indexed by PC. -/
  instrs : Array (URMInstr numRegs)
  /-- The output register (Tourlakis V_1 convention). -/
  outputReg : Fin numRegs
  /-- Input register assignment: input slot `i` writes
  to register `inputRegs i`. -/
  inputRegs : Fin numInputs → Fin numRegs
  /-- Distinct input slots map to distinct registers. -/
  inputRegs_inj : Function.Injective inputRegs
  /-- The output register is disjoint from every input
  register. -/
  outputReg_not_input : ∀ i, inputRegs i ≠ outputReg
```

Drop the `numInputs : ℕ` field; lift `numInputs` into a
type parameter. All other fields and invariants are
preserved.

While touching the T1 module, update its module
docstring's `## Main definitions` entry for `URMProgram`
to describe it as the arity-indexed structure (replacing
"program structure carrying instruction array, register
count, input register assignment..." with "arity-indexed
(by `numInputs`) program structure carrying instruction
array, register count, input register assignment...").

- [ ] **Step 0.2: Refactor `URMState`**

```lean
-- Replace this:
@[ext]
structure URMState (P : URMProgram) where
  pc : ℕ
  regs : Fin P.numRegs → ℕ

-- With this:
@[ext]
structure URMState {a : ℕ} (P : URMProgram a) where
  /-- Program counter (0-indexed; Tourlakis's I(0) = 1
  is mapped to 0 here). -/
  pc : ℕ
  /-- Register contents, indexed by `Fin P.numRegs`. -/
  regs : Fin P.numRegs → ℕ
```

The `{a : ℕ}` implicit is inferred at every callsite
from `P : URMProgram a`.

- [ ] **Step 0.3: Refactor `URMState.step`**

```lean
def URMState.step {a : ℕ} (P : URMProgram a)
    (s : URMState P) : URMState P :=
  -- body unchanged
  if h : s.pc < P.instrs.size then
    match P.instrs[s.pc]'h with
    | URMInstr.assign i c =>
        { pc := s.pc + 1
          regs := Function.update s.regs i c }
    | URMInstr.inc i =>
        { pc := s.pc + 1
          regs := Function.update s.regs i (s.regs i + 1) }
    | URMInstr.dec i =>
        { pc := s.pc + 1
          regs := Function.update s.regs i (s.regs i - 1) }
    | URMInstr.jumpZ i l₁ l₂ =>
        { pc := if s.regs i = 0 then l₁ else l₂
          regs := s.regs }
    | URMInstr.stop => s
  else s
```

Add `{a : ℕ}` to the signature; body unchanged.

- [ ] **Step 0.4: Refactor `URMState.runFor` and reduction lemmas**

```lean
def URMState.runFor {a : ℕ} (P : URMProgram a)
    (s : URMState P) : ℕ → URMState P
  | 0 => s
  | n + 1 => URMState.runFor P (URMState.step P s) n

@[simp] theorem URMState.runFor_zero {a : ℕ}
    (P : URMProgram a) (s : URMState P) :
    URMState.runFor P s 0 = s := rfl

@[simp] theorem URMState.runFor_succ {a : ℕ}
    (P : URMProgram a) (s : URMState P) (n : ℕ) :
    URMState.runFor P s (n + 1)
      = URMState.runFor P (URMState.step P s) n := rfl

theorem URMState.runFor_add {a : ℕ}
    (P : URMProgram a) (s : URMState P) (m n : ℕ) :
    URMState.runFor P s (m + n)
      = URMState.runFor P (URMState.runFor P s m) n := by
  induction m generalizing s with
  | zero => simp only [Nat.zero_add, URMState.runFor]
  | succ m ih =>
    rw [Nat.add_right_comm m 1 n, Nat.add_one]
    change URMState.runFor P (URMState.step P s) (m + n)
      = URMState.runFor P
          (URMState.runFor P (URMState.step P s) m) n
    exact ih (URMState.step P s)
```

Bodies unchanged; only the signature gains `{a : ℕ}`.

- [ ] **Step 0.5: Refactor `URMState.init`**

```lean
def URMState.init {a : ℕ} (P : URMProgram a)
    (v : Fin a → ℕ) : URMState P where
  pc := 0
  regs := fun r =>
    match (List.finRange a).find?
        (fun i => decide (P.inputRegs i = r)) with
    | some i => v i
    | none   => 0
```

Two changes: `{a : ℕ}` added to the signature, and
`Fin P.numInputs` (which no longer exists) is replaced
by `Fin a`. `List.finRange P.numInputs` becomes
`List.finRange a`.

- [ ] **Step 0.6: Verify T1 builds**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ZeroTestURM.olean
lake build GebLean.Utilities.ZeroTestURM
```

Expected: clean build with no warnings. The refactor is
mechanical; any error indicates a missed signature site.

- [ ] **Step 0.7: Commit Task 0**

```bash
jj describe -m "refactor(urm): arity-index URMProgram

Lift URMProgram's numInputs field into a type
parameter; propagate through URMState, URMState.step,
URMState.runFor (with reduction lemmas), URMState.init.
The refactor is mathematically vacuous (field-form and
parameter-form carry identical content); its purpose is
to enable T2's CompiledFragment a extends URMProgram a
factoring.

Step T2 task 0 of 13 (T1 prerequisite)."
jj new
```

---

## Task 1 — Module skeleton

**Files:**

- Create: `GebLean/LawvereERKSim.lean`

- [ ] **Step 1.1: Create the skeleton module**

```lean
import GebLean.LawvereER
import GebLean.Utilities.ZeroTestURM

/-!
# erToK: ER → K^sim_2 via zero-test URM simulation

The compiler half of the erToK construction: emit a
`URMProgram` from an `ERMor1 a` term such that running the
URM long enough produces `e.interp v` in the output
register.

This module's T2 tranche introduces the compiler interface
(`compileER`), its runtime witness
(`compileER_runtime`), and the correctness theorem
(`compileER_runFor`). The Ksim simulator (`simulate`),
runtime bound (`boundExprK`), and final assembly
(`erToK`, `erToKN`, `erToKFunctor`) are added in
subsequent steps T3–T5.

## Main definitions

- `URMInstrRaw`: ℕ-indexed instruction intermediate used
  by compiler combinators before the final register-count
  is known.
- `URMInstrRaw.toBounded`: total conversion from a raw
  instruction to a `URMInstr r`, given a bound proof on
  every register index appearing in the raw instruction.
- `CompiledFragment`: a self-contained compiled URM
  fragment carrying instruction array, register count,
  reserved-zero register, input register assignment, and
  output register. Compositional building block for
  combining sub-fragments into larger fragments.
- `CompiledFragment.toURMProgram`: auto-generated by the
  `extends URMProgram a` clause; forgets the reserved-zero
  fields and returns the underlying `URMProgram a`.
- `compileFrag_zero`, `compileFrag_succ`,
  `compileFrag_proj`, `compileFrag_sub`,
  `compileFrag_comp`, `compileFrag_bsum`,
  `compileFrag_bprod`: per-ER-constructor fragment
  combinators.
- `compileER`: the top-level recursive driver
  `{a : ℕ} → ERMor1 a → URMProgram`.
- `compileER_runtime`: structural-recursive runtime
  witness `{a : ℕ} → ERMor1 a → (Fin a → ℕ) → ℕ`.

## Main statements

- `compileER_runFor`: correctness theorem stating that
  running `compileER e` for any step count
  `t' ≥ compileER_runtime e v` leaves the output register
  holding `e.interp v`.

## References

- Tourlakis 2018 §0.1.0.37 (pp. 15–16): URM semantics.
- Tourlakis 2018 p. 19: worked URM examples (M template
  for `λx.x`, N template for `λx.x+1`, R^XY_Z template
  for `λxy.xy`).
- Tourlakis 2018 p. 20: Loop-to-URM translation template
  with per-Loop scratch register B.
- Tourlakis 2018 p. 21: bounded-recursion URM template.
- Tourlakis 2018 §0.1.0.42 (p. 18): `f ∈ E^n` is
  URM-computable within time bound in `E^n` (existence
  of the runtime witness).
- Spec §5 (ER → URM compiler):
  `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`.

## Tags

URM, compiler, ER, Tourlakis, simulation
-/

namespace GebLean

namespace LawvereERKSim

open GebLean.ZeroTestURM

end LawvereERKSim

end GebLean
```

- [ ] **Step 1.2: Verify the skeleton builds**

Run:

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereERKSim.olean
lake build GebLean.LawvereERKSim
```

Expected: clean build with no warnings (the module is
empty besides the namespace).

- [ ] **Step 1.3: Commit Task 1**

Project rule (CLAUDE.md): use `jj` for state-mutating
operations, not raw `git commit`. The working-copy commit
is the current task's work; set its description with `jj
describe`, then `jj new` to start a fresh working-copy
commit for the next task:

```bash
jj describe -m "feat(ertok): module skeleton for LawvereERKSim

Set up the new module GebLean/LawvereERKSim.lean to host
the T2-T5 declarations of the erToK direction.  Register
the T2 tranche's planned main definitions in the module
docstring; add T3-T5 entries when those steps land.

Spec §9 module layout; Step T2 task 1 of 13."
jj new
```

---

## Task 2 — Raw-instruction intermediate and conversion

**Files:**

- Modify: `GebLean/LawvereERKSim.lean` (append)

- [ ] **Step 2.1: Define `URMInstrRaw`**

Append inside `namespace LawvereERKSim`:

```lean
/-- Raw URM instruction with ℕ-indexed registers and
absolute PC labels. Compiler combinators emit raw
instructions during composition; the final
`CompiledFragment` constructs the `URMInstr numRegs`
array by converting each raw instruction through
`URMInstrRaw.toBounded` once `numRegs` is known.

The five constructors mirror `URMInstr` exactly except
register indices are plain ℕ instead of `Fin r`. Tourlakis
2018 §0.1.0.37 p. 16. -/
inductive URMInstrRaw : Type
  /-- `assignR i c` is Tourlakis's `V_i ← c`. -/
  | assignR (i c : ℕ) : URMInstrRaw
  /-- `incR i` is Tourlakis's `V_i ← V_i + 1`. -/
  | incR (i : ℕ) : URMInstrRaw
  /-- `decR i` is Tourlakis's `V_i ← V_i ∸ 1`. -/
  | decR (i : ℕ) : URMInstrRaw
  /-- `jumpZR i l₁ l₂` is Tourlakis's two-target
  zero-test jump. -/
  | jumpZR (i l₁ l₂ : ℕ) : URMInstrRaw
  /-- `stopR` is Tourlakis's halt. -/
  | stopR : URMInstrRaw
  deriving Repr, DecidableEq, Inhabited
```

- [ ] **Step 2.2: Define `URMInstrRaw.regBound`**

```lean
/-- The maximum register index referenced by a raw
instruction, plus 1. Provides the lower bound on
`numRegs` needed to type the instruction as
`URMInstr numRegs`. -/
def URMInstrRaw.regBound : URMInstrRaw → ℕ
  | .assignR i _ => i + 1
  | .incR i => i + 1
  | .decR i => i + 1
  | .jumpZR i _ _ => i + 1
  | .stopR => 0
```

- [ ] **Step 2.3: Define `URMInstrRaw.toBounded`**

```lean
/-- Convert a raw instruction to a bounded `URMInstr r`,
given a bound proof on the raw instruction's register
index. Total function; the bound proof is consumed at the
`Fin r` construction site. -/
def URMInstrRaw.toBounded
    (r : ℕ) (instr : URMInstrRaw)
    (h : instr.regBound ≤ r) : URMInstr r :=
  match instr, h with
  | .assignR i c, h => .assign ⟨i, h⟩ c
  | .incR i, h => .inc ⟨i, h⟩
  | .decR i, h => .dec ⟨i, h⟩
  | .jumpZR i l₁ l₂, h => .jumpZ ⟨i, h⟩ l₁ l₂
  | .stopR, _ => .stop
```

The `h : instr.regBound ≤ r` premise unfolds per
constructor to `i + 1 ≤ r` (i.e., `i < r`) for the
register-indexing cases, and `0 ≤ r` (trivially true) for
the `stopR` case. The anonymous constructor `⟨i, h⟩`
relies on `Nat.lt_iff_add_one_le` (definitional in
mathlib) to convert `i + 1 ≤ r` to `i < r`. If the
unfolding does not happen automatically, replace
`⟨i, h⟩` with `⟨i, Nat.lt_of_succ_le h⟩` (explicit lemma
invocation).

- [ ] **Step 2.4: Define `URMInstrRaw.toBoundedArray`**

The bound proof on a per-instruction basis is not
discharged automatically by `cases ins <;> simp <;>
omega`: the lambda's `ins` is an arbitrary `URMInstrRaw`,
and the `assignR i c` branch leaves a goal
`i + 1 ≤ r` with `i : ℕ` unconstrained. The principled
remedy is a list-level boundedness predicate plus a
batch conversion that carries the list-membership
hypothesis pointwise via `List.attach`.

```lean
/-- All raw instructions in a list have register bound
≤ `r`. -/
def URMInstrRaw.boundedBy (r : ℕ) (l : List URMInstrRaw) :
    Prop :=
  ∀ ins ∈ l, URMInstrRaw.regBound ins ≤ r

/-- Batch-convert a `URMInstrRaw.boundedBy r`-witnessed list
of raw instructions to an `Array (URMInstr r)`. Uses
`List.attach` to carry the membership proof pointwise. -/
def URMInstrRaw.toBoundedArray (r : ℕ) (l : List URMInstrRaw)
    (h : URMInstrRaw.boundedBy r l) :
    Array (URMInstr r) :=
  (l.attach.map (fun ⟨ins, hmem⟩ =>
    URMInstrRaw.toBounded r ins (h ins hmem))).toArray
```

`List.attach` is in Lean core; it produces
`List { x // x ∈ l }`. The lambda destructures the
membership proof `hmem : ins ∈ l` and feeds it into the
list-level boundedness witness `h`.

Atomic combinators in Task 5 use `URMInstrRaw.toBoundedArray`
with an explicit list-level bound proof (one
`URMInstrRaw.boundedBy 4 rawList` per combinator, dispatched
by case analysis over the concrete instruction list).
The composite combinators in Tasks 6, 7, 8 produce
their boundedness proofs by composition: a sub-fragment
`F` already carries the invariant that its instructions
are `URMInstr F.numRegs`-typed; after re-indexing via
`URMInstr.reindex inj` into the outer register space,
the boundedness lift is automatic (because `inj` lands
in `Fin outer.numRegs`).

- [ ] **Step 2.5: Verify build**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereERKSim.olean
lake build GebLean.LawvereERKSim
```

Expected: clean build with no warnings.

- [ ] **Step 2.6: Commit Task 2**

```bash
jj describe -m "feat(ertok): raw-instruction intermediate URMInstrRaw

Mirror URMInstr with ℕ-indexed registers as URMInstrRaw;
convert to URMInstr r via URMInstrRaw.toBounded given a
per-instruction register-bound proof; batch-convert
boundedness-witnessed lists to URMInstr-arrays via
URMInstrRaw.toBoundedArray over List.attach.  Use the raw form
in per-constructor combinators to emit instructions
before the final numRegs is known.

Spec §5.1 register-allocation discipline; Step T2 task 2
of 13."
jj new
```

---

## Task 3 — `CompiledFragment` structure

**Files:**

- Modify: `GebLean/LawvereERKSim.lean` (append)

- [ ] **Step 3.1: Define `CompiledFragment`**

Append inside `namespace LawvereERKSim`:

```lean
/-- A compiled URM fragment for a sub-expression of arity
`a`. Compositional building block: per-ER-constructor
combinators (`compileFrag_*`) glue sub-fragments into
larger fragments by register-index injection and
PC-shifting; the top-level `compileER` returns the
fragment's underlying `URMProgram a` via the
auto-generated `.toURMProgram`.

Extends `URMProgram a` (the arity-indexed URM kernel
program type, Task 0 refactor); adds the reserved-zero
convention used to encode unconditional `goto` via
`jumpZ V_z l l` per spec §5.1.

Convention: the reserved-zero register is `⟨0, …⟩` and
the first instruction in `instrs` is `assign ⟨0, …⟩ 0`,
defensively initialising it. -/
@[ext] structure CompiledFragment (a : ℕ)
    extends URMProgram a where
  /-- 0 < numRegs (the reserved-zero register exists). -/
  numRegs_pos : 0 < numRegs
  /-- Reserved-zero register `⟨0, numRegs_pos⟩` disjoint
  from all input registers. -/
  zeroReg_not_input : ∀ i, inputRegs i ≠ ⟨0, numRegs_pos⟩
  /-- Reserved-zero register disjoint from the output
  register. -/
  zeroReg_not_output : (⟨0, numRegs_pos⟩ : Fin numRegs)
    ≠ outputReg
```

The `extends URMProgram a` clause inherits all fields
(`numRegs`, `instrs`, `outputReg`, `inputRegs`) and both
URMProgram invariants (`inputRegs_inj`,
`outputReg_not_input`). Lean auto-generates the forgetful
projection `CompiledFragment.toURMProgram :
CompiledFragment a → URMProgram a`.

- [ ] **Step 3.2: Define `CompiledFragment.zeroReg`**

```lean
/-- The reserved-zero register `⟨0, F.numRegs_pos⟩`. -/
def CompiledFragment.zeroReg {a : ℕ}
    (F : CompiledFragment a) : Fin F.numRegs :=
  ⟨0, F.numRegs_pos⟩
```

- [ ] **Step 3.3: Verify build**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereERKSim.olean
lake build GebLean.LawvereERKSim
```

Expected: clean build with no warnings.

- [ ] **Step 3.4: Commit Task 3**

```bash
jj describe -m "feat(ertok): CompiledFragment compositional building block

Introduce CompiledFragment a as a refinement of
URMProgram a (Task 0's arity-indexed kernel) adding
numRegs_pos and two reserved-zero disjointness
invariants.  The extends clause auto-generates the
forgetful toURMProgram projection.

Spec §5.1; Step T2 task 3 of 13."
jj new
```

---

## Task 4 — Emission helpers (M-template, preserving-transfer, goto)

**Files:**

- Modify: `GebLean/LawvereERKSim.lean` (append)

This task defines three reusable raw-instruction emitter
helpers consumed by the per-constructor combinators in
Tasks 5–8. Each helper returns a list of
`URMInstrRaw` plus the post-emission PC offset (number of
instructions emitted).

- [ ] **Step 4.1: Define `URMRaw.goto`**

Append:

```lean
/-- Encode unconditional `goto l` as Tourlakis's
informal shorthand (p. 19): two-target zero-test jump on
the reserved-zero register `V_z` (= register 0). Both
branches go to `l`, so the jump is unconditional.

Returns a single raw instruction. -/
def URMRaw.goto (l : ℕ) : URMInstrRaw :=
  .jumpZR 0 l l
```

- [ ] **Step 4.2: Define `URMRaw.transferLoop` (destructive transfer)**

Destructive register-transfer loop, adapted from
Tourlakis 2018 p. 19's M program for `λx.x` (the body of
M minus its trailing `stop`, with `V_2`/`V_1` generalised
to `src`/`dst`). M itself is a 5-instruction *complete
URM* (lines 1–5 of Tourlakis's p. 19 listing, including
the closing `stop` at line 5); this fragment is the
4-instruction *body* used as a reusable building block.

The template emits four raw instructions starting at PC
offset `pcBase`:

```text
pcBase:     jumpZR src     pcBase+4   pcBase+1
pcBase+1:   decR src
pcBase+2:   incR dst
pcBase+3:   goto pcBase
pcBase+4:   -- exit
```

Effect: when execution reaches `pcBase`, the loop runs
`V_src` times, decrementing `V_src` and incrementing
`V_dst` each iteration. On exit, `V_src = 0` and
`V_dst = V_dst_initial + V_src_initial`. Exit PC is
`pcBase + 4`.

```lean
/-- Destructive transfer `V_dst ← V_dst + V_src;
V_src ← 0`. Body of Tourlakis 2018 p. 19's M program for
`λx.x`, generalised to arbitrary `src` and `dst` and
omitting the trailing `stop`. Emits exactly 4 raw
instructions starting at PC offset `pcBase`; exit PC is
`pcBase + 4`.

Returns the instruction list. The caller is responsible
for placing the returned instructions at `pcBase` in the
overall fragment. -/
def URMRaw.transferLoop (pcBase src dst : ℕ) :
    List URMInstrRaw :=
  [ .jumpZR src (pcBase + 4) (pcBase + 1),
    .decR src,
    .incR dst,
    URMRaw.goto pcBase ]
```

- [ ] **Step 4.3: Define `URMRaw.transferLoopLen`**

```lean
/-- Number of raw instructions emitted by
`transferLoop`. -/
def URMRaw.transferLoopLen : ℕ := 4
```

- [ ] **Step 4.4: Define `URMRaw.preservingTransfer`**

The preserving-transfer idiom uses two M-template loops
plus a tmp register. From the architecture overview's
"Destructive vs preserving transfers" section: loop 1
zeroes V_src into V_dst and V_tmp; loop 2 restores V_src
from V_tmp.

Layout (5 instructions for loop 1 at PCs
`pcBase..pcBase+4`; 4 instructions for loop 2 at PCs
`pcBase+5..pcBase+8`; total 9 instructions; exit PC =
`pcBase + 9`):

```lean
/-- Preserving transfer `V_dst ← V_dst + V_src;
V_src unchanged`. Two destructive-transfer loops via a
tmp register; spec §5.1 register-allocation discipline.
Emits exactly 9 raw instructions starting at PC offset
`pcBase`; exit PC is `pcBase + 9`. -/
def URMRaw.preservingTransfer
    (pcBase src dst tmp : ℕ) : List URMInstrRaw :=
  -- Loop 1: V_src consumed; V_dst, V_tmp accumulate.
  -- PCs pcBase..pcBase+4 (5 instructions):
  [ .jumpZR src (pcBase + 5) (pcBase + 1),  -- pcBase
    .decR src,                              -- pcBase+1
    .incR dst,                              -- pcBase+2
    .incR tmp,                              -- pcBase+3
    URMRaw.goto pcBase,                     -- pcBase+4
  -- Loop 2: V_tmp consumed; V_src restored.
  -- PCs pcBase+5..pcBase+8 (4 instructions):
    .jumpZR tmp (pcBase + 9) (pcBase + 6),  -- pcBase+5
    .decR tmp,                              -- pcBase+6
    .incR src,                              -- pcBase+7
    URMRaw.goto (pcBase + 5) ]              -- pcBase+8
```

The first loop's `goto pcBase` jumps back to the loop
test at `pcBase`; the second loop's `goto pcBase+5`
jumps back to its own test at `pcBase+5`.

- [ ] **Step 4.5: Define `URMRaw.preservingTransferLen`**

```lean
/-- Number of raw instructions emitted by
`preservingTransfer`. -/
def URMRaw.preservingTransferLen : ℕ := 9
```

- [ ] **Step 4.6: Verify build**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereERKSim.olean
lake build GebLean.LawvereERKSim
```

Expected: clean build with no warnings. The
fixed-length-constant pattern means the helpers are
`Decidable`-free total functions whose PC arithmetic
reduces to concrete `Nat` literals at every callsite.

- [ ] **Step 4.7: Commit Task 4**

```bash
jj describe -m "feat(ertok): emission helpers transferLoop and preservingTransfer

Encode unconditional jump via the reserved-zero register
as URMRaw.goto; emit Tourlakis p. 19's destructive
transfer in 4 instructions as URMRaw.transferLoop; emit
the preserving variant (two transfer loops via a tmp
register) in 9 instructions as URMRaw.preservingTransfer.

Spec §5.1 destructive vs preserving transfer discipline;
Step T2 task 4 of 13."
jj new
```

---

## Task 5 — Atom fragment compilers (`zero`, `succ`, `proj`, `sub`)

**Files:**

- Modify: `GebLean/LawvereERKSim.lean` (append)

Defines four per-constructor fragment combinators for the
atomic ER constructors. None of these need sub-fragments;
they emit fixed instruction sequences from scratch.

- [ ] **Step 5.1: Define `compileFrag_zero`**

`ERMor1.zero : ERMor1 0`. Output is the constant `0`.
Per spec §5.1: `V_out ← 0; stop`. Two instructions.

The compiled fragment has `numRegs = 2`: register 0 is
the reserved-zero (initialized by `assign 0 0` at PC 0),
register 1 is the output. No inputs.

```lean
/-- Fragment for `ERMor1.zero`. Tourlakis 2018 §0.1.0.37
p. 16 instruction set; spec §5.1 zero template. Output is
the constant 0; emits `assign V_z 0; assign V_out 0;
stop`. -/
def compileFrag_zero : CompiledFragment 0 where
  numRegs := 2
  numRegs_pos := by decide
  inputRegs := Fin.elim0
  outputReg := ⟨1, by decide⟩
  instrs := #[
    .assign ⟨0, by decide⟩ 0,
    .assign ⟨1, by decide⟩ 0,
    .stop ]
  inputRegs_inj := by
    intro a _ _
    exact Fin.elim0 a
  outputReg_not_input := by
    intro i _
    exact Fin.elim0 i
  zeroReg_not_input := by
    intro i _
    exact Fin.elim0 i
  zeroReg_not_output := by decide
```

- [ ] **Step 5.2: Define `compileFrag_succ`**

`ERMor1.succ : ERMor1 1`. Output is `(ctx 0).succ`.

Per spec §5.1: clone the input to the output via
preserving-transfer, then increment the output once,
then stop. Compiled fragment: `numRegs = 4`. Register 0:
reserved-zero. Register 1: output. Register 2: input
slot 0. Register 3: tmp scratch for preserving-transfer.

Instructions:

```text
PC 0:   assign V_z 0          -- reserved-zero init
PC 1..9: preservingTransfer pcBase=1, src=2, dst=1, tmp=3
                              -- copies V_2 → V_1, preserves V_2
PC 10:  inc V_out
PC 11:  stop
```

```lean
/-- Fragment for `ERMor1.succ`. Tourlakis 2018 p. 19
N-template (M plus one increment); spec §5.1 succ
template. Copies the single input to the output
non-destructively, then increments. -/
def compileFrag_succ : CompiledFragment 1 :=
  let rawList : List URMInstrRaw :=
    (.assignR 0 0)
      :: (URMRaw.preservingTransfer 1 2 1 3
          ++ [.incR 1, .stopR])
  -- numRegs = 4 (registers 0..3 used).
  have hBound : URMInstrRaw.boundedBy 4 rawList := by
    -- The list is concrete (1 + 9 + 2 = 12 instructions);
    -- every register index in {0, 1, 2, 3} is < 4.
    -- Unfold membership through the let-binding, then
    -- rcases the resulting finite disjunction.
    intro ins hmem
    simp only [rawList, URMRaw.preservingTransfer,
      URMRaw.goto, List.mem_cons, List.mem_append,
      List.mem_singleton] at hmem
    rcases hmem with
      rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  { numRegs := 4
    numRegs_pos := by decide
    inputRegs := fun _ => ⟨2, by decide⟩
    outputReg := ⟨1, by decide⟩
    instrs := URMInstrRaw.toBoundedArray 4 rawList hBound
    inputRegs_inj := by
      intro i j _
      exact Subsingleton.elim _ _
    outputReg_not_input := by
      intro i h
      have hv : (⟨2, by decide⟩ : Fin 4)
        = ⟨1, by decide⟩ := h
      exact absurd (Fin.mk.inj_iff.mp hv).1 (by decide)
    zeroReg_not_input := by
      intro i h
      have hv : (⟨2, by decide⟩ : Fin 4)
        = ⟨0, by decide⟩ := h
      exact absurd (Fin.mk.inj_iff.mp hv).1 (by decide)
    zeroReg_not_output := by decide }
```

The structural-invariant proofs reuse the
`Fin.mk.inj_iff` extractor to reduce `Fin` equality to
`ℕ` equality, then `decide` (or arithmetic via `omega`)
closes the goal. The `Subsingleton.elim` step for
`inputRegs_inj` exploits that `Fin 1` has at most one
element.

The `cases ins <;>
          simp only [URMInstrRaw.regBound] <;> omega`
chain handles the per-instruction `regBound ≤ 4` proof:
each raw instruction in `rawList` has `regBound ≤ 4`
(the largest index used is `3`, hence `regBound ≤ 4`).

If `cases ins <;>
          simp only [URMInstrRaw.regBound] <;> omega`
does not elaborate (because `simp` does not fully unfold
The `URMInstrRaw.boundedBy 4 rawList` proof obligation
discharges over the concrete instruction list by
unfolding `rawList`, unfolding the
`preservingTransfer`/`goto` helpers, applying
`List.mem_cons` / `List.mem_append` /
`List.mem_singleton` to flatten the membership, then
`rcases` over the resulting finite disjunction of
equalities followed by `decide` per case.

If the `rcases` chain becomes inconvenient (the count of
`rfl`s must match the unfolded list length), the
implementer can switch to a single-line
`by intro ins hmem; revert hmem; decide` provided
`URMInstrRaw.boundedBy 4 rawList` reduces to a decidable
proposition in Lean's kernel (which it does when
`rawList` is a closed term and `URMInstrRaw` has
decidable equality, both of which hold here).

- [ ] **Step 5.3: Define `compileFrag_proj`**

`ERMor1.proj i : ERMor1 k` for `i : Fin k`. Output is
`ctx i`.

Per spec §5.1: copy `V_in_i` to `V_out` via the
preserving-transfer idiom (so the input is preserved for
any other proj-use). Compiled fragment: `numRegs = k + 3`.
Register 0: reserved-zero. Register 1: output. Registers
`2..(2+k-1)`: input slots, with slot `j` at register
`2+j`. Register `2+k`: tmp scratch for the
preserving-transfer.

```lean
/-- Fragment for `ERMor1.proj i`. Spec §5.1 proj
template. Preserving-transfer from input slot `i`'s
register to the output. -/
def compileFrag_proj {k : ℕ} (i : Fin k) :
    CompiledFragment k :=
  let rawList : List URMInstrRaw :=
    (.assignR 0 0)
      :: ((URMRaw.preservingTransfer 1 (2 + i.val) 1 (2 + k))
          ++ [.stopR])
  have hBound : URMInstrRaw.boundedBy (k + 3) rawList := by
    intro ins hmem
    simp only [rawList, URMRaw.preservingTransfer,
      URMRaw.goto, List.mem_cons, List.mem_append,
      List.mem_singleton] at hmem
    rcases hmem with
      rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    all_goals (simp only [URMInstrRaw.regBound];
      have : i.val < k := i.isLt; omega)
  { numRegs := k + 3
    numRegs_pos := by omega
    inputRegs := fun j => ⟨2 + j.val, by omega⟩
    outputReg := ⟨1, by omega⟩
    instrs := URMInstrRaw.toBoundedArray (k + 3) rawList hBound
    inputRegs_inj := by
      intro p q hpq
      have : (⟨2 + p.val, by omega⟩ : Fin (k + 3))
        = ⟨2 + q.val, by omega⟩ := hpq
      apply Fin.ext
      have h := (Fin.mk.inj_iff.mp this).1
      omega
    outputReg_not_input := by
      intro p hp
      have : (⟨2 + p.val, by omega⟩ : Fin (k + 3))
        = ⟨1, by omega⟩ := hp
      have h := (Fin.mk.inj_iff.mp this).1
      omega
    zeroReg_not_input := by
      intro p hp
      have : (⟨2 + p.val, by omega⟩ : Fin (k + 3))
        = ⟨0, by omega⟩ := hp
      have h := (Fin.mk.inj_iff.mp this).1
      omega
    zeroReg_not_output := by
      intro h
      have hh : (⟨0, by omega⟩ : Fin (k + 3))
        = ⟨1, by omega⟩ := h
      have hh' := (Fin.mk.inj_iff.mp hh).1
      omega }
```

- [ ] **Step 5.4: Define `compileFrag_sub`**

`ERMor1.sub : ERMor1 2`. Output is `(ctx 0) - (ctx 1)`
(truncated subtraction).

Per spec §5.1: derived Loop program
`Z ← X; Loop Y { Z ← Z ∸ 1 } end`, then Loop-to-URM
translation. Compiled fragment: `numRegs = 6`. Register
0: reserved-zero. Register 1: output (= `Z`). Register 2:
input 0 (`X`). Register 3: input 1 (`Y`). Register 4:
tmp for preserving-transfer of `X` (so input 0 is
preserved). Register 5: tmp for the outer-Loop scratch
register `B` (Tourlakis p. 20 per-Loop scratch).

Instructions:

```text
PC 0:    assign V_z 0
PC 1-9:  preservingTransfer 1 src=2 dst=1 tmp=4
                                 -- V_out ← V_X (preserving)
-- Loop-to-URM expansion of `Loop V_Y { V_out ← V_out ∸ 1 }`:
PC 10-?: preservingTransfer 10 src=3 dst=5 tmp=?
                                 -- copy V_Y to scratch B (preserves V_Y)
   ...
-- Or equivalently: Tourlakis's per-Loop bookkeeping.
PC ?:    stop
```

Concrete instruction-by-instruction layout for `sub`:

```text
PC 0:   assign V_z 0
PC 1-9: preservingTransfer 1 2 1 4         -- V_1 ← V_2 (preserves V_2)
PC 10-18: preservingTransfer 10 3 5 ???    -- problem: need another tmp
```

The preserving-transfer of `Y` into the outer-Loop scratch
register needs a second tmp register; we don't have one
within the fragment. Either widen the fragment by one
register (`numRegs = 7`), or perform a destructive copy
of `Y` to the loop scratch (since `Y` is needed only
once after the copy, this is acceptable).

Resolved layout (destructive copy of `Y` into scratch
`B`):

```text
PC 0:   assign V_z 0
PC 1-9: preservingTransfer 1 2 1 4         -- V_1 ← V_2 (preserves V_2)
PC 10-13: transferLoop 10 src=3 dst=5         -- V_5 ← V_3 (destroys V_3)
-- Loop body: while V_5 > 0, decrement V_1, decrement V_5:
PC 14:  jumpZR V_5 PC_exit PC_body
PC 15:  dec V_5
PC 16:  dec V_1
PC 17:  goto PC=14
PC 18:  stop      -- exit
```

Register count: 6. Reserved-zero invariant: V_z = 0
holds throughout (only PC 0 writes V_z, and the goto at
PC 17 is `jumpZR V_z 14 14`).

```lean
/-- Fragment for `ERMor1.sub`. Spec §5.1 sub template:
preserving-transfer X to output; destructive copy of Y
to scratch; outer loop decrementing both output and
scratch. Tourlakis 2018 p. 19 M-template plus
Loop-to-URM expansion (p. 20). -/
def compileFrag_sub : CompiledFragment 2 :=
  let rawList : List URMInstrRaw :=
    (.assignR 0 0)
      :: ((URMRaw.preservingTransfer 1 2 1 4)
          ++ (URMRaw.transferLoop 10 3 5)
          ++ [ .jumpZR 5 18 15,
               .decR 5,
               .decR 1,
               URMRaw.goto 14,
               .stopR ])
  have hBound : URMInstrRaw.boundedBy 6 rawList := by
    intro ins hmem
    simp only [rawList, URMRaw.preservingTransfer,
      URMRaw.transferLoop, URMRaw.goto,
      List.mem_cons, List.mem_append,
      List.mem_singleton] at hmem
    rcases hmem with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  { numRegs := 6
    numRegs_pos := by decide
    inputRegs :=
      Fin.cases (⟨2, by decide⟩ : Fin 6)
        (Fin.cases (⟨3, by decide⟩ : Fin 6) Fin.elim0)
    outputReg := ⟨1, by decide⟩
    instrs := URMInstrRaw.toBoundedArray 6 rawList hBound
    inputRegs_inj := by
      intro p q hpq
      -- `Fin 2` has values `0` and `1`; case-split both;
      -- discharge each combination by reflexivity or by
      -- contradicting `hpq` via decidable inequality.
      fin_cases p <;> fin_cases q <;>
        first | rfl | (exfalso; revert hpq; decide)
    outputReg_not_input := by
      intro p hp
      fin_cases p <;> exact absurd hp (by decide)
    zeroReg_not_input := by
      intro p hp
      fin_cases p <;> exact absurd hp (by decide)
    zeroReg_not_output := by decide }
```

- [ ] **Step 5.5: Verify build**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereERKSim.olean
lake build GebLean.LawvereERKSim
```

Expected: clean build with no warnings.

- [ ] **Step 5.6: Commit Task 5**

```bash
jj describe -m "feat(ertok): atom fragment compilers zero, succ, proj, sub

Realize Tourlakis 2018 p. 19 M and N templates and p. 20
Loop-to-URM expansion in the four atomic combinators
compileFrag_zero, compileFrag_succ, compileFrag_proj,
compileFrag_sub.

Spec §5.1 atomic templates; Step T2 task 5 of 13."
jj new
```

---

## Task 6 — `comp` fragment compiler

**Files:**

- Modify: `GebLean/LawvereERKSim.lean` (append)

`ERMor1.comp f gs` with `f : ERMor1 k`, `gs : Fin k →
ERMor1 a`. Output is
`f.interp (fun i => (gs i).interp ctx)`.

Per spec §5.1.2: sequentially run each sub-URM `gs i`,
storing its output in a dedicated register; then
destructively transfer those outputs into `f`'s input
slot registers; then run `f`'s URM. The composite
fragment's outer numRegs is the sum (plus glue
registers) of all sub-fragments' numRegs.

### Construction

For each sub-fragment `frag_g_i := compileFrag (gs i)`
(arity `a`, the outer arity), and `frag_f := compileFrag
f` (arity `k`):

- Register layout (left-to-right block layout):
  - Block 0: reserved-zero (1 reg).
  - Block 1: outer output (1 reg).
  - Block 2: outer inputs (a regs).
  - Block 3..(2+k): sub-fragment `gs i`'s registers
    (excluding its zero-reg, which is shared with the
    outer reserved-zero; so size `frag_g_i.numRegs - 1`
    each, but more precisely the injection drops the
    sub's zero-reg slot from the outer layout).
  - Final block: `frag_f`'s registers (excluding its
    zero-reg).
- Each sub-fragment's instructions are re-indexed (its
  zero-reg → outer zero-reg, its inputs → outer inputs
  at the same positions, its other registers → fresh
  outer registers) and PC-shifted.
- Glue instructions: after each `gs i`'s instructions
  (replacing its trailing `.stop`), emit an M-template
  destructively transferring `gs i`'s output register
  into `f`'s input slot `i` register.

Because this combinator carries the largest amount of
register-injection and PC-shifting bookkeeping among the
seven combinators, the construction factors out
`URMInstr.reindex` and `URMInstr.shiftPC` as named
helpers.

- [ ] **Step 6.1: Define `URMInstr.reindex`**

```lean
/-- Re-index the register references of a `URMInstr r`
through an injection `f : Fin r → Fin r'`. PC labels are
left unchanged (caller is responsible for PC-shifting
separately). -/
def URMInstr.reindex {r r' : ℕ} (f : Fin r → Fin r') :
    URMInstr r → URMInstr r'
  | .assign i c => .assign (f i) c
  | .inc i => .inc (f i)
  | .dec i => .dec (f i)
  | .jumpZ i l₁ l₂ => .jumpZ (f i) l₁ l₂
  | .stop => .stop
```

- [ ] **Step 6.2: Define `URMInstr.shiftPC`**

```lean
/-- Shift the PC labels of a `URMInstr r` by a constant
`Δ`. Register references are unchanged. -/
def URMInstr.shiftPC {r : ℕ} (Δ : ℕ) :
    URMInstr r → URMInstr r
  | .assign i c => .assign i c
  | .inc i => .inc i
  | .dec i => .dec i
  | .jumpZ i l₁ l₂ => .jumpZ i (l₁ + Δ) (l₂ + Δ)
  | .stop => .stop
```

- [ ] **Step 6.3: Define `compileFrag_comp`**

The combinator takes the already-compiled sub-fragments
as arguments and glues them. Top-level `compileER`
(Task 9) is the recursive driver that calls
`compileFrag_comp` on `compileER`-emitted sub-fragments.

```lean
/-- Fragment for `ERMor1.comp f gs`. Spec §5.1.2:
sequentially run each sub-URM `gs i`, destructively
transfer its output into `f`'s i-th input slot, then run
`f`'s URM. Tourlakis 2018 p. 21 "concatenate M_g and
M_f". -/
def compileFrag_comp {k a : ℕ}
    (frag_f : CompiledFragment k)
    (frag_gs : Fin k → CompiledFragment a) :
    CompiledFragment a :=
  -- Outer numRegs:
  --   1 (zero) + 1 (outer output) + a (outer inputs)
  --   + Σ_i (frag_gs i).numRegs - 1 (drop each's zero-reg)
  --   + frag_f.numRegs - 1 (drop f's zero-reg)
  -- For implementation: build the register-injection
  -- functions per block, then assemble the instruction
  -- array.
  sorry
```

The body of `compileFrag_comp` is the longest
implementation task in T2. The sketch:

1. Compute the outer register count as `numRegs = 2 + a +
   S_g + S_f`, where `S_g = Σ_i ((frag_gs i).numRegs - 1)`
   and `S_f = (frag_f.numRegs - 1)`. Subtracting 1 per
   sub-fragment accounts for the merged zero-reg.
2. Compute `inj_g_i : Fin (frag_gs i).numRegs → Fin
   numRegs` for each `i`: maps `gs i`'s zero-reg to outer
   zero-reg; `gs i`'s `inputRegs j` (which equals `outer
   inputRegs j` in the outer layout since outer inputs
   are at positions `2..2+a-1`) maps to outer input `j`;
   `gs i`'s other registers map to fresh slots in `gs
   i`'s block.
3. Compute `inj_f : Fin frag_f.numRegs → Fin numRegs`:
   maps `f`'s zero-reg to outer zero-reg; `f`'s
   `inputRegs i` to a fresh register `V_f_in_i` allocated
   in `f`'s block; `f`'s `outputReg` to outer `outputReg`
   (so `f`'s output is the composite's output); `f`'s
   other registers to fresh slots.
4. Compute PC offsets: block 0 is the `assign V_z 0`
   prelude (1 instruction); each `gs i`'s block starts at
   PC `1 + Σ_{j<i} (frag_gs j).instrs.size + i *
   transferLoopLen`; `f`'s block starts after all `gs i`'s
   blocks and their connecting M-templates.
5. Emit:

```text
PC 0:   assign V_z 0
PC 1..: gs_0's instructions (re-indexed via inj_g_0,
        PC-shifted by 1)
        -- replace gs_0's final .stop with the M-template
        -- transferring gs_0's output (via inj_g_0) to
        -- V_f_in_0:
        transferLoop ... src=(inj_g_0 frag_gs[0].outputReg)
                       dst=(inj_f frag_f.inputRegs 0)
...
After all gs_i's and their connecting M-templates:
        f's instructions (re-indexed via inj_f,
        PC-shifted by f's start offset)
```

Given the length of this construction, the
implementer's task is to:

1. Define one fresh-block-allocation helper that returns
   a function `Fin block_size → Fin numRegs` for a given
   block start and size.
2. Compose them into the per-fragment injections.
3. Concatenate the re-indexed, PC-shifted instruction
   arrays plus connecting M-templates.
4. Discharge the four structural invariants by case
   analysis on the per-block-disjointness of register
   indices.

The body should not exceed ~150 Lean lines. Replace the
`sorry` placeholder with the full implementation in this
step.

The structural invariants:

- `inputRegs_inj`: the outer `inputRegs : Fin a → Fin
  numRegs` is `fun j => ⟨2 + j.val, ...⟩`, the same as
  `compileFrag_proj`. Injectivity follows from `j.val +
  2` injective in `j.val`.
- `outputReg_not_input`: outer output is at register 1,
  outer inputs at registers `2..2+a-1`, disjoint by
  arithmetic.
- `zeroReg_not_input`, `zeroReg_not_output`: outer
  zero-reg is at register 0, disjoint from registers 1
  (output) and `2..2+a-1` (inputs).

Note: the `sorry` placeholder in Step 6.3 above is the
guidance scaffold. The implementer replaces it with the
full ~150-line body. The build will not compile until
the `sorry` is removed; Step 6.4's verification step
covers this.

- [ ] **Step 6.4: Verify build**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereERKSim.olean
lake build GebLean.LawvereERKSim
```

Expected: clean build with no warnings. The `sorry` from
Step 6.3 must be removed; replace with the full
construction described in Step 6.3's sketch.

- [ ] **Step 6.5: Commit Task 6**

```bash
jj describe -m "feat(ertok): comp fragment compiler

Glue sub-fragments in compileFrag_comp by register-space
injection and PC-shifting; transfer sub-output to f-input
via transferLoop; run f after the wiring step.  Tourlakis
2018 p. 21 sequential concatenation; spec §5.1.2 g-to-f
wiring.

Spec §5.1.2; Step T2 task 6 of 13."
jj new
```

---

## Task 7 — `bsum` fragment compiler

**Files:**

- Modify: `GebLean/LawvereERKSim.lean` (append)

`ERMor1.bsum f` with `f : ERMor1 (k+1)`. Output is
`natBSum (ctx 0) (fun i => f.interp (Fin.cons i (Fin.tail
ctx)))`. Arity `k+1`; slot 0 is the bound; slots
`1..k` are the outer parameters.

Per spec §5.1 and §5.1.1: outer Loop over the bound
variable; per-iteration prologue writes the iteration
index into `f`'s slot-0 scratch and re-clones outer
parameters into `f`'s slot-`1..k` scratches; inner body
invokes `compileFrag f`'s instructions and adds the
result into the accumulator (which is the bsum's output
register).

- [ ] **Step 7.1: Define `compileFrag_bsum`**

```lean
/-- Fragment for `ERMor1.bsum f`. Spec §5.1, §5.1.1.
Outer Loop with iteration-counter register `V_i`
incrementing each iteration and bound register `V_x`
decrementing each iteration. Per-iteration prologue
re-clones outer parameters and writes `V_i` to f's
slot-0 scratch. Inner body invokes `compileFrag f` and
M-template-adds f's output into the bsum's output
register. Tourlakis 2018 p. 21 bounded-recursion
template. -/
def compileFrag_bsum {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) :
    CompiledFragment (k + 1) :=
  sorry
```

### Construction sketch

Outer register layout (k+1 inputs: slot 0 is bound;
slots `1..k` are outer parameters):

- Register 0: reserved-zero.
- Register 1: outer output (= accumulator `V_acc`).
- Register 2: outer input slot 0 (bound `V_x_in`).
- Registers `3..(2+k)`: outer input slots `1..k`.
- Register `3+k`: loop-count register `V_x` (a
  destructive clone of `V_x_in` so the input is
  preserved).
- Register `4+k`: iteration index `V_i` (initialized 0,
  incremented each iteration).
- Register `5+k`: scratch tmp for preserving-transfer of
  `V_i` to `f`'s slot-0 scratch in the per-iteration
  prologue.
- Registers `6+k..(6+k+(k+1)-1) = (6+k..6+2k)`: `f`'s
  input-slot scratches (cloned from outer params + the
  iteration index each iteration).
- Register `7+2k`: scratch tmp for preserving-transfer
  of outer params (one shared tmp; reused after each
  preserving-transfer leaves it zero).
- Remaining registers: `f`'s internal registers
  (re-indexed via the standard `inj_f`).

Instructions:

```text
PC 0:   assign V_z 0
PC 1:   assign V_acc 0                  -- accumulator init
PC 2-10: preservingTransfer 2 V_x_in V_x tmp_outer
                                        -- clone bound into V_x
PC 11:  assign V_i 0                    -- iteration index init
-- Outer-loop top:
PC top: jumpZ V_x exit body
PC body: dec V_x
PC body+1..body+9: preservingTransfer ... V_i → f_slot_0_scratch
                                        -- write iteration index
-- For each outer parameter slot j ∈ 1..k:
PC ...: preservingTransfer ... outer_param_j → f_slot_j_scratch
        (and reset tmp_outer to 0 between transfers by
         destructively consuming any leftover)
-- Inner body: compileFrag f's instructions
--   re-indexed (its slot 0 → f_slot_0_scratch; its slot
--   j → f_slot_j_scratch; its outputReg → f's output
--   scratch; its zero-reg → outer zero-reg; its other
--   regs → fresh outer regs) and PC-shifted.
--   Final .stop in f's block is REPLACED by an
--   M-template adding f's output destructively into
--   V_acc.
PC ...: inc V_i
PC ...: goto top
PC exit: stop
```

Replace the `sorry` in Step 7.1 with the full
construction following this sketch. Body is similar in
structure to `compileFrag_comp` but with an outer loop
wrapping the inner `f` invocation.

Implementation guidance:

1. Compute `numRegs` from the layout (formula above).
2. Define `inj_f : Fin (frag_f.numRegs) → Fin numRegs`
   that maps `f`'s zero-reg → outer zero-reg; `f`'s
   inputRegs 0 → f_slot_0_scratch; `f`'s inputRegs j
   (j ∈ 1..k) → f_slot_j_scratch; `f`'s outputReg → a
   designated f-output-scratch register; `f`'s other
   regs → fresh slots.
3. Compute PC offsets for each block (init prelude;
   outer-loop top; per-iteration prologue; inner `f`'s
   block; accumulator update; iteration index update;
   back-jump; exit). The offsets are computed by adding
   instruction-block lengths step-by-step.
4. Emit the instructions in order, applying
   `URMInstr.reindex` and `URMInstr.shiftPC` to `f`'s
   block.
5. The final `.stop` of `f`'s block is replaced by an
   M-template adding `f`'s output (via `inj_f
   frag_f.outputReg`) destructively into `V_acc`.

Per-iteration prologue size is `O(k+1)`
preserving-transfers (each of length 9), so the prologue
itself is ~`9 * (k+1)` instructions per outer iteration.

Note: the iteration-index register `V_i` must be
*non-destructively* copied to `f`'s slot-0 scratch each
iteration (because we increment `V_i` after the body
runs; if we destructively cloned it, we'd zero it before
the next iteration's increment, breaking the loop
counter). Outer parameters similarly need
preserving-transfer copies into `f`'s slot scratches
each iteration. Both use the standard
`URMRaw.preservingTransfer` helper.

- [ ] **Step 7.2: Verify build**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereERKSim.olean
lake build GebLean.LawvereERKSim
```

Expected: clean build with no warnings. The `sorry` from
Step 7.1 must be removed; replace with the full
construction described in Step 7.1's sketch.

- [ ] **Step 7.3: Commit Task 7**

```bash
jj describe -m "feat(ertok): bsum fragment compiler

Emit Tourlakis 2018 p. 21 bounded-recursion template for
ERMor1.bsum f as compileFrag_bsum.  Drive an outer loop
on the bound register with a per-iteration prologue
(writing the iteration index and re-cloning outer
parameters) and an accumulator update via transferLoop.

Spec §5.1, §5.1.1; Step T2 task 7 of 13."
jj new
```

---

## Task 8 — `bprod` fragment compiler

**Files:**

- Modify: `GebLean/LawvereERKSim.lean` (append)

`ERMor1.bprod f` mirrors `bsum f` with two changes:

1. Accumulator initial value is 1 (not 0).
2. Accumulator update is multiplication (not addition).
   Multiplication is itself a loop: `V_acc ← V_acc *
   V_f_out` is the inner R^XY_Z template of Tourlakis
   p. 19 — multiply by a value by adding `V_acc` to a
   scratch register `V_f_out` times.

- [ ] **Step 8.1: Define `compileFrag_bprod`**

Construction parallels `compileFrag_bsum` except:

- `PC 1: assign V_acc 1` instead of `assign V_acc 0`.
- The accumulator update at the end of each outer
  iteration is the R^XY_Z multiplication template
  (Tourlakis p. 19): `V_acc_tmp ← V_acc; V_acc ← 0;
  Loop V_f_out { V_acc ← V_acc + V_acc_tmp (destructive
  on V_acc_tmp; restore V_acc_tmp after the inner inc
  loop)`. This update emits a nested loop, in contrast to
  `bsum`'s single transferLoop addition.

Schematic for the accumulator update (Tourlakis p. 19's
R^XY_Z, with X = V_f_out, Y = V_acc, Z = new V_acc):

```text
-- mult_update: V_acc ← V_acc * V_f_out (destructive on V_f_out;
-- V_acc replaced):
-- Step 1: clone V_acc into V_acc_tmp (preserving):
PC m: preservingTransfer m V_acc V_acc_tmp tmp_scratch
PC m+9: assign V_acc 0
-- Step 2: outer loop on V_f_out:
PC m+10: jumpZ V_f_out exit body
PC body: dec V_f_out
-- inner loop: V_acc ← V_acc + V_acc_tmp (preserving on V_acc_tmp):
PC body+1: preservingTransfer (body+1) V_acc_tmp V_acc tmp_scratch2
PC body+10: goto (m+10)        -- back to outer-loop top
PC exit: ...
```

Requires two additional scratch registers (V_acc_tmp,
tmp_scratch2). Total outer numRegs is greater than
`bsum`'s by 2.

```lean
/-- Fragment for `ERMor1.bprod f`. Spec §5.1, §5.1.1.
Mirrors `compileFrag_bsum` with multiplication
accumulator instead of addition; multiplication uses
Tourlakis 2018 p. 19's R^XY_Z nested-loop template.
Initial accumulator value 1 (empty product). -/
def compileFrag_bprod {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) :
    CompiledFragment (k + 1) :=
  sorry
```

Implementation guidance: copy `compileFrag_bsum`'s
implementation; substitute the addition update with the
R^XY_Z multiplication update; widen the numRegs by 2 to
fit the additional scratch registers; adjust PC offsets
accordingly.

- [ ] **Step 8.2: Verify build**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereERKSim.olean
lake build GebLean.LawvereERKSim
```

Expected: clean build with no warnings. The `sorry` from
Step 8.1 must be removed; replace with the full
construction.

- [ ] **Step 8.3: Commit Task 8**

```bash
jj describe -m "feat(ertok): bprod fragment compiler

Mirror compileFrag_bsum with a multiplicative accumulator
in compileFrag_bprod.  Emit the multiplicative update
via Tourlakis 2018 p. 19's R^XY_Z nested-loop template.

Spec §5.1, §5.1.1; Step T2 task 8 of 13."
jj new
```

---

## Task 9 — Top-level `compileER`

**Files:**

- Modify: `GebLean/LawvereERKSim.lean` (append)

`compileER : {a : ℕ} → ERMor1 a → URMProgram` is the
recursive driver that dispatches to each per-constructor
fragment combinator.

- [ ] **Step 9.1: Define `compileERFrag`**

The recursive driver returns a `CompiledFragment`, then
`compileER` wraps that into a `URMProgram`.

```lean
/-- Recursive driver: emit a `CompiledFragment a` for
each `ERMor1 a` constructor by dispatching to the
per-constructor combinators. -/
def compileERFrag : {a : ℕ} → ERMor1 a → CompiledFragment a
  | _, .zero => compileFrag_zero
  | _, .succ => compileFrag_succ
  | _, .proj i => compileFrag_proj i
  | _, .sub => compileFrag_sub
  | _, .comp f gs =>
      compileFrag_comp (compileERFrag f)
        (fun i => compileERFrag (gs i))
  | _, .bsum f => compileFrag_bsum (compileERFrag f)
  | _, .bprod f => compileFrag_bprod (compileERFrag f)
```

The recursion is structural on `ERMor1 a` (well-founded
on the inductive's depth). Lean accepts this without
explicit termination annotations because each recursive
call is on a syntactic subexpression of the input.

- [ ] **Step 9.2: Define `compileER`**

```lean
/-- The top-level ER → URM compiler. Returns a
`URMProgram a` (arity-indexed per Task 0's refactor)
whose execution on input `v : Fin a → ℕ` produces
`e.interp v` in the output register. Spec §5; Tourlakis
2018 §0.1.0.37 (pp. 15–16) URM semantics; Tourlakis
2018 pp. 19–21 per-template constructions. -/
def compileER {a : ℕ} (e : ERMor1 a) : URMProgram a :=
  (compileERFrag e).toURMProgram
```

- [ ] **Step 9.3: Verify build**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereERKSim.olean
lake build GebLean.LawvereERKSim
```

Expected: clean build with no warnings.

- [ ] **Step 9.4: Commit Task 9**

```bash
jj describe -m "feat(ertok): top-level compileER recursive driver

Dispatch to per-constructor fragment combinators on
ERMor1 structure in compileERFrag; wrap the resulting
fragment as a URMProgram in compileER.

Spec §5; Step T2 task 9 of 13."
jj new
```

---

## Task 10 — `compileER_runtime`

**Files:**

- Modify: `GebLean/LawvereERKSim.lean` (append)

`compileER_runtime e v : ℕ` returns the URM step count
sufficient to compute `e.interp v` on input `v` through
`compileER e`. Structural recursion on `e` matching the
template structure.

Per spec §5.2: atoms have constant step count;
`comp` is sum of children plus prelude overhead;
`bsum`/`bprod` is outer-loop-count × (per-iteration
prologue cost + child runtime).

Step counts per atom (instruction count of the compiled
fragment plus run-through count for each loop):

- `zero`: 3 instructions (`assign V_z; assign V_out 0;
  stop`), executed once → 3 steps.
- `succ`: prologue 1 + preservingTransfer 9 (run-time
  step count depends on input value `v 0`) + inc 1 + stop
  The preservingTransfer's loop runs `v 0` times for loop
  1 and `v 0` times for loop 2; per-iteration cycle ≈ 5
  instructions. Total ≈ `11 + 10 · (v 0)` steps.
- `proj i`: similar to `succ` minus the trailing `inc`.
  Total ≈ `11 + 10 · (v i)` steps.
- `sub`: prologue (1) plus preservingTransfer of `V_X`
  (`9 + 10 · v 0`) plus transferLoop of `V_Y` into scratch
  (`4 + 5 · v 1`) plus the inner subtraction loop
  (`5 · v 1` iterations) plus stop. Total bounded by a
  polynomial in `max (v 0) (v 1)`.
- `comp f gs`: sum of `compileER_runtime (gs i) v` over
  `i ∈ Fin k`, each glue M-template's runtime
  (`4 + 5 · (gs i).interp v`), `compileER_runtime f (fun
  i => (gs i).interp v)`, and a small constant for the
  trailing stop.
- `bsum f`: outer-loop init prelude (constant) + outer
  loop count `v 0` × per-iteration cost; per-iteration
  cost = per-iteration prologue runtime
  (`O(k+1)` preserving-transfers, each `9 + 10 * v_j`
  where `v_j` is the relevant outer param value, plus
  `9 + 10 * i` for the iteration-index clone where `i`
  is the current loop index) + `compileER_runtime f
  (Fin.cons i (Fin.tail v))` + accumulator-update
  M-template cost (`4 + 5 * f.interp (Fin.cons i
  (Fin.tail v))`).
- `bprod f`: same structure as `bsum f` with
  multiplication update; the multiplication update cost
  is `9 + (current_acc + 1) + (5 * f.interp_value *
  current_acc)` or similar — the dominant cost is
  proportional to `current_acc * f.interp_value` per
  iteration.

Exact closed-form constants are unnecessary for
correctness. The runtime witness can be any
upper-bound-respecting `ℕ` function defined by structural
recursion on `e`. The simplest path: return a
sufficiently-large step count by structural recursion,
without trying to be tight.

- [ ] **Step 10.1: Define `compileER_runtime`**

No new mathlib imports are required: sums over `Fin n`
are realised via `List.finRange n` (already imported by
T1) folded through `List.foldl (· + ·) 0`, and sums over
the iteration count of `bsum`/`bprod` via `List.range
bound` (Lean core). The arity of `f` in the
`bsum`/`bprod` branches is named explicitly (`k`) so
`Fin.cons i (Fin.tail v) : Fin (k + 1) → ℕ` unifies
cleanly against `f`'s signature `ERMor1 (k + 1)`.

```lean
/-- Runtime witness: a step count sufficient for
`URMState.runFor (compileER e) v` to reach a state where
the output register holds `e.interp v`. Structural
recursion on `e`; per-template costs match the spec §5.2
shape. Tourlakis 2018 §0.1.0.42 (p. 18) `f ∈ E^n` is
URM-computable within time `t ∈ E^n`. -/
def compileER_runtime : {a : ℕ} → ERMor1 a →
    (Fin a → ℕ) → ℕ
  | _, .zero, _ => 3
  | _, .succ, v => 12 + 10 * v 0
  | _, .proj i, v => 11 + 10 * v i
  | _, .sub, v => 20 + 10 * v 0 + 10 * v 1
  | _, .comp (k := k) f gs, v =>
      let inner : Fin k → ℕ := fun i => (gs i).interp v
      let glue : ℕ :=
        ((List.finRange k).map
          (fun i => compileER_runtime (gs i) v
            + 4 + 5 * inner i)).foldl (· + ·) 0
      glue + compileER_runtime f inner + 2
  | _, .bsum (k := k) f, v =>
      let bound : ℕ := v 0
      let perIter : ℕ → ℕ := fun i =>
        let ctx_f : Fin (k + 1) → ℕ :=
          Fin.cons i (Fin.tail v)
        let outerSum : ℕ :=
          ((List.finRange k).map (Fin.tail v)).foldl
            (· + ·) 0
        compileER_runtime f ctx_f
        + 50 + 10 * (i + outerSum)
        + 5 * f.interp ctx_f
      30 + 10 * bound +
        ((List.range bound).map perIter).foldl (· + ·) 0
  | _, .bprod (k := k) f, v =>
      let bound : ℕ := v 0
      let perIter : ℕ → ℕ := fun i =>
        let ctx_f : Fin (k + 1) → ℕ :=
          Fin.cons i (Fin.tail v)
        let outerSum : ℕ :=
          ((List.finRange k).map (Fin.tail v)).foldl
            (· + ·) 0
        compileER_runtime f ctx_f
        + 60 + 10 * (i + outerSum)
        + 5 * f.interp ctx_f
      40 + 10 * bound +
        ((List.range bound).map perIter).foldl (· + ·) 0
```

The exact constants (3, 12, 11, 20, 30, 40, 50, 60) are
upper-bound placeholders chosen large enough to dominate
the real per-template runtime. The proof in Task 11
needs only `compileER_runtime e v ≤ t' → run-correctly
t'`, so any upper-bound function over the real runtime
is acceptable; the structural shape is final.

If a constant turns out to be too small for the
correctness proof to close in Task 11, increase it
inline; the structural recursion does not change.

- [ ] **Step 10.2: Verify build**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereERKSim.olean
lake build GebLean.LawvereERKSim
```

Expected: clean build with no warnings. No new imports
are required (the definition uses `List.finRange` from
`Mathlib.Data.List.FinRange` already imported at T1,
plus Lean core's `List.range`, `List.map`, `List.foldl`,
`Fin.cons`, `Fin.tail`).

- [ ] **Step 10.3: Commit Task 10**

```bash
jj describe -m "feat(ertok): compileER_runtime structural recursion

Define compileER_runtime e v as a ℕ-valued runtime
witness by structural recursion on e.  Match per-template
costs from spec §5.2; choose constants to upper-bound
the real URM step count.

Spec §5.2; Tourlakis 2018 §0.1.0.42; Step T2 task 10 of
13."
jj new
```

---

## Task 11 — `compileER_runFor` correctness theorem

**Files:**

- Modify: `GebLean/LawvereERKSim.lean` (append)

The correctness theorem stating that running the compiled
URM for at least `compileER_runtime e v` steps produces
the correct output. Proof by induction on `e`.

- [ ] **Step 11.1: State the theorem**

```lean
/-- Correctness theorem: running `compileER e` for at
least `compileER_runtime e v` steps places `e.interp v`
in the output register. Spec §5.2 compileER_runFor
statement; Tourlakis 2018 §0.1.0.37 simulation lemma. -/
theorem compileER_runFor {a : ℕ} (e : ERMor1 a)
    (v : Fin a → ℕ) (t' : ℕ)
    (ht' : compileER_runtime e v ≤ t') :
    ((URMState.init (compileER e) v).runFor t').regs
        (compileER e).outputReg
      = e.interp v := by
  sorry
```

- [ ] **Step 11.2: Prove the atom cases**

```lean
  induction e with
  | zero =>
    -- Run-for-3 case: V_z init, V_out := 0, stop.
    -- After 3 steps the URM is in the halt state and
    -- V_out = 0 = ERMor1.zero.interp v.
    sorry
  | succ =>
    sorry
  | proj i =>
    sorry
  | sub =>
    sorry
  | comp f gs ih_f ih_gs =>
    sorry
  | bsum f ih_f =>
    sorry
  | bprod f ih_f =>
    sorry
```

Each case's proof is structured. Run-decomposition uses
`URMState.runFor_add` as the primary tool (split a
`t' = m + n` run into its first `m` and trailing `n`
portions); `URMState.runFor_succ` is used only at the
innermost step where peeling one instruction at a time is
needed (e.g., evaluating the effect of one `inc` or one
`assign`).

The hypothesis `ht' : compileER_runtime e v ≤ t'`
introduces a slack `s := t' - compileER_runtime e v` (and
`t' = compileER_runtime e v + s` by `Nat.add_sub_cancel'`).
The proof rewrites the run as
`runFor (compileER_runtime e v + s) = runFor s applied
after runFor compileER_runtime e v`, then applies the
halt-state self-loop semantics of `URMState.step`
(Tourlakis p. 15) to absorb the extra `s` steps. The
combinator-level structural induction's inductive
hypotheses are applied to `s = 0` or to the exact runtime
budget; the slack absorption is one extra lemma.

1. Unfold `compileER` and `compileER_runtime` per the
   constructor.
2. Apply `URMState.runFor_add` to split the run at
   per-block boundaries (init prelude; sub-fragment runs;
   glue transfers; final stop).
3. Peel inner steps with `runFor_succ` and evaluate
   register updates via `Function.update_apply`.
4. Apply the inductive hypothesis to each sub-run.
5. Discharge the slack `s ≥ 0` via halt-state self-loop.

The proofs are likely the longest part of T2; expect each
case to be 30–80 lines. The total for the theorem is
estimated at 200–400 lines.

Implementation strategy:

1. Prove each atomic case (`zero`, `succ`, `proj`,
   `sub`) by direct simulation (apply `runFor_add` to
   isolate the halt-state self-loop slack; peel the
   non-slack portion with `runFor_succ`; track register
   values via `Function.update`'s simp lemmas; use `omega`
   for arithmetic).
2. Prove `comp f gs` by decomposing the run via repeated
   `runFor_add` into each `gs i`'s run, each connecting
   transferLoop's run, and the final `f` run, applying the
   inductive hypotheses for each sub-run.
3. Prove `bsum f` and `bprod f` by an inner induction on
   the bound register `v 0`. Base case: `v 0 = 0`, the
   outer loop exits immediately, accumulator stays at
   initial value. Inductive step: one outer-loop iteration
   runs the per-iteration prologue, the inner `f` (via
   `ih_f`), and the accumulator update; accumulator goes
   from `acc_prev` to `acc_prev + f.interp (Fin.cons i
   (Fin.tail v))` for `bsum` (or `acc_prev * f.interp ...`
   for `bprod`).

Replace each `sorry` placeholder in Step 11.2 with the
case-specific proof. Lean intermediate lemmas (e.g., a
`transferLoop_correct` lemma proving that running a
transferLoop block from a state where `V_src = n` for `4 +
5 * n` steps leaves `V_src = 0` and `V_dst = V_dst_prev +
n`, with the rest of the state unchanged) factor out the
repetitive simulation arguments. The implementer can
introduce 3–5 such intermediate lemmas as needed.

- [ ] **Step 11.3: Verify build**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereERKSim.olean
lake build GebLean.LawvereERKSim
```

Expected: clean build with no warnings. All `sorry`s from
Steps 11.1 and 11.2 must be removed.

- [ ] **Step 11.4: Commit Task 11**

```bash
jj describe -m "feat(ertok): compileER_runFor correctness theorem

Prove compileER_runFor: running URMState.runFor (compileER
e) for t' ≥ compileER_runtime e v steps yields e.interp v
at the output register.  Discharge by structural
induction on e with per-constructor proofs.

Spec §5.2; Step T2 task 11 of 13."
jj new
```

---

## Task 12 — Axiom audit and final verification

**Files:**

- No code changes; verification only.

- [ ] **Step 12.1: Run the build cleanly from scratch**

```bash
rm -f .lake/build/lib/lean/GebLean/LawvereERKSim.olean
lake build GebLean.LawvereERKSim
```

Expected: clean build, no warnings.

- [ ] **Step 12.2: Run the axiom check on the module**

The vendored axiom-check script extracts only the first
`namespace` line per file (line 38 of
`scripts/check-axioms.sh`), which silently false-passes
files with nested namespaces. `LawvereERKSim.lean` has
nested namespaces (`GebLean` → `LawvereERKSim`).
Workaround: run `#print axioms` per declaration directly
in a scratch buffer.

For each public declaration added in this step
(`URMInstrRaw`, `URMInstrRaw.toBounded`,
`CompiledFragment`, `CompiledFragment.toURMProgram`
(auto-generated by `extends`), `compileFrag_zero`,
`compileFrag_succ`, `compileFrag_proj`, `compileFrag_sub`,
`compileFrag_comp`, `compileFrag_bsum`,
`compileFrag_bprod`, `compileERFrag`, `compileER`,
`compileER_runtime`, `compileER_runFor`), run:

```bash
echo 'import GebLean.LawvereERKSim
open GebLean.LawvereERKSim
#print axioms compileER
#print axioms compileER_runtime
#print axioms compileER_runFor
-- (and the others)
' > /tmp/audit_t2.lean
lake env lean /tmp/audit_t2.lean
```

Expected: each `#print axioms` output is one of:

- `'<name>' depends on axioms: [propext]` (allowed; same
  allowlist as T1).
- `'<name>' depends on axioms: [propext, Quot.sound]`
  (both allowed).
- `'<name>' does not depend on any axioms.` (preferred).

Any `Classical.choice`, `Classical.choose`, or
`Classical.em` in the output indicates a constructive-
discipline violation; fix in the offending declaration.

The cross-workstream defect that
`scripts/check-axioms.sh` extracts only the first
`namespace` line per file (line 38 of the script) and
thus silently false-passes files with nested namespaces
remains out of scope for T2. The same workaround is
applied at T1 (`#print axioms` per declaration directly).
A separate remediation task is to either patch the
vendored script under `scripts/` or report the defect
upstream to the `lean4-skills` repository; that task
lives outside the erToK workstream and is tracked in the
project's general infrastructure backlog.

- [ ] **Step 12.3: Manual lint of the module**

Inspect `GebLean/LawvereERKSim.lean` by hand:

- Every `def`, `structure`, `inductive`, `theorem` has a
  `/-- … -/` docstring.
- Every docstring with literature content cites Tourlakis
  2018 (§0.1.0.37, p. 19, p. 20, p. 21, or §0.1.0.42) or
  the spec by §.
- No occurrences of banned style words ("load-bearing",
  "key", "important", "elegant", "crucial", "beautiful",
  "clever", "neat", "powerful", "interesting", "insight").
- No `sorry`, no `admit`, no `noncomputable`, no
  `Classical.*`.
- Lines ≤ 100 characters.
- No development-history references in docstrings.

- [ ] **Step 12.4: Verify all 15 spec-named declarations are present**

The plan defines fifteen public declarations for the T2
tranche of `GebLean/LawvereERKSim.lean`:

```text
URMInstrRaw
URMInstrRaw.toBounded
CompiledFragment
CompiledFragment.toURMProgram   -- auto-generated by extends
compileFrag_zero
compileFrag_succ
compileFrag_proj
compileFrag_sub
compileFrag_comp
compileFrag_bsum
compileFrag_bprod
compileERFrag
compileER
compileER_runtime
compileER_runFor
```

Additional emission/internal helpers introduced by this
plan (`URMInstrRaw.regBound`, `URMInstrRaw.boundedBy`,
`URMInstrRaw.toBoundedArray`, `URMInstr.reindex`,
`URMInstr.shiftPC`, `URMRaw.goto`,
`URMRaw.transferLoop`, `URMRaw.transferLoopLen`,
`URMRaw.preservingTransfer`,
`URMRaw.preservingTransferLen`,
`CompiledFragment.zeroReg`) support the public
declarations but are not part of the spec's named set.

Confirm each spec-named declaration is present by
running:

```bash
grep -E '^(def|theorem|structure|inductive|abbrev) (URMInstrRaw|CompiledFragment|compileFrag_|compileERFrag|compileER|compileER_runtime|compileER_runFor)' GebLean/LawvereERKSim.lean
```

Expected: 15 (or more if internal helpers are also
listed). Missing declarations indicate the
implementation diverged from the plan; investigate.

- [ ] **Step 12.5: Commit Task 12 (verification record)**

Task 12 is verification-only, no code changes. The
current working-copy commit (created by Task 11's
trailing `jj new`) is empty; describe it as the
verification record.

```bash
jj describe -m "chore(ertok): Step T2 verification — axiom-clean, lint-clean

Verify that #print axioms on each compileFrag_*,
compileERFrag, compileER, compileER_runtime,
compileER_runFor passes (propext + Quot.sound
allowlist); confirm by manual lint that docstrings
cite Tourlakis on every declaration and carry no banned
wordings.

Step T2 task 12 of 13 — Step T2 complete."
jj new
```

---

## Spec coverage check

| Spec section | Plan task |
| --- | --- |
| §5 (compileER public interface) | Task 9 |
| §5.1 atomic templates (zero/succ/proj/sub) | Tasks 5.1–5.4 |
| §5.1 prelude — localised variant adopted; see Divergence subsection | Tasks 5.3, 6.3, 7.1, 8.1 (per-call preserving-transfer; no global prelude walk) |
| §5.1 destructive vs preserving transfers | Task 4 |
| §5.1 goto encoding via `V_z` | Task 4 (URMRaw.goto) |
| §5.1.1 per-iteration prologue for bsum/bprod | Tasks 7.1, 8.1 |
| §5.1.2 g-to-f wiring for comp f gs | Task 6.3 |
| §5.2 compileER_runtime | Task 10 |
| §5.2 compileER_runFor correctness | Task 11 |
| §9 module layout (LawvereERKSim.lean) | Task 1 |
| §10 constructive discipline | All tasks (no Classical anywhere) |
| §12.1 axiom check | Task 12.2 |
| §12.2 ZeroTestURM matches Tourlakis §0.1.0.37 | T1 (handled at T1; not in T2 scope) |
| §12.3 §0.1.0.37 simulation lemma transcription | T3 (simulator); not in T2 scope |
| §12.4 §0.1.0.44 proof transcription | T5 (assembly); not in T2 scope |
| §12.5 level claim for `simulate` | T3 (simulator); not in T2 scope |
| §12.6 level claim for `boundExprK` | T4 (runtime bound); not in T2 scope |
| §12.7 every construction cited | Task 12.3 |
| §12.8 per-template correctness coverage | Task 11 |
| §12.9 no phantom infrastructure | Task 12.3 manual lint |
| §12.10 independence from kToER side | Task 1 (no LawvereKSimER import) |
| §12.11 no CSLib URM import | Task 1 (no `import Cslib`) |

Coverage: complete for T2-scope items. Spec §12.2–§12.6
are out of T2's scope (they cover T1 and T3–T5
constructions). The Tourlakis 2018 citations required by
§12.7 are distributed across Tasks 4–11's docstrings
(each declaration cites its source page).

## Out of scope

This plan covers Step T2 only (ER → URM compiler with
runtime witness and correctness theorem). Subsequent
plans for the same erToK spec:

- T3 (K^sim simulator): `simulate`, `simulate_interp`,
  plus the four supporting K^sim composites
  (`KMor1.natK`, `KMor1.maxK`, `KMor1.maxOver`,
  `KMor1.pow2_iter`) per spec §6 and §3.1.
- T4 (runtime bound): `boundExprK`,
  `boundExprK_dominates` per spec §7.
- T5 (`erToK` assembly + functor): `erToK`,
  `erToK_interp`, `erToK_level`, `erToKN`,
  `erToKFunctor` per spec §8.

Each subsequent step gets its own plan + adversarial
review + execution cycle. The T3–T5 declarations extend
`GebLean/LawvereERKSim.lean` (per spec §9 single-module
layout); the module's docstring's `## Main definitions`
section grows incrementally across T2–T5.
