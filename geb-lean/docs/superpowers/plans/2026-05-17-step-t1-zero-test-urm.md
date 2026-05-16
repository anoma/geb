# Step T1 — Zero-test URM kernel — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Land the URM kernel for the erToK direction:
`URMInstr` inductive (5 instructions matching Tourlakis
§0.1.0.37 p. 16), `URMProgram` structure with input/output
register conventions and structural invariants,
`URMState` with `step` and `runFor`, `URMState.init` via
`List.find?` (constructive), plus the basic reduction
lemmas.

**Architecture:** One new module at
`GebLean/Utilities/ZeroTestURM.lean` depending on Lean
core plus two lightweight mathlib helpers
(`Mathlib.Data.List.FinRange` for `List.finRange`,
`Mathlib.Logic.Function.Basic` for `Function.update`).
The module is the foundation that subsequent steps
(T2 compiler, T3 simulator, T4 runtime bound, T5 erToK
assembly) consume.

**Tech Stack:** Lean 4 + mathlib4 (transitive). Build via
`lake build`, test via `lake test`. The lakefile sets
`warningAsError = true`; every Lean linter warning fails
the build.

**Spec:**
[`docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`](../specs/2026-05-16-er-to-k-via-cslib-urm-design.md)
§4 (URM kernel) plus §10 (constructive discipline)
plus §12.1 (axiom check) plus §12.2 (URM correspondence).
The spec is the source of truth for all literature
citations and docstring text; this plan transcribes the
implementation.

**Master design:**
[`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`](../../research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md)
§4 (predecessor; superseded by the round-2 spec for the
kernel-instruction-set choice, retained as background on
the simulation construction).

**Tourlakis citation:** Tourlakis 2018
`PR-complexity-topics.pdf` §0.1.0.37 (pp. 15–16). The
five-instruction set, the V_1-is-output convention, the
"stop self-loops" semantic clause, and the initial-state
convention (`v_1(0) = 0`, `v_i(0) = a_{i-1}` for inputs,
`v_i(0) = 0` for working registers, `I(0) = 1` with our
0-indexed shift to `I(0) = 0`) all come from this lemma.

---

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [File structure](#file-structure)
- [Style and discipline reminders](#style-and-discipline-reminders)
  - [Verifying a clean build](#verifying-a-clean-build)
  - [Test discipline (kernel-reduction caveat)](#test-discipline-kernel-reduction-caveat)
- [Task 1 — Module skeleton and `URMInstr` inductive](#task-1--module-skeleton-and-urminstr-inductive)
- [Task 2 — `URMProgram` structure with structural invariants](#task-2--urmprogram-structure-with-structural-invariants)
- [Task 3 — `URMState` structure and `step` function](#task-3--urmstate-structure-and-step-function)
- [Task 4 — `runFor` step-counted runner with reduction lemmas](#task-4--runfor-step-counted-runner-with-reduction-lemmas)
- [Task 5 — `URMState.init` via constructive `List.find?`](#task-5--urmstateinit-via-constructive-listfind)
- [Task 6 — Axiom audit and final verification](#task-6--axiom-audit-and-final-verification)
- [Spec coverage check](#spec-coverage-check)
- [Out of scope](#out-of-scope)

<!-- END doctoc -->

## File structure

**Created:**

- `GebLean/Utilities/ZeroTestURM.lean` — `URMInstr`
  inductive (5 constructors), `URMProgram` structure,
  `URMState` structure, `URMState.step`, `URMState.runFor`,
  `URMState.init`, universal reduction lemmas. Imports
  `Mathlib.Data.List.FinRange` (for `List.finRange`) and
  `Mathlib.Logic.Function.Basic` (for `Function.update`).

**Modified:**

None. Per the kToER-side convention, utility modules are
imported only by their consuming higher-level modules.
The new `Utilities/ZeroTestURM.lean` is consumed by
`LawvereERKSim.lean` in Step T2; T1 only creates the
module. No umbrella import in `GebLean.lean` is added.

**Tests:** no separate `GebLeanTests/` module is created
in T1. The universal reduction lemmas
(`runFor_zero`, `runFor_succ`, `runFor_add`) added inside
the main module are the verification for T1. Program-
specific tests over `compileER`-emitted URMs land in T2
when there are actual programs to test.

## Style and discipline reminders

Each task's code must follow `CLAUDE.md` and
`.claude/rules/lean-coding.md`:

- Lines ≤ 100 characters.
- Spaces around binary operators in source.
- Every implemented function/definition/structure/theorem
  carries a literature reference in its docstring
  (Tourlakis 2018 §0.1.0.37 pp. 15–16 or spec §4).
- Module docstring with required sections (title,
  summary, main definitions, main statements, references).
- Use `simp only [...]` not bare `simp [...]` per the
  flexible-tactic linter.
- No `sorry`, no `admit`, no warnings
  (`warningAsError = true`).
- No banned words from `CLAUDE.md`'s style list (no "load-
  bearing", "key", "important", "elegant", etc.).
- No `noncomputable`, no `Classical.choose`,
  `Classical.choice`, or `Classical.em` on any declaration.
- `markdownlint-cli2` clean if any docs are touched.
- Two structural invariants of `URMProgram`
  (`inputRegs_inj` and `outputReg_not_input`) are
  independent and must both be enforced (spec §4.1).

### Verifying a clean build

To force re-elaboration of a single module:

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ZeroTestURM.olean
lake build GebLean.Utilities.ZeroTestURM
```

After each task, before committing, run this command for
the module touched in the task. Inspect the full output
for `error:` lines.

### Test discipline (kernel-reduction caveat)

`URMState.runFor` over Tourlakis's M-template (loop
incrementing a destination while decrementing a source)
triggers a chain of `step` applications; each unfolds
`Function.update` and the match on `URMInstr`. Kernel
reduction of `runFor P s n` for any non-trivial `n` and
`P` containing loops is expensive and may exceed
reasonable build time.

T1 therefore confines verification to **universally
quantified `@[simp]` reduction lemmas**
(`runFor_zero`, `runFor_succ`, `runFor_add`) added
inside the main module. No `#guard` over `runFor` on a
specific program is added at T1. End-to-end verification
of compiled URMs lives at T2 via the universal
`compileER_runFor` correctness statement.

## Task 1 — Module skeleton and `URMInstr` inductive

**Files:**

- Create: `GebLean/Utilities/ZeroTestURM.lean`

- [ ] **Step 1.1: Create the skeleton module**

```lean
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Function.Basic

/-!
# Zero-test URM kernel

An unbounded register machine (URM) with five primitive
instructions, matching Tourlakis 2018 `PR-complexity-topics.pdf`
§0.1.0.37 (pp. 15–16):

- `assign i c` (Tourlakis `V_i ← c`): write the constant
  `c` to register `i`; advance PC.
- `inc i` (Tourlakis `V_i ← V_i + 1`): increment register
  `i`; advance PC.
- `dec i` (Tourlakis `V_i ← V_i ∸ 1`): truncated decrement
  of register `i`; advance PC.
- `jumpZ i l₁ l₂` (Tourlakis
  `if V_i = 0 goto l₁ else goto l₂`): two-target
  conditional jump on register `i` being zero.
- `stop`: halt (self-loop on PC and registers).

This URM is structurally distinct from CSLib's
Shepherdson–Sturgis URM (`Cslib.Computability.URM.*`),
which uses an equality jump `J m n q` (level 2 in K^sim)
rather than a zero-test jump (level 1 in K^sim). See spec
§2.1 for the rationale.

## Main definitions

- `URMInstr`: the five-instruction inductive type.
- `URMProgram`: program structure with input/output
  register conventions.
- `URMState`: machine state (PC + registers).
- `URMState.step`: one-step transition function.
- `URMState.runFor`: step-counted iteration.
- `URMState.init`: initial state from input vector via
  constructive `List.find?` lookup.

## References

- Tourlakis 2018 §0.1.0.37 (pp. 15–16): simulation
  lemma, source of the five-instruction set and the
  initial-state convention.
- Spec §4:
  `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`.

## Tags

URM, register machine, Tourlakis, zero-test
-/

namespace GebLean

namespace ZeroTestURM

end ZeroTestURM

end GebLean
```

- [ ] **Step 1.2: Verify the skeleton builds**

Run: `lake build GebLean.Utilities.ZeroTestURM`
Expected: clean build with no warnings (the module is
empty besides the namespace).

- [ ] **Step 1.3: Define `URMInstr`**

Inside `namespace ZeroTestURM`, in
`GebLean/Utilities/ZeroTestURM.lean`:

```lean
/-- URM instructions matching Tourlakis 2018 §0.1.0.37
(p. 16): assign a constant, increment, truncated
decrement, two-target zero-test jump, halt.

The parameter `r : ℕ` is the register count; `Fin r`
keeps register indices in-range. -/
inductive URMInstr (r : ℕ) : Type
  /-- `assign i c` is Tourlakis's `V_i ← c`: write the
  constant `c` to register `i`; advance PC. -/
  | assign (i : Fin r) (c : ℕ) : URMInstr r
  /-- `inc i` is Tourlakis's `V_i ← V_i + 1`. -/
  | inc (i : Fin r) : URMInstr r
  /-- `dec i` is Tourlakis's `V_i ← V_i ∸ 1` (truncated
  decrement). -/
  | dec (i : Fin r) : URMInstr r
  /-- `jumpZ i l₁ l₂` is Tourlakis's
  `if V_i = 0 goto l₁ else goto l₂`. -/
  | jumpZ (i : Fin r) (l₁ l₂ : ℕ) : URMInstr r
  /-- `stop` is Tourlakis's halt instruction:
  PC and registers unchanged when executed (self-loop). -/
  | stop : URMInstr r
  deriving Repr, DecidableEq, Inhabited
```

- [ ] **Step 1.4: Verify the inductive type compiles**

Run:

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ZeroTestURM.olean
lake build GebLean.Utilities.ZeroTestURM
```

Expected: clean build with no warnings. The `deriving`
clause must succeed for all three classes; failure
indicates a missing decidable-equality instance for `Fin`
or a missing `Repr` for one of the field types (both
should resolve automatically given the imports).

If `deriving Inhabited` fails to elaborate (possible on
parameterised inductives in older mathlib pins), drop
`Inhabited` from the `deriving` clause and add a
separate instance declaration after `URMInstr`:

```lean
instance {r : ℕ} : Inhabited (URMInstr r) := ⟨.stop⟩
```

- [ ] **Step 1.5: Commit Task 1**

Project rule (CLAUDE.md): use `jj` for state-mutating
operations, not raw `git commit`. The
working-copy commit is the current task's work; set
its description with `jj describe`, then `jj new` to
start a fresh working-copy commit for the next task:

```bash
jj describe -m "feat(urm): introduce URMInstr inductive

Five-instruction zero-test URM matching Tourlakis 2018
§0.1.0.37 (pp. 15-16): assign / inc / dec / jumpZ / stop.

Spec §4.1; Step T1 task 1 of 6."
jj new
```

---

## Task 2 — `URMProgram` structure with structural invariants

**Files:**

- Modify: `GebLean/Utilities/ZeroTestURM.lean` (append)

- [ ] **Step 2.1: Define `URMProgram`**

Append in `namespace ZeroTestURM`:

```lean
/-- A URM program: instruction array plus
input/output register convention.

Per Tourlakis 2018 §0.1.0.37 (p. 15): "V_1 is the output
variable while the V_i, for i = 2, …, n+1, are input
variables." `outputReg` and `inputRegs` make this
convention explicit; the two structural invariants
`inputRegs_inj` and `outputReg_not_input` are
independent (distinct input slots map to distinct
registers; the output register is disjoint from every
input register).

PC labels range over `{0, …, instrs.size − 1}`. PC ≥
`instrs.size` is the implicit halt state (Tourlakis
p. 15: stop "continues forever 'trivially', without
changing either the V_i or the instruction number"). -/
structure URMProgram where
  /-- Number of registers. -/
  numRegs : ℕ
  /-- Number of inputs. -/
  numInputs : ℕ
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

- [ ] **Step 2.2: Verify**

Run:

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ZeroTestURM.olean
lake build GebLean.Utilities.ZeroTestURM
```

Expected: clean build with no warnings.

- [ ] **Step 2.3: Commit Task 2**

```bash
jj describe -m "feat(urm): introduce URMProgram structure

Program structure carrying instruction array, register
count, input register assignment (with injectivity
invariant), and output register (with disjoint-from-inputs
invariant).  Implements Tourlakis 2018 §0.1.0.37 (p. 15)
V_1-is-output convention.

Spec §4.1; Step T1 task 2 of 6."
jj new
```

---

## Task 3 — `URMState` structure and `step` function

**Files:**

- Modify: `GebLean/Utilities/ZeroTestURM.lean` (append)

- [ ] **Step 3.1: Define `URMState`**

Append in `namespace ZeroTestURM`:

```lean
/-- Machine state during URM execution: PC and register
contents.  Indexed by the program whose registers are
being tracked (the `numRegs` field of `P` fixes the
register-vector arity). -/
structure URMState (P : URMProgram) where
  /-- Program counter (0-indexed; Tourlakis's I(0) = 1
  is mapped to 0 here). -/
  pc : ℕ
  /-- Register contents, indexed by `Fin P.numRegs`. -/
  regs : Fin P.numRegs → ℕ
```

- [ ] **Step 3.2: Define `URMState.step`**

Append:

```lean
/-- One step of URM execution.  Pattern-matches on the
instruction at the current PC and updates state per
Tourlakis 2018 §0.1.0.37 (p. 16).  Past the end of the
instruction array, `step` is the identity (matching the
stop self-loop convention). -/
def URMState.step (P : URMProgram) (s : URMState P) :
    URMState P :=
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

`P` is explicit in the signature (matching spec §4.2).
Dot-notation call sites such as `s.runFor n` rely on
Lean's generalised field notation to infer `P` from the
receiver's `URMState P` type; direct call sites pass
`P` explicitly, e.g. `URMState.step P s`.

- [ ] **Step 3.3: Verify build**

Run:

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ZeroTestURM.olean
lake build GebLean.Utilities.ZeroTestURM
```

Expected: clean build with no warnings.

- [ ] **Step 3.4: Commit Task 3**

```bash
jj describe -m "feat(urm): introduce URMState and URMState.step

URMState carries PC and register vector indexed by the
program's numRegs; step pattern-matches on the
instruction at the current PC per Tourlakis 2018
§0.1.0.37 (p. 16).  Past the end of the instruction
array, step is the identity (stop self-loop convention,
Tourlakis p. 15).

Spec §4.2; Step T1 task 3 of 6."
jj new
```

---

## Task 4 — `runFor` step-counted runner with reduction lemmas

**Files:**

- Modify: `GebLean/Utilities/ZeroTestURM.lean` (append)

- [ ] **Step 4.1: Define `URMState.runFor`**

Append in `namespace ZeroTestURM`:

```lean
/-- Run the URM for `n` steps starting from `s`.
Constructive (no `Classical.choose`); `n` steps past
the halt state self-loop (Tourlakis p. 15).

`P` is explicit (matching spec §4.2). -/
def URMState.runFor (P : URMProgram) (s : URMState P) :
    ℕ → URMState P
  | 0 => s
  | n + 1 => (URMState.step P s).runFor n
```

- [ ] **Step 4.2: Add reduction lemmas**

Append:

```lean
/-- Reduction lemma: zero-step execution returns the
initial state. -/
@[simp] theorem URMState.runFor_zero
    (P : URMProgram) (s : URMState P) :
    s.runFor 0 = s := rfl

/-- Reduction lemma: `runFor (n+1)` peels one step at
the front. -/
@[simp] theorem URMState.runFor_succ
    (P : URMProgram) (s : URMState P) (n : ℕ) :
    s.runFor (n + 1) = (URMState.step P s).runFor n := rfl

/-- Step-additivity: running for `m + n` steps equals
running for `m`, then continuing `n` more from there. -/
theorem URMState.runFor_add
    (P : URMProgram) (s : URMState P) (m n : ℕ) :
    s.runFor (m + n) = (s.runFor m).runFor n := by
  induction m generalizing s with
  | zero => simp only [Nat.zero_add, URMState.runFor]
  | succ m ih =>
    change s.runFor (m + 1 + n) = (s.runFor (m + 1)).runFor n
    rw [Nat.add_right_comm m 1 n, Nat.add_one]
    change (URMState.step P s).runFor (m + n)
      = ((URMState.step P s).runFor m).runFor n
    exact ih (URMState.step P s)
```

The `| zero` case uses `simp only [Nat.zero_add,
URMState.runFor]` (not bare `simp [...]` per the
plan's `simp only` discipline at line 112) rather than
`rfl` because Lean 4's `Nat.add` is recursion on the
right argument: `0 + n` is not definitionally equal to
`n` (the equality is `Nat.zero_add`, a theorem). The
goal `s.runFor (0 + n) = (s.runFor 0).runFor n`
rewrites to `s.runFor n = s.runFor n` via
`Nat.zero_add` plus `URMState.runFor`'s `0` clause; it
then closes by reflexivity, which `simp only`
discharges automatically.

If the `rw [Nat.add_right_comm m 1 n, Nat.add_one]`
chain fails to elaborate (because `m + 1 + n` reduces
differently in the current mathlib pin), fall back to
`omega`:

```lean
  | succ m ih =>
    have h : m + 1 + n = (m + n) + 1 := by omega
    rw [h]
    change (URMState.step P s).runFor (m + n)
      = ((URMState.step P s).runFor m).runFor n
    exact ih (URMState.step P s)
```

The earlier-rewrite form is preferred; the `omega` form
is the documented fallback.

- [ ] **Step 4.3: Verify build**

Run:

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ZeroTestURM.olean
lake build GebLean.Utilities.ZeroTestURM
```

Expected: clean build with no warnings. The three
reduction lemmas (`runFor_zero`, `runFor_succ`,
`runFor_add`) are the universal verification for T1;
no program-specific smoke test is added at this step
(per the spec's test-discipline note: kernel reduction
over loop patterns is expensive; T1's tests are
confined to universal reduction lemmas; T2's
`compileER_runFor` is the universal correctness
statement for emitted programs).

- [ ] **Step 4.4: Commit Task 4**

```bash
jj describe -m "feat(urm): URMState.runFor with universal reduction lemmas

Step-counted execution: runFor 0 = identity;
runFor (n+1) = step then runFor n; runFor_add for
additivity.

Spec §4.2; Step T1 task 4 of 6."
jj new
```

---

## Task 5 — `URMState.init` via constructive `List.find?`

**Files:**

- Modify: `GebLean/Utilities/ZeroTestURM.lean` (append)

- [ ] **Step 5.1: Define `URMState.init`**

Append in `namespace ZeroTestURM`:

```lean
/-- Initial state for program `P` with input vector `v`:
PC = 0; registers default to 0, with input slots `i`
placed at `P.inputRegs i`.

Uses Lean core's `List.find?` over `List.finRange
P.numInputs` (constructive search returning
`Option (Fin P.numInputs)`) rather than
`Classical.choose`, per the constructive discipline.
`P.inputRegs_inj` ensures the returned `some i` value is
unique when it exists; when `r` is not in `P.inputRegs`'
image, `find?` returns `none` and the register defaults
to 0.

The choice `pc := 0` shifts Tourlakis's 1-indexed
`I(0) = 1` to 0-indexed `I(0) = 0`.  The shift is
consistent across all later constructions. -/
def URMState.init (P : URMProgram)
    (v : Fin P.numInputs → ℕ) : URMState P where
  pc := 0
  regs := fun r =>
    match (List.finRange P.numInputs).find?
        (fun i => decide (P.inputRegs i = r)) with
    | some i => v i
    | none   => 0
```

- [ ] **Step 5.2: Verify build**

Run:

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ZeroTestURM.olean
lake build GebLean.Utilities.ZeroTestURM
```

Expected: clean build with no warnings. No program-
specific example is added at this step; per the spec's
test-discipline note, kernel reduction over
`List.find?` on `List.finRange` for non-trivial cases
is expensive and unreliable. The correctness of
`URMState.init` for emitted compiler programs is
verified at T2 via `compileER_runFor`.

- [ ] **Step 5.3: Commit Task 5**

```bash
jj describe -m "feat(urm): URMState.init via constructive List.find?

Initial state construction: PC = 0; registers default to
0 with input slots placed at inputRegs i.  Uses
List.find? over List.finRange (from
Mathlib.Data.List.FinRange) — constructive,
Option-valued — per the spec's constructive discipline.

Spec §4.3 + §10; Step T1 task 5 of 6."
jj new
```

---

## Task 6 — Axiom audit and final verification

**Files:**

- No code changes; verification only.

- [ ] **Step 6.1: Run the build cleanly from scratch**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ZeroTestURM.olean
lake build GebLean.Utilities.ZeroTestURM
```

Expected: clean build, no warnings.

- [ ] **Step 6.2: Run the axiom check on the kernel's file**

Use the project's axiom-check script. The script
(vendored from `lean4-skills`) takes a file or directory
path as its argument:

```bash
bash scripts/check-axioms.sh GebLean/Utilities/ZeroTestURM.lean
```

Expected: the `STANDARD_AXIOMS` allowlist covers
`propext`, `Quot.sound`, `quot.sound`;
`Classical.choice` is NOT in the allowlist (the script's
local-modification comment, lines 17–22 of
`scripts/check-axioms.sh`, documents that
`Classical.choice` flagging is enabled). Any
`Classical.choice` dependency in any declaration emits
a `FAIL` line.

For each `URMState.*` declaration introduced in this
step (`step`, `runFor`, `runFor_zero`, `runFor_succ`,
`runFor_add`, `init`), the check must report no
unauthorised axioms.

- [ ] **Step 6.3: Manual lint of the module**

Inspect `GebLean/Utilities/ZeroTestURM.lean` by hand:

- Every `def`, `structure`, `inductive`, `theorem` has a
  `/-- … -/` docstring.
- Every docstring with literature content cites
  Tourlakis 2018 §0.1.0.37 (or the spec) by §, p., or
  paragraph reference.
- No occurrences of "load-bearing", "key", "important",
  "elegant", "crucial", "beautiful" or other banned
  adjectives from the style guide.
- No `URMComputes` structure, no `urmSeq` / `urmIf` /
  `urmLoop` combinators, no `urmDecToReg` / `urmCopyReg`
  helpers — these are explicitly forbidden by spec
  §4.4 (T1 is just the kernel; combinator and helper
  work that spec §4.4 lists as absent does not appear
  in this module).
- No `sorry`, no `admit`, no `noncomputable`, no
  `Classical.*`.

- [ ] **Step 6.4: Commit Task 6 (verification record)**

Task 6 is verification-only, no code changes. The
current working-copy commit (created by Task 5's
trailing `jj new`) is empty; describe it as the
verification record. Empty commits are explicitly
permitted under jj's default workflow — no
`--allow-empty` flag is needed.

```bash
jj describe -m "chore(urm): Step T1 verification — axiom-clean, lint-clean

scripts/check-axioms.sh GebLean/Utilities/ZeroTestURM.lean
passes; manual lint of docstrings confirms Tourlakis
§0.1.0.37 citations on every declaration and no banned
wordings.

Step T1 task 6 of 6 — Step T1 complete."
jj new
```

---

## Spec coverage check

| Spec section | Plan task |
| --- | --- |
| §4.1 `URMInstr` (5 constructors) | Task 1 |
| §4.1 `URMProgram` structure | Task 2 |
| §4.1 `inputRegs_inj` invariant | Task 2 |
| §4.1 `outputReg_not_input` invariant | Task 2 |
| §4.2 `URMState` structure | Task 3 |
| §4.2 `URMState.step` | Task 3 |
| §4.2 `URMState.runFor` | Task 4 |
| §4.2 reduction lemmas (`runFor_zero`, `runFor_succ`, `runFor_add`) | Task 4 |
| §4.3 `URMState.init` via `List.find?` | Task 5 |
| §4.4 negative-spec ("does NOT contain") | Implicit (no combinators/URMComputes added) |
| §10 constructive discipline | Tasks 5, 6 |
| §12.1 axiom check | Task 6 |
| §12.2 URM matches Tourlakis §0.1.0.37 | Task 6 (manual lint) |
| §12.11 No CSLib URM import | Task 1 (imports `Mathlib.Data.List.FinRange` and `Mathlib.Logic.Function.Basic`; no CSLib reach) |

Coverage: complete. No spec section is uncovered by a
task.

## Out of scope

This plan covers Step T1 only (URM kernel). Subsequent
plans for the same erToK spec:

- T2 (ER → URM compiler): `compileER`,
  `compileER_runtime`, per-ER-constructor templates per
  spec §5.
- T3 (Ksim simulator): `simulate`, `simulate_interp`,
  plus the four supporting K^sim composites
  (`natK`, `maxK`, `maxOver`, `pow2_iter`) per spec §6
  and §3.1.
- T4 (runtime bound): `boundExprK`,
  `boundExprK_dominates` per spec §7.
- T5 (`erToK` assembly + functor): `erToK`,
  `erToK_interp`, `erToK_level`, `erToKN`,
  `erToKFunctor` per spec §8.

Each subsequent step gets its own plan + adversarial
review + execution cycle.
