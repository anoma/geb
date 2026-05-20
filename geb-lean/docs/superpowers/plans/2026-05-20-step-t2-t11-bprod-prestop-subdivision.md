# Step T2 Task 11e.6.a.iii-bprod — pre-stop sub-division

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary](#summary)
- [Top-level statement](#top-level-statement)
- [Register and PC layout recap](#register-and-pc-layout-recap)
- [Sub-task DAG](#sub-task-dag)
- [Sub-task list](#sub-task-list)
  - [Sub-task 11e.6.a.iii-bprod.0 — PC-bound infrastructure](#sub-task-11e6aiii-bprod0--pc-bound-infrastructure)
  - [Sub-task 11e.6.a.iii-bprod.1.a — zero-sweep correctness alias](#sub-task-11e6aiii-bprod1a--zero-sweep-correctness-alias)
  - [Sub-task 11e.6.a.iii-bprod.1.b — prologue correctness alias](#sub-task-11e6aiii-bprod1b--prologue-correctness-alias)
  - [Sub-task 11e.6.a.iii-bprod.1.c.0 — accUpdate prep (two transferLoops)](#sub-task-11e6aiii-bprod1c0--accupdate-prep-two-transferloops)
  - [Sub-task 11e.6.a.iii-bprod.1.c.1 — inner mul partial invariant + base](#sub-task-11e6aiii-bprod1c1--inner-mul-partial-invariant--base)
  - [Sub-task 11e.6.a.iii-bprod.1.c.2 — inner mul step (j to j + 1)](#sub-task-11e6aiii-bprod1c2--inner-mul-step-j-to-j--1)
  - [Sub-task 11e.6.a.iii-bprod.1.c.3 — inner mul outer iteration](#sub-task-11e6aiii-bprod1c3--inner-mul-outer-iteration)
  - [Sub-task 11e.6.a.iii-bprod.1.c.4 — accUpdate assembly](#sub-task-11e6aiii-bprod1c4--accupdate-assembly)
  - [Sub-task 11e.6.a.iii-bprod.1.d — f-body embedding](#sub-task-11e6aiii-bprod1d--f-body-embedding)
  - [Sub-task 11e.6.a.iii-bprod.2 — partial invariant and base case](#sub-task-11e6aiii-bprod2--partial-invariant-and-base-case)
  - [Sub-task 11e.6.a.iii-bprod.3.phase_i0 — zero-sweep preservation](#sub-task-11e6aiii-bprod3phase_i0--zero-sweep-preservation)
  - [Sub-task 11e.6.a.iii-bprod.3.phase_i1 — prologue preservation](#sub-task-11e6aiii-bprod3phase_i1--prologue-preservation)
  - [Sub-task 11e.6.a.iii-bprod.3.phase_i2 — f-body preservation](#sub-task-11e6aiii-bprod3phase_i2--f-body-preservation)
  - [Sub-task 11e.6.a.iii-bprod.3.phase_i3 — accUpdate + incR + goto](#sub-task-11e6aiii-bprod3phase_i3--accupdate--incr--goto)
  - [Sub-task 11e.6.a.iii-bprod.4 — induction glue (i to i + 1)](#sub-task-11e6aiii-bprod4--induction-glue-i-to-i--1)
  - [Sub-task 11e.6.a.iii-bprod.5 — outer iteration (i = 0 to v 0)](#sub-task-11e6aiii-bprod5--outer-iteration-i--0-to-v-0)
  - [Sub-task 11e.6.a.iii-bprod.6 — final assembly](#sub-task-11e6aiii-bprod6--final-assembly)
- [Inductive variable](#inductive-variable)
- [Cross-references and IH form](#cross-references-and-ih-form)
- [Followup items](#followup-items)
- [References](#references)

<!-- END doctoc -->

## Summary

This document sub-divides Task 11e.6.a.iii-bprod, the bprod
pre-stop correctness theorem
`compileER_pre_stop_correct_bprod`, into seventeen
implementer-sized sub-tasks. The target lemma states that for
every `f : ERMor1 (k + 1)` and `v : Fin (k + 1) → ℕ`, there
exists `T0 ≤ compileER_runtime (.bprod f) v` such that at step
`T0` the URM program `compileER (.bprod f)` has its PC at
`(compileER (.bprod f)).instrs.size - 1`, its output register
contains `(.bprod f).interp v`, and on every earlier step the
PC is strictly below `instrs.size - 1`. The proof mirrors the
landed `compileER_pre_stop_correct_bsum`
(`BSum.lean`) but threads a *multiplicative* accumulator update
in place of the additive one. New work lands in
`GebLean/LawvereERKSim/BProd.lean`, imported between `BSum` and
the `LawvereERKSim` index. The chain reuses without
modification: the program-embedding framework
(`Embedding.lean`), the loop dischargers (`Loops.lean`), the
shared zero-sweep / prologue helpers landed during the bsum
chain (`compileFrag_comp_subBlock_inputCopies_correct`,
`compileFrag_bsum_zeroSweep_correct`), the comp f-body
embedding pattern, and the structural-numRegs identity
`compileER_numRegs_eq_compileERFrag_numRegs`. Estimated total
LOC: 4500-5500.

The bprod accUpdate is the `R^XY_Z` multiplication template
from Tourlakis 2018 p. 19: a 21-instruction block that
destructively copies the accumulator and f-output to scratch
registers and then iterates an inner addition loop B times
(where B is the f-output). Because the inner loop is itself
a bsum-shaped jumpZR + decR + preservingTransfer + goto
pattern, sub-task 1.c is decomposed into five internal
sub-tasks 1.c.0 through 1.c.4 that mirror the outer bsum
phase structure on a miniature scale.

## Top-level statement

The non-negotiable signature for the assembly lemma, modelled
on `compileER_pre_stop_correct_bsum` (`BSum.lean` tail):

```lean
private theorem compileER_pre_stop_correct_bprod
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (ih_f : ∀ (v' : Fin (k + 1) → ℕ),
      ∃ T0 : ℕ,
        T0 ≤ compileER_runtime f v' ∧
        (URMState.runFor (compileER f)
              (URMState.init (compileER f) v') T0).pc
            = (compileER f).instrs.size - 1 ∧
        (URMState.runFor (compileER f)
              (URMState.init (compileER f) v') T0).regs
            (compileER f).outputReg
          = f.interp v' ∧
        (∀ k' < T0,
          (URMState.runFor (compileER f)
              (URMState.init (compileER f) v') k').pc
            < (compileER f).instrs.size - 1))
    (v : Fin (k + 1) → ℕ) :
    ∃ T0 : ℕ,
      T0 ≤ compileER_runtime (.bprod f : ERMor1 (k + 1)) v ∧
      (URMState.runFor (compileER (.bprod f : ERMor1 (k + 1)))
            (URMState.init
              (compileER (.bprod f : ERMor1 (k + 1))) v) T0).pc
          = (compileER (.bprod f : ERMor1 (k + 1))).instrs.size - 1 ∧
      (URMState.runFor (compileER (.bprod f : ERMor1 (k + 1)))
            (URMState.init
              (compileER (.bprod f : ERMor1 (k + 1))) v) T0).regs
          (compileER (.bprod f : ERMor1 (k + 1))).outputReg
        = (.bprod f : ERMor1 (k + 1)).interp v ∧
      (∀ k' < T0,
        (URMState.runFor (compileER (.bprod f : ERMor1 (k + 1)))
            (URMState.init
              (compileER (.bprod f : ERMor1 (k + 1))) v) k').pc
          < (compileER (.bprod f : ERMor1 (k + 1))).instrs.size - 1)
```

The signature substitutes `.bprod f` for `.bsum f` in the
landed bsum signature. The IH form is the standard
existential pre-stop form, so the bridge
`compileER_pre_stop_to_runFor` (`Embedding.lean`) consumes the
bprod pre-stop conclusion unmodified, enabling Task 11g
(`compileER_runFor_bprod`) as a thin three-line wrapper.

## Register and PC layout recap

Source: `compileFrag_bprod` (`Compiler.lean` lines 1190-1440).
Names below match the `let`-bindings inside that definition.

Register layout (outer arity `k + 1`):

- `0`: `V_z` (reserved zero).
- `1`: `V_acc` = outer `outputReg`. Multiplicative
  accumulator.
- `2`: `V_bound_in` = outer input slot `0` (the bound).
- `3..k+2`: `V_param_j` for `j ∈ Fin k` = outer input slots
  `1..k`.
- `k + 3`: `V_x` = destructive clone of `V_bound_in`.
- `k + 4`: `V_i` = iteration index.
- `k + 5`: `tmp1` = scratch for the per-iteration prologue's
  `preservingTransfer`.
- `k + 6`: `tmp2` = scratch for the prelude's clone of
  `V_bound_in` into `V_x`.
- `k + 7`: `V_acc_clone` = multiplicative scratch
  (destructive copy of `V_acc` per iteration).
- `k + 8`: `V_factor` = destructive copy of f's output
  (the multiplicand for the current iteration).
- `k + 9`: `V_mul_tmp` = scratch for `preservingTransfer`
  inside the inner add loop.
- `fBase = k + 10 .. nR - 1`: f's reindexed register block,
  where `nR = fBase + frag_f.numRegs`.

The `k + 10` offset matches `compileER_numRegs (.bprod f)`
after the session-6 off-by-one correction (the original
`k + 9` would have aliased `V_mul_tmp` at index `k + 9` with
`fBase` at the same index).

PC layout (absolute offsets, where `a := k + 1` is f's arity):

- `0..3`: prelude — four `assignR` (`V_z`, `V_acc`, `V_x`,
  `V_i` all set to `0`).
- `4..12`: clone of `V_bound_in` into `V_x` via
  `preservingTransfer 4 vBoundIn vX tmp2` (9 instructions).
- `13`: `incR vAcc` — initialises the multiplicative
  accumulator to `1` (the empty product).
- `topPC = 14`: `jumpZR vX exitPC bodyStartPC` (loop top).
- `bodyStartPC = 15`: `decR vX`.
- `zeroSweepBase = 16`: `bsum_zeroSweep frag_f fBase` —
  `frag_f.numRegs` `assignR (fBase + r) 0` instructions
  (shared verbatim with bsum; the bprod compiler imports
  `bsum_zeroSweep` from `Compiler.lean`).
- `prologueBase = 16 + frag_f.numRegs`: per-iteration prologue,
  `a` blocks of `bsum_prologueBlock` (each
  `preservingTransfer`, 9 instructions); the slot-0 block
  copies `V_i` into f's input slot 0, the slot-`s` block for
  `s > 0` copies outer parameter `V_param_{s-1}` into f's
  input slot `s`.
- `bodyPCBase = 16 + frag_f.numRegs + 9 * a`: f's reindexed
  body (`frag_f.instrs.size - 1` instructions; trailing
  `stopR` dropped via `frag_f.instrs.pop.toList.map`).
- `trBase = bodyPCBase + fBodyLen`: start of the
  multiplicative `R^XY_Z` accumulator-update block (21
  instructions, see breakdown below).
- `mul_outerCopy_AccBase = trBase`: `transferLoop trBase
  vAcc vAccClone` (4 instructions). Destructively copies the
  current accumulator value `A` into `V_acc_clone`; leaves
  `V_acc = 0` and `V_acc_clone = A`.
- `mul_outerCopy_FactorBase = trBase + 4`: `transferLoop
  (trBase + 4) (fBase + frag_f.outputReg.val) vFactor`
  (4 instructions). Destructively copies f's output `B` into
  `V_factor`; leaves f's output register at 0 and `V_factor
  = B`.
- `mul_innerTopPC = trBase + 8`: `jumpZR vFactor
  (trBase + 20) (trBase + 9)`. Inner-loop top: exit to
  cleanup if `V_factor = 0`, otherwise enter inner body.
- `mul_innerBodyStartPC = trBase + 9`: `decR vFactor`.
- `mul_innerAccAdd_Base = trBase + 10`: `preservingTransfer
  (trBase + 10) vAccClone vAcc vMulTmp` (9 instructions).
  Adds `A` into `V_acc` while preserving `V_acc_clone`.
- `mul_innerGoto = trBase + 19`: `goto (trBase + 8)`.
- `mul_resetPC = trBase + 20`: `assignR vAccClone 0` (1
  instruction). Resets the scratch clone to 0 after the
  inner loop completes.
- `incIPC = trBase + 21`: `incR vI`.
- `gotoTopPC = trBase + 22`: `goto topPC`.
- `exitPC = trBase + 23`: `stopR`. This is
  `instrs.size - 1`.

Disjoint blocks for register-embedding purposes:

- The "outer scaffolding" block `{V_z, V_acc, V_bound_in,
  V_param_1..k, V_x, V_i, tmp1, tmp2, V_acc_clone,
  V_factor, V_mul_tmp}` covers indices `0..k+9`; it is
  disjoint from f's body block `fBase..fBase +
  frag_f.numRegs - 1`.
- The f-body embedding (analogue of bsum's
  `ProgramEmbedsFragment_compileFrag_bsum_fBody`) places f's
  reindexed registers at `fBase = k + 10`; "outside the
  f-body" means outer indices `< fBase` together with the
  implicit upper bound `nR`.

## Sub-task DAG

```text
              [bprod.0 PC-bound infra]
                       |
        +--------------+-------------+
        |              |             |
[bprod.1.a            [bprod.1.b     [bprod.1.c.0 copy phase]
 zeroSweep            prologue              |
 _correct + bound]    _correct +     [bprod.1.c.1 inner mul
 alias of bsum's]     bound]          partial inv + base]
        |              |                    |
        |              |             [bprod.1.c.2 inner mul step]
        |              |                    |
        |              |             [bprod.1.c.3 inner mul outer]
        |              |                    |
        |              |             [bprod.1.c.4 accUpdate
        |              |              assembly + bound]
        +--------------+-------------+
                       |
              [bprod.1.d f-body embedding]
                       |
              [bprod.2 partial_invariant + base]
                       |
                       v
              [bprod.3.phase_i0  zeroSweep preservation]
                       |
              [bprod.3.phase_i1  prologue preservation]
                       |
              [bprod.3.phase_i2  f-body preservation
                                 (consumes ih_f)]
                       |
              [bprod.3.phase_i3  accUpdate + incR vI →
                                 partial_invariant @ (i+1)]
                       |
              [bprod.4 step glue: i → i + 1]
                       |
              [bprod.5 outer iteration i = 0 → v 0]
                       |
              [bprod.6 final assembly:
                       prelude + clone + incR vAcc +
                       outer loop + exit jumpZR + stopR]
                       |
                       v
        [compileER_pre_stop_correct_bprod]
```

The chain mirrors the bsum DAG with two structural
adjustments: (i) the accUpdate sub-task 1.c expands into five
sub-tasks (1.c.0 through 1.c.4) reflecting the internal inner
mul loop's own partial-invariant decomposition; (ii) bprod.2's
base case must additionally handle the `incR vAcc` step at PC
13 that initialises the accumulator to 1 before the loop
begins.

## Sub-task list

Each sub-task lists the lemma signature(s) it lands, its
inputs and dependencies, outputs (declarations added to
`BProd.lean`), an LOC estimate, and notes drawn from the Task
11 handoff's `Patterns learned` section.

### Sub-task 11e.6.a.iii-bprod.0 — PC-bound infrastructure

Signatures (definitions, all `private`):

```lean
private def bprod_topPC : ℕ := 14
private def bprod_bodyStartPC : ℕ := 15
private def bprod_zeroSweepBase : ℕ := 16

private def bprod_prologueBase {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  16 + frag_f.numRegs

private def bprod_bodyPCBase {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  16 + frag_f.numRegs + 9 * (k + 1)

private def bprod_trBase {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  bprod_bodyPCBase frag_f + (frag_f.instrs.size - 1)

private def bprod_mul_innerTopPC {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  bprod_trBase frag_f + 8

private def bprod_mul_innerBodyStartPC {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  bprod_trBase frag_f + 9

private def bprod_mul_resetPC {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  bprod_trBase frag_f + 20

private def bprod_incIPC {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  bprod_trBase frag_f + 21

private def bprod_gotoTopPC {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  bprod_trBase frag_f + 22

private def bprod_exitPC {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) : ℕ :=
  bprod_trBase frag_f + 23

private theorem compileFrag_bprod_size {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) :
    (compileFrag_bprod frag_f).instrs.size
      = 39 + frag_f.numRegs + 9 * (k + 1)
        + frag_f.instrs.size

private theorem bprod_exitPC_eq_size_pred {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) :
    bprod_exitPC frag_f
      = (compileFrag_bprod frag_f).instrs.size - 1
```

Inputs: `compileFrag_bprod`'s named offsets (`Compiler.lean`
lines 1190-1440). Following the bsum.0 convention,
`compileFrag_bprod_size` lands co-located with
`compileFrag_bprod` in `Compiler.lean` (not in `BProd.lean`),
analogously to bsum.0's relocation of
`compileFrag_bsum_size`.

Outputs: PC-layout constants in `BProd.lean`; size lemma
in `Compiler.lean`.

Estimated LOC: 200-250 in `BProd.lean`, plus 80-100 in
`Compiler.lean` for the size lemma.

Notes: keep all `BProd.lean` constants `private`. Prefer
`let` over `set` inside proofs to avoid omega's loss of
syntactic identity (Pattern 9). Re-derive `instrs.size`
expressions via `URMInstrRaw.toBoundedArray_size`
(`Compiler.lean`). The 21-instruction accUpdate block is the
single largest divergence from bsum's PC layout (where the
analogous block is 4 instructions); double-check the
arithmetic during the size lemma's manual segment counting.

The `bprod_trBase` definition uses `frag_f.instrs.size - 1`.
This is safe because `lastInstr_isStop` (a
`CompiledFragment` invariant) guarantees `frag_f.instrs.size
≥ 1`; the `- 1` therefore cannot underflow.

### Sub-task 11e.6.a.iii-bprod.1.a — zero-sweep correctness alias

Signatures: thin re-export of
`compileFrag_bsum_zeroSweep_correct` and
`compileFrag_bsum_zeroSweep_pc_strict_bound` from
`BSum.lean` (already un-`private`d during bsum.1.b). The
bprod zero-sweep block is literally
`bsum_zeroSweep frag_f fBase` (`Compiler.lean` line 1266),
so the same correctness lemma applies after `pcBase` and
`P` are instantiated to the bprod compiled fragment.

```lean
private theorem compileFrag_bprod_zeroSweep_correct
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (s : URMState (compileFrag_bprod frag_f).toURMProgram)
    (h_pc : s.pc = bprod_zeroSweepBase) :
    let totalSteps : ℕ := frag_f.numRegs
    let s' := URMState.runFor _ s totalSteps
    s'.pc = bprod_zeroSweepBase + frag_f.numRegs ∧
    (∀ r : Fin frag_f.numRegs,
        s'.regs ⟨(k + 10) + r.val, by ...⟩ = 0) ∧
    (∀ q : Fin (compileFrag_bprod frag_f).numRegs,
        (∀ r : Fin frag_f.numRegs,
          q.val ≠ (k + 10) + r.val) →
        s'.regs q = s.regs q)

private theorem compileFrag_bprod_zeroSweep_pc_strict_bound : ...
```

Inputs: `compileFrag_bsum_zeroSweep_correct` (`BSum.lean`,
landed bsum.1.a), instantiated at `pcBase = bprod_zeroSweepBase`,
`P = (compileFrag_bprod frag_f).toURMProgram`, `fBase = k + 10`.

Outputs: bprod-flavoured wrappers around the bsum lemmas.

Estimated LOC: 80-120.

Notes: the bsum lemmas are already abstract over `P` and
`pcBase`, so the wrapping is mechanical. The follow-up to
migrate these helpers to `Loops.lean` (bsum followup item 4)
remains open and is *not* prerequisite to bprod.1.a; the alias
strategy keeps the bsum/bprod-specific names available while
deferring the extraction.

### Sub-task 11e.6.a.iii-bprod.1.b — prologue correctness alias

Signatures: thin re-export of `compileFrag_bsum_prologue_correct`
and `compileFrag_bsum_prologue_pc_strict_bound` (themselves
landed in bsum.1.b as aliases of
`compileFrag_comp_subBlock_inputCopies_correct` /
`_pc_strict_bound` from `Comp.lean`).

```lean
private theorem compileFrag_bprod_prologue_correct
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (zReg tmp : Fin (compileFrag_bprod frag_f).numRegs)
    (srcs dsts : Fin (k + 1) →
      Fin (compileFrag_bprod frag_f).numRegs)
    (h_disj : inputCopies_disj
      (compileFrag_bprod frag_f).toURMProgram zReg tmp
      srcs dsts)
    (H : ∀ s : Fin (k + 1),
      preservingTransferInstrs
        (compileFrag_bprod frag_f).toURMProgram
        (bprod_prologueBase frag_f + 9 * s.val)
        (srcs s) (dsts s) tmp zReg)
    (vSrc : Fin (k + 1) → ℕ)
    (s : URMState (compileFrag_bprod frag_f).toURMProgram)
    (h_pc : s.pc = bprod_prologueBase frag_f)
    (h_z : s.regs zReg = 0) (h_tmp0 : s.regs tmp = 0)
    (h_srcs : ∀ j, s.regs (srcs j) = vSrc j)
    (h_dsts0 : ∀ j, s.regs (dsts j) = 0) :
    let totalSteps : ℕ := 9 * vPrefixSum vSrc (k + 1) + 2 * (k + 1)
    let s' := URMState.runFor _ s totalSteps
    s'.pc = bprod_prologueBase frag_f + 9 * (k + 1) ∧
    s'.regs zReg = 0 ∧
    s'.regs tmp = 0 ∧
    (∀ j : Fin (k + 1), s'.regs (dsts j) = vSrc j) ∧
    (∀ j : Fin (k + 1), s'.regs (srcs j) = vSrc j) ∧
    (∀ r : Fin _,
        (∀ j : Fin (k + 1), r ≠ dsts j) → r ≠ tmp →
        s'.regs r = s.regs r)

private theorem compileFrag_bprod_prologue_pc_strict_bound : ...
```

Inputs: `compileFrag_comp_subBlock_inputCopies_correct` and
`_pc_strict_bound` (`Comp.lean`).

Outputs: bprod-flavoured wrappers; no migration of the shared
helpers (deferred to followup task #654 item 1).

Estimated LOC: 80-120.

Notes: the bprod prologue's `srcs` map is structurally
identical to bsum's: slot 0 → `V_i` (the iteration index),
slot `s > 0` → `V_param_{s-1}` (an outer parameter). The
`dsts` map is f's reindexed input slots (offset by `fBase =
k + 10`).

### Sub-task 11e.6.a.iii-bprod.1.c.0 — accUpdate prep (two transferLoops)

Signature:

```lean
private structure compileFrag_bprod_accUpdate_prep_post
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (vAccIn vFOut : ℕ)
    (s : URMState (compileFrag_bprod frag_f).toURMProgram)
    : Prop where
  pc_eq : s.pc = bprod_mul_innerTopPC frag_f
  acc_zero : s.regs ⟨1, by ...⟩ = 0
  acc_clone_eq : s.regs ⟨k + 7, by ...⟩ = vAccIn
  fOut_zero : s.regs ⟨(k + 10) + frag_f.outputReg.val, by ...⟩
    = 0
  factor_eq : s.regs ⟨k + 8, by ...⟩ = vFOut
  mulTmp_zero : s.regs ⟨k + 9, by ...⟩ = 0

private theorem compileFrag_bprod_accUpdate_prep_correct
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (vAccIn vFOut : ℕ)
    (sPre : URMState (compileFrag_bprod frag_f).toURMProgram)
    (h_pc : sPre.pc = bprod_trBase frag_f)
    (h_acc : sPre.regs ⟨1, by ...⟩ = vAccIn)
    (h_acc_clone_zero : sPre.regs ⟨k + 7, by ...⟩ = 0)
    (h_fOut : sPre.regs ⟨(k + 10) + frag_f.outputReg.val, _⟩
      = vFOut)
    (h_factor_zero : sPre.regs ⟨k + 8, by ...⟩ = 0)
    (h_mulTmp_zero : sPre.regs ⟨k + 9, by ...⟩ = 0) :
    let totalSteps : ℕ := (4 * vAccIn + 1) + (4 * vFOut + 1)
    let s' := URMState.runFor _ sPre totalSteps
    compileFrag_bprod_accUpdate_prep_post frag_f vAccIn vFOut s' ∧
    (∀ q : Fin (compileFrag_bprod frag_f).numRegs,
      q.val ≠ 1 →
      q.val ≠ k + 7 →
      q.val ≠ k + 8 →
      q.val ≠ (k + 10) + frag_f.outputReg.val →
      s'.regs q = sPre.regs q)

private theorem compileFrag_bprod_accUpdate_prep_pc_strict_bound : ...
```

Inputs: `transferLoop_correct` and
`transferLoop_correct_pc_strict_bound` (`Loops.lean`),
applied twice with distinct register pairs. Instruction
presence at `trBase`, `trBase + 4` via a fresh
`compileFrag_bprod_accUpdate_prep_instr_at` segment-peeling
helper (modelled on bsum.3.phase_i0's
`compileFrag_bsum_zeroSweep_instr_at`).

Outputs: prep-phase post structure and correctness lemma. The
preservation property is a separate conjunct in the
correctness lemma's conclusion, not a field of the structure
(the structure cannot reference the pre-state as a
free identifier).

Estimated LOC: 400-500 (including the segment-peeling helper
for instruction presence; ~250 LOC of mechanical proof on the
segment helper, plus ~200 LOC for the two-`transferLoop`
composition via `URMState.runFor_add`).

Notes: the two prep transferLoops destroy `V_acc` and
f's output respectively. The post-state has them both at 0,
with their values transferred to `V_acc_clone` and
`V_factor`. The preservation conjunct does *not* mention
the f-body's non-output registers, even though they remain
preserved; that fact is delegated to bprod.3.phase_i2's
`f_other_zero` carry-over in the outer partial invariant.
The correctness lemma's docstring should record this design
decision so an implementer encountering the lemma in
isolation understands why the f-body's non-output registers
are not asserted preserved here.

### Sub-task 11e.6.a.iii-bprod.1.c.1 — inner mul partial invariant + base

Signatures:

```lean
private structure compileFrag_bprod_mul_partial_invariant
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (vAccIn vFOut : ℕ)
    (j : ℕ) (hj : j ≤ vFOut)
    (s : URMState (compileFrag_bprod frag_f).toURMProgram)
    : Prop where
  hj_le : j ≤ vFOut := hj
  pc_eq : s.pc = bprod_mul_innerTopPC frag_f
  zReg_zero : s.regs ⟨0, by ...⟩ = 0
  acc_clone_eq : s.regs ⟨k + 7, by ...⟩ = vAccIn
  factor_eq : s.regs ⟨k + 8, by ...⟩ = vFOut - j
  mulTmp_zero : s.regs ⟨k + 9, by ...⟩ = 0
  acc_eq : s.regs ⟨1, by ...⟩ = vAccIn * j

private theorem compileFrag_bprod_mul_partial_base
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (vAccIn vFOut : ℕ)
    (sPrep : URMState (compileFrag_bprod frag_f).toURMProgram)
    (h_post : compileFrag_bprod_accUpdate_prep_post
                frag_f vAccIn vFOut sPrep) :
    compileFrag_bprod_mul_partial_invariant frag_f vAccIn vFOut
      0 (Nat.zero_le _) sPrep
```

The invariant carries 7 clauses. At `j = 0`: `V_factor = B`
(the unmodified copy), `V_acc = A * 0 = 0` (still 0 after
the prep transferLoop destroyed it). At `j = B`: `V_factor =
0`, `V_acc = A * B`. Preservation of the four mul-scratch
registers' surroundings is *not* a clause of the structure;
the inner-mul block touches only those four registers, so the
caller-side preservation property is established by
bprod.1.c.4 (accUpdate assembly) as a conjunct of the
producing lemma's conclusion, mirroring the prep lemma's
shape (sub-task 1.c.0).

Inputs: the post-state from bprod.1.c.0 directly.

Outputs: inner mul partial invariant + base lemma.

Estimated LOC: 250-350. The base case is a thin field
re-projection from the prep post-state (no URM steps are
taken — the invariant at `j = 0` is the immediate output of
prep).

Notes: use field-projection over destructure (Pattern 10).
`acc_eq` at the base reduces to `0 = vAccIn * 0`, immediate
from `Nat.mul_zero`.

### Sub-task 11e.6.a.iii-bprod.1.c.2 — inner mul step (j to j + 1)

Signature:

```lean
private theorem compileFrag_bprod_mul_partial_step
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (vAccIn vFOut : ℕ)
    (j : Fin vFOut)
    (sPre : URMState (compileFrag_bprod frag_f).toURMProgram)
    (h_inv : compileFrag_bprod_mul_partial_invariant frag_f
              vAccIn vFOut j.val j.isLt.le sPre) :
    ∃ T0 : ℕ,
      T0 = 9 * vAccIn + 5 ∧
      compileFrag_bprod_mul_partial_invariant frag_f vAccIn vFOut
          (j.val + 1) (Nat.succ_le_of_lt j.isLt)
        (URMState.runFor _ sPre T0) ∧
      (∀ k' < T0,
        (URMState.runFor _ sPre k').pc
          < bprod_mul_resetPC frag_f)
```

The 5 control steps decompose as: 1 jumpZR (taken to inner
body since `V_factor = vFOut - j.val > 0` for `j.val < vFOut`),
1 decR, (`9 * vAccIn + 2`) preservingTransfer, 1 goto.
Total: `9 * vAccIn + 5` steps. Inlined-conjunction convention
applies (T0 is closed-form; Pattern 16).

Inputs: `URMState.step_of_getElem?_jumpZ` (zero-branch
discharge requires `V_factor ≠ 0`), `URMState.step_of_getElem?_dec`,
`preservingTransfer_correct` (`Loops.lean`),
`URMState.step_of_getElem?_jump` (the goto macro).
Instruction-presence segment-peeling via a new helper
`compileFrag_bprod_accUpdate_innerBody_instr_at` (fourth
instance of the segment-peeling pattern; see followup item 1
in this document's followup section).

Outputs: inner mul step preservation lemma.

Estimated LOC: 550-700.

Notes: re-establish the invariant clauses:

- `pc_eq`: returns to `bprod_mul_innerTopPC` via the goto.
- `factor_eq`: `V_factor` decreases from `vFOut - j.val` to
  `vFOut - (j.val + 1)`, exactly as `decR` produces.
- `acc_eq`: `V_acc` increases from `vAccIn * j.val` to
  `vAccIn * j.val + vAccIn = vAccIn * (j.val + 1)`. The
  `preservingTransfer` adds the value of `V_acc_clone =
  vAccIn` into `V_acc` while preserving `V_acc_clone` itself.
- `acc_clone_eq`: preserved by `preservingTransfer`.
- `mulTmp_zero`: ends at 0 (preservingTransfer's defining
  property).

For the strict PC bound, observe that the entire inner-body
sequence lives in `[bprod_mul_innerTopPC,
bprod_mul_resetPC)`, with the goto's final step setting PC =
`bprod_mul_innerTopPC` (which is `< bprod_mul_resetPC` since
the reset PC is at offset +12).

### Sub-task 11e.6.a.iii-bprod.1.c.3 — inner mul outer iteration

Signatures:

```lean
private theorem compileFrag_bprod_mul_partial_aux
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (vAccIn vFOut : ℕ)
    (sPrep : URMState (compileFrag_bprod frag_f).toURMProgram)
    (h_prep : compileFrag_bprod_accUpdate_prep_post
                frag_f vAccIn vFOut sPrep)
    (j : ℕ) (hj : j ≤ vFOut) :
    ∃ T0 : ℕ,
      T0 = j * (9 * vAccIn + 5) ∧
      compileFrag_bprod_mul_partial_invariant frag_f vAccIn vFOut
          j hj (URMState.runFor _ sPrep T0) ∧
      (∀ k' < T0,
        (URMState.runFor _ sPrep k').pc
          < bprod_mul_resetPC frag_f)

private theorem compileFrag_bprod_mul_partial
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (vAccIn vFOut : ℕ)
    (sPrep : URMState (compileFrag_bprod frag_f).toURMProgram)
    (h_prep : compileFrag_bprod_accUpdate_prep_post
                frag_f vAccIn vFOut sPrep) :
    ∃ T0 : ℕ,
      T0 = vFOut * (9 * vAccIn + 5) ∧
      compileFrag_bprod_mul_partial_invariant frag_f vAccIn vFOut
          vFOut (Nat.le_refl _) (URMState.runFor _ sPrep T0) ∧
      (∀ q : Fin (compileFrag_bprod frag_f).numRegs,
        q.val ≠ 1 → q.val ≠ k + 8 → q.val ≠ k + 9 →
        (URMState.runFor _ sPrep T0).regs q = sPrep.regs q) ∧
      (∀ k' < T0, ...)
```

Each of `compileFrag_bprod_mul_partial_step`,
`compileFrag_bprod_mul_partial_aux`, and
`compileFrag_bprod_mul_partial` carries an additional
preservation conjunct in the same shape: the URM steps of the
inner-mul block touch only `V_acc` (= 1), `V_factor` (= k+8),
and `V_mul_tmp` (= k+9) — three registers, not four
(`V_acc_clone` = k+7 is read-only inside the inner loop, since
`preservingTransfer` preserves its source). The conjunct
states preservation outside those three indices.

Inputs: `compileFrag_bprod_mul_partial_base` (bprod.1.c.1),
`compileFrag_bprod_mul_partial_step` (bprod.1.c.2).

Outputs: outer-iteration outer loop (over `j ∈ [0, vFOut]`),
its `_partial` specialisation at `j = vFOut`, and the
preservation conjunct enumerated above. Mirrors bsum.5's
`compileFrag_bsum_partial_aux` / `compileFrag_bsum_partial`.

Estimated LOC: 350-450.

Notes: induction on `j : ℕ` with `∀ j ≤ vFOut` strengthening.
Base case is `compileFrag_bprod_mul_partial_base` at `j = 0`
(takes 0 URM steps); step case is
`compileFrag_bprod_mul_partial_step` for `j.val + 1`. The
strict PC bound `< bprod_mul_resetPC frag_f` is the tight
bound for the inner-mul loop in isolation; the consumer
(bprod.1.c.4) strengthens it to `< bprod_incIPC frag_f` by
composing the exit `jumpZR` and the reset `assignR` steps,
both of which sit at PCs `< bprod_incIPC`.

### Sub-task 11e.6.a.iii-bprod.1.c.4 — accUpdate assembly

Signatures:

```lean
private theorem compileFrag_bprod_accUpdate_correct
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (vAccIn vFOut : ℕ)
    (sPre : URMState (compileFrag_bprod frag_f).toURMProgram)
    (h_pc : sPre.pc = bprod_trBase frag_f)
    (h_acc : sPre.regs ⟨1, by ...⟩ = vAccIn)
    (h_acc_clone_zero : sPre.regs ⟨k + 7, by ...⟩ = 0)
    (h_fOut : sPre.regs ⟨(k + 10) + frag_f.outputReg.val, _⟩
      = vFOut)
    (h_factor_zero : sPre.regs ⟨k + 8, by ...⟩ = 0)
    (h_mulTmp_zero : sPre.regs ⟨k + 9, by ...⟩ = 0) :
    let totalSteps : ℕ :=
      (4 * vAccIn + 1) + (4 * vFOut + 1)
        + vFOut * (9 * vAccIn + 5) + 1 + 1
    let s' := URMState.runFor _ sPre totalSteps
    s'.pc = bprod_incIPC frag_f ∧
    s'.regs ⟨1, by ...⟩ = vAccIn * vFOut ∧
    s'.regs ⟨k + 7, by ...⟩ = 0 ∧
    s'.regs ⟨k + 8, by ...⟩ = 0 ∧
    s'.regs ⟨(k + 10) + frag_f.outputReg.val, _⟩ = 0 ∧
    s'.regs ⟨k + 9, by ...⟩ = 0 ∧
    (∀ r : Fin _,
        r.val ≠ 1 →
        r.val ≠ k + 7 →
        r.val ≠ k + 8 →
        r.val ≠ k + 9 →
        r.val ≠ (k + 10) + frag_f.outputReg.val →
        s'.regs r = sPre.regs r)

private theorem compileFrag_bprod_accUpdate_pc_strict_bound : ...
```

The `+ 1 + 1` accounts for the exit jumpZR (taken to
`bprod_mul_resetPC` since `V_factor = 0` at end of inner
loop) and the `assignR V_acc_clone 0` reset step. The final
PC `bprod_incIPC` is `bprod_mul_resetPC + 1` — i.e., the
PC after the reset, ready for `incR vI`.

Inputs: `compileFrag_bprod_accUpdate_prep_correct`
(bprod.1.c.0), `compileFrag_bprod_mul_partial` (bprod.1.c.3),
plus a single `URMState.step_of_getElem?_jumpZ` step for the
exit and a single `URMState.step_of_getElem?_assign` step for
the reset.

Outputs: accUpdate-level correctness + strict bound. The
`vAccIn * vFOut` clause encodes the multiplicative semantics
(the entire purpose of the R^XY_Z block).

Estimated LOC: 400-500.

Notes: the slack-free closed-form for `totalSteps` is
`9 * vAccIn * vFOut + 9 * vFOut + 4 * vAccIn + 4` after
algebraic simplification. The implementer should leave the
fully-expanded form in the lemma signature; downstream
sub-tasks (bprod.3.phase_i3, bprod.4) substitute via
`Nat.mul_add` / `Nat.add_mul` / `Nat.mul_comm` as needed.

The preservation conjunct in the conclusion above lists five
register exclusions (`V_acc`, `V_acc_clone`, `V_factor`,
`V_mul_tmp`, and f-output). Its proof composes two
preservation facts via `URMState.runFor_add`:
the prep-phase preservation conjunct (from bprod.1.c.0's
correctness lemma, which excludes `V_acc`, `V_acc_clone`,
`V_factor`, and f-output) with the inner-mul-loop
preservation conjunct (from bprod.1.c.3's
`compileFrag_bprod_mul_partial`, which excludes `V_acc`,
`V_factor`, and `V_mul_tmp`). The union of exclusions covers
all five registers listed in the assembly conjunct; the
intersection (`V_acc`) is the only register written by both
phases, so the composition is straightforward.

### Sub-task 11e.6.a.iii-bprod.1.d — f-body embedding

Signature:

```lean
private theorem ProgramEmbedsFragment_compileFrag_bprod_fBody
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) :
    ProgramEmbedsFragment
      (compileFrag_bprod frag_f).toURMProgram
      frag_f
      (k + 10)
      (16 + frag_f.numRegs + 9 * (k + 1))
      (frag_f.instrs.size - 1)
```

The constants are: `fBase = k + 10` (the new bprod offset, vs
bsum's `k + 7`), `bodyPCBase = 16 + frag_f.numRegs + 9 * (k + 1)`
(vs bsum's `15 + frag_f.numRegs + 9 * (k + 1)`),
embedded-program length `frag_f.instrs.size - 1` (the trailing
`-1` matches the `.pop`-emitted body pattern; Pattern 14).

Inputs: `ProgramEmbedsFragment` (`Embedding.lean`), the
`compileFrag_bprod` definition (`Compiler.lean` lines
1190-1440), the indexing lemmas from `URMInstrRaw.toBoundedArray`
(`Compiler.lean`).

Outputs: f-body embedding lemma. Direct analogue of
`ProgramEmbedsFragment_compileFrag_bsum_fBody` (`BSum.lean`,
landed bsum.1.d).

Estimated LOC: 400-500.

Notes: the embedding bounds proof relies on the disjoint
register-block analysis recapped above (k + 10 outer
scaffolding indices vs `frag_f.numRegs` inner indices). The
PC-offset unfolding follows the recipe in bsum.1.d: unfold
`compileFrag_bprod`, expose the seven-segment raw-list
decomposition (`prelude ++ loopTop ++ zeroSweep ++ prologue
++ fBody ++ accUpdate ++ epilogue`), and split the index
access into the fifth (fBody) segment. The bprod prelude is
14 instructions (vs bsum's 13) due to the extra `incR vAcc`
at PC 13.

### Sub-task 11e.6.a.iii-bprod.2 — partial invariant and base case

Signatures:

```lean
private structure compileFrag_bprod_partial_invariant
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : ℕ) (hi : i ≤ v 0)
    (s : URMState (compileFrag_bprod frag_f).toURMProgram)
    : Prop where
  hi_le : i ≤ v 0 := hi
  pc_eq : s.pc = bprod_topPC
  zReg_zero : s.regs ⟨0, _⟩ = 0
  outer_inputs : ∀ (j : Fin (k + 1)),
    s.regs ⟨2 + j.val, by ...⟩ = v j
  vX_eq : s.regs ⟨k + 3, by ...⟩ = v 0 - i
  vI_eq : s.regs ⟨k + 4, by ...⟩ = i
  tmp1_zero : s.regs ⟨k + 5, by ...⟩ = 0
  tmp2_zero : s.regs ⟨k + 6, by ...⟩ = 0
  accClone_zero : s.regs ⟨k + 7, by ...⟩ = 0
  factor_zero : s.regs ⟨k + 8, by ...⟩ = 0
  mulTmp_zero : s.regs ⟨k + 9, by ...⟩ = 0
  acc_eq : s.regs ⟨1, by ...⟩
    = natBProd i (fun j =>
        f.interp (Fin.cons j.val (Fin.tail v)))

private theorem compileFrag_bprod_partial_base
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ) :
    let outer := (compileFrag_bprod (compileERFrag f)).toURMProgram
    let s_init := URMState.init outer v
    compileFrag_bprod_partial_invariant (compileERFrag f) f v 0
      (Nat.zero_le _) (URMState.runFor outer s_init
                         (7 + 9 * (v 0)))
```

The invariant carries 12 clauses (vs bsum's 9): three
additional zero-state clauses for the bprod-specific scratch
registers `V_acc_clone`, `V_factor`, `V_mul_tmp`. The
`fBody_zero` clause is *not* carried (per bsum's session-6
refactor: phase_i2 only establishes f-output, not the full
body; the next iteration's phase_i0 zero-sweep re-establishes
the full block).

The base-case run-time is the prelude's full length:
`7 + 9 * (v 0)` URM steps. This decomposes as:

- 4 `assignR` steps (V_z, V_acc, V_x, V_i all to 0).
- `preservingTransfer 4 vBoundIn vX tmp2`: takes
  `9 * (v 0) + 2` steps to copy `v 0` from `V_bound_in` into
  `V_x`.
- 1 `incR vAcc` step (initialises accumulator to 1).

Total: `4 + (9 * (v 0) + 2) + 1 = 7 + 9 * (v 0)`.

Inputs: `URMState.init_regs_zero_outside_inputs`
(`Atoms.lean`), `URMState.runFor_zero` /
`URMState.runFor_succ` (`Embedding.lean`),
`preservingTransfer_correct` (`Loops.lean`).

Outputs: structure and base lemma.

Estimated LOC: 500-600 (about 100 LOC more than bsum.2 due
to the three extra scratch-register clauses and the extra
`incR vAcc` discharge).

Notes: at `i = 0`, `natBProd 0 _ = 1`, so the `acc_eq`
clause reduces to `s.regs ⟨1, _⟩ = 1`, which holds after
the prelude executes (`assignR vAcc 0` followed by
`incR vAcc`). Note this is the key difference from bsum.2's
base case (`natBSum 0 _ = 0`, ending at `acc = 0`). Use
field-projection over destructure (Pattern 10).

### Sub-task 11e.6.a.iii-bprod.3.phase_i0 — zero-sweep preservation

Signature:

```lean
private structure compileFrag_bprod_phase_i0_post
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (s : URMState (compileFrag_bprod frag_f).toURMProgram)
    : Prop where
  pc_eq : s.pc = bprod_prologueBase frag_f
  -- All carry-over clauses from partial_invariant @ i.val:
  -- zReg_zero, outer_inputs, vX_eq (decremented), vI_eq,
  -- tmp1_zero, tmp2_zero, accClone_zero, factor_zero,
  -- mulTmp_zero, acc_eq.
  fBody_zero : ∀ r : Fin frag_f.numRegs,
    s.regs ⟨(k + 10) + r.val, by ...⟩ = 0

private theorem compileFrag_bprod_partial_phase_i0
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (sPre : URMState
      (compileFrag_bprod (compileERFrag f)).toURMProgram)
    (h_inv : compileFrag_bprod_partial_invariant
              (compileERFrag f) f v i.val i.isLt.le sPre) :
    let T0 : ℕ := 2 + (compileERFrag f).numRegs
    compileFrag_bprod_phase_i0_post (compileERFrag f) f v i
      (URMState.runFor _ sPre T0) ∧
    (∀ k' < T0,
      (URMState.runFor _ sPre k').pc
        < bprod_prologueBase (compileERFrag f))
```

The 2 steps before the zero-sweep are the loop-top
`jumpZR vX exitPC bodyStartPC` (which jumps to `bodyStartPC =
15` when `vX > 0`, i.e., when `i.val < v 0`) and the `decR vX`
at `bodyStartPC`. Inlined-conjunction convention applies
(T0 is closed-form; Pattern 16).

Inputs: `compileFrag_bprod_zeroSweep_correct` (bprod.1.a),
`URMState.step_of_getElem?_jumpZ` and
`URMState.step_of_getElem?_dec` (`Embedding.lean`).

Outputs: phase-i.0 post structure and preservation lemma.

Estimated LOC: 650-750 (~150 LOC more than bsum.3.phase_i0
due to the three additional zero-state clauses requiring
carry-over from the partial invariant and the `+1` PC offset
throughout).

Notes: the precondition `i.val < v 0` makes `vX > 0` at
`sPre`, so the `jumpZR` takes the non-zero branch to
`bodyStartPC`. Use `Nat.lt_or_ge` + `rcases` (Pattern 2).
A fresh `compileFrag_bprod_zeroSweep_instr_at` segment-peeling
helper is needed (first instance of the segment-peeling
pattern in bprod, modelled on bsum's
`compileFrag_bsum_zeroSweep_instr_at`).

### Sub-task 11e.6.a.iii-bprod.3.phase_i1 — prologue preservation

Signature:

```lean
private structure compileFrag_bprod_phase_i1_post
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (s : URMState (compileFrag_bprod frag_f).toURMProgram)
    : Prop where
  pc_eq : s.pc = bprod_bodyPCBase frag_f
  -- f's input slots now hold (Fin.cons i.val (Fin.tail v)),
  -- f-body otherwise zero, outer scaffolding (incl. all
  -- mul-scratch regs) preserved at zero.
  f_inputs : ∀ (j : Fin (k + 1)),
    s.regs ⟨(k + 10) + (frag_f.inputRegs j).val, by ...⟩
      = Fin.cons i.val (Fin.tail v) j
  f_other_zero : ∀ (r : Fin frag_f.numRegs),
    (∀ j : Fin (k + 1), r ≠ frag_f.inputRegs j) →
    s.regs ⟨(k + 10) + r.val, by ...⟩ = 0
  -- carry-over of zReg_zero, outer_inputs, vX_eq (with
  -- i.val subtracted), vI_eq, tmp{1,2}_zero,
  -- accClone_zero, factor_zero, mulTmp_zero, acc_eq.

private theorem compileFrag_bprod_partial_phase_i1
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (sPre : URMState
      (compileFrag_bprod (compileERFrag f)).toURMProgram)
    (h_i0 : compileFrag_bprod_phase_i0_post (compileERFrag f) f v
              i sPre) :
    let T0 : ℕ := 9 * vPrefixSum (Fin.cons i.val (Fin.tail v))
                    (k + 1) + 2 * (k + 1)
    compileFrag_bprod_phase_i1_post (compileERFrag f) f v i
      (URMState.runFor _ sPre T0) ∧
    (∀ k' < T0,
      (URMState.runFor _ sPre k').pc
        < bprod_bodyPCBase (compileERFrag f))
```

Inputs: `compileFrag_bprod_prologue_correct` (bprod.1.b),
applied with `srcs` set to the prologue-source map (slot 0 →
`V_i`, slot `s > 0` → `V_param_{s-1}`), and `dsts` set to f's
reindexed input slots.

Outputs: phase-i.1 post structure and preservation lemma.

Estimated LOC: 600-700.

Notes: `set_option maxHeartbeats 4000000 in` may be needed
on the main preservation lemma due to the conditional shape
of `bsum_prologueSrc` (Pattern: see bsum.3.phase_i1's note on
the prologue-source map's heartbeats inflation). A fresh
segment-peeling helper `compileFrag_bprod_prologueBlock_instr_at`
is needed (second instance of the segment-peeling pattern in
bprod). Inlined-conjunction convention applies.

### Sub-task 11e.6.a.iii-bprod.3.phase_i2 — f-body preservation

Signature:

```lean
private structure compileFrag_bprod_phase_i2_post
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (s : URMState (compileFrag_bprod frag_f).toURMProgram)
    : Prop where
  pc_eq : s.pc = bprod_trBase frag_f
  f_output : s.regs ⟨(k + 10) + frag_f.outputReg.val, by ...⟩
    = f.interp (Fin.cons i.val (Fin.tail v))
  -- carry-over: outer scaffolding (zReg, outer_inputs, vX,
  -- vI, tmp1, tmp2, accClone, factor, mulTmp, acc)
  -- preserved by the f-body embedding.

private theorem compileFrag_bprod_partial_phase_i2
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (ih_f : ∀ (v' : Fin (k + 1) → ℕ),
      ∃ T0 : ℕ, T0 ≤ compileER_runtime f v' ∧ ...)
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (sPre : URMState
      (compileFrag_bprod (compileERFrag f)).toURMProgram)
    (h_i1 : compileFrag_bprod_phase_i1_post (compileERFrag f) f v
              i sPre) :
    ∃ T0 : ℕ,
      T0 ≤ compileER_runtime f (Fin.cons i.val (Fin.tail v)) ∧
      compileFrag_bprod_phase_i2_post (compileERFrag f) f v i
        (URMState.runFor _ sPre T0) ∧
      (∀ k' < T0,
        (URMState.runFor _ sPre k').pc
          < bprod_trBase (compileERFrag f))
```

Inputs: `ProgramEmbedsFragment_compileFrag_bprod_fBody`
(bprod.1.d), `stateEmbedsFrag_runFor` and
`stateEmbedsFrag_runFor_outside_preserved` (`Embedding.lean`),
and the IH `ih_f` instantiated at
`Fin.cons i.val (Fin.tail v)`.

Outputs: phase-i.2 post structure and preservation lemma.
Direct analogue of `compileFrag_bsum_partial_phase_i2`
(`BSum.lean`).

Estimated LOC: 550-650.

Notes: this is the only sub-task that consumes `ih_f`.
Carry-over of outer scaffolding (including all three
mul-scratch registers) follows from
`stateEmbedsFrag_step_outside_preserved`. The `acc_eq`
carry-over is crucial: f's body must not touch any of the
outer scaffolding registers, which holds because all such
registers have indices `< fBase = k + 10`, outside f's
reindexed block.

Use `URMState.init` inline (not let-bound) before pattern-
matching on its regs projection (Pattern 17: let-bound
`URMState.init` blocks regs-projection reduction).

### Sub-task 11e.6.a.iii-bprod.3.phase_i3 — accUpdate + incR + goto

Signature:

```lean
private theorem compileFrag_bprod_partial_phase_i3
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (sPre : URMState
      (compileFrag_bprod (compileERFrag f)).toURMProgram)
    (h_i2 : compileFrag_bprod_phase_i2_post (compileERFrag f) f v
              i sPre) :
    let A_i := natBProd i.val
      (fun j => f.interp (Fin.cons j.val (Fin.tail v)))
    let B_i := f.interp (Fin.cons i.val (Fin.tail v))
    let T0 : ℕ :=
      ((4 * A_i + 1) + (4 * B_i + 1)
        + B_i * (9 * A_i + 5) + 1 + 1) + 2
    compileFrag_bprod_partial_invariant (compileERFrag f) f v
        (i.val + 1) (Nat.succ_le_of_lt i.isLt)
      (URMState.runFor _ sPre T0) ∧
    (∀ k' < T0,
      (URMState.runFor _ sPre k').pc
        < (compileFrag_bprod (compileERFrag f)).instrs.size - 1)
```

The `+ 2` accounts for `incR vI` and `goto topPC`. The
accUpdate's step count is the full closed form from
bprod.1.c.4; T0 is closed-form (Pattern 16).

Inputs: `compileFrag_bprod_accUpdate_correct` (bprod.1.c.4),
`URMState.step_of_getElem?_inc` (for `incR vI`),
`URMState.step_of_getElem?_jump` (the `goto` macro expands
to a `jumpZR ⟨0, _⟩` against the zero register, taken
because `zReg_zero` holds).

Outputs: phase-i.3 preservation lemma. No intermediate post
structure (the conclusion is directly `partial_invariant @
(i.val + 1)`).

Note on the strict PC bound's upper limit: the accUpdate
block executes at PCs in `[trBase, gotoTopPC]`, all of which
are `> bprod_topPC = 14`. The final `goto topPC` step returns
PC to `topPC`. The strict-PC-bound conclusion therefore
cannot use `bprod_topPC` (intermediate PCs exceed it); it
must use `(compileFrag_bprod (compileERFrag f)).instrs.size - 1`,
the exit PC, which is the maximal in-program PC.

Estimated LOC: 700-850. This is the largest single phase
lemma in the bprod chain because the accumulator update
re-establishes the twelve invariant clauses at `i.val + 1`.
The per-clause split is `2 + 5 + 5 = 12`: two via the
epilogue's two URM instructions, five via the accUpdate's
output state, and five via carry-over from phase_i2:

- `pc_eq`: returns to `bprod_topPC` via the `goto`
  (epilogue).
- `vI_eq`: incremented from `i.val` to `i.val + 1` by the
  `incR vI` epilogue step.
- `acc_eq`: re-established by the accUpdate via the
  multiplicative recurrence `natBProd (i.val + 1) g =
  natBProd i.val g * g i.val`. The new accumulator value is
  `A_i * B_i = natBProd i.val * f.interp (Fin.cons i.val
  (Fin.tail v))`. Use `natBProd_rec` (`LawvereERPrimrec.lean`
  line 21) or the unfolding `natBProd (i + 1) g = natBProd i
  g * g i`.
- `accClone_zero`, `factor_zero`, `mulTmp_zero`,
  `f-output zero` (a corollary of `factor_zero` and the
  prep destructive copy): all re-established by the
  accUpdate's output state. (`f-output zero` is itself not
  an invariant clause but is needed for the next iteration's
  phase_i0 zero-sweep to behave; it is supplied by the
  accUpdate post-state.)
- `vX_eq`, `zReg_zero`, `outer_inputs`, `tmp1_zero`,
  `tmp2_zero`: carry-over from phase_i2 (the accUpdate
  touches none of these registers; the preservation conjunct
  from bprod.1.c.4 covers them). Note `hi_le` is a Prop
  parameter carried via the structure's default value, not a
  state-bearing clause; it does not count toward the 12-
  clause split.

The accUpdate's output state has `V_acc_clone = 0`,
`V_factor = 0`, `V_mul_tmp = 0`, and the f-output register at
0 — verified in bprod.1.c.4's conclusion. These four
zero-state facts plus `acc_eq` constitute the five "via
accUpdate" clauses listed above.

A fresh segment-peeling helper
`compileFrag_bprod_accUpdateBlock_instr_at` is needed (third
instance of the segment-peeling pattern in bprod, after the
zero-sweep and prologue instance), covering all 21
instructions in the accUpdate block plus the two-instruction
epilogue prefix.

### Sub-task 11e.6.a.iii-bprod.4 — induction glue (i to i + 1)

Signature:

```lean
private theorem compileFrag_bprod_partial_step
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (ih_f : ∀ (v' : Fin (k + 1) → ℕ),
      ∃ T0 : ℕ, T0 ≤ compileER_runtime f v' ∧ ...)
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (sPre : URMState
      (compileFrag_bprod (compileERFrag f)).toURMProgram)
    (h_inv : compileFrag_bprod_partial_invariant
              (compileERFrag f) f v i.val i.isLt.le sPre) :
    let A_i := natBProd i.val
      (fun j => f.interp (Fin.cons j.val (Fin.tail v)))
    let B_i := f.interp (Fin.cons i.val (Fin.tail v))
    ∃ T0 : ℕ,
      T0 ≤ (2 + (compileERFrag f).numRegs)
            + (9 * vPrefixSum (Fin.cons i.val (Fin.tail v))
                  (k + 1) + 2 * (k + 1))
            + compileER_runtime f (Fin.cons i.val (Fin.tail v))
            + ((4 * A_i + 1) + (4 * B_i + 1)
                + B_i * (9 * A_i + 5) + 1 + 1 + 2) ∧
      compileFrag_bprod_partial_invariant (compileERFrag f) f v
          (i.val + 1) (Nat.succ_le_of_lt i.isLt)
        (URMState.runFor _ sPre T0) ∧
      (∀ k' < T0,
        (URMState.runFor _ sPre k').pc
          < (compileFrag_bprod (compileERFrag f)).instrs.size - 1)
```

Inputs: the four phase preservation lemmas (bprod.3.phase_i0
through bprod.3.phase_i3), plus their strict-bound
counterparts. Mirrors `compileFrag_bsum_partial_step`
(`BSum.lean` session-6 commit `8c1ba576`).

Outputs: i-step glue lemma.

Estimated LOC: 300-400.

Notes: PC-window case split over four intervals
(phase_i0 = `[topPC, prologueBase)`,
phase_i1 = `[prologueBase, bodyPCBase)`,
phase_i2 = `[bodyPCBase, trBase)`,
phase_i3 = `[trBase, topPC)` via the goto's return).
Each phase's tight in-block strict PC bound is weakened to
the step-level bound `< bprod_exitPC` (equivalently
`< instrs.size - 1`) via transitivity with the phase's
intra-block invariant. The conclusion is existential because
phase_i2's T0 is from `ih_f`'s witness.

### Sub-task 11e.6.a.iii-bprod.5 — outer iteration (i = 0 to v 0)

Signatures:

```lean
private theorem compileFrag_bprod_partial_aux
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (ih_f : ...)
    (v : Fin (k + 1) → ℕ)
    (i : ℕ) (hi : i ≤ v 0) :
    let perIter : ℕ → ℕ := fun j =>
      let A_j : ℕ :=
        natBProd j
          (fun i' => f.interp (Fin.cons i' (Fin.tail v)))
      let B_j : ℕ := f.interp (Fin.cons j (Fin.tail v))
      (2 + (compileERFrag f).numRegs)
        + (9 * vPrefixSum (Fin.cons j (Fin.tail v)) (k + 1)
            + 2 * (k + 1))
        + compileER_runtime f (Fin.cons j (Fin.tail v))
        + ((4 * A_j + 1) + (4 * B_j + 1)
            + B_j * (9 * A_j + 5) + 1 + 1 + 2)
    ∃ T0 : ℕ,
      T0 ≤ (7 + 9 * (v 0))
            + ((List.range i).map perIter).foldl (· + ·) 0 ∧
      compileFrag_bprod_partial_invariant (compileERFrag f) f v
          i hi (URMState.runFor _ s_init T0) ∧
      (∀ k' < T0,
        (URMState.runFor _ s_init k').pc
          < (compileFrag_bprod (compileERFrag f)).instrs.size - 1)

private theorem compileFrag_bprod_partial
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (ih_f : ...)
    (v : Fin (k + 1) → ℕ) :
    ∃ T0 : ℕ,
      T0 ≤ (7 + 9 * (v 0))
            + ((List.range (v 0)).map perIter).foldl (· + ·) 0 ∧
      compileFrag_bprod_partial_invariant (compileERFrag f) f v
          (v 0) (Nat.le_refl _) (URMState.runFor _ s_init T0) ∧
      (∀ k' < T0, ...)
```

`perIter` is the `let`-bound function shown in the
`_aux` signature; its body is the per-iter step-count bound
established in bprod.4, with `A_j = natBProd j (...)` and
`B_j = f.interp (Fin.cons j (Fin.tail v))` inlined.

Inputs: `compileFrag_bprod_partial_base` (bprod.2),
`compileFrag_bprod_partial_step` (bprod.4). Mirrors
`compileFrag_bsum_partial` and its `_aux` helper (`BSum.lean`
session-6 commit `b2c6d3c4`).

Outputs: outer-iteration outer loop. Final state is
`partial_invariant @ (v 0)`, i.e., the loop has executed
`v 0` iterations; `V_x = v 0 - v 0 = 0`; `V_i = v 0`;
`V_acc = natBProd (v 0) (...)`.

Estimated LOC: 450-550.

Notes: induction on `i ≤ v 0`. Use `Nat.lt_or_ge` + `rcases`
(Pattern 2). Also lands
`compileFrag_bprod_prelude_pc_strict_bound`, a thin helper for
the prelude's `7 + 9 * (v 0)` step-ladder strict PC bound
(second copy of the prelude step ladder in the bprod chain,
after `compileFrag_bprod_partial_base`; followup item to
extract). Its signature:

```lean
private theorem compileFrag_bprod_prelude_pc_strict_bound
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (k' : ℕ) (hk' : k' < 7 + 9 * (v 0)) :
    let outer :=
      (compileFrag_bprod (compileERFrag f)).toURMProgram
    let s_init := URMState.init outer v
    (URMState.runFor outer s_init k').pc
      < (compileFrag_bprod (compileERFrag f)).instrs.size - 1
```

### Sub-task 11e.6.a.iii-bprod.6 — final assembly

Signature: `compileER_pre_stop_correct_bprod` (the top-level
statement given above).

Inputs: `compileFrag_bprod_partial` (bprod.5). After the
outer loop's last iteration, the PC is at the loop top
`topPC = 14`; the final `jumpZR vX exitPC bodyStartPC` takes
the *zero* branch (since `V_x = v 0 - v 0 = 0`) to
`exitPC = bprod_exitPC`, which is the trailing `stopR` and is
the last instruction (`= instrs.size - 1`). The final `T0`
adds 1 to bprod.5's output for the `jumpZR` step.

Outputs: top-level pre-stop lemma. Mirrors
`compileER_pre_stop_correct_bsum` (`BSum.lean` session-6
commit `f10bdb02`).

Estimated LOC: 350-450.

**Critical risk to flag at start of bprod.6**: the current
`compileER_runtime (.bprod (k := k) f) v` formula
(`Compiler.lean` lines 1625-1639) provides per-iter slack
`compileER_runtime f ctx_f + 60 + 2 * (k + 1) + 10 * (i +
outerSum) + 5 * f.interp ctx_f + nRegs_f`. The actual per-iter
cost surfaced by bprod.4 is:

```text
(2 + nRegs_f)                              -- phase i.0
+ (9 * outerSum_i + 2 * (k + 1))           -- phase i.1
+ compileER_runtime f ctx_f                -- phase i.2
+ (9 * A_i * B_i + 9 * B_i + 4 * A_i + 4)  -- phase i.3 accUpdate
+ 2                                         -- incR + goto
```

where `outerSum_i = vPrefixSum (Fin.cons i.val (Fin.tail v))
(k + 1) = i + outerSum + (rest)`. Subtracting actual from
runtime: `52 - 9*A_i*B_i - 4*B_i - 4*A_i` is *negative* for
`A_i, B_i > 0`. The runtime's `5 * f.interp ctx_f = 5 * B_i`
term cannot cover the multiplicative `9 * A_i * B_i` term
because `A_i` grows multiplicatively across iterations.

This is a latent specification defect inherited from Task 10's
runtime design (which mirrored bsum's additive structure
without accounting for multiplication's accumulating cost).

**The runtime correction is a prerequisite to bprod.6 and
should land as a separate commit before bprod.6 begins**
(analogous to the bsum.6 session-6 commit `f8e7a28a` that
patched the bsum/bprod per-iter `+ 2 * (k + 1)`). Two
candidate corrections, listed in order of minimality:

1. **Recursive multiplicative term**: change `5 * f.interp
   ctx_f` to a sum that captures the actual cost shape. The
   reviewer-recommended specific form is to rewrite the bprod
   branch of `compileER_runtime` as a `List.range bound`-fold
   whose per-iter cost references the running accumulator at
   `i` directly, mirroring `natBProd`'s `Nat.rec` shape so the
   slack arithmetic in bprod.5's induction step decomposes
   cleanly. Letting `A_i := natBProd i (...)` and
   `B := f.interp ctx_f`, the algebraic content of the
   per-iter expression is
   `9 * B * A_i + 4 * A_i + 9 * B + 8`; embedding it in a
   fold-shape rather than an indexed `+` avoids the
   `Nat.rec`-vs-`List.range`-fold mismatch.
2. **Polynomial outer bound**: replace the per-iter expression
   entirely with a polynomial in `bound` and a global maximum
   of f's output. The cost: the bound becomes much looser
   (potentially super-exponentially loose); breaks the
   per-iter additive structure required for bprod.5's
   induction step.

Candidate 1 is the minimal correction and the recommended
approach. The implementer's checklist:

1. Author the runtime correction in `Compiler.lean`. Keep it
   compatible with bprod.5's `_aux` `perIter` shape (the fold
   structure must match).
2. Run `lake build` and verify the change compiles cleanly
   with no axiom regressions
   (`mcp__lean-lsp__lean_verify compileER_runtime`).
3. Re-verify `compileER_numRegs_eq_compileERFrag_numRegs`
   still type-checks (it does not depend on the runtime,
   only on `numRegs`).
4. Commit the runtime correction as a `fix(ertok):` commit
   on its own, separately from bprod.6's `feat(ertok):`
   landing.
5. Proceed with bprod.6's slack arithmetic using the corrected
   runtime; the structural-numRegs identity
   `compileER_numRegs_eq_compileERFrag_numRegs` closes the
   final piece exactly as it did for bsum.6.

Notes on the assembly proof itself: discharge the final
`jumpZR` step via `URMState.step_of_getElem?_jumpZ`
(`Embedding.lean`) with `s.regs vX = 0` (from the
partial-invariant `vX_eq : ... = v 0 - v 0 = 0` clause at
`i = v 0`). The PC immediately becomes
`bprod_exitPC = instrs.size - 1`, satisfying the pre-stop
existential.

## Inductive variable

The outer loop is parameterised by `i : ℕ` with `i ≤ v 0`,
identically to bsum. Bprod's `vX` register holds `v 0 - i`;
`vI` register holds `i`. The partial-invariant carries `i`
as an external parameter. The iteration count `v 0` is read
from outer register `2`.

The inner mul loop is parameterised by `j : ℕ` with
`j ≤ vFOut`, where `vFOut = f.interp ctx_f_i` is the f-output
for the current outer iteration. Bprod's `V_factor` register
holds `vFOut - j`; bprod's `V_acc` holds `vAccIn * j` where
`vAccIn = natBProd i (...)` is the accumulator at outer
iteration entry.

## Cross-references and IH form

The IH on f matches the existential pre-stop form of
`compileER_pre_stop_correct_*`. This IH is consumed in
bprod.3.phase_i2 only.

The bprod chain produces a single output existential of the
standard shape; no inner-mul-loop IH propagates out of the
chain (the inner mul loop is fully discharged within
bprod.1.c.*). The bridge `compileER_pre_stop_to_runFor`
(`Embedding.lean`) discharges Task 11g (the bprod runFor
wrapper) directly from `compileER_pre_stop_correct_bprod`.

The bprod prologue source map is identical to bsum's
`bsum_prologueSrc` (`Compiler.lean` line 817); the bprod
compiler imports it directly. The induced `f`-input vector
matches `Fin.cons i.val (Fin.tail v)`, identical to bsum's
threading.

## Followup items

Items observed during sub-division that belong on the
post-T2 followup branch (task #654):

1. Extract a shared `compileFrag_bprod_rawList_scaffold`
   helper (or `compileFrag_bprod_segment_at` parameterised by
   segment offset and extractor) to deduplicate ~70% overlap
   across the five segment-peeling helpers in the bprod
   chain: `compileFrag_bprod_accUpdate_prep_instr_at`
   (bprod.1.c.0), `compileFrag_bprod_accUpdate_innerBody_instr_at`
   (bprod.1.c.2), `compileFrag_bprod_zeroSweep_instr_at`
   (phase_i0), `compileFrag_bprod_prologueBlock_instr_at`
   (phase_i1), and `compileFrag_bprod_accUpdateBlock_instr_at`
   (phase_i3). Bsum's followup item 15 records the analogous
   bsum scaffold; consider extracting both into a shared
   `LawvereERKSim/SegmentPeeling.lean` (or extending
   `Loops.lean`) under constructor-agnostic names.
2. Phase the bsum-shared zero-sweep helper extraction in two
   steps: first extract a constructor-agnostic alias in
   `Loops.lean` (or a new shared submodule); next, leave
   `bsum_zeroSweep` in `Compiler.lean` as a re-export so
   existing bsum consumers keep building; finally, migrate
   consumers to the new name incrementally. The current
   short-term choice — bprod's compiler imports
   `bsum_zeroSweep` from `Compiler.lean` directly — leaves
   the misleading `bsum_` prefix on a helper that both
   constructors consume; the phased migration corrects this
   without breaking the bsum chain.
3. Extract a shared `bprod_mul_partial` family or a
   `multiplicative_loop_correct` template that captures the
   inner-mul loop's bsum-shaped structure abstractly, with
   `vAccIn` / `vFOut` as parameters. The current bprod.1.c.0
   through 1.c.4 chain is structurally analogous to bsum's
   pre-stop chain (jumpZR + decR + preservingTransfer + goto
   over a counter `j`); the abstraction would reduce
   duplication and clarify the multiplicative-as-iterated-
   additive recurrence.
4. Reconcile bprod's `incR vAcc` at PC 13 with the
   `compileER_runtime` outer constant `40 + 10 * bound` (vs
   bsum's `30 + 10 * bound`). The actual prelude delta over
   bsum is 1 step (`incR vAcc`); the chosen `+ 10` is
   loose-by-design (covering 1 prelude step plus 9 slots of
   per-bound headroom that may or may not be needed). Verify
   after bprod.6 whether the headroom is necessary or can be
   trimmed; document the final choice in the
   `compileER_runtime` docstring.
5. Audit the `## Main definitions` / `## Main statements`
   sections of the new `BProd.lean` docstring against the
   actually-public surface (bsum followup item 12 records
   the analogous bsum audit).
6. Add `/-! ### ... -/` section markers to `BProd.lean`
   around its logical phases (PC-bound infra, three
   sub-block helpers, f-body embedding, partial-invariant,
   phase preservations, outer iteration, final assembly)
   for navigability (bsum followup item 5, generalised).
7. Re-evaluate `private` promotions across submodules once
   Task 11h (top-level structural induction) and Task 12
   (axiom audit + manual lint) land. Two known anticipated
   public consumers: bprod.0's `bprod_exitPC` (consumed by
   bprod.6's final-step instruction lookup) and
   `compileFrag_bprod_size` (consumed by Compiler.lean's
   `compileER_numRegs_eq_compileERFrag_numRegs`'s bprod
   case). Both already exist in bsum's pattern.
8. After bprod.1.c.4 lands, consider extracting the
   `(4 * A + 1) + (4 * B + 1) + B * (9 * A + 5) + 1 + 1`
   closed-form arithmetic into a named lemma
   `bprod_accUpdate_steps_eq` for reuse in bprod.3.phase_i3
   and bprod.4.
9. **Runtime fix audit**: after bprod.6's runtime correction
   lands (per the critical risk flagged above), audit the
   bsum and comp runtime formulas with the same lens. The
   bsum chain's `+ 50` → `+ 50 + 2 * (k + 1)` fix may have
   masked a similar latent issue; a holistic review during
   Task 12's axiom audit is recommended.
10. Audit bprod's `fBody_zero` placement after both bprod
    and the prior bsum chains have landed (paralleling the
    bsum followup item 3). The current design drops
    `fBody_zero` from the top-of-loop invariant per Pattern
    18 (the next iteration's phase_i0 re-establishes it);
    confirm this asymmetry against bsum's final landed
    pattern and decide whether a normalised placement is
    worth a refactor.

## References

- Handoff:
  `docs/superpowers/plans/2026-05-18-step-t2-t11-handoff.md`.
- Plan:
  `docs/superpowers/plans/2026-05-17-step-t2-er-to-urm-compiler.md`.
- Spec:
  `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`
  (bprod semantics §5.1.1).
- bsum sub-division (template):
  `docs/superpowers/plans/2026-05-19-step-t2-t11-bsum-prestop-subdivision.md`.
- Compiler: `GebLean/LawvereERKSim/Compiler.lean`
  (`compileFrag_bprod` lines 1190-1440;
  `bsum_prologueSrc` line 817; `bsum_prologueBlock` line 832;
  `bsum_zeroSweep` line 867;
  `compileER_runtime` lines 1594-1639 (full definition;
  bprod branch at lines 1625-1639);
  `compileER_numRegs_eq_compileERFrag_numRegs` line 1542).
- BSum model: `GebLean/LawvereERKSim/BSum.lean`
  (full bsum pre-stop chain landed in sessions 5-6, 5036
  lines).
- Comp model: `GebLean/LawvereERKSim/Comp.lean`
  (`compileFrag_comp_subBlock_inputCopies_correct` line
  1269; the f-body embedding pattern in
  `ProgramEmbedsFragment_compileFrag_comp_fBody` lines
  105-307).
- Embedding: `GebLean/LawvereERKSim/Embedding.lean`
  (`ProgramEmbedsFragment`, `StateEmbedsFrag`,
  `stateEmbedsFrag_runFor_outside_preserved`,
  `compileER_pre_stop_to_runFor`).
- Loops: `GebLean/LawvereERKSim/Loops.lean`
  (`transferLoop_correct`, `preservingTransfer_correct`,
  bound counterparts).
- Atoms: `GebLean/LawvereERKSim/Atoms.lean`
  (`URMState.init_regs_inputRegs`,
  `URMState.init_regs_zero_outside_inputs`).
- ER semantics: `GebLean/LawvereER.lean`
  (`ERMor1.interp_bprod` lines 139-145;
  `natBProd` line 67).
- natBProd recursion: `GebLean/LawvereERPrimrec.lean`
  (`natBProd_rec` line 21).
- Tourlakis 2018 §0.1.0.42 (p. 18) URM-computability;
  Tourlakis 2018 pp. 19-21 per-template constructions
  (R^XY_Z multiplication at p. 19).
