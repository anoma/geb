# Step T2 Task 11e.6.a.iii-bsum — pre-stop sub-division

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Summary

This document sub-divides Task 11e.6.a.iii-bsum, the bsum
pre-stop correctness theorem
`compileER_pre_stop_correct_bsum`, into nine implementer-sized
sub-tasks. The target lemma states that for every
`f : ERMor1 (k + 1)` and `v : Fin (k + 1) → ℕ`, there exists
`T0 ≤ compileER_runtime (.bsum f) v` such that at step `T0` the
URM program `compileER (.bsum f)` has its PC at
`(compileER (.bsum f)).instrs.size - 1`, its output register
contains `(.bsum f).interp v`, and on every earlier step the PC
is strictly below `instrs.size - 1`. The proof mirrors the
landed `compileER_pre_stop_correct_comp` (Comp.lean lines
4915-5400) but threads an outer induction over the bsum
iteration index instead of the comp sub-block index. New work
lands in a new `GebLean/LawvereERKSim/BSum.lean` submodule
imported between `Atoms` and the `LawvereERKSim` index. The
chain reuses without modification: the program-embedding
framework (`Embedding.lean`), the loop dischargers
(`Loops.lean`), and the f-body embedding pattern from
`Comp.lean`'s `ProgramEmbedsFragment_compileFrag_comp_fBody`
(lines 105-307, adapted to the bsum layout). Estimated total
LOC: 3000-3600.

## Top-level statement

The non-negotiable signature for the assembly lemma, modelled
on `compileER_pre_stop_correct_comp` (Comp.lean lines
4915-4960):

```lean
private theorem compileER_pre_stop_correct_bsum
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
      T0 ≤ compileER_runtime (.bsum f : ERMor1 (k + 1)) v ∧
      (URMState.runFor (compileER (.bsum f : ERMor1 (k + 1)))
            (URMState.init
              (compileER (.bsum f : ERMor1 (k + 1))) v) T0).pc
          = (compileER (.bsum f : ERMor1 (k + 1))).instrs.size - 1 ∧
      (URMState.runFor (compileER (.bsum f : ERMor1 (k + 1)))
            (URMState.init
              (compileER (.bsum f : ERMor1 (k + 1))) v) T0).regs
          (compileER (.bsum f : ERMor1 (k + 1))).outputReg
        = (.bsum f : ERMor1 (k + 1)).interp v ∧
      (∀ k' < T0,
        (URMState.runFor (compileER (.bsum f : ERMor1 (k + 1)))
            (URMState.init
              (compileER (.bsum f : ERMor1 (k + 1))) v) k').pc
          < (compileER (.bsum f : ERMor1 (k + 1))).instrs.size - 1)
```

The signature copies the four conjuncts of
`compileER_pre_stop_correct_comp` verbatim and substitutes
`.bsum f` for `.comp f gs`. Bsum has a single IH on `f` (no
`gs` family). The IH form is the same existential pre-stop
form, so the bridge `compileER_pre_stop_to_runFor`
(`Embedding.lean` lines 825-870) consumes the bsum pre-stop
conclusion unmodified.

## Register and PC layout recap

Source: `compileFrag_bsum` (Compiler.lean lines 897-1100).
Names below match the `let`-bindings inside that definition.

Register layout (outer arity `k + 1`):

- `0`: `V_z` (reserved zero).
- `1`: `V_acc` = outer `outputReg`. Accumulator.
- `2`: `V_bound_in` = outer input slot `0` (the bound).
- `3..k+2`: `V_param_j` for `j ∈ Fin k` = outer input slots
  `1..k`.
- `k + 3`: `V_x` = destructive clone of `V_bound_in`.
- `k + 4`: `V_i` = iteration index.
- `k + 5`: `tmp1` = scratch for the per-iteration prologue's
  `preservingTransfer`.
- `k + 6`: `tmp2` = scratch for the prelude's clone of
  `V_bound_in` into `V_x`.
- `fBase = k + 7 .. nR - 1`: f's reindexed register block,
  where `nR = fBase + frag_f.numRegs`.

PC layout (absolute offsets, where `a := k + 1` is f's arity):

- `0..3`: prelude — four `assignR` (`V_z`, `V_acc`, `V_x`,
  `V_i` all set to `0`).
- `4..12`: clone of `V_bound_in` into `V_x` via
  `preservingTransfer 4 vBoundIn vX tmp2` (9 instructions).
- `topPC = 13`: `jumpZR vX exitPC bodyStartPC` (loop top).
- `bodyStartPC = 14`: `decR vX`.
- `zeroSweepBase = 15`: `bsum_zeroSweep frag_f fBase` —
  `frag_f.numRegs` `assignR (fBase + r) 0` instructions.
- `prologueBase = 15 + frag_f.numRegs`: per-iteration prologue,
  `a` blocks of `bsum_prologueBlock` (each `preservingTransfer`,
  9 instructions); the slot-0 block copies `V_i` into f's input
  slot 0, the slot-`s` block for `s > 0` copies outer parameter
  `V_param_{s-1}` into f's input slot `s`.
- `bodyPCBase = 15 + frag_f.numRegs + 9 * a`: f's reindexed
  body (`frag_f.instrs.size - 1` instructions; trailing
  `stopR` dropped).
- `trBase = bodyPCBase + fBodyLen`: `transferLoop trBase
  (fBase + frag_f.outputReg.val) vAcc` (4 instructions); adds
  f's output into the accumulator.
- `incIPC = trBase + 4`: `incR vI`.
- `gotoTopPC = trBase + 5`: `goto topPC`.
- `exitPC = trBase + 6`: `stopR`. This is
  `instrs.size - 1`.

Disjoint blocks for register-embedding purposes:

- The "outer scaffolding" block `{V_z, V_acc, V_bound_in,
  V_param_1..k, V_x, V_i, tmp1, tmp2}` covers indices
  `0..k+6`; it is disjoint from f's body block
  `fBase..fBase + frag_f.numRegs - 1`.
- The f-body embedding (analogue of comp's
  `ProgramEmbedsFragment_compileFrag_comp_fBody`) places f's
  reindexed registers at `fBase`; "outside the f-body" means
  outer indices `< fBase` together with the implicit upper
  bound `nR`.

## Sub-task DAG

```text
              [bsum.0 PC-bound infra]
                       |
        +--------------+-------------+
        |              |             |
[bsum.1.a            [bsum.1.b     [bsum.1.c
 zeroSweep            prologue      accUpdate
 _correct + bound]    _correct +    _correct +
                      bound]        bound]
        |              |             |
        +--------------+-------------+
                       |
              [bsum.1.d f-body embedding]
                       |
              [bsum.2 partial_invariant + base]
                       |
                       v
              [bsum.3.phase_i0   zeroSweep preservation]
                       |
              [bsum.3.phase_i1   prologue preservation]
                       |
              [bsum.3.phase_i2   f-body preservation
                                 (consumes ih_f)]
                       |
              [bsum.3.phase_i3   accUpdate + incR vI →
                                 partial_invariant @ (i+1)]
                       |
              [bsum.4 step glue: i → i + 1]
                       |
              [bsum.5 outer iteration i = 0 → v 0]
                       |
              [bsum.6 final assembly:
                      prelude + clone + outer loop +
                      exit jumpZR + stopR]
                       |
                       v
        [compileER_pre_stop_correct_bsum]
```

The chain mirrors the comp DAG with one additional per-iteration
phase (i.0 zero-sweep) absent from comp, since comp has no
per-iteration register reset. Conversely, bsum has one fewer
top-level layer: there is no inductive family `gs` providing
its own outer iteration; the outer iteration over `i ∈
[0, v 0)` plays the role of comp's outer iteration over
`m ∈ [0, k]`.

## Sub-task list

Each sub-task lists the lemma signature(s) it lands, its
inputs and dependencies, outputs (declarations added to
`BSum.lean`), an LOC estimate, and notes drawn from the Task
11 handoff's `Patterns learned` section.

### Sub-task 11e.6.a.iii-bsum.0 — PC-bound infrastructure

Signature:

```lean
private def compileFrag_bsum_pcOf {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) (i : ℕ) : ℕ

private theorem compileFrag_bsum_pcOf_zero {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) :
    compileFrag_bsum_pcOf frag_f 0 = 13

private theorem compileFrag_bsum_pcOf_succ {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) (i : ℕ)
    (hi_lt : i < (placeholder : ℕ)) :
    compileFrag_bsum_pcOf frag_f (i + 1)
      = compileFrag_bsum_pcOf frag_f i + 0
```

The bsum analogue is degenerate: every iteration begins at the
same PC `topPC = 13` (the loop is jump-driven, not unfolded as
a linear chain). Implementers should drop the `_succ` lemma
and instead define `compileFrag_bsum_topPC : ℕ := 13` as a
named constant, plus per-phase offsets `bsum_bodyStartPC`,
`bsum_zeroSweepBase`, `bsum_prologueBase`, `bsum_bodyPCBase`,
`bsum_trBase`, `bsum_incIPC`, `bsum_gotoTopPC`, `bsum_exitPC`,
each as `frag_f`-parametric `def`s.

Inputs: `compileFrag_bsum`'s named offsets (Compiler.lean
lines 918-949).

Outputs: PC-layout constants and their reduction lemmas,
including `bsum_exitPC_eq_size_pred : bsum_exitPC frag_f
= (compileFrag_bsum frag_f).instrs.size - 1`.

Estimated LOC: 150-200.

Notes: keep all constants `private`. Prefer `let` over `set`
inside proofs to avoid omega's loss of syntactic identity (see
Pattern 9 of the handoff). Re-derive `instrs.size`
expressions via `URMInstrRaw.toBoundedArray_size` (Loops.lean,
landed in 11b).

### Sub-task 11e.6.a.iii-bsum.1.a — zero-sweep sub-block correctness

Signature:

```lean
private theorem compileFrag_bsum_zeroSweep_correct
    {a : ℕ}
    (P : URMProgram a) (pcBase fBase : ℕ)
    (numRegs_f : ℕ)
    (H : ∀ r : Fin numRegs_f,
      P.instrs[pcBase + r.val]? = some
        (URMInstr.assign ⟨fBase + r.val, by ...⟩ 0))
    (s : URMState P) (h_pc : s.pc = pcBase)
    (h_outside : ∀ q : Fin P.numRegs,
      (∀ r : Fin numRegs_f, q.val ≠ fBase + r.val) →
      True) :
    let totalSteps : ℕ := numRegs_f
    let s' := URMState.runFor P s totalSteps
    s'.pc = pcBase + numRegs_f ∧
    (∀ r : Fin numRegs_f,
        s'.regs ⟨fBase + r.val, by ...⟩ = 0) ∧
    (∀ q : Fin P.numRegs,
        (∀ r : Fin numRegs_f, q.val ≠ fBase + r.val) →
        s'.regs q = s.regs q)

private theorem compileFrag_bsum_zeroSweep_pc_strict_bound
    {a : ℕ} (P : URMProgram a) (pcBase fBase : ℕ)
    (numRegs_f : ℕ)
    (H : ∀ r : Fin numRegs_f,
      P.instrs[pcBase + r.val]? = some
        (URMInstr.assign ⟨fBase + r.val, by ...⟩ 0))
    (s : URMState P) (h_pc : s.pc = pcBase)
    (k' : ℕ) (h_k' : k' < numRegs_f) :
    (URMState.runFor P s k').pc < pcBase + numRegs_f
```

Inputs: `URMState.step_of_getElem?_assign` (Embedding.lean,
landed in 11d). No analogue exists in the landed comp chain;
this is genuinely new.

Outputs: two lemmas in `BSum.lean`.

Estimated LOC: 250-300.

Notes: each `assignR` step takes exactly one URM step. Proof
by induction on `r ∈ Fin numRegs_f`. Use Lean-core `Fin.cases`
(Pattern 1: mathlib's `fin_cases` pulls in `Classical.choice`).

### Sub-task 11e.6.a.iii-bsum.1.b — prologue sub-block correctness

Signature:

```lean
private theorem compileFrag_bsum_prologue_correct
    {a : ℕ}
    (P : URMProgram a) (pcBase : ℕ)
    (zReg tmp : Fin P.numRegs)
    (srcs dsts : Fin a → Fin P.numRegs)
    (h_disj : inputCopies_disj P zReg tmp srcs dsts)
    (H : ∀ s : Fin a,
      preservingTransferInstrs P (pcBase + 9 * s.val)
        (srcs s) (dsts s) tmp zReg)
    (vSrc : Fin a → ℕ)
    (s : URMState P) (h_pc : s.pc = pcBase)
    (h_z : s.regs zReg = 0) (h_tmp0 : s.regs tmp = 0)
    (h_srcs : ∀ j : Fin a, s.regs (srcs j) = vSrc j)
    (h_dsts0 : ∀ j : Fin a, s.regs (dsts j) = 0) :
    let totalSteps : ℕ := 9 * vPrefixSum vSrc a + 2 * a
    let s' := URMState.runFor P s totalSteps
    s'.pc = pcBase + 9 * a ∧
    s'.regs zReg = 0 ∧
    s'.regs tmp = 0 ∧
    (∀ j : Fin a, s'.regs (dsts j) = vSrc j) ∧
    (∀ j : Fin a, s'.regs (srcs j) = vSrc j) ∧
    (∀ r : Fin P.numRegs,
        (∀ j : Fin a, r ≠ dsts j) → r ≠ tmp →
        s'.regs r = s.regs r)

private theorem compileFrag_bsum_prologue_pc_strict_bound : ...
```

Inputs and dependencies: this is a *direct re-export* of
`compileFrag_comp_subBlock_inputCopies_correct` and
`_pc_strict_bound` (Comp.lean lines 1269-1323). The bsum
prologue is structurally identical to comp's input-copies
phase. Followup item 8 in the handoff observes this overlap;
the sub-task may either alias the comp lemma or copy its
signature into a fresh helper named for bsum.

Outputs: bsum-flavoured wrapper around the existing comp
input-copies helper, or a refactor that extracts the shared
helper into `Loops.lean`.

Estimated LOC: 100-150 if aliasing, 300 if extracting; prefer
aliasing.

Notes: the bsum prologue's source-vector `vSrc` has a special
slot-0 (`V_i`) plus slots `1..k` (outer parameters); the
slot-0 source is the iteration index, slot-`s` source is the
outer parameter `s - 1`. This is fully captured by allowing
`srcs : Fin a → Fin P.numRegs` to be any function; the bsum
caller (sub-task bsum.3.phase_i1) instantiates it.

### Sub-task 11e.6.a.iii-bsum.1.c — accumulator-update sub-block correctness

Signature:

```lean
private theorem compileFrag_bsum_accUpdate_correct
    {a : ℕ}
    (P : URMProgram a) (pcBase : ℕ)
    (src dst : Fin P.numRegs)
    (h_disj : src ≠ dst)
    (H : transferLoopInstrs P pcBase src dst)
    (vSrc vAcc : ℕ)
    (s : URMState P) (h_pc : s.pc = pcBase)
    (h_src : s.regs src = vSrc) (h_dst : s.regs dst = vAcc) :
    let totalSteps : ℕ := 4 * vSrc + 1
    let s' := URMState.runFor P s totalSteps
    s'.pc = pcBase + 4 ∧
    s'.regs dst = vAcc + vSrc ∧
    s'.regs src = 0 ∧
    (∀ r : Fin P.numRegs, r ≠ src → r ≠ dst →
        s'.regs r = s.regs r)

private theorem compileFrag_bsum_accUpdate_pc_strict_bound : ...
```

Inputs: `transferLoop_correct` (Loops.lean, landed 11c.1) and
`transferLoop_correct_pc_strict_bound` (Comp.lean lines around
11e.6.a.iii-comp.0). These are stated over an abstract
URMProgram; the bsum caller wires `src = fBase +
frag_f.outputReg.val` and `dst = vAcc = 1`.

Outputs: bsum-flavoured wrapper and bound lemma.

Estimated LOC: 100-150.

Notes: `transferLoop` is destructive in the source register:
the post-state has `src = 0`. This is what makes the
`zReg_zero` clause of the partial invariant re-establishable
at the next iteration's top, given that the source for the
next iteration's update is the f-body output, which the
zero-sweep flushes.

### Sub-task 11e.6.a.iii-bsum.1.d — f-body embedding

Signature:

```lean
private theorem ProgramEmbedsFragment_compileFrag_bsum_fBody
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1)) :
    ProgramEmbedsFragment
      (compileFrag_bsum frag_f).toURMProgram
      frag_f
      (k + 7)
      (15 + frag_f.numRegs + 9 * (k + 1))
      frag_f.instrs.size
```

The constants are: `fBase = k + 7`, `bodyPCBase = 15 +
frag_f.numRegs + 9 * (k + 1)`, embedded-program length
`frag_f.instrs.size`.

Inputs: `ProgramEmbedsFragment` (Embedding.lean), the
`compileFrag_bsum` definition (Compiler.lean lines 897-1100),
the indexing lemmas from `URMInstrRaw.toBoundedArray`
(Loops.lean, landed 11b).

Outputs: one lemma in `BSum.lean`. Direct analogue of
`ProgramEmbedsFragment_compileFrag_comp_fBody` (Comp.lean
lines 105-307).

Estimated LOC: 300-400.

Notes: the embedding bounds proof relies on the disjoint
register-block analysis recapped above. The PC-offset
unfolding follows the recipe in Comp.lean lines 105-307:
unfold `compileFrag_bsum`, expose `prelude ++ loopTop ++
zeroSweep ++ prologue ++ fBody ++ accUpdate ++ epilogue` as
the raw list, split the index access into the seventh
segment.

### Sub-task 11e.6.a.iii-bsum.2 — partial invariant and base case

Signatures:

```lean
private structure compileFrag_bsum_partial_invariant
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : ℕ) (hi : i ≤ v 0)
    (s : URMState (compileFrag_bsum frag_f).toURMProgram)
    : Prop where
  hi_le : i ≤ v 0 := hi
  pc_eq : s.pc = 13
  zReg_zero : s.regs ⟨0, (compileFrag_bsum frag_f).numRegs_pos⟩ = 0
  outer_inputs : ∀ (j : Fin (k + 1)),
    s.regs ⟨2 + j.val, by ...⟩ = v j
  vX_eq : s.regs ⟨k + 3, by ...⟩ = v 0 - i
  vI_eq : s.regs ⟨k + 4, by ...⟩ = i
  tmp1_zero : s.regs ⟨k + 5, by ...⟩ = 0
  tmp2_zero : s.regs ⟨k + 6, by ...⟩ = 0
  acc_eq : s.regs ⟨1, by ...⟩
    = natBSum i (fun j =>
        f.interp (Fin.cons j.val (Fin.tail v)))
  fBody_zero : ∀ r : Fin frag_f.numRegs,
    s.regs ⟨(k + 7) + r.val, by ...⟩ = 0

private theorem compileFrag_bsum_partial_base
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ) :
    let outer := (compileFrag_bsum (compileERFrag f)).toURMProgram
    let s_init := URMState.init outer v
    compileFrag_bsum_partial_invariant (compileERFrag f) v 0
      (Nat.zero_le _) (URMState.runFor outer s_init 13)
```

The invariant carries 10 clauses (vs comp's 8): the prologue
state is summarised by `outer_inputs` (the outer parameters
remain in place), `vX_eq` and `vI_eq` (the loop control
registers), `acc_eq` (the running sum), `fBody_zero` (cleared
by the zero-sweep at every iteration except possibly the
final exit, but the invariant is stated at the top of the
loop, before the iteration body), plus the four "global"
clauses (`pc_eq`, `zReg_zero`, `tmp1_zero`, `tmp2_zero`).

Inputs: `URMState.init_regs_zero_outside_inputs`
(Atoms.lean), `URMState.runFor_zero` /
`URMState.runFor_succ` (Embedding.lean), and the prelude's 13
instructions (4 `assignR` + 9 `preservingTransfer`). The
13-step run-time is the prelude's full length.

Outputs: structure and base lemma. The 13-step base subsumes
both the four leading `assignR`s and the `preservingTransfer
4 vBoundIn vX tmp2` block (Compiler.lean lines 950-955).

Estimated LOC: 400-500.

Notes: at `i = 0`, `natBSum 0 _ = 0`, so the `acc_eq` clause
reduces to `s.regs ⟨1, _⟩ = 0`, which holds after
`assignR vAcc 0`. The prelude's `preservingTransfer` requires
discharging `preservingTransfer_correct`. Use field-projection
(`h_inv.fieldName`) over `obtain ⟨..⟩` destructuring
(Pattern 10 of the handoff).

### Sub-task 11e.6.a.iii-bsum.3.phase_i0 — zero-sweep preservation

Signature:

```lean
private structure compileFrag_bsum_phase_i0_post
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (s : URMState (compileFrag_bsum frag_f).toURMProgram)
    : Prop where
  pc_eq : s.pc = 15 + frag_f.numRegs
  -- All carry-over clauses from partial_invariant @ i.val.

private theorem compileFrag_bsum_partial_phase_i0
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (sPre : URMState
      (compileFrag_bsum (compileERFrag f)).toURMProgram)
    (h_inv : compileFrag_bsum_partial_invariant
              (compileERFrag f) v i.val i.isLt.le sPre) :
    ∃ T0 : ℕ,
      T0 = 2 + (compileERFrag f).numRegs ∧
      compileFrag_bsum_phase_i0_post (compileERFrag f) f v i
        (URMState.runFor _ sPre T0) ∧
      (∀ k' < T0,
        (URMState.runFor _ sPre k').pc
          < 15 + (compileERFrag f).numRegs)
```

The 2 steps before the zero-sweep are the loop-top `jumpZR vX
exitPC bodyStartPC` (which jumps to `bodyStartPC = 14` when
`vX > 0`, i.e., when `i < v 0`) and the `decR vX` at
`bodyStartPC`.

Inputs: `compileFrag_bsum_zeroSweep_correct` (bsum.1.a),
`URMState.step_of_getElem?_jumpZ` /
`URMState.step_of_getElem?_dec` (Embedding.lean).

Outputs: phase-i.0 post structure and preservation lemma.

Estimated LOC: 350-450.

Notes: the precondition `i.val < v 0` makes `vX > 0` at
`sPre`, so the `jumpZR` takes the non-zero branch to
`bodyStartPC`. Use `Nat.lt_or_ge` + `rcases` (Pattern 2: by_cases
can pull Classical.choice).

### Sub-task 11e.6.a.iii-bsum.3.phase_i1 — prologue preservation

Signature:

```lean
private structure compileFrag_bsum_phase_i1_post
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (s : URMState (compileFrag_bsum frag_f).toURMProgram)
    : Prop where
  pc_eq : s.pc = 15 + frag_f.numRegs + 9 * (k + 1)
  -- f's input slots now hold (Fin.cons i.val (Fin.tail v)),
  -- f-body otherwise zero, all outer scaffolding preserved.
  f_inputs : ∀ (j : Fin (k + 1)),
    s.regs ⟨(k + 7) + (frag_f.inputRegs j).val, by ...⟩
      = Fin.cons i.val (Fin.tail v) j
  f_other_zero : ∀ (r : Fin frag_f.numRegs),
    (∀ j : Fin (k + 1), r ≠ frag_f.inputRegs j) →
    s.regs ⟨(k + 7) + r.val, by ...⟩ = 0
  -- carry-over of zReg_zero, outer_inputs, vX_eq (with i.val
  -- subtracted), vI_eq, tmp{1,2}_zero, acc_eq.

private theorem compileFrag_bsum_partial_phase_i1
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (sPre : URMState
      (compileFrag_bsum (compileERFrag f)).toURMProgram)
    (h_i0 : compileFrag_bsum_phase_i0_post (compileERFrag f) f v
              i sPre) :
    ∃ T0 : ℕ,
      T0 = 9 * (vPrefixSum (Fin.cons i.val (Fin.tail v)) (k + 1))
              + 2 * (k + 1) ∧
      compileFrag_bsum_phase_i1_post (compileERFrag f) f v i
        (URMState.runFor _ sPre T0) ∧
      (∀ k' < T0, ...)
```

Inputs: `compileFrag_bsum_prologue_correct` (bsum.1.b),
applied with `srcs` set to the bsum prologue-source map (slot
0 → `V_i`, slot `s > 0` → `V_param_{s-1}`), and `dsts` set to
f's reindexed input slots.

Outputs: phase-i.1 post structure and preservation lemma.

Estimated LOC: 450-550.

Notes: the source register `bsum_prologueSrc k s` is defined
in Compiler.lean line 817 by `if s.val = 0 then k + 4 else
s.val + 2`. Discharge the prologue-source case-split with
explicit pattern match on `Fin (k + 1)` (Pattern 1). The
`acc_eq` clause's value `natBSum i.val (...)` is unchanged
since the prologue does not touch `V_acc`.

### Sub-task 11e.6.a.iii-bsum.3.phase_i2 — f-body preservation

Signature:

```lean
private structure compileFrag_bsum_phase_i2_post
    {k : ℕ}
    (frag_f : CompiledFragment (k + 1))
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (s : URMState (compileFrag_bsum frag_f).toURMProgram)
    : Prop where
  pc_eq : s.pc = 15 + frag_f.numRegs + 9 * (k + 1)
                  + (frag_f.instrs.size - 1)
  f_output : s.regs ⟨(k + 7) + frag_f.outputReg.val, by ...⟩
    = f.interp (Fin.cons i.val (Fin.tail v))
  -- carry-over: outer scaffolding (zReg, outer_inputs, vX, vI,
  -- tmp1, tmp2, acc) preserved by the f-body embedding.

private theorem compileFrag_bsum_partial_phase_i2
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (ih_f : ∀ (v' : Fin (k + 1) → ℕ),
      ∃ T0 : ℕ, T0 ≤ compileER_runtime f v' ∧ ...)
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (sPre : URMState
      (compileFrag_bsum (compileERFrag f)).toURMProgram)
    (h_i1 : compileFrag_bsum_phase_i1_post (compileERFrag f) f v
              i sPre) :
    ∃ T0 : ℕ,
      T0 ≤ compileER_runtime f (Fin.cons i.val (Fin.tail v)) ∧
      compileFrag_bsum_phase_i2_post (compileERFrag f) f v i
        (URMState.runFor _ sPre T0) ∧
      (∀ k' < T0,
        (URMState.runFor _ sPre k').pc
          < 15 + (compileERFrag f).numRegs + 9 * (k + 1)
            + ((compileERFrag f).instrs.size - 1))
```

Inputs: `ProgramEmbedsFragment_compileFrag_bsum_fBody`
(bsum.1.d), `stateEmbedsFrag_runFor` and
`stateEmbedsFrag_runFor_outside_preserved` (Embedding.lean), and
the IH `ih_f` instantiated at
`Fin.cons i.val (Fin.tail v)`.

Outputs: phase-i.2 post structure and preservation lemma.
Direct analogue of `compileFrag_comp_subBlocks_partial_phase_i2`
(Comp.lean line 2978).

Estimated LOC: 500-600.

Notes: this is the only sub-task that consumes `ih_f`. The IH
gives an existential `T0_f ≤ compileER_runtime f (...)` with PC
at `(compileER f).instrs.size - 1`; the embedding maps that to
PC `bodyPCBase + frag_f.instrs.size - 1`. The carry-over of
outer scaffolding follows from `stateEmbedsFrag_step_outside_preserved`
(handoff Session 1, commit `8947b0ac`). `acc_eq` carry-over is
crucial: f's body must not touch `V_acc`, which holds because
`V_acc = 1` is outside f's reindexed block `[fBase, fBase +
frag_f.numRegs)`.

### Sub-task 11e.6.a.iii-bsum.3.phase_i3 — accUpdate + incR + goto

Signature:

```lean
private theorem compileFrag_bsum_partial_phase_i3
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (sPre : URMState
      (compileFrag_bsum (compileERFrag f)).toURMProgram)
    (h_i2 : compileFrag_bsum_phase_i2_post (compileERFrag f) f v
              i sPre) :
    ∃ T0 : ℕ,
      T0 = 4 * f.interp (Fin.cons i.val (Fin.tail v)) + 1 + 2 ∧
      compileFrag_bsum_partial_invariant (compileERFrag f) v
          (i.val + 1) (Nat.succ_le_of_lt i.isLt)
        (URMState.runFor _ sPre T0) ∧
      (∀ k' < T0,
        (URMState.runFor _ sPre k').pc < 13)
```

The `+ 2` accounts for `incR vI` and `goto topPC`. The
strict-bound conclusion says that on every step before
returning to the top, the PC stays in `[trBase, gotoTopPC]`,
which is strictly less than the loop-top `13` only because the
goto's destination is reached at the *final* step; on
intermediate steps the PC is `≥ 13`. The actual bound is
`gotoTopPC + 1` (i.e., `≤ exitPC`); revisit during
implementation.

Inputs: `compileFrag_bsum_accUpdate_correct` (bsum.1.c),
`URMState.step_of_getElem?_inc`,
`URMState.step_of_getElem?_jump` (the `goto` macro expands
to a `jumpZR ⟨0, _⟩` against the zero register).

Outputs: phase-i.3 preservation lemma. No intermediate post
structure (the conclusion is directly
`partial_invariant @ (i.val + 1)`), matching comp.2.inv-phase_i3
(Comp.lean line 3534).

Estimated LOC: 500-600.

Notes: re-establish `acc_eq` at `i.val + 1`: the new
accumulator value equals `natBSum (i.val + 1) (fun j =>
f.interp (Fin.cons j.val (Fin.tail v)))`. Use `natBSum`'s
recursion: `natBSum (n + 1) g = natBSum n g + g n`. Locate the
mathlib unfolding lemma via `lean_local_search`.

The `vX_eq` clause re-establishes as `v 0 - (i.val + 1)`
since `decR` already happened in phase i.0. The `fBody_zero`
clause re-establishes because the zero-sweep at the *next*
iteration's phase i.0 will flush it; at the moment of the
phase-i.3 → next-iteration partial-invariant transition, the
`fBody_zero` clause is *not* yet re-established. This means
the invariant cannot include `fBody_zero` at the top of the
loop; instead it should hold only at the start of each
iteration after phase i.0. Implementers should adjust the
invariant: either weaken `fBody_zero` to "f's body is in some
arbitrary state" (and have phase i.0 strengthen it) or move the
invariant boundary to after phase i.0.

### Sub-task 11e.6.a.iii-bsum.4 — induction glue (i → i + 1)

Signature:

```lean
private theorem compileFrag_bsum_partial_step
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (ih_f : ∀ (v' : Fin (k + 1) → ℕ),
      ∃ T0 : ℕ, T0 ≤ compileER_runtime f v' ∧ ...)
    (v : Fin (k + 1) → ℕ)
    (i : Fin (v 0))
    (sPre : URMState
      (compileFrag_bsum (compileERFrag f)).toURMProgram)
    (h_inv : compileFrag_bsum_partial_invariant
              (compileERFrag f) v i.val i.isLt.le sPre) :
    ∃ T0 : ℕ,
      T0 ≤ (2 + (compileERFrag f).numRegs)
            + (9 * vPrefixSum (Fin.cons i.val (Fin.tail v))
                  (k + 1) + 2 * (k + 1))
            + compileER_runtime f (Fin.cons i.val (Fin.tail v))
            + (4 * f.interp (Fin.cons i.val (Fin.tail v)) + 1 + 2) ∧
      compileFrag_bsum_partial_invariant (compileERFrag f) v
          (i.val + 1) (Nat.succ_le_of_lt i.isLt)
        (URMState.runFor _ sPre T0) ∧
      (∀ k' < T0,
        (URMState.runFor _ sPre k').pc
          < (compileFrag_bsum (compileERFrag f)).instrs.size - 1)
```

Inputs: the four phase preservation lemmas (bsum.3.phase_i0
through bsum.3.phase_i3), plus their strict-bound
counterparts. Mirrors `compileFrag_comp_subBlocks_partial_step`
(Comp.lean line 4348).

Outputs: m-step glue lemma.

Estimated LOC: 350-450.

Notes: the bound aligns with the bsum branch of
`compileER_runtime` (Compiler.lean lines 1426-1440). Restore
omega's syntactic identity across `compileERFrag f` vs `frag_f`
via explicit `have h_eq : ... := rfl` bridges (Pattern 9).

### Sub-task 11e.6.a.iii-bsum.5 — outer iteration (i = 0 to v 0)

Signature:

```lean
private theorem compileFrag_bsum_partial_aux
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (ih_f : ...)
    (v : Fin (k + 1) → ℕ)
    (i : ℕ) (hi : i ≤ v 0) :
    ∃ T0 : ℕ,
      T0 ≤ 13 + (...iteration-sum bound from runtime...) ∧
      compileFrag_bsum_partial_invariant (compileERFrag f) v
          i hi (URMState.runFor _ s_init T0) ∧
      (∀ k' < T0,
        (URMState.runFor _ s_init k').pc
          < (compileFrag_bsum (compileERFrag f)).instrs.size - 1)

private theorem compileFrag_bsum_partial
    {k : ℕ}
    (f : ERMor1 (k + 1))
    (ih_f : ...)
    (v : Fin (k + 1) → ℕ) :
    ∃ T0 : ℕ,
      T0 ≤ 13 + (...full bsum-runtime iteration sum...) ∧
      compileFrag_bsum_partial_invariant (compileERFrag f) v
          (v 0) (Nat.le_refl _) (URMState.runFor _ s_init T0) ∧
      (∀ k' < T0, ...)
```

Inputs: `compileFrag_bsum_partial_base` (bsum.2),
`compileFrag_bsum_partial_step` (bsum.4). Mirrors
`compileFrag_comp_subBlocks_partial` (Comp.lean line 4761) and
its `_aux` helper (line 4606).

Outputs: outer-iteration outer loop. Final state is
`partial_invariant @ (v 0)`, i.e., the loop has executed v 0
iterations; `V_x = v 0 - v 0 = 0`; `V_i = v 0`; `V_acc =
natBSum (v 0) (...)`.

Estimated LOC: 300-400.

Notes: induction on `i ≤ v 0` (the bound from outer input
slot 0). Use `Fin.cases` on `Fin (v 0)` if iterating over
`i : Fin (v 0)`; alternatively, induct on `i : ℕ` with a
`∀ i ≤ v 0` strengthening (cf. Comp.lean line 4606's
`_aux` form).

### Sub-task 11e.6.a.iii-bsum.6 — final assembly

Signature: `compileER_pre_stop_correct_bsum` (the top-level
statement given above).

Inputs: `compileFrag_bsum_partial` (bsum.5). After the outer
loop's last iteration, the PC is at the loop top `13`; the
final `jumpZR vX exitPC bodyStartPC` takes the *zero* branch
(since `V_x = 0`) to `exitPC = trBase + 6`, which is the
trailing `stopR` and is the last instruction
(`= instrs.size - 1`). The final `T0` adds 1 to bsum.5's
output for the `jumpZR` step.

Outputs: top-level pre-stop lemma. Mirrors
`compileER_pre_stop_correct_comp` (Comp.lean line 4915).

Estimated LOC: 250-350.

Notes: discharge the final `jumpZR` step via
`URMState.step_of_getElem?_jumpZ` (Embedding.lean) with
`s.regs vX = 0` (from the partial-invariant
`vX_eq : ... = v 0 - v 0 = 0` clause at `i = v 0`).

The runtime bound from `compileER_runtime` for bsum
(Compiler.lean lines 1426-1440) needs to be matched: the
constant `30 + 10 * bound` plus the per-iteration sum.
Reconcile the prelude's 13 instructions plus the post-loop
single `jumpZR` step (1 step) against the constant `30`. The
remaining `10 * bound` slack pads each iteration's
`decR + jumpZR + zero-sweep + incR + goto` overhead.

## Inductive variable

The outer loop is parameterised by the natural number `i :
ℕ` with `i ≤ v 0`. Bsum's `vX` register holds `v 0 - i` (the
remaining iterations); `vI` register holds `i` itself. The
partial-invariant carries `i` as an external parameter via
`compileFrag_bsum_partial_invariant ... i hi ...`. The
iteration count `v 0` is read from the bsum's first input
slot (outer register `2`).

Mapping at iteration boundaries: at the start of iteration
`i.val ∈ [0, v 0)` (i.e., entering phase i.0), the invariant
holds at `i.val`; at the end of phase i.3, the invariant
holds at `i.val + 1`. The bsum.5 outer iteration drives
`i` from `0` to `v 0`. At `i = 0` (the base) and at `i = v 0`
(the loop exit), the invariant clauses give us the entry and
final states respectively.

Comp's analogous parameter was `m ≤ k` (`m : ℕ` ranging over
the indexed family `gs : Fin k → ERMor1 a`); bsum's analogue
is the iteration index `i ≤ v 0`, ranging over a `Fin (v 0)`
when accessed.

## Cross-references and IH form

The IH on f matches the existential pre-stop form of
`compileER_pre_stop_correct_*` (atoms in Atoms.lean; comp in
Comp.lean line 4915). This IH is consumed in sub-task
bsum.3.phase_i2 only.

The bsum chain produces a single output existential of the
same shape; no `gs`-family IH is required. The bridge
`compileER_pre_stop_to_runFor` (Embedding.lean lines 825-870)
will discharge Task 11f (the bsum runFor wrapper) directly
from `compileER_pre_stop_correct_bsum`, exactly as Task 11e.7
discharges the comp runFor wrapper from
`compileER_pre_stop_correct_comp`.

Wiring analogue: the bsum prologue source map
`bsum_prologueSrc` (Compiler.lean line 817) wires slot 0 of
f's input vector to outer register `V_i` (containing the
iteration index `i`) and slot `s > 0` to outer register
`s + 2` (an outer parameter). The induced `f`-input vector
matches `Fin.cons i.val (Fin.tail v)` (Compiler.lean line
1431); the bsum semantics `natBSum (v 0) (fun i => f.interp
(Fin.cons i (Fin.tail v)))` (LawvereER.lean lines 90-92)
threads through via this prologue.

## Followup items

Items observed during sub-division that belong on the
post-T2 followup branch (task #654):

1. Extract the now-shared input-copies helpers
   (`inputCopies_disj`,
   `compileFrag_comp_subBlock_inputCopies_correct`,
   `compileFrag_comp_subBlock_inputCopies_pc_strict_bound`)
   from `Comp.lean` into `Loops.lean` (or a new
   `SharedInputCopies.lean` submodule) under
   constructor-agnostic names (e.g. `inputCopies_correct`,
   `inputCopies_pc_strict_bound`); the current
   `compileFrag_comp_*` prefix is misleading once bsum and
   bprod also consume them. Bsum's `prologue` wrappers were
   landed in sub-task 11e.6.a.iii-bsum.1.b as thin aliases
   over the comp helpers (which were un-`private`d for that
   purpose). The followup migrates the shared helpers to a
   neutral location and renames; bsum's `prologue_correct` /
   `prologue_pc_strict_bound` wrappers then realias the
   renamed helpers, and bprod consumes them too.
2. Extract `compileFrag_bsum_pcOf` and its layout constants
   into a parallel of `compileFrag_comp_pcOf` even though
   bsum's per-iteration PC layout is trivial (every iteration
   starts at `topPC = 13`); the naming convention should
   match comp for downstream uniformity.
3. Re-evaluate the partial-invariant's `fBody_zero` clause's
   placement (top-of-loop versus after-phase-i.0): if
   placement-after-phase-i.0 is cleaner, document the
   asymmetry with comp and consider mirroring in bprod.
4. Once bprod lands, factor out
   `bsum_zeroSweep_correct` and
   `bsum_accUpdate_correct` into `Loops.lean` under
   constructor-agnostic names if bprod can share them.
5. Add `/-! ### ... -/` section markers to `BSum.lean` around
   the six logical phases (PC-bound infra, three sub-block
   helpers, f-body embedding, partial-invariant, phase
   preservations, outer iteration, final assembly), per
   handoff followup item 13.
6. Audit whether `Atoms.lean`'s
   `URMState.init_regs_inputRegs` reference should migrate to
   `Embedding.lean` before `BSum.lean` lands, so `BSum.lean`
   imports `Loops` rather than `Atoms` (handoff followup
   item 10).
7. Minor items raised by the bsum.0 code-quality review:
   (a) hoist `length_preservingTransfer` /
   `length_transferLoop` helpers from `compileFrag_bsum_size`'s
   inline `have` blocks into `Loops.lean` if bprod's parallel
   size lemma `compileFrag_bprod_size` reuses them;
   (b) trim development-history phrasing from
   `bsum_exitPC_eq_size_pred`'s docstring once the lemma's
   final shape stabilises;
   (c) consider `abbrev` rather than `def` for the three
   unparameterised PC constants (`bsum_topPC`,
   `bsum_bodyStartPC`, `bsum_zeroSweepBase`) if `bsum_topPC`
   appears in `simp only` lists in later sub-tasks;
   (d) add a rationale comment to `bsum_trBase` explaining the
   `bodyPCBase + (frag_f.instrs.size - 1)` decomposition.

## References

- Handoff:
  `docs/superpowers/plans/2026-05-18-step-t2-t11-handoff.md`.
- Plan:
  `docs/superpowers/plans/2026-05-17-step-t2-er-to-urm-compiler.md`.
- Spec:
  `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`
  (bsum semantics §5.1.1).
- Compiler: `GebLean/LawvereERKSim/Compiler.lean`
  (`compileFrag_bsum` lines 897-1100;
  `bsum_prologueSrc` line 817; `bsum_prologueBlock` line 832;
  `bsum_zeroSweep` line 867; `compileER_runtime` lines
  1410-1455).
- Comp model: `GebLean/LawvereERKSim/Comp.lean`
  (`compileFrag_comp_subBlock_inputCopies_correct` line 1269;
  `_gsBody_correct` line 1340; `_outputTransfer_correct` line
  1551; `compileFrag_comp_pcOf` line 1614;
  `compileFrag_comp_partial_invariant` line 1813;
  `compileFrag_comp_subBlocks_partial_base` line 1934;
  `_phase_i1` line 2265; `_phase_i2` line 2978; `_phase_i3`
  line 3534; `_step` line 4348; `_aux` line 4606; `_partial`
  line 4761; `compileER_pre_stop_correct_comp` line 4915).
- Embedding: `GebLean/LawvereERKSim/Embedding.lean`
  (`ProgramEmbedsFragment`, `StateEmbedsFrag`,
  `stateEmbedsFrag_runFor_outside_preserved`,
  `compileER_pre_stop_to_runFor` lines 825-870).
- Loops: `GebLean/LawvereERKSim/Loops.lean`
  (`transferLoop_correct`, `preservingTransfer_correct`,
  bound counterparts).
- Atoms: `GebLean/LawvereERKSim/Atoms.lean`
  (`URMState.init_regs_inputRegs`,
  `URMState.init_regs_zero_outside_inputs`).
- ER semantics: `GebLean/LawvereER.lean`
  (`ERMor1.interp_bsum` lines 130-134).
