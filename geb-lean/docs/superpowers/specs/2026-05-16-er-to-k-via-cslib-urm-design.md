# erToK via zero-test URM simulation — design

> **Status (2026-05-20).** §4 (URM kernel) and §5 (ER → URM
> compiler with `compileER_runtime` and `compileER_runFor`) are
> implemented. T1 landed §4 in `GebLean/Utilities/ZeroTestURM.lean`;
> T2 landed §5 in eight submodules under
> `GebLean/LawvereERKSim/{Compiler,Embedding,Loops,Atoms,Comp,BSum,BProd,Top}.lean`
> (≈ 28 000 LOC), re-exported via `GebLean/LawvereERKSim.lean`.
> Every public declaration is `[propext, Quot.sound]`-only.
> §6–§8 (K^sim simulator, runtime bound, erToK assembly) and §11
> (categorical iso) remain forward-looking design; the next
> workstream T3 will re-spec §6 against the actually-landed §4/§5
> shapes. See
> [`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`](../../research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md)
> § "Phase 2 partial-completion note" for cross-references.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [1 Scope](#1-scope)
- [2 What is transcribed and what is not](#2-what-is-transcribed-and-what-is-not)
  - [2.1 URM kernel: own zero-test URM, not CSLib's](#21-urm-kernel-own-zero-test-urm-not-cslibs)
  - [2.2 ZeroTestURM (formal, §0.1.0.37 p. 15–16)](#22-zerotesturm-formal-01037-p-1516)
- [3 Inventory of existing Ksim composites](#3-inventory-of-existing-ksim-composites)
  - [3.1 Ksim composites that need to be built](#31-ksim-composites-that-need-to-be-built)
- [4 URM kernel (`GebLean/Utilities/ZeroTestURM.lean`)](#4-urm-kernel-gebleanutilitieszerotesturmlean)
  - [4.1 Inductive instruction type](#41-inductive-instruction-type)
  - [4.2 Step relation and step-counted runner](#42-step-relation-and-step-counted-runner)
  - [4.3 Initial state and total runtime](#43-initial-state-and-total-runtime)
  - [4.4 What this module does NOT contain](#44-what-this-module-does-not-contain)
- [5 ER to URM compiler](#5-er-to-urm-compiler)
  - [5.1 Per-ER-constructor templates](#51-per-er-constructor-templates)
    - [5.1.1 Per-iteration prologue for `bsum` and `bprod`](#511-per-iteration-prologue-for-bsum-and-bprod)
    - [5.1.2 g-to-f wiring for `comp f gs`](#512-g-to-f-wiring-for-comp-f-gs)
  - [5.2 Compiler correctness](#52-compiler-correctness)
- [6 Ksim simulator](#6-ksim-simulator)
  - [6.1 The simulating functions](#61-the-simulating-functions)
  - [6.2 Realisation as a Ksim term](#62-realisation-as-a-ksim-term)
    - [Base case](#base-case)
    - [Step case](#step-case)
    - [Level total](#level-total)
  - [6.3 Correctness theorem](#63-correctness-theorem)
- [7 Ksim runtime bound](#7-ksim-runtime-bound)
  - [7.1 The bound expression](#71-the-bound-expression)
  - [7.2 Construction of `r_e`](#72-construction-of-r_e)
  - [7.3 Domination theorem](#73-domination-theorem)
- [8 erToK assembly (`GebLean/LawvereERKSim.lean`)](#8-ertok-assembly-gebleanlawvereerksimlean)
  - [8.1 Definition](#81-definition)
  - [8.2 Level bound](#82-level-bound)
  - [8.3 Interpretation preservation](#83-interpretation-preservation)
  - [8.4 Functor lift](#84-functor-lift)
- [9 Module layout](#9-module-layout)
  - [9.1 Dependency graph](#91-dependency-graph)
- [10 Constructive discipline](#10-constructive-discipline)
- [11 Step decomposition](#11-step-decomposition)
- [12 Adversarial-review punch list](#12-adversarial-review-punch-list)
  - [12.1 Constructive discipline preserved](#121-constructive-discipline-preserved)
  - [12.2 ZeroTestURM matches Tourlakis §0.1.0.37](#122-zerotesturm-matches-tourlakis-01037)
  - [12.3 §0.1.0.37 simulation lemma transcription](#123-01037-simulation-lemma-transcription)
  - [12.4 §0.1.0.44 proof transcription](#124-01044-proof-transcription)
  - [12.5 Level claim for `simulate`](#125-level-claim-for-simulate)
  - [12.6 Level claim for `boundExprK`](#126-level-claim-for-boundexprk)
  - [12.7 Every construction has a citation](#127-every-construction-has-a-citation)
  - [12.8 Per-template correctness coverage](#128-per-template-correctness-coverage)
  - [12.9 No phantom infrastructure](#129-no-phantom-infrastructure)
  - [12.10 Independence from kToER side](#1210-independence-from-ktoer-side)
  - [12.11 No CSLib-URM-driven infrastructure](#1211-no-cslib-urm-driven-infrastructure)
- [13 Citations](#13-citations)
  - [13.1 External (Tourlakis 2018, `PR-complexity-topics.pdf`)](#131-external-tourlakis-2018-pr-complexity-topicspdf)
  - [13.2 Internal repository references](#132-internal-repository-references)
- [14 Out of scope](#14-out-of-scope)

<!-- END doctoc -->

## 1 Scope

Construction of `erToK : ERMor1 a → KMor1 a` of K^sim level
≤ 2 with `(erToK e).interp v = e.interp v`, and its
functor lift `erToKFunctor : LawvereERCat ⥤
LawvereKSimDCat 2`. Forms one direction of the categorical
equivalence between `LawvereERCat` and `LawvereKSimDCat 2`
(Tourlakis 2018 Corollary 0.1.0.44).

The kToER direction is complete; see master design
[§3](../../research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md)
and `GebLean/LawvereKSimER.lean`. The strict categorical
isomorphism (master design §11) is out of scope here;
becomes its own spec once erToKFunctor lands.

## 2 What is transcribed and what is not

This spec is a transcription of Tourlakis 2018 §0.1.0.37
(simulation lemma, p. 15–16), §0.1.0.43 (Ritchie–Cobham,
p. 21), and §0.1.0.44 proof (p. 22), with explicit
realisations in Lean using existing K^sim composites from
`GebLean/Utilities/KArith.lean`.

### 2.1 URM kernel: own zero-test URM, not CSLib's

The URM kernel is built directly in
`GebLean/Utilities/ZeroTestURM.lean`. CSLib provides a
URM at `Cslib.Computability.URM.*` (4 instructions:
`Z n` zero, `S n` succ, `T m n` transfer, `J m n q`
equality jump). Our URM and CSLib's bisimulate at the
function-class level (both are Turing-complete URMs);
they do not bisimulate step-for-step.

The structural difference that matters for the K^sim_2
construction is the *jump primitive*. Our URM's jump is
zero-test (`if V_i = 0 goto l_1 else goto l_2`), which
the K^sim simulator's per-instruction step realises via
`KMor1.cond` — K^sim level 1 (`KArith.lean:264`,
verified). CSLib's jump is general equality
(`J m n q` tests `regs[m] = regs[n]` for arbitrary
`m`, `n`), which would require the K^sim term
`KMor1.eq` — level 2 (`KArith.lean:469`, verified).
A per-instruction step using `KMor1.eq` is at level 2;
the outer simrec on time then adds 1, pushing the
simulator to level 3 and exceeding the K^sim_2 budget.

CSLib's URM is usable for this construction only if its
emitted programs are restricted to `J m c q` patterns
against a reserved register `c` holding zero (so that
equality reduces to zero-test). Carrying that
restriction predicate through every signature and every
simulator-correctness proof is more code than building a
50–100-line URM with the five Tourlakis primitives
directly. We choose the own-URM path.

### 2.2 ZeroTestURM (formal, §0.1.0.37 p. 15–16)

| Instruction | Effect |
| --- | --- |
| `V_i ← c` (any constant `c`) | `v_i := c`; `pc := pc + 1` |
| `V_i ← V_i + 1` | `v_i := v_i + 1`; `pc := pc + 1` |
| `V_i ← V_i ∸ 1` | `v_i := max(v_i − 1, 0)`; `pc := pc + 1` |
| `if V_i = 0 goto l_1 else goto l_2` | `pc := l_1` if `v_i = 0`, else `pc := l_2` |
| `stop` | `pc := pc`; registers unchanged (self-loop) |

Five instruction types. Tourlakis's URM has no general
register-transfer `V_i ← V_j`, no unconditional `goto l`,
and no `V_i ← 0`-as-primitive; these appear in worked
examples as derived shorthands. Tourlakis's worked
example M for `λx.x` (p. 19) uses `goto 1` as informal
shorthand for `if V_z = 0 goto 1 else goto 1` where
`V_z` is a register holding zero, since §0.1.0.37's case
analysis has no `goto` branch.

## 3 Inventory of existing Ksim composites

This section catalogues what is already in the repository
so this spec does not invent duplicates. Every K^sim atom
the construction uses below points here.

| Name | Type | Level | File:line | Tourlakis citation |
| --- | --- | --- | --- | --- |
| `KMor1.zero` | `KMor1 n` | 0 | `LawvereKSim.lean:36` | K_0 initial fn (§0.1.0.2 p. 1) |
| `KMor1.succ` | `KMor1 1` | 0 | `LawvereKSim.lean:38` | `λx.x+1` (§0.1.0.2 p. 1) |
| `KMor1.proj` | `KMor1 n` | 0 | `LawvereKSim.lean:40` | not in Tourlakis (standard) |
| `KMor1.one` | `KMor1 0` | 0 | `KArith.lean:31` | not in Tourlakis (standard) |
| `KMor1.pred` | `KMor1 1` | 1 | `KArith.lean:44` | `λx.x ∸ 1` (§0.1.0.17(4) p. 6) |
| `KMor1.isZero` | `KMor1 1` | 1 | `KArith.lean:78` | `λx.1 ∸ x` (§0.1.0.17(3) p. 6) |
| `KMor1.signum` | `KMor1 1` | 1 | `KArith.lean:420` (private; listed for completeness, not used in §3.1–§8) | not in Tourlakis (standard) |
| `KMor1.add` | `KMor1 2` | 1 | `KArith.lean:111` | `λxy.x+y` (§0.1.0.17(1) p. 6) |
| `KMor1.cond` | `KMor1 3` | 1 (`:264`) | `KArith.lean:222` | `switch` (§0.1.0.17(6) p. 6) |
| `KMor1.mult` | `KMor1 2` | 2 | `KArith.lean:301` | `λxy.xy` (§0.1.0.17(b) p. 6) |
| `KMor1.monus` | `KMor1 2` | 2 | `KArith.lean:403` | `λxy.x ∸ y` (§0.1.0.17(a) p. 6) |
| `KMor1.pow2` | `KMor1 1` | 2 | `KArith.lean:500` | `λx.2^x` (§0.1.0.17(c) p. 7) |
| `KMor1.rec1` | `KMor1 (a+1)` | (closes simrec) | `LawvereKSim.lean:137` | not in Tourlakis (project-internal) |
| `KMor1.permArgs` | `KMor1 n` | passthrough | `LawvereKSim.lean:154` | not in Tourlakis (project-internal) |

`KMor1.cond` (== Tourlakis's `switch`) is the level-1
primitive driving the simulator's PC dispatch:
`cond(0, y, z) = y`, `cond(x+1, y, z) = z`
(`KArith.lean:249` simp lemma `KMor1.interp_cond`,
verified shape `if ctx 0 = 0 then ctx 1 else ctx 2`).

### 3.1 Ksim composites that need to be built

The construction below uses these named composites that
are not yet in the repository:

- `KMor1.natK : ℕ → KMor1 0`. Constant `c` morphism;
  built by `c`-fold composition of `succ` with `zero`.
  Level 0. Citation: Tourlakis §0.1.0.2 (p. 1: K_0's
  closure under substitution yields all natural-number
  constants from `λx.x+1` applied to `zero`). When used
  inside a `KMor1 n`-valued context (for example, as a
  branch inside the simulator's step function),
  `natK c` is lifted via
  `KMor1.comp (natK c) (Fin.elim0 : Fin 0 → KMor1 n)`;
  the lift is level 0.
- `KMor1.maxK : KMor1 2`. Binary maximum,
  `max(x, y) = (x ∸ y) + y`. Level 2 by `comp` taking
  the max of `monus` (level 2) and `add` (level 1).
  Citation: the identity `max(x, y) = (x ∸ y) + y` is
  elementary and not stated by Tourlakis; the
  constituent operations are §0.1.0.17(1) (`+`) and
  §0.1.0.17(a) (`∸`). The identity is to be proved as
  a one-line lemma in `LawvereERKSim.lean`.
- `KMor1.maxOver : (a : ℕ) → KMor1 a`. `a`-ary maximum
  defined by the recursion `maxOver 0 = zero`;
  `maxOver (a+1) = maxK ∘ ⟨proj_0, maxOver a ∘ shift⟩`.
  Level ≤ 2 (level 0 at `a = 0`; level 2 for `a ≥ 2`).
  Citation: the n-ary recursion is folklore
  (associative-binary-op extended to n-ary; no
  Tourlakis location establishes the recursion).
  Tourlakis §0.1.0.44 proof (p. 22) uses `max(x⃗)` as a
  bound argument — this is a *use* citation only. The
  recursion's correctness is by induction on `a`.
- `KMor1.pow2_iter : ℕ → KMor1 1`. `r`-fold composition
  of `KMor1.pow2` with itself. Level 2 by induction on
  `r` using `comp`'s max rule. Citation:
  §0.1.0.17(c) (p. 7) establishes `λx.2^x ∈ K^sim_2`,
  realised by `KMor1.pow2`; §0.1.0.44 proof (p. 22)
  uses an iterated tower of exponentials
  `A^r_n(max x⃗)` as the runtime majorant. Tourlakis's
  `A^r_n` is not formalised here; `pow2_iter` is a
  strictly weaker but sufficient majorant — for each
  `e : ERMor1 a` there exists `r_e` such that
  `pow2_iter r_e ∘ maxOver a` dominates the runtime of
  `compileER e`. This is enough for §7.3.

These four are built in §6.2 and §7 below.

## 4 URM kernel (`GebLean/Utilities/ZeroTestURM.lean`)

### 4.1 Inductive instruction type

```lean
inductive URMInstr (r : ℕ) : Type
  | assign  (i : Fin r) (c : ℕ)              : URMInstr r
  | inc     (i : Fin r)                       : URMInstr r
  | dec     (i : Fin r)                       : URMInstr r
  | jumpZ   (i : Fin r) (l₁ l₂ : ℕ)           : URMInstr r
  | stop                                      : URMInstr r
```

Five cases, one per Tourlakis §0.1.0.37 (p. 16) instruction
type. `Fin r` keeps register indices in-range.

```lean
structure URMProgram where
  numRegs    : ℕ
  numInputs  : ℕ
  instrs     : Array (URMInstr numRegs)
  outputReg  : Fin numRegs
  inputRegs  : Fin numInputs → Fin numRegs
  inputRegs_inj : Function.Injective inputRegs
  outputReg_not_input : ∀ i, inputRegs i ≠ outputReg
```

The two structural invariants `inputRegs_inj` and
`outputReg_not_input` are independent constraints
(distinct input slots map to distinct registers; the
output register is disjoint from every input register).
Neither implies the other.

`numInputs ≤ numRegs`. Per Tourlakis §0.1.0.37 (p. 15):
"V_1 is the output variable while the V_i, for i = 2, …,
n+1, are input variables." Our `outputReg` and
`inputRegs` make this convention explicit, and
`outputReg_not_input` enforces the disjointness Tourlakis
relies on for the base case `v_1(0, a⃗_n) = 0` (the
output register starts at 0, distinct from any input
slot). PC labels are
`0, 1, …, instrs.size − 1`. PC ≥ `instrs.size` is the
implicit halt state (per Tourlakis: "since once the
instruction stop is reached the computation continues
forever 'trivially', that is, without changing either the
V_i or the instruction number" — p. 15).

### 4.2 Step relation and step-counted runner

```lean
structure URMState (P : URMProgram) where
  pc   : ℕ
  regs : Fin P.numRegs → ℕ

def URMState.step (P : URMProgram) (s : URMState P) :
    URMState P :=
  if h : s.pc < P.instrs.size then
    match P.instrs[s.pc] with
    | .assign i c   => ⟨s.pc + 1, Function.update s.regs i c⟩
    | .inc i        => ⟨s.pc + 1, Function.update s.regs i (s.regs i + 1)⟩
    | .dec i        => ⟨s.pc + 1, Function.update s.regs i (s.regs i - 1)⟩
    | .jumpZ i l₁ l₂ => ⟨if s.regs i = 0 then l₁ else l₂, s.regs⟩
    | .stop         => s
  else s

def URMState.runFor (P : URMProgram) (s : URMState P) :
    ℕ → URMState P
  | 0 => s
  | n + 1 => (URMState.step P s).runFor n
```

Constructive, computable. `runFor` corresponds to
Tourlakis's "y-th ID of a computation" (p. 15). Past the
stop instruction, `step` is the identity, matching
Tourlakis's "continues forever 'trivially'" clause.

### 4.3 Initial state and total runtime

```lean
def URMState.init (P : URMProgram) (v : Fin P.numInputs → ℕ) :
    URMState P where
  pc := 0  -- Tourlakis's I(0) = 1 mapped to 0
  regs := fun r =>
    match (List.finRange P.numInputs).find?
        (fun i => decide (P.inputRegs i = r)) with
    | some i => v i
    | none   => 0
```

Uses Lean core's `List.find?` over `List.finRange
P.numInputs` (constructive search returning
`Option (Fin P.numInputs)`) rather than
`Classical.choose`, per the constructive discipline
(§10). `inputRegs_inj` (§4.1) ensures the returned
`some i` value is unique when it exists; when `r` is
not in `P.inputRegs`' image, `find?` returns `none`
and the register defaults to 0.

The total ER expression's input arity is `P.numInputs`; we
do not write a separate `runtimeBound` Lean function (the
runtime bound is constructed as a K^sim term in §7, not as
a Nat-level function).

### 4.4 What this module does NOT contain

No `URMComputes` structure, no `urmSeq`/`urmIf`/`urmLoop`
combinators, no `urmDecToReg`/`urmCopyReg` helpers. Tourlakis
§0.1.0.37 reasons directly about programs and IDs; the
compiler in §5 emits programs by per-ER-constructor
templates without combinator infrastructure.

## 5 ER to URM compiler

### 5.1 Per-ER-constructor templates

Each ER constructor `e : ERMor1 a` compiles to a `URMProgram
P_e` with `P_e.numInputs = a`. The compiler is a single
recursive Lean function:

```lean
def compileER : {a : ℕ} → ERMor1 a → URMProgram
```

Templates, one per ER constructor:

| ER constructor | URM template (per Tourlakis pp. 19–21) |
| --- | --- |
| `ERMor1.zero` | `V_out ← 0; stop`. 2 instructions. |
| `ERMor1.succ` | `V_out ← V_in + 1; stop`. Encoded as `V_out ← 0; loop V_in times {V_out ← V_out + 1}; V_out ← V_out + 1; stop` (transfer + succ via Tourlakis's M template, p. 19, plus one extra inc). |
| `ERMor1.proj i` | Transfer V_{in_i} to V_out. Tourlakis M template (p. 19): zero V_out; loop V_{in_i} times {V_out ← V_out + 1}; stop. |
| `ERMor1.sub` | Derived Loop program `Z ← X; Loop Y { Z ← Z ∸ 1 } end` (recursing on Y per §0.1.0.17(a)'s `x ∸ (y+1) = (x ∸ y) ∸ 1`), then translated to URM via the Loop-to-URM template (p. 20). |
| `ERMor1.comp f gs` | Sequential composition with explicit g→f wiring (see §5.1.2 below). Tourlakis p. 21 "We can (essentially) concatenate M_g and M_f". |
| `ERMor1.bsum f` | Outer Loop with two distinct registers: a loop-count register `V_x` (initialised to `ctx 0`, decremented each iteration) and an iteration-index register `V_i` (initialised to 0, incremented each iteration). Per-iteration prologue (see §5.1.1 below) writes `V_i` into `f`'s slot-0 scratch and re-clones `f`'s outer-parameter inputs; inner body invokes `compileER f`'s instruction sequence and accumulates into the output register. Tourlakis p. 21 bounded-recursion template (specialised: iterator `g(i, y⃗, z) := z + f(i, y⃗)`, basis `h(y⃗) := 0`). |
| `ERMor1.bprod f` | Same shape (two distinct registers `V_x`, `V_i`; per-iteration prologue); iterator `g(i, y⃗, z) := z · f(i, y⃗)`, basis `h(y⃗) := 1`. Per-iteration step `z ← z · f(i, y⃗)` uses the same loop-to-URM expansion as bsum's accumulator update, with multiplication replacing addition; multiplication itself is the inner loop from Tourlakis p. 19's R^XY_Z worked example. |

The "transfer V_a to V_b" idiom in Tourlakis's M template
(p. 19) and the unconditional jump `goto l` (Tourlakis's
informal shorthand) translate formally as:

- `goto l` ≡ `if V_z = 0 goto l else goto l` where
  `V_z` is a reserved register holding `0`. Every
  compiled URM emits `V_z ← 0` at PC 0 as its first
  instruction; no later instruction writes `V_z`.
  This is the project's formal encoding of Tourlakis's
  informal `goto l` shorthand (Tourlakis p. 19 uses
  `goto 1` as syntactic sugar; §0.1.0.37's case
  analysis has no `goto` case, so the encoding via
  `V_z = 0` is forced by faithfulness to the formal
  URM).
- `V_b ← V_a` ≡ M-template (loop V_a times {V_b ← V_b +
  1}), with V_a *destructively consumed* by the loop's
  inner `V_a ← V_a ∸ 1` step.

**Register-allocation discipline: pre-clone at the
prelude.** Tourlakis's M-template (p. 19) is destructive
of the *source*: the loop `V_dest ← V_dest + 1` is
guarded by `V_src ← V_src ∸ 1`. A single M-template
invocation copying `V_in → V_dest` zeroes `V_in`. To
support multiple `proj i` reads of the same input
register inside `comp`, the compiler pre-clones each
input at the program prelude using the standard URM
preserving-transfer idiom:

```text
-- Preserving transfer V_a → V_b (V_a unchanged):
Loop V_a {
  V_b   ← V_b   + 1
  V_tmp ← V_tmp + 1
}
-- Now V_a = 0, V_b = original, V_tmp = original.
Loop V_tmp {
  V_a ← V_a + 1
}
-- Now V_a = original, V_tmp = 0.
```

This is two URM loops per preserving-transfer (the
double-increment loop plus the restoration loop). The
pattern is standard register-machine technique;
analogous decoupling appears in Tourlakis's per-Loop
scratch register `B` (p. 20), which serves the same
purpose of decoupling a loop's count from its variable.
The M-program for `λx.x` (p. 19) is a one-loop
specialisation that does *not* preserve the source
because λx.x is the output-from-V_2 case where source
preservation is unneeded.

**Prelude construction.** At compile time, `compileER`
walks `e` and counts `k_i` (the number of `proj i`
consumers of each input slot `i` for `i : Fin a`). The
prelude emits, for each input `i` and each consumer
index `j < k_i`, a fresh scratch register `V_src_{i,j}`
plus a preserving-transfer block `V_{inputRegs i} →
V_src_{i,j}` (two loops). After the prelude, all
consumers read from distinct `V_src_{i,j}` registers,
and per-template `proj i` may consume its assigned
scratch destructively. The original input registers are
preserved across the prelude.

Prelude instruction count: `O(k_i · t)` per input,
where `t` is the URM cost of two preserving-transfer
loops (each loop is constant-size + body); total is
linear in `Σ_i k_i`, hence linear in the size of `e`.

The per-ER-constructor templates above (§5.1) then use
destructive transfers only, reading from
prelude-prepared clones. The recursive `compileER`
allocates fresh PC labels and register indices via a
state-monad pattern (a `Nat`-valued counter for each).

#### 5.1.1 Per-iteration prologue for `bsum` and `bprod`

`bsum f` and `bprod f` translate to an outer Loop over
the bound variable (the recursion variable of the
bounded-recursion `g(i, y⃗, z)`). Per Tourlakis p. 21's
template, each outer iteration computes one application
of `f(i, y⃗)` and folds it into the accumulator. The
pre-clone-at-prelude discipline (which runs once at PC
0) does not handle re-cloning across iterations of an
outer loop. Each outer iteration therefore emits a
*per-iteration prologue* before invoking `compileER f`'s
instruction sequence:

1. Write the current iteration counter `i` into `f`'s
   slot-0 scratch register. `i` is held in a dedicated
   loop-index register `V_i` (initialised to 0 at the
   outer-loop entry, incremented at the end of each
   iteration); the prologue emits a preserving-transfer
   `V_i → f's slot-0 scratch`.
2. For each of `f`'s outer-parameter input slots (slots
   `1..arity(f) − 1`, i.e. every slot except `f`'s
   slot 0 which receives the iteration counter `i`
   per step 1), re-clone the corresponding outer-clone
   register `V_src_{j,k}` into `f`'s slot-j scratch via
   preserving-transfer. The outer clones (allocated by
   the prelude) are preserved across iterations because
   each preserving-transfer leaves the source intact.
3. Reset `f`'s output-register scratch to 0 (or to the
   accumulator value, depending on whether `f`'s
   compilation accumulates or overwrites — `compileER`'s
   convention is to write a fresh result into a fresh
   output register per invocation, so we just zero it).

After the prologue, `compileER f`'s instruction sequence
runs deterministically; the result is folded into the
outer accumulator (addition for `bsum`, multiplication
for `bprod`). Instruction count of the per-iteration
prologue is `O(arity(f))` preserving-transfers; total
overhead is `O(arity(f) · loop-bound)`, absorbed into
the `boundExprK e` runtime bound (§7).

#### 5.1.2 g-to-f wiring for `comp f gs`

Convention for `compileER` outputs: every
`compileER e' : URMProgram` allocates a fresh output
register `V_out_{e'}` on entry and writes its result
there at the time `stop` is reached. The caller of
`compileER e'` reads `V_out_{e'}` after the sub-URM's
PC range completes.

For `compileER (comp f gs)` with `f : ERMor1 b`,
`gs : Fin b → ERMor1 a`:

1. Allocate `V_out_{gs i}` for each `i : Fin b` (one
   register per sub-URM output).
2. Emit `compileER (gs 0)`, then `compileER (gs 1)`,
   …, then `compileER (gs (b-1))` in sequence,
   PC-shifted appropriately. After each sub-URM
   completes, its result sits in `V_out_{gs i}`.
3. Allocate `V_in_{f, 0}, …, V_in_{f, b-1}` as `f`'s
   input slot registers, and emit `b` destructive
   transfers `V_out_{gs i} → V_in_{f, i}` via the
   M-template (one loop per transfer). These
   transfers consume `V_out_{gs i}` and produce
   `V_in_{f, i}` holding `gs[i]`'s value.
4. Compile `f` recursively as `compileER f`, with `f`'s
   `inputRegs` mapping its slot `i` to `V_in_{f, i}`.
   `f`'s internal `proj k` constructors read from
   `V_in_{f, k}`, applying the pre-clone-at-prelude
   discipline (§5.1 prelude construction) locally to
   the sub-URM if a slot is read multiple times by `f`.
5. The result `V_out_{f}` is the output of
   `compileER (comp f gs)`.

This convention makes each sub-URM's prelude and
output register fully local: no sub-URM's register
indices collide with another's, and every `proj` read
inside `f` is satisfied by the prelude-prepared
clones of `V_in_{f, i}`.

### 5.2 Compiler correctness

```lean
def compileER_runtime : {a : ℕ} → ERMor1 a → (Fin a → ℕ) → ℕ

theorem compileER_runFor
    {a : ℕ} (e : ERMor1 a) (v : Fin a → ℕ)
    (t' : ℕ) (ht' : compileER_runtime e v ≤ t') :
    ((URMState.init (compileER e) v).runFor t').regs
      (compileER e).outputReg
    = e.interp v
```

`compileER_runtime e v` is the explicit Lean-`Nat`
runtime witness (no `∃`): structural recursion on `e`
returns the step count of the compiled URM on input `v`.
Atoms: constant (≤ 3 instructions). `comp f gs`: sum of
children's runtimes plus prelude overhead. `bsum f` /
`bprod f`: outer loop count `× (per-iteration prologue
cost + compileER_runtime f children)`. Theorem proof:
structural induction on `e` matching the per-template
analysis above.

Per Tourlakis §0.1.0.42 (p. 18): "any `λx⃗.f(x⃗) ∈ E^n` is
URM-computable within time `λx⃗.t(x⃗) ∈ E^n`" (Lemma
0.1.0.42, for `n ≥ 2`). Our case ER = E^3 corresponds to
Tourlakis's `n = 3` (within the `n ≥ 2` range the Lemma
covers). The `t` we construct here is in fact in ER for
our compiled URMs; we do not state this as a separate
theorem because §7 provides the K^sim-side bound.
(Tourlakis §0.1.0.43, p. 21, is the Ritchie–Cobham
equivalence containing this Lemma.)

## 6 Ksim simulator

### 6.1 The simulating functions

Direct transcription of Tourlakis §0.1.0.37 (p. 15–16). For
a URM `P` with `numRegs = m`, define `m + 1` simulating
functions by simultaneous primitive recursion on time:

- `v_i(y, x⃗) :=` value of register `V_i` in the y-th ID
  with input `x⃗`, for `i ∈ Fin m`.
- `I(y, x⃗) :=` PC value in the y-th ID with input `x⃗`.

In Tourlakis's notation (p. 16):

```text
v_i(0, x⃗) = (init-state regs[i] under x⃗)
I(0, x⃗)   = 0      -- our 0-indexed PC; Tourlakis uses 1
v_i(y+1, x⃗) = case on I(y, x⃗):
  if at pc k the instruction is "V_i ← c":           c
  if at pc k the instruction is "V_i ← V_i + 1":     v_i(y, x⃗) + 1
  if at pc k the instruction is "V_i ← V_i ∸ 1":     v_i(y, x⃗) ∸ 1
  otherwise:                                          v_i(y, x⃗)
I(y+1, x⃗) = case on I(y, x⃗):
  if "if V_i = 0 goto l₁ else goto l₂" and v_i(y) = 0: l₁
  if same instruction and v_i(y) > 0:                 l₂
  if "stop":                                          I(y, x⃗)
  otherwise:                                          I(y, x⃗) + 1
```

Each case is selected by the predicate `I(y, x⃗) = k` for
the specific PC label `k`. By Tourlakis §0.1.0.20 (p. 7),
`λx.x = a ∈ K^sim_{1,*}` (predicate at level 1), so the
predicate-level analysis closes. §6.2 realises the
selection without invoking general equality: PC dispatch
runs through a `cond`-chain on `pred^k(I)` (zero iff
`I = k`) rather than through `KMor1.eq`, keeping the
K^sim term at level 1 per §2.1's rationale.

### 6.2 Realisation as a Ksim term

```lean
def simulate (P : URMProgram) :
    KMor1 (1 + P.numInputs)
```

The argument list is `(y, x⃗)` where `y` is the time bound
and `x⃗` is the input vector. The output is `v_{outputReg}
(y, x⃗)` — the value of the output register at time `y`.

Implementation: a K^sim simrec with system size
`P.numRegs + 1`. The components are indexed by `Fin
(P.numRegs + 1)`; component `0` is `I(y, x⃗)`, components
`1..numRegs` are `v_0(y, x⃗), …, v_{numRegs−1}(y, x⃗)`. The
simrec's output index `i : Fin (P.numRegs + 1)` is
`P.outputReg + 1`.

#### Base case

For each component `j : Fin (P.numRegs + 1)`:

```text
h_0(x⃗) = 0                              -- I(0, x⃗) = 0
h_{j+1}(x⃗) = if j ∈ inputRegs.range
              then x⃗[inputRegs⁻¹ j]
              else 0                    -- v_j(0, x⃗)
```

Each base function is at K^sim level 0 (`zero`,
projections, fixed lookup).

#### Step case

For each component, the step function takes `(time-var,
x⃗, I_prev, v_0_prev, …)` and dispatches on `I_prev`.
Within each PC branch (selecting a specific instruction
`instrs[k]`), the per-component case analysis inspects
that specific instruction:

```text
step_0(prev_ctx) := PC-dispatch over I_prev = k for
  k = 0, …, instrs.size − 1:
    case instrs[k]:
      "if V_i = 0 goto l₁ else goto l₂":
        cond(v_i_prev, natK l₁, natK l₂)
      "stop":     I_prev
      _:          I_prev + 1

step_{j+1}(prev_ctx) := PC-dispatch over I_prev = k for
  k = 0, …, instrs.size − 1:
    case instrs[k]:
      "V_j ← c":             natK c
      "V_j ← V_j + 1":       v_j_prev + 1
      "V_j ← V_j ∸ 1":       v_j_prev ∸ 1
      any instruction not   v_j_prev
      mutating V_j:
```

The PC-dispatch is a nested chain of `cond` invocations:

```text
PC-dispatch over I_prev for k = 0, 1, …, instrs.size − 1:
  cond(I_prev,         branch_0,
       cond(I_prev ∸ 1, branch_1,
            cond(I_prev ∸ 2, branch_2,
                 … natK 0)))     -- default (unreachable)
```

`I_prev ∸ k` is zero iff `I_prev = k`. The chain has
length `instrs.size`. Each `cond` is level 1; each
`I_prev ∸ k` is `pred^k(I_prev)`, a composition of `pred`
(level 1) with itself `k` times; `cond` with level-1
arguments stays at level 1.

Each leaf branch is one of:

- `natK c` (level 0)
- `v_i_prev + 1` (i.e., `succ ∘ proj_{i+1+(a+1)}`; level 0)
- `v_i_prev ∸ 1` (i.e., `pred ∘ proj_{i+1+(a+1)}`; level 1)
- `v_i_prev` (i.e., `proj_{i+1+(a+1)}`; level 0)
- `I_prev` (`proj_{a+1}`; level 0)
- `I_prev + 1` (`succ ∘ proj_{a+1}`; level 0)
- `cond(v_i_prev, natK l₁, natK l₂)` (level 1)

All branches are at level ≤ 1. The PC-dispatch chain is at
level 1. The full step function is at level 1.

#### Level total

Simrec with system size `P.numRegs + 1`, base at level 0,
step at level 1: overall level `max(0, 1) + 1 = 2`.

This matches Tourlakis §0.1.0.37's conclusion: "All the
simulating functions are in K^sim_2" (p. 15).

### 6.3 Correctness theorem

```lean
theorem simulate_interp (P : URMProgram)
    (y : ℕ) (v : Fin P.numInputs → ℕ) :
    (simulate P).interp (Fin.cons y v)
      = ((URMState.init P v).runFor y).regs P.outputReg
```

Proof: induction on `y`. Base case: `simrec`'s base case
matches `URMState.init`'s register vector. Step case:
`simrec`'s step matches one `URMState.step` invocation,
case-by-case on the instruction at `pc`.

## 7 Ksim runtime bound

### 7.1 The bound expression

Per Tourlakis §0.1.0.44 proof (p. 22): for `f ∈ E^{n+1}`,
the runtime `t_f` of any URM computing `f` satisfies
`t_f(x⃗) ≤ A^r_n(max(x⃗))` everywhere, by §0.1.0.27
(p. 10). For our case `n+1 = 3` (ER = E^3), `n = 2` and
the bound is an iterated tower of exponentials in
`max(x⃗)`. We realise the bound as `r_e`-fold composition
of `KMor1.pow2` (`λx.2^x ∈ K^sim_2` per §0.1.0.17(c)).
The spec does not claim this literally equals `A^r_2`
(Tourlakis's Ackermann iteration is outside the project's
PDF excerpt); it claims only that an iterated tower of
`pow2` of finite height majorises the runtime, which is
what §0.1.0.44's proof scheme needs.

```lean
def boundExprK : {a : ℕ} → ERMor1 a → KMor1 a
```

For each `e : ERMor1 a`, `boundExprK e` is the K^sim term
`pow2_iter r_e ∘ maxOver a` where:

- `r_e : ℕ` is a Lean-level function of `e`'s structure
  (computed from the bsum/bprod nesting depth of `e` and
  the constants accumulated through composition;
  recursion shape in §7.2).
- `maxOver a : KMor1 a` is the `a`-ary maximum named
  composite (§3.1).
- `pow2_iter r_e : KMor1 1` is `r_e`-fold composition of
  `KMor1.pow2` applied to `proj 0`.

`boundExprK e` has K^sim level 2: `maxOver` is level 2,
`pow2_iter` is level 2 (composition of `pow2`'s), and
their composition stays at level 2.

### 7.2 Construction of `r_e`

`r_e : ℕ` is defined by structural recursion on `e` such
that `boundExprK_dominates` (§7.3) holds. The spec does not
pin concrete constants; the implementation derives them by
structural induction on `e` following Tourlakis §0.1.0.42
proof (pp. 18–21). The recursion shape is:

- Atoms (`zero`, `succ`, `proj i`, `sub`): `r_e` is a
  small constant.
- `comp f gs`: `r_e` is monotone in `r_f` and the
  `r_{gs i}`'s; the proof appeals to Tourlakis p. 21's
  concatenation argument plus the substitution-stability
  of §0.1.0.27(4).
- `bsum f`, `bprod f`: `r_e = r_f + c` for some constant
  `c ≥ 1`; the bounded-recursion case of §0.1.0.42's
  induction is what raises the Ackermann level by a
  constant.

The spec commits only to the recursion *shape*: `r_e` is
non-decreasing in the `r`'s of `e`'s subexpressions, and
strictly increases at `bsum`/`bprod` (the bounded-recursion
case). Concrete constants are determined during
implementation. The level claim (level 2) is independent
of the specific constants: `pow2_iter r` is at level 2
for every `r`.

### 7.3 Domination theorem

To state §7.3 constructively, §5.2's `compileER_runFor`
returns the runtime witness as an explicit Lean-`Nat`
function `compileER_runtime : ERMor1 a → (Fin a → ℕ) →
ℕ` (no `∃`), with the per-template `t_e(v)` computed by
structural recursion on `e` (atoms: constant; comp: sum
of children plus prelude overhead; bsum/bprod: outer
loop count times inner runtime plus per-iteration
prologue cost).

The intermediate lemma:

```lean
theorem boundExprK_majorizes_runtime {a : ℕ}
    (e : ERMor1 a) (v : Fin a → ℕ) :
    compileER_runtime e v ≤ (boundExprK e).interp v
```

is proved by structural induction on `e`, with `r_e`
(§7.2) chosen large enough to dominate at each
constructor. The domination theorem follows:

```lean
theorem boundExprK_dominates {a : ℕ} (e : ERMor1 a)
    (v : Fin a → ℕ) :
    ∀ s ≥ (boundExprK e).interp v,
      ((URMState.init (compileER e) v).runFor s).regs
        (compileER e).outputReg
      = e.interp v
```

Proof: `s ≥ (boundExprK e).interp v ≥ compileER_runtime
e v` (by `boundExprK_majorizes_runtime`), then apply
`compileER_runFor` with `t := compileER_runtime e v`.

## 8 erToK assembly (`GebLean/LawvereERKSim.lean`)

### 8.1 Definition

Direct transcription of Tourlakis §0.1.0.44 proof line
`f = λx⃗. v_1(A^r_n(max x⃗), x⃗)` (p. 22), with `n = 2`:

```lean
def erToK {a : ℕ} (e : ERMor1 a) : KMor1 a :=
  KMor1.comp (simulate (compileER e))
    (Fin.cons (boundExprK e) (fun i => KMor1.proj i))
```

The first argument of `simulate` is the time bound
(`boundExprK e`); the remaining `a` arguments are the
projections `proj_0, …, proj_{a−1}` placing the ER inputs
into the simulator's input slots. The simulator's output is
the value of `compileER e`'s output register after running
for `boundExprK e` steps, which equals `e.interp v` by
§5.2 + §7.3 + §6.3.

### 8.2 Level bound

```lean
theorem erToK_level {a : ℕ} (e : ERMor1 a) :
    (erToK e).level ≤ 2
```

`simulate (compileER e)` is at level 2 (§6.2);
`boundExprK e` is at level 2 (§7.1); projections are at
level 0; composition takes `max` over children and adds 0
(per `KMor1.level`'s `.comp` case at
`LawvereKSim.lean:109`). So `erToK e` is at level 2.

### 8.3 Interpretation preservation

```lean
theorem erToK_interp {a : ℕ} (e : ERMor1 a)
    (v : Fin a → ℕ) :
    (erToK e).interp v = e.interp v
```

Proof:

1. `simulate_interp` (§6.3) gives
   `(simulate (compileER e)).interp
   (Fin.cons ((boundExprK e).interp v) v)
   = ((URMState.init (compileER e) v).runFor
   ((boundExprK e).interp v)).regs (compileER e).outputReg`.
2. `boundExprK_dominates` (§7.3) gives
   `((URMState.init (compileER e) v).runFor
   ((boundExprK e).interp v)).regs (compileER e).outputReg
   = e.interp v`.
3. Compose: `(erToK e).interp v = e.interp v`. ∎

### 8.4 Functor lift

```lean
def erToKN {a m : ℕ} (e : ERMorN a m) : KMorN a m :=
  fun i => erToK (e i)

theorem erToKN_interp {a m : ℕ} (e : ERMorN a m)
    (v : Fin a → ℕ) (i : Fin m) :
    (erToKN e i).interp v = (e i).interp v

def erToKFunctor : LawvereERCat ⥤ LawvereKSimDCat 2 where
  obj n := n
  map ⟦e⟧ := ⟦erToK e, erToK_level e⟧
  map_id := /- via erToK_interp -/
  map_comp := /- via erToK_interp -/
```

Functor laws follow from `erToK_interp` plus quotient-class
equality (`LawvereERQuot.lean`, `LawvereKSimQuot.lean`).

## 9 Module layout

Two new files (`LawvereERKSim.lean` for the ER → K
direction here is distinct from the already-landed
`LawvereKSimER.lean` for the K → ER direction):

```text
GebLean/Utilities/ZeroTestURM.lean
  - URMInstr inductive (5 cases per §0.1.0.37)
  - URMProgram structure
  - URMState structure and step/runFor
  - URMState.init via Fin.find

GebLean/LawvereERKSim.lean
  - compileER : ERMor1 a → URMProgram (§5)
  - compileER_runFor correctness (§5.2)
  - simulate : URMProgram → KMor1 (1 + numInputs) (§6)
  - simulate_interp correctness (§6.3)
  - KMor1.natK, KMor1.maxK, KMor1.maxOver,
    KMor1.pow2_iter (§3.1)
  - boundExprK : ERMor1 a → KMor1 a (§7.1)
  - boundExprK_dominates (§7.3)
  - erToK : ERMor1 a → KMor1 a (§8.1)
  - erToK_level, erToK_interp (§8.2, §8.3)
  - erToKN, erToKN_interp (§8.4)
  - erToKFunctor (§8.4)
```

Re-exports updated in `GebLean.lean` per project policy.

### 9.1 Dependency graph

```text
Utilities.ZeroTestURM: depends on Lean core and on
  lightweight mathlib helpers: `Mathlib.Data.List.FinRange`
  for `List.finRange`, `Mathlib.Logic.Function.Basic` for
  `Function.update`. Lean core supplies `List.find?` and
  the basic `Fin`/`Array` machinery.

LawvereERKSim: depends on
  GebLean.LawvereER, GebLean.LawvereERInterp,
  GebLean.LawvereERQuot, GebLean.LawvereKSim,
  GebLean.LawvereKSimInterp, GebLean.LawvereKSimQuot,
  GebLean.Utilities.KArith,
  GebLean.Utilities.ZeroTestURM.
```

No imports from `LawvereKSimER` (the kToER side); the two
halves of the equivalence are independent until the
categorical-iso spec composes them.

## 10 Constructive discipline

- No `noncomputable` declarations.
- No `Classical.choice`, `Classical.choose`, `Classical.em`
  in any definition or proof.
  `URMState.init` uses Lean core's `List.find?` over
  `List.finRange P.numInputs` (not `Classical.choose`).
- No `axiom`. No `admit`.
- `sorry` permitted only between commits per `CLAUDE.md`;
  not in committed code.
- Verified post-implementation by `scripts/check-axioms.sh`
  on the cycle's pre-commit checklist.

## 11 Step decomposition

Replacing master-design steps 6–10:

- **Step T1 — URM kernel.** `Utilities/ZeroTestURM.lean`.
  Inductive type, semantics, runFor, init. ≈ 100 Lean
  lines. One review round expected.
- **Step T2 — Per-ER-constructor compiler templates and
  correctness.** `compileER` and `compileER_runFor` in
  `LawvereERKSim.lean`. The bulk of new template work
  lives here. ≈ 400–600 Lean lines. Two to three review
  rounds expected.
- **Step T3 — K^sim simulator.** `simulate` and
  `simulate_interp`, plus the four supporting K^sim
  composites of §3.1 (`natK`, `maxK`, `maxOver`,
  `pow2_iter`). ≈ 300–500 Lean lines. Two review rounds
  expected.
- **Step T4 — Runtime bound.** `boundExprK` and
  `boundExprK_dominates`. ≈ 200–300 Lean lines. One to
  two review rounds expected.
- **Step T5 — `erToK` assembly + functor.** `erToK`,
  `erToK_interp`, `erToK_level`, `erToKN`,
  `erToKFunctor`. ≈ 150–250 Lean lines. One review round
  expected.

Critical path: T1 → T2 → T4 → T5; T3 parallels T2 but
precedes T4 (since T4 consumes the K^sim composites
`pow2_iter`, `maxOver` built in T3). The strict iso
(master design §11) is its own subsequent spec.

## 12 Adversarial-review punch list

The round-N adversary (per
[`docs/process.md`](../../process.md) § Adversarial review)
verifies each claim below and reports findings in
`.review-N.md`.

The most important obligation: **every named construction
in §§3.1, 4, 5, 6, 7, 8 has at least one citation, and
every cited claim is verifiable at the cited source.**
Citations of two kinds:

- External (Tourlakis 2018 §-N, page P, with the exact
  wording the citation is meant to ground).
- Internal (`File.lean:line` for any existing repository
  artefact reused).

### 12.1 Constructive discipline preserved

Claim: no `Classical.*` or `noncomputable` in any
committed declaration or proof. Adversary obligation:
grep the post-cycle codebase plus the in-spec
`URMState.init` definition;
confirm `List.find?` is used, not `Classical.choose`.

### 12.2 ZeroTestURM matches Tourlakis §0.1.0.37

Claim: §4.1's `URMInstr` has exactly the five cases of
§0.1.0.37 (Tourlakis p. 16). Adversary obligation: read
p. 16 case-by-case against `URMInstr`'s constructors;
flag any mismatch.

### 12.3 §0.1.0.37 simulation lemma transcription

Claim: §6.1's `v_i` and `I` recursion equations are the
same as Tourlakis p. 16 line-by-line, modulo 0-indexed vs
1-indexed PC. Adversary obligation: tabulate each
recursion equation against Tourlakis p. 16; verify the
0-indexed shift is consistent across base and step.

### 12.4 §0.1.0.44 proof transcription

Claim: §8.1's `erToK e := comp (simulate (compileER e))
[boundExprK e, proj_0, …, proj_{a−1}]` matches Tourlakis
p. 22 `f = λx⃗. v_1(A^r_n(max x⃗), x⃗)` for `n = 2`.
Adversary obligation: trace each piece of the Lean
definition against the Tourlakis formula; verify the
runtime argument `boundExprK e` corresponds to `A^r_n(max
x⃗)`.

### 12.5 Level claim for `simulate`

Claim: §6.2 step function is at K^sim level ≤ 1; outer
simrec adds 1 → level 2. Adversary obligation: trace
`KMor1.level` (`LawvereKSim.lean:105`) on the step's
constructors. Confirm `cond` is level 1, `pred` is level
1, `succ` is level 0, `proj` is level 0, `natK c` is level
0, all chains and compositions preserve level. No
`KMor1.eq` (level 2) anywhere.

### 12.6 Level claim for `boundExprK`

Claim: §7.1's `boundExprK e` is at K^sim level ≤ 2.
Adversary obligation: trace `KMor1.level` on `pow2` (level
2), `maxK` (level 2), `maxOver` (level 2), and their
compositions; confirm no level-3 escapes.

### 12.7 Every construction has a citation

For each new named construction in §3.1, §4, §5, §6, §7,
§8 (URMInstr, URMProgram, URMState, step, runFor, init,
compileER, simulate, natK, maxK, maxOver, pow2_iter,
boundExprK, erToK, erToKFunctor, plus the per-template
sub-constructions in §5.1), check that the spec cites
either:

- the Tourlakis §, p. that establishes the construction's
  shape; or
- an internal repository module:line that this
  construction reuses.

Flag any construction without a citation, or any citation
that does not match the cited source. Spot-check 4–6
citations by reading the cited page.

### 12.8 Per-template correctness coverage

Claim: §5.1's seven per-ER-constructor templates each
produce a URM that correctly computes the ER constructor's
interpretation. Adversary obligation: walk through each
template's instruction sequence by hand for one small
input; confirm the URM trace reaches a halted state with
the expected output. Pay special attention to register
allocation (no template overwrites another's working
register) and PC label offset (subprogram inlining
preserves `goto` and `if … goto` target validity).

### 12.9 No phantom infrastructure

Claim: this spec does not specify any construction that is
not required for §8's `erToK_interp` proof. Adversary
obligation: trace the proof obligation of `erToK_interp`
(§8.3) backwards through §7.3, §6.3, §5.2; verify each
construction in §§3.1, 4, 5, 6, 7 contributes to that
trace. Flag any orphan construction.

### 12.10 Independence from kToER side

Claim: no import in `ZeroTestURM.lean` or
`LawvereERKSim.lean` resolves to `LawvereKSimER` or
`LawvereKSimMajorization`. Adversary obligation: trace
the §9.1 dependency graph against the actual imports
emitted into the new files.

### 12.11 No CSLib-URM-driven infrastructure

Claim: this spec does not import any of CSLib's URM
modules (`Cslib.Computability.URM.*`); the URM kernel
is the own `Utilities/ZeroTestURM.lean`. Adversary
obligation: grep the new modules for `import Cslib` and
for references to `Cslib.URM.*` names; expect zero
matches.

## 13 Citations

### 13.1 External (Tourlakis 2018, `PR-complexity-topics.pdf`)

- §0.1.0.2 (p. 1): definition of K_n (Axt–Heinermann
  hierarchy).
- §0.1.0.4 (p. 2): `λx.A_n(x) ∈ K_n` (Ackermann function
  at level n).
- §0.1.0.7 (p. 3): definition of K^sim_n.
- §0.1.0.9 (p. 3): `λx.A_n(x) ∈ K^sim_n`.
- §0.1.0.17 (p. 6): catalogue of K^sim functions.
  Subitems used: (1) `λxy.x+y ∈ K_1`; (3) `λx.1 ∸ x ∈
  K_1`; (4) `λx.x ∸ 1 ∈ K_1`; (6) `switch ∈ K_1`; (a)
  `λxy.x ∸ y ∈ K_2`; (b) `λxy.xy ∈ K_2`; (c) `λx.2^x ∈
  K_2`.
- §0.1.0.20 (p. 7): `λx.x = a ∈ K^sim_{1,*}`,
  `λx.x ≤ a ∈ K^sim_{1,*}`, `λx.x < a ∈ K^sim_{1,*}`.
- §0.1.0.27 (p. 10): bounding lemma. Parts (3) and (4)
  used: `f ∈ E^2` ⇒ `f(x⃗) ≤ C · max(x⃗)^n + k`;
  `f ∈ E^{n+1}, n ≥ 2` ⇒ `f(x⃗) ≤ A^k_n(max(x⃗))`.
- §0.1.0.36 (p. 15): definition of "runtime majorisation"
  for a URM.
- §0.1.0.37 (p. 15–16): **simulation lemma.** The
  transcription source for §6 of this spec. Sets up
  `v_i`, `I` simulating functions with their recursion
  equations; concludes "All the simulating functions are
  in K^sim_2."
- §0.1.0.42 (p. 18): `λx⃗.f(x⃗) ∈ E^n` ⇒ `λx⃗.f(x⃗)` is
  URM-computable within time `λx⃗.t(x⃗) ∈ E^n`. Used in
  §5.2 to ground the runtime witness's existence.
- §0.1.0.43 (p. 21): Ritchie–Cobham property. Used as
  framing for §5–§7 (the runtime bound is in ER for any
  ER expression).
- §0.1.0.44 (p. 22): `K^sim_n = E^{n+1}`. Used in §8.1 as
  the source of `erToK`'s shape `f = λx⃗. v_1(A^r_n(max
  x⃗), x⃗)`.
- pp. 19–21 worked URM examples and templates:
  - M URM for `λx.x` (p. 19) — single-loop destructive
    transfer of V_2 into V_1.
  - N URM for `λx.x+1` (p. 19) — M plus extra
    increment.
  - R^XY_Z URM for `λxy.xy` (p. 19) — nested-loop
    multiplication.
  - Loop-to-URM translation template (p. 20) with
    per-Loop scratch register B.
  - Bounded-recursion URM template (p. 21) — basis
    `z ← h(y⃗)`, iterator `z ← g(i, y⃗, z)`, decrement
    of bound register per iteration.

### 13.2 Internal repository references

- `GebLean/LawvereKSim.lean:34` — `KMor1` inductive
  definition.
- `GebLean/LawvereKSim.lean:105` — `KMor1.level`.
- `GebLean/LawvereKSim.lean:137` — `KMor1.rec1` (single-
  output simrec specialisation).
- `GebLean/LawvereKSim.lean:154` — `KMor1.permArgs`
  (precomposition with projections).
- `GebLean/LawvereKSimInterp.lean:22` — `KMor1.interp`.
- `GebLean/LawvereKSimInterp.lean:162` —
  `KMor1.interp_simrec` simp lemma (public face of the
  simrec interp recursion; the private helper
  `KMor1.interp_simrec_eq_simrecVec` begins at line 122).
- `GebLean/Utilities/KArith.lean:31` — `KMor1.one`
  (constant 1).
- `GebLean/Utilities/KArith.lean:44` — `KMor1.pred`
  (level 1).
- `GebLean/Utilities/KArith.lean:78` — `KMor1.isZero`
  (level 1).
- `GebLean/Utilities/KArith.lean:111` — `KMor1.add`
  (level 1).
- `GebLean/Utilities/KArith.lean:222` — `KMor1.cond`
  (Tourlakis switch, level 1).
- `GebLean/Utilities/KArith.lean:249` — `KMor1.interp_cond`
  simp lemma.
- `GebLean/Utilities/KArith.lean:301` — `KMor1.mult`
  (level 2).
- `GebLean/Utilities/KArith.lean:403` — `KMor1.monus`
  (level 2).
- `GebLean/Utilities/KArith.lean:500` — `KMor1.pow2`
  (level 2).
- `GebLean/LawvereKSimQuot.lean` — `KMorNQuo`, quotient by
  extensional interp equality, `LawvereKSimDCat`.
- `GebLean/LawvereERQuot.lean` — `ERMorNQuo`,
  `LawvereERCat`.
- Master design (`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`)
  — overall framing of the kToER ↔ erToK equivalence project.
- Internal Appendix A (`docs/lawvere-k-sim-hierarchy.md`)
  — informational background; this spec re-derives the
  construction directly from Tourlakis 2018 rather than
  via Appendix A's intermediate transcription, but
  Appendix A's lines 1223–1310 served as cross-check
  during round-2 revisions.

## 14 Out of scope

- The strict categorical iso `kToERFunctor ⋙ erToKFunctor
  = 𝟭` and reverse (master design §11). Becomes its own
  spec once §8.4's `erToKFunctor` lands.
- K^sim ⊇ K_n for n > 2. The construction generalises
  (Tourlakis §0.1.0.44 covers `n ≥ 2`), but this spec
  targets n+1 = 3 (i.e., ER = E^3).
- CSLib's `Cslib.URM` (Shepherdson–Sturgis URM with
  equality-jump primitive). Not imported by this spec;
  see §2.1 for the rationale.
- Replacement of `GebLean/Utilities/RegisterMachine.lean`
  (the abstract register-machine kernel used elsewhere in
  the project, e.g. by `LawvereTreeERArith.lean`). Out of
  scope here.
