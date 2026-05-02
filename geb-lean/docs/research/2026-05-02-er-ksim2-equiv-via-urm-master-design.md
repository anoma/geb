# Master design — ER ↔ K^sim_2 categorical equivalence via URM simulation

> **Status.** Step 0 master design. Awaits adversarial review and
> user sign-off before per-step cycles begin.
>
> **Position in the project.** Supersedes the direct-translation
> `kToER` strategy (preserved as renamed `kToERDirect` /
> `kToERNDirect` infrastructure with proven level-0 and level-1
> dominance results) per the architectural pivot recorded in
> `docs/research/2026-05-02-ksim-to-er-architectural-pivot-handoff.md`.
> Provides the master structure within which twelve subsequent
> brainstorm + writing-plans + adversarial-review cycles execute,
> closing both `kToER` and `erToK` directions on a shared URM
> kernel.

---

## §1 Status and motivation

### §1.1 What the prior strategy attempted

The direct-translation `kToER : KMor1 → ERMor1` (now renamed
`kToERDirect`) translated each K^sim morphism to an `ERMor1` term
by structural recursion. The simrec case used
`ERMor1.boundedRec base step bound` with a bespoke
`kSimTowerBound` ER expression giving a pointwise tower-of-
exponentials bound on the K^sim function value. Five plan
iterations attempted to discharge the dominance theorem
`kSimTowerBound_dominates_inline`. All failed at related load-
bearing claims (impossible PolyBound assumptions, false bounds at
level-1 children, glossed `Nat.rec` ↔ `Nat.iterate` bridges, false
absorption inequalities involving a `3^E` coefficient field).

### §1.2 Why the strategy was misaligned with the literature

The published proofs of the elementary-recursive ↔ K^sim
equivalence (notation: Tourlakis 2018 §0.1.0.44,
`K^sim_n = E^{n+1}` for n ≥ 2; the `E^{n+1}` here is the
Grzegorczyk-hierarchy notation that the literature uses
interchangeably with our `ERMor1` formalization at n+1 = 3 —
see §1.4) do not construct an ER expression that bounds the
K^sim function's value pointwise. They route through
register-machine simulation: Tourlakis's §0.1.0.44 reduces
to §0.1.0.43 (Ritchie–Cobham property) and §0.1.0.15
(`K^sim_n = L_n`). Ritchie–Cobham, in our project's
terminology, states that a function is in ER iff it is
computable on some URM with runtime bounded by an ER
expression. The bound is on URM *runtime*, not on the
function's *value*.

The asymmetry of the project's prior strategy is also visible:
the `erToK` direction had been designed via URM simulation per
Appendix A of `docs/lawvere-k-sim-hierarchy.md`, whereas
`kToERDirect` used direct categorical translation. Symmetric
literature alignment requires URM simulation in both directions.

### §1.3 What this design closes

A URM kernel definition with Tourlakis's six primitive
instructions (cited Tourlakis 2018 §0.1.0.43 proof, p. 19);
catalogues of URM subroutines emulating each ER and K^sim
constructor and of ER and K^sim subroutines emulating each URM
primitive; per-program compilers and per-URM simulators
constructed as one-line `match` over source-language constructors
or URM instructions; runtime-bound bookkeeping via a
`URMComputes` structure carrying a Lean step-bound function plus
a tower-witness; functor liftings; strict categorical
isomorphism `LawvereERCat ≅ LawvereKSimDCat 2` packaged as a mathlib
`Equivalence`.

### §1.4 What "ER" means in this project, and what it does not

This project formalizes a specific construction of the
elementary-recursive functions:

- The morphism inductive `ERMor1` with constructors `zero`,
  `succ`, `proj`, `sub`, `comp`, `bsum`, `bprod` (per
  `GebLean/LawvereER.lean`), matching Wikipedia's
  elementary-recursive-function definition.
- The categorical packaging `LawvereERCat` (objects `ℕ`,
  morphisms quotients of `ERMor1` by extensional equality of
  interpretations).

The literature commonly characterizes the same function class
as `E^3`, the third level of the Grzegorczyk hierarchy. The
two are provably equivalent — the same total functions on `ℕ`
arise — but are constructed quite differently: the
Grzegorczyk hierarchy is built iteratively, with each level
`E^{n+1}` obtained from `E^n` by closing under bounded
recursion using a level-`n` bounding function. **This
project does not formalize the Grzegorczyk construction, and
every step in the proof chain below uses ER directly without
invoking the ER ↔ E^3 equivalence as a logical dependency.**

Throughout this design, when literature citations refer to
`E^n` or `E^3` (notably Tourlakis 2018 §0.1.0.27, §0.1.0.43,
§0.1.0.44), those references are used for the proof
**structure** that they exhibit (URM simulation, runtime
bound shape, hierarchy correspondence) — not as logical
dependencies. Concretely: every claim of the form "this
expression is in `E^n`" in the literature is replaced in our
proof by "this expression is in `ER`" by direct construction
in our `ERMor1` inductive plus its named composites
(`pred`, `discN`, `boundedRec`, etc., per `Utilities/ERArith.lean`
and `LawvereERPolynomialBound.lean`). The cited literature
guides what to construct; the constructions live entirely
inside our `ERMor1` formalization.

The bound shape `tower h (linear of inputs)` for fixed `h ≤
2` is itself in ER directly: `2^x ∈ ER` (Tourlakis 2018
§0.1.0.17 (c) gives this construction in K^sim, and the same
construction applies in ER using `bsum`/`bprod`-based bounded
exponentiation), iterated `h` times stays in ER by closure
of ER under composition.

---

## §2 The 0–11 cycle structure

Each cycle consists of brainstorming + sequential-thinking +
writing-plans, followed by adversarial brainstorming + sequential-
thinking, iterated until convergence. Per CLAUDE.md's literature-
citation discipline (transcription workstreams), every planned
function, definition, or theorem in the cycle's plan carries a
literature reference; every implemented entity carries the same
reference in its docstring.

### Step 0 — Master design (this document)

Lays out the full structure. Adversarial review obligated to
re-run the prior failure-mode hypotheses (§14) against the
proposal.

### Step 1 — `RegisterMachine.lean` audit and gap-fill

Audit the existing 166-line `GebLean/Utilities/RegisterMachine.lean`
for sufficiency relative to §3 below. Likely outcome: small
additive lemmas (sequence-of-steps composition over arbitrary
configs; possibly a multi-input `ElementaryBound` parallel
structure). May be near-empty.

### Step 2 — `URMConcrete.lean`

Define `URMInstr` (Tourlakis's six primitives), `URMProgram`,
`toRegisterMachine`, the `URMComputes` structure (§3.4), and the
composition combinators `urmSeq`, `urmIf`, `urmLoop` (§4) with
both stepBound arithmetic and tower-witness arithmetic.

### Step 3 — ER simulator for URM (`ERSubroutinesURM.lean`)

Catalogue: ER subroutines emulating each URM primitive instruction.
Per-URM simulator combinator (`simulateInER : URMProgram →
ERMorN ...`) using the catalogue plus a PC-dispatch tree over
the program's instructions and `boundedRec` over time. Validates
that ER as a target language is rich enough to host a URM
simulator before the harder runtime-bound work.

### Step 4 — K^sim_2 → URM compiler (`URMSubroutinesKSim.lean` and the compiler)

Catalogue: URM subroutines emulating each `KMor1` constructor at
level ≤ 2, each carrying a `URMComputes` proof. Compiler
`compileKSim : KMor1 a → KMor1.level f ≤ 2 → URMProgram` defined
as a one-line `match` over `KMor1` constructors. Validates that
URM as a target is rich enough to express K^sim_2.

### Step 5 — ER runtime bound on the compiled URM

For each `f : KMor1 a` of level ≤ 2, construct the runtime-bound
ER expression `boundExpr f : ERMor1 a` and prove
`(compileKSim f).URMComputes.stepBound ≤ boundExpr f.interp`. The
bound shape is `tower h_f (vMax v + offset_f)` where `h_f` and
`offset_f` are computed from `f`'s simrec nesting; `boundExpr f`
is constructed in ER as iterated `2^x` per Tourlakis 2018
§0.1.0.27 (4) plus a linear shift.

### Step 6 — Compose into the `kToER` functor

`kToER : KMor1 a → KMor1.level f ≤ 2 → ERMor1 a` defined as
`simulateInER (compileKSim f) (boundExpr f, project_inputs, zeros)`
followed by output-register projection. Multi-output `kToERN`,
quotient-lift to `kToERFunctor : LawvereKSimDCat 2 ⥤ LawvereERCat`,
interp-preservation `kToER_interp`, functor laws.

### Step 7 — K^sim_2 simulator for URM (`KSimSubroutinesURM.lean`)

Mirror of step 3. Catalogue: K^sim subroutines emulating each
URM primitive instruction. `simulateInKSim : URMProgram →
KSimMorN ...` using the catalogue plus PC-dispatch and `simrec`
over time. (This is the construction described prose-only in
Appendix A.3 of `docs/lawvere-k-sim-hierarchy.md`; this cycle
realizes it in Lean.)

### Step 8 — ER → URM compiler (`URMSubroutinesER.lean` and the compiler)

Mirror of step 4. Catalogue: URM subroutines emulating each
`ERMor1` constructor (`zero`, `succ`, `proj`, `sub`, `comp`,
`bsum`, `bprod`), each with `URMComputes`. Compiler
`compileER : ERMor1 a → URMProgram` as a one-line `match`.

### Step 9 — K^sim_2 runtime bound on the compiled URM

Mirror of step 5. For each `e : ERMor1 a`, construct
`boundExprK e : KMor1 a` of level ≤ 2 and prove
`(compileER e).URMComputes.stepBound ≤ boundExprK e.interp`. Shape:
`tower h_e (vMax v + offset_e)` constructed in K^sim using
`2^x ∈ K^sim_2` per Tourlakis §0.1.0.17 (c).

### Step 10 — Compose into the `erToK` functor

Mirror of step 6. `erToK : ERMor1 a → KMor1 a` of level ≤ 2,
multi-output `erToKN`, `erToKFunctor : LawvereERCat ⥤
LawvereKSimDCat 2`, `erToK_interp`, functor laws.

### Step 11 — Categorical isomorphism (`LawvereERKSimEquivalence.lean`)

Strict equality `kToERFunctor ⋙ erToKFunctor = 𝟭 (LawvereKSimDCat 2)` and
`erToKFunctor ⋙ kToERFunctor = 𝟭 LawvereERCat`. Each holds
because both functors preserve interpretation pointwise, the
morphism categories are quotients by extensional-equality of
interpretations, and both functors are identity on objects.
Mathlib `Equivalence` derived as a wrapper (the candidate is
`equivOfIso` or the `Equivalence.mk` constructor with
`eqToIso`-built unit and counit; pin down exact API at this
cycle).

### Parallelization

Steps 3 and 4 share only the URM definition from step 2 and
operate on disjoint catalogues; they may be developed
concurrently via `superpowers:subagent-driven-development`.
Same for the mirror pair, steps 7 and 8. Steps 5 and 9 depend
on their preceding compiler step; steps 6 and 10 depend on
3-or-7 plus 4-or-8 plus 5-or-9.

### Per-step expected size

| Step | Expected size |
|---|---|
| 0 | This document; ~25 pages |
| 1 | Empty or near-empty cycle |
| 2 | Substantial; URM kernel + combinators |
| 3 | Substantial; ER simulator catalogue + assembly |
| 4 | Substantial; K^sim → URM catalogue + compiler |
| 5 | Medium; runtime-bound construction + dominance proof |
| 6 | Medium; functor lifting + interp-preservation |
| 7 | Substantial (mirror of step 3) |
| 8 | Substantial (mirror of step 4) |
| 9 | Medium (mirror of step 5) |
| 10 | Medium (mirror of step 6) |
| 11 | Small; categorical packaging |

---

## §3 URM definition

### §3.1 Primitives

Tourlakis 2018 §0.1.0.43 proof, PR-complexity-topics.pdf p. 19,
exhibits URMs with the following six instruction types
(transliterated from Tourlakis's notation):

```lean
inductive URMInstr (r : ℕ) : Type
  | zeroReg   (i : Fin r)              : URMInstr r
  | incReg    (i : Fin r)              : URMInstr r
  | decReg    (i : Fin r)              : URMInstr r
  | condJump  (i : Fin r) (t : ℕ)      : URMInstr r
  | gotoInstr (t : ℕ)                  : URMInstr r
  | stop                               : URMInstr r
```

Semantics on PC and register vector:

| Instruction | PC update | Register update |
|---|---|---|
| `zeroReg i` | `pc + 1` | `regs[i] := 0` |
| `incReg i` | `pc + 1` | `regs[i] := regs[i] + 1` |
| `decReg i` | `pc + 1` | `regs[i] := regs[i] ∸ 1` (truncated) |
| `condJump i t` | `t` if `regs[i] = 0`, else `pc + 1` | unchanged |
| `gotoInstr t` | `t` | unchanged |
| `stop` | `pc` (self-loop) | unchanged |

**Note on `condJump` shape.** Tourlakis's literal notation is
two-target: `if V_i = 0 goto m else goto m'`. Our `condJump i
t` is one-target: jump to `t` on zero, fall through to `pc + 1`
otherwise. Tourlakis's two-target form is recovered by a named
composite `condJumpTwoTarget i t1 t2 := condJump i t1;
gotoInstr t2`, which is the first entry of the helper-named-
composite catalogue. Expressively identical; the simplification
reduces the simulator's per-instruction case arity by one
branch.

### §3.2 `URMProgram`

```lean
structure URMProgram where
  numRegs : ℕ
  instrs : List (URMInstr numRegs)
  outputReg : Fin numRegs
```

A program is a finite list of instructions over a fixed register
arity, plus a designated output register. The PC ranges over
`{0, …, instrs.length}`; PC = `instrs.length` is the implicit
halt state (no instruction at that index, transition self-loops).

### §3.3 Link to abstract `RegisterMachine`

```lean
def URMProgram.toRegisterMachine (P : URMProgram) :
    RegisterMachineNS.RegisterMachine where
  numStates := P.instrs.length + 1
  numRegs := P.numRegs
  startState := 0
  transition := fun pc regs =>
    match P.instrs[pc.val]? with
    | none => (pc, regs)                          -- halt fixpoint
    | some instr => instrSemantics instr pc regs
```

`instrSemantics` dispatches on the instruction and returns
`(new_pc, new_regs)` per the table in §3.1. Out-of-range PC is a
self-loop. The existing `step`, `run`, `runFromConfig`, `runReg`
operations in `RegisterMachine.lean` apply to
`P.toRegisterMachine` immediately.

### §3.4 `URMComputes` — correctness with bound

```lean
structure URMComputes
    (P : URMProgram)
    (n : ℕ)
    (initRegs : Fin n → Fin P.numRegs)
    (outReg : Fin P.numRegs)
    (f : (Fin n → ℕ) → ℕ) where
  stepBound : (Fin n → ℕ) → ℕ
  correct :
    ∀ v t, stepBound v ≤ t →
    runReg P.toRegisterMachine
           (initialRegsFrom v initRegs) t outReg = f v
  towerHeight : ℕ
  towerOffset : ℕ
  towerDominates :
    ∀ v, stepBound v ≤ tower towerHeight (vMax v + towerOffset)
```

Where `initialRegsFrom v initRegs : Fin P.numRegs → ℕ` places `v`
at the indices listed by `initRegs` and 0 elsewhere; `vMax v` is
`Fin.foldr max 0 v` (zero on empty input).

`initRegs` is required to be injective: the URM's input
register-slots are distinct. The compiler ensures this by
allocating fresh register indices for each input. The
injectivity hypothesis is carried as a separate field of
`URMComputes` (or as a precondition on the structure's
constructor); concrete encoding to be settled at step 2.

The fields' meanings:

- `stepBound` — Lean `Nat`-valued function expressing the URM's
  exact step count as ordinary arithmetic on the input vector.
  Composes naturally under sequential / conditional / loop
  combinators (§4).
- `correct` — once at least `stepBound v` steps have elapsed, the
  output register holds `f v`. Uses `≤ t`, not `= stepBound`,
  because the `stop` self-loop guarantees stability past the
  bound (running longer does no harm).
- `towerHeight, towerOffset` — Lean `Nat` constants per
  subroutine, fixed once and for all. Together they witness the
  literature-aligned tower bound on `stepBound`.
- `towerDominates` — the closing inequality, a per-subroutine
  obligation. The shape `tower h (vMax v + offset)` lines up with
  Tourlakis 2018 §0.1.0.27 clauses (1)-(4) and Cutland Theorem
  4.1.1.

The structure is constructive: no field uses `∃`, all
witnesses are explicit Lean functions or constants. Step-0 design
is to keep the structure unconditionally constructive in line with
CLAUDE.md.

### §3.5 Lifting to `ElementaryBound`

`RegisterMachine.lean`'s `ElementaryBound` (lines 102-145, unary
shape) is recovered from `URMComputes`:

```lean
def URMComputes.toElementaryBound
    (uc : URMComputes P n initRegs outReg f) (v : Fin n → ℕ) :
    ElementaryBound where
  f := fun _ => uc.stepBound v
  height := uc.towerHeight
  offset := uc.towerOffset + vMax v
  dominated := fun _ => /- proof from `uc.towerDominates v` plus
                         arithmetic on the `vMax v` shift; concrete
                         proof in step 2 -/
                        _
```

Existing downstream uses of `ElementaryBound` in
`LawvereTreeERArith.lean` are unaffected.

---

## §4 Composition combinators in URM

Each combinator takes one or more `URMComputes` instances and
produces a `URMComputes` instance for the combined program. The
`stepBound` arithmetic is concrete Lean `Nat` arithmetic
(sum / max / iterated sum). The tower-witness arithmetic is
derived from existing Module A lemmas
(`Utilities/ComputationalComplexity.lean`); the design names
the lemmas to apply but defers the precise `(towerHeight,
towerOffset)` formulas to step 2's cycle.

### §4.1 Sequential composition `urmSeq`

`urmSeq P Q rmap : URMProgram`: run `P` first, then `Q` with
`Q`'s registers remapped via `rmap` (so `Q` sees `P`'s output
registers as its inputs). Defined by appending instruction
lists with PC-shift on `Q`'s `condJump` and `gotoInstr` targets.

`URMComputes` arithmetic:

- `stepBound (P;Q) v = stepBound P v + stepBound Q v'`
  where `v'` is `Q`'s input wired from `P`'s output on `v`.
- Tower witness derived using `tower_succ_pow_bound` (or
  `tower_succ_pow_bound_strong` for the `h ≥ 2` case) from
  `Utilities/ComputationalComplexity.lean`. Concrete formula:
  step 2's cycle. Sum-of-two-tower-bounded functions stays at
  the same height with a linear offset shift when both heights
  are ≥ 1, and bumps height by 1 when starting from height 0.

### §4.2 Conditional composition `urmIf`

`urmIf cond P Q : URMProgram`: at instruction 0, test `cond` (a
register expression); branch to either `P` or `Q`'s prelude.
Defined via `condJump` on the test register.

`URMComputes` arithmetic:

- `stepBound (urmIf c P Q) v
   = max(stepBound P v, stepBound Q v) + O(1)`.
- Tower witness: `towerHeight = max(towerHeight P, towerHeight
  Q)`; offset increases by a small constant. No height jump
  (max at same level absorbs `O(1)` additive overhead).

### §4.3 Bounded loop `urmLoop`

`urmLoop counter body : URMProgram`: execute `body` exactly
`regs[counter]` many times. Defined via the standard pattern
(Tourlakis 2018 p. 20):

```text
B ← counter
goto L
M:
  body
  B ← B ∸ 1
L: condJump B (L+1)
   gotoInstr M
L+1:
```

`URMComputes` arithmetic:

- `stepBound (urmLoop c P) v
   = sum_{i < c_v} stepBound_P (state_i) + O(c_v)`
  where `c_v` is `regs[c]` as a function of `v` and `state_i`
  is the register vector at iteration `i`.
- Tower witness derived using `polynomial_iter_tower_bound`
  from `Utilities/ComputationalComplexity.lean`, which states:
  iterating a polynomially-bounded step over a linearly-bounded
  initial value `j` times stays bounded by `tower 2 (linear of
  inputs)`. Concrete formula: step 2's cycle. The
  height-jump-per-loop-nesting matches the level grading of
  Tourlakis's hierarchy: each simrec / loop layer contributes
  at most one step in the tower, and the K^sim_2 case (two
  nested loops over polynomial bodies) lands in `tower 2`.

### §4.4 Composition arithmetic summary

For the load-bearing case (K^sim_2 → URM compilation), the
goal of the §4 arithmetic is for the URM compiled from any
K^sim morphism of level ≤ 2 to land in `tower 2` for its
`stepBound`. The bound `tower 2 (linear)` is in ER directly
(via iterated `2^x`-style ER expressions; see §1.4 and §8.4).
The shape mirrors the bound shape that Tourlakis 2018
§0.1.0.27 (4) and §0.1.0.43-44 use for `E^3`-runtimes (the
`A_2`-tower bound), but the construction in our project lives
entirely in `ERMor1` and does not invoke the ER ↔ E^3
equivalence. Step 2's cycle proves that the combinator
arithmetic carries the bound through.

---

## §5 The four catalogues

Each catalogue is a Lean module exporting a list of named
program / term entries, each with its `URMComputes` (or
`ERSimulatorRealizes` / `KSimSimulatorRealizes`) lemma. Compilers
and simulators are then literal `match` expressions referencing
catalogue entries. The catalogues partition by translation
direction.

### §5.1 `URMSubroutinesER.lean` — URM realizations of ER atoms

Used by the ER → URM compiler (step 8).

| ER constructor | URM subroutine | `stepBound` | `tH` |
|---|---|---|---|
| `ERMor1.zero` | `urmSubrZero` | `1` | `0` |
| `ERMor1.succ` | `urmSubrSucc` | `1` | `0` |
| `ERMor1.proj i` | `urmSubrProj i` | `v[i] + 1` (copy) | `0` |
| `ERMor1.sub` | `urmSubrSub` | `v[1] + 1` (dec loop) | `0` |
| `ERMor1.comp f gs` | `urmSubrComp` (comb.) | sum over subs | per §4.1 |
| `ERMor1.bsum f` | `urmSubrBsum` (comb.) | iter sum | per §4.3 |
| `ERMor1.bprod f` | `urmSubrBprod` (comb.) | iter sum + mult | per §4.3 |

(`tH` abbreviates `towerHeight`. Combinator entries delegate
their tower-height arithmetic to the corresponding §4
combinator; concrete formulas land in step 2's cycle.)

Plus a small set of helper named composites (`copyReg`, `addRegConst`,
`zeroReg-via-decrement-loop` if `decReg` is used in place of
`zeroReg` for some purpose; `mvRegToReg`).

### §5.2 `URMSubroutinesKSim.lean` — URM realizations of K^sim atoms

Used by the K^sim → URM compiler (step 4).

| K^sim constructor | URM subroutine | `stepBound` | `tH` |
|---|---|---|---|
| `KMor1.zero` | `urmSubrKZero` | `1` | `0` |
| `KMor1.succ` | `urmSubrKSucc` | `1` | `0` |
| `KMor1.proj i` | `urmSubrKProj i` | `v[i] + 1` | `0` |
| `KMor1.comp f gs` | `urmSubrKComp` (comb.) | sum over subs | per §4.1 |
| `KMor1.simrec _ _ i` | `urmSubrKSimrec` (comb.) | iter sum | per §4.3 |
| `KMor1.raise f` | `urmSubrKRaise` (comb.) | passthrough | same as f |

The level grading of the source K^sim term controls the
`towerHeight` of the compiled URM: every K^sim term of level
≤ 2 produces a URM whose total `stepBound` is bounded by
`tower 2 (linear inputs)` (per Module A's
`polynomial_iter_tower_bound` and `tower_succ_pow_bound_strong`,
which together stabilize the height at 2 once reached). The
`tower 2 (linear)` bound is itself in ER (constructed
directly from `ERMor1.bsum`/`bprod`-based exponentiation; see
§8.4).

### §5.3 `ERSubroutinesURM.lean` — ER realizations of URM primitives

Used by the URM → ER simulator (step 3).

Each entry is an ER subroutine that, given a packed
register-state encoding, returns the encoding after one URM
step under that primitive. PC and register components are
unpacked, updated, and re-packed by the subroutine.

- **`erInstrZeroReg i`** (for `zeroReg i`) — set the `i`-th
  register component to 0; advance PC by 1.
- **`erInstrIncReg i`** (for `incReg i`) — increment the
  `i`-th register component; advance PC by 1.
- **`erInstrDecReg i`** (for `decReg i`) — truncated decrement
  on the `i`-th register component; advance PC by 1.
- **`erInstrCondJump i t`** (for `condJump i t`) — registers
  unchanged; PC := `t` if `regs[i] = 0`, else PC := `pc + 1`.
- **`erInstrGoto t`** (for `gotoInstr t`) — registers
  unchanged; PC := `t`.
- **`erInstrStop`** (for `stop`) — identity on the full state.

Plus a per-URM **dispatch combinator** `erDispatch P : ERMor1 a`
that performs PC-conditioned selection over `P.instrs.length + 1`
branches via a `discN`-tree, returning the corresponding
per-instruction subroutine's effect on the state. The simulator's
step is `erDispatch P` applied at each iteration of `boundedRec`
over time.

### §5.4 `KSimSubroutinesURM.lean` — K^sim realizations of URM primitives

Used by the URM → K^sim simulator (step 7). Mirror of §5.3,
substituting `KMor1` for `ERMor1` and `simrec` for `boundedRec`.
Per Appendix A.3 of `docs/lawvere-k-sim-hierarchy.md`, the K^sim
PC-dispatch uses `switch` (Tourlakis 2018 §0.1.0.17 (6)) rather
than `discN`; both are fixed level-1 K^sim functions.

---

## §6 The simulators

### §6.1 ER simulator for URM

```lean
def simulateInER (P : URMProgram) : ERMorN (1 + P.numRegs) P.numRegs :=
  fun outReg =>
    -- pack initial state, iterate erDispatch P over the time bound,
    -- unpack and project the output register
    extractReg outReg ∘ stateBoundedRec ∘ packInitialState
  where
    stateBoundedRec :=
      ERMor1.boundedRec (encode_initial_state)
                        (erDispatch P)
                        (state_value_bound)
```

Where `extractReg outReg`, `packInitialState`, `state_value_bound`
are auxiliary ER expressions:

- `packInitialState : ERMor1 (1 + numRegs)` packs the initial PC =
  0 plus the input register vector into a single Szudzik code.
- `erDispatch P : ERMor1 1` (in ambient context) maps the packed
  state to its successor under one URM step.
- `state_value_bound : ERMor1 (1 + numRegs)` gives a polynomial-
  in-(time-and-max-input) bound on the packed state encoding,
  controlling `boundedRec`. Concrete shape: each register's
  value at iteration `i` is at most `max_initial + i` (one URM
  step changes any register by at most ±1). The packed Szudzik
  encoding of `(PC, regs)` is bounded by the product
  `(P.instrs.length + 1) · ∏ (max_initial + time + 1)`, which
  is polynomial in `(max_initial + time)`. This polynomial is
  expressed in ER as iterated multiplication; bounded by
  `Nat.seqPackBound`-style reasoning from Module A.
- `extractReg outReg : ERMor1 1` decodes the final state and
  projects the requested register.

The Szudzik packing of register-vector iteration state happens
inside the ER expression; at the API surface (`ERMorN`),
projection is by `Fin` selection.

**Multi-output independence.** Each component of the
`ERMorN` simulator is an independent `ERMor1` expression
(`(simulateInER P) i` for each `i : Fin P.numRegs` is its own
ER term); they share no computation. This is fine for
correctness — each component's interpretation independently
agrees with the URM's `runReg` at register `i`. It does mean
the ERMorN's syntactic size is `O(numRegs)` times an
underlying simulator size; this is a syntactic concern, not a
runtime/semantic concern. Optimizations sharing the
`stateBoundedRec` across outputs are possible but not needed
for correctness; they would not affect the URM-runtime bound
that closes the equivalence.

**State-value-bound correctness.** The `boundedRec` requires
that the iteration state never exceeds `state_value_bound`.
For a URM iteration starting from `encode_initial_state` and
applying `erDispatch P` `time` times, each step changes at
most one register by ±1 and the PC by O(1); the state at
iteration `i` is therefore bounded by `state_value_bound v`
for any `i ≤ time`. This is a step-by-step monotonicity
argument; proof obligation lives at step 3's cycle.

### §6.2 K^sim simulator for URM

Mirror of §6.1 with `simrec` in place of `boundedRec` and
`switch`-tree in place of `discN`-tree. Per Appendix A.3 of
`docs/lawvere-k-sim-hierarchy.md`.

### §6.3 Simulator interp-preservation

```lean
theorem simulateInER_interp
    (P : URMProgram)
    (outReg : Fin P.numRegs)
    (timeBound : ℕ) (regs : Fin P.numRegs → ℕ) :
  ((simulateInER P) outReg).interp (timeBound, regs)
    = runReg P.toRegisterMachine regs timeBound outReg
```

Proof outline: by induction on `timeBound`, with the inductive
step using `runReg_succ` (existing in `RegisterMachine.lean`)
plus the per-instruction interp lemmas (one per URM primitive,
in `ERSubroutinesURM.lean`). Mirror `simulateInKSim_interp`.

---

## §7 The compilers

### §7.1 K^sim_2 → URM compiler

```lean
def compileKSim : ∀ {a : ℕ} (f : KMor1 a), f.level ≤ 2 → URMProgram
  | _, .zero,        _ => urmSubrKZero  ...
  | _, .succ,        _ => urmSubrKSucc
  | _, .proj i,      _ => urmSubrKProj i
  | _, .comp f gs,   h => urmSubrKComp (compileKSim f h_f)
                                       (fun i => compileKSim (gs i) h_gs)
  | _, .simrec ...,  h => urmSubrKSimrec
                            (fun j => compileKSim (h_base j) h_h)
                            (fun j => compileKSim (g_step j) h_g)
                            i
  | _, .raise f,     h => urmSubrKRaise (compileKSim f h')
```

One-line per constructor: each line invokes a catalogue entry or
combinator from §5.2. The `compileKSim` function's type is
mechanically derived; all real work is in the catalogue.

### §7.2 ER → URM compiler

```lean
def compileER : ∀ {a : ℕ}, ERMor1 a → URMProgram
  | _, .zero      => urmSubrZero  ...
  | _, .succ      => urmSubrSucc
  | _, .proj i    => urmSubrProj i
  | _, .sub       => urmSubrSub
  | _, .comp f gs => urmSubrComp (compileER f) (gs.map compileER)
  | _, .bsum f    => urmSubrBsum (compileER f)
  | _, .bprod f   => urmSubrBprod (compileER f)
```

Mirror.

### §7.3 Compiler interp-preservation

```lean
theorem compileKSim_URMComputes
    {a : ℕ} (f : KMor1 a) (h : f.level ≤ 2) :
  (compileKSim f h).URMComputes_for f.interp
```

The aggregate `URMComputes` instance is built by structural
recursion: each constructor case applies the catalogue entry's
`URMComputes` and the relevant composition combinator's
`URMComputes`. By the design of §3.4 and §4, this is mechanical;
no global dominance argument needed.

---

## §8 The runtime-bound function

### §8.1 Per-`f` `boundExpr`

For each `f : KMor1 a` with `f.level ≤ 2`, define
`boundExpr f : ERMor1 a` as a tower-elementary ER expression
satisfying `(compileKSim f h).URMComputes.stepBound v ≤
boundExpr f.interp v` for all `v`.

The shape: `boundExpr f := tower (h_f) (max_input + offset_f)`,
constructed in ER as iterated `2^x` composed with an additive
shift; `max_input` is built from `bsum`-of-projections
expressing `Fin.foldr max 0`. Both `h_f` and `offset_f` are
Lean `Nat`-valued functions of `f`'s structure, computed
bottom-up.

The tight target is `h_f ≤ 2` for every `f.level ≤ 2`, with
the precise arithmetic per K^sim constructor:

- **Atoms** (`zero`, `succ`, `proj`): `h_f = 0`,
  `offset_f = small const`.
- **`comp` over atoms**: `h_f = 0`, offset shift sums to a
  small constant per Module A's sum-of-tower-0 bound.
- **`simrec` of level-1 over atoms / level-1**: `h_f = 2`,
  `offset_f = log-shift` per `polynomial_iter_tower_bound`
  (which lands at `tower 2` for polynomial-step iteration over
  linear initial).
- **`comp` once at height 2**: `h_f = 2` stays (no bump),
  offset shift is logarithmic per
  `tower_succ_pow_bound_strong`.
- **Nested `simrec` at level 2** (body at level ≤ 1, hence
  `h ≤ 2`): `h_f = 2` stays, offset shift is logarithmic per
  `tower_succ_pow_bound_strong`.
- **`raise f`**: `h_f` passthrough, `offset_f` passthrough.

Concrete formulas: step 5's cycle. Tight bound 2 across all
K^sim_2 morphisms by Module A's height-fixed lemma. The
result matches our target: every URM compiled from a K^sim_2
term has `stepBound` bounded by a `tower 2 (linear)` ER
expression. The `tower 2 (linear)` shape is the same shape
the literature labels `A_2^k`-bounded (Tourlakis 2018
§0.1.0.27 (4)); we construct it directly in `ERMor1` (see
§1.4 and §8.4) without invoking the literature's
characterization in the Grzegorczyk hierarchy.

### §8.2 Mirror `boundExprK e : KMor1 a`

For each `e : ERMor1 a`, construct `boundExprK e : KMor1 a` of
level ≤ 2 in K^sim using `2^x ∈ K^sim_2` per Tourlakis 2018
§0.1.0.17 (c). Mirror arithmetic on tower height per ER
constructor.

### §8.3 Reuse of existing infrastructure

- `Utilities/ComputationalComplexity.lean`: `tower`,
  `tower_succ_pow_bound` (sequential composition tower-jump),
  `polynomial_iter_tower_bound` (loop-induced bound landing in
  `tower 2`), `tower_succ_pow_bound_strong` (height-fixed
  variant for `h ≥ 2`).
- `LawvereERPolynomialBound.lean`: `ERMor1.PolyBound`,
  `log_le_towerHeight`, per-constructor builders. Used to
  certify that the constructed `boundExpr f` is genuinely an ER
  expression at the correct level.

### §8.4 Why `boundExpr f` is in ER (direct construction)

For `f : KMor1 a` with `f.level ≤ 2`, the §8.1 arithmetic
gives `h_f ≤ f.level + small_const` (each comp/simrec/raise
adds at most a constant to `h_f`, and the K^sim term tree
has depth bounded by `f.level`). For `f.level ≤ 2`, this
means `h_f ≤ 2 + small_const`.

`boundExpr f := tower h_f (vMax v + offset_f)` is constructed
directly in `ERMor1`:

- `vMax v` is the iterated maximum of inputs, expressed in
  ER as a chain of `discN`-based pairwise maxima. Linear
  growth in inputs.
- `tower h x` (height ≤ 2) is constructed in ER by iterated
  `2^x`. The base step `2^x` is the ER expression
  `bsum (proj 0 ↦ ∏_{i < x} 2)` (or an equivalent named
  composite), which is in `ERMor1` directly via `bprod` of
  the constant `2`. Iterating up to height 2 stays in ER by
  closure under `comp`. Concretely, the named composites for
  `tower 0`, `tower 1`, `tower 2` live in `Utilities/ERArith.lean`
  (or a small extension) and each carries its `interp` lemma.
- The additive shift is `comp` with `succ`-iterated, also in
  ER directly.

No invocation of the Grzegorczyk-hierarchy `E^3 = ER`
equivalence; the construction is a direct `ERMor1` term.

The `ERMor1.PolyBound` infrastructure from
`LawvereERPolynomialBound.lean` is the Lean-side encoding of
"this `ERMor1` term has tower-shape value bound": it
certifies, per constructor, that the `boundExpr f` term
lives at the correct ER level. Step 5's cycle shows the
per-constructor `boundExpr` cases are all in ER's named-
composite catalogue.

---

## §9 The functors and interp-preservation

### §9.1 `kToER`

```lean
def kToER {a : ℕ} (f : KMor1 a) (h : f.level ≤ 2) : ERMor1 a :=
  let P := compileKSim f h
  let sim := simulateInER P
  -- wire: time = boundExpr f.interp; inputs = projections;
  -- working / output regs = zeros; project final outReg.
  ERMor1.comp (sim P.outputReg)
              (boundExpr f, projections, zero-padding)
```

Multi-output `kToERN : KMorN a m → KMorN.level f ≤ 2 → ERMorN a m`
is pointwise.

### §9.2 `kToER_interp`

```lean
theorem kToER_interp
    {a : ℕ} (f : KMor1 a) (h : f.level ≤ 2) (v : Fin a → ℕ) :
  (kToER f h).interp v = f.interp v
```

Proof outline:

1. By `simulateInER_interp` (§6.3), `(simulateInER P)` at the
   right output register applied to `(t, regs)` returns
   `runReg P.toRegisterMachine regs t outReg`.
2. By `compileKSim_URMComputes` (§7.3), `compileKSim f h` has
   `URMComputes.stepBound` ≤ some elementary function, and
   `runReg ... = f.interp v` once `t ≥ stepBound v`.
3. By construction, the `time` argument fed to the simulator is
   `boundExpr f.interp v ≥ stepBound v` (the runtime-bound
   theorem from step 5).
4. Combine: `(kToER f h).interp v
   = runReg ... (boundExpr f.interp v) outReg = f.interp v`.

### §9.3 Functor lift

`kToERFunctor : LawvereKSimDCat 2 ⥤ LawvereERCat`:

- `obj n := n` (identity on objects: both categories have ℕ as
  arities).
- `map ⟦f, h⟧ := ⟦kToER f h⟧` — well-defined on quotient classes
  by `kToER_interp`: extensionally equal K^sim representatives
  produce extensionally equal ER outputs.
- Functor laws (`map_id`, `map_comp`) — proven by `kToER_interp`
  combined with the categorical interpretation lemmas
  (`LawvereKSimDCat`'s `id_eq` and `comp_eq` reduce to interpretation
  identities).

### §9.4 `erToK` mirror

Symmetric construction; symmetric statements; symmetric proofs.

---

## §10 The categorical isomorphism

### §10.1 Strict equality of round-trip functor compositions

```lean
theorem kToERFunctor_erToKFunctor :
  kToERFunctor ⋙ erToKFunctor = 𝟭 (LawvereKSimDCat 2)
theorem erToKFunctor_kToERFunctor :
  erToKFunctor ⋙ kToERFunctor = 𝟭 LawvereERCat
```

Both hold strictly (functor equality, not natural isomorphism)
because:

1. `obj` fields agree: all four functors are identity on objects
   (both categories have ℕ as objects, and our functors use
   `obj n := n`).
2. `map` fields agree: for any morphism class `⟦f⟧`,
   `(F ⋙ G).map ⟦f⟧ = G.map (F.map ⟦f⟧)`. By interp-preservation
   of both `F` and `G`, this morphism class has the same
   interpretation as `⟦f⟧`. Since the morphism categories are
   quotients by extensional-equality of interpretations,
   "same interpretation" = "same morphism". Hence
   `(F ⋙ G).map ⟦f⟧ = ⟦f⟧ = 𝟭.map ⟦f⟧`.

The proof reduces to one application of interp-preservation per
direction plus quotient-class-equality from interp-equality.

### §10.2 Equivalence wrapper

```lean
def lawvereERCatEquivKSimCat2 : LawvereERCat ≌ LawvereKSimDCat 2 :=
  -- via mathlib `equivOfIso` (or equivalent constructor)
  -- with the strict functor equalities lifted to nat isos
  -- via `eqToIso`.
  CategoryTheory.Equivalence.mk
    erToKFunctor kToERFunctor
    (eqToIso erToKFunctor_kToERFunctor.symm)
    (eqToIso kToERFunctor_erToKFunctor)
```

(Exact mathlib API to be pinned during step 11.)

### §10.3 Why iso, not just equivalence

The strict iso (functor-equality round-trip) gives strictly more
structural information than the bare equivalence. Anything proved
for `LawvereKSimDCat 2` morphisms (e.g. categorical limits, products,
structural lemmas) transports along the iso without natural-
transformation-coherence overhead.

---

## §11 Module file layout

Existing landed (no changes to load-bearing path):

```text
GebLean/Utilities/RegisterMachine.lean       (abstract kernel; reused)
GebLean/Utilities/Tower.lean                 (tower function + lemmas)
GebLean/Utilities/ComputationalComplexity.lean   (Module A)
GebLean/LawvereERPolynomialBound.lean        (Module B; PolyBound)
GebLean/Utilities/KSimSzudzikSimrec.lean     (Szudzik infrastructure;
                                              the kSimPackedBase/Step
                                              and kSimTowerBound parts
                                              remain dead code from
                                              the renamed direct path)
GebLean/LawvereKSim.lean
GebLean/LawvereKSimInterp.lean
GebLean/LawvereKSimQuot.lean
GebLean/LawvereKSimCat.lean                  (Phase 1 K^sim category)
GebLean/LawvereERQuot.lean
GebLean/Utilities/ERArith.lean
GebLean/Utilities/ERTreeArith.lean
GebLean/LawvereKSimERDirect.lean             (renamed direct-translation;
                                              level-0 and level-1
                                              dominance results retained
                                              as valid mathematics)
GebLean/LawvereKSimPolynomialBound.lean      (KMor1.linearBound; level-0
                                              and level-1 dominance;
                                              level0Shape; ConstantOrShiftedProj)
```

New files (proposed):

```text
GebLean/Utilities/URMConcrete.lean           [step 2]
  URMInstr (6 primitives), URMProgram, toRegisterMachine,
  URMComputes structure, urmSeq / urmIf / urmLoop combinators
  with stepBound and tower-witness arithmetic.

GebLean/Utilities/URMSubroutinesER.lean      [step 8]
  Catalogue of URM subroutines emulating each ERMor1
  constructor, each with URMComputes.

GebLean/Utilities/URMSubroutinesKSim.lean    [step 4]
  Catalogue of URM subroutines emulating each KMor1
  constructor at level ≤ 2, each with URMComputes.

GebLean/Utilities/ERSubroutinesURM.lean      [step 3]
  Catalogue of ERMor1 subroutines emulating each URM
  primitive, plus erDispatch combinator and simulateInER
  assembly.

GebLean/Utilities/KSimSubroutinesURM.lean    [step 7]
  Catalogue of KMor1 subroutines emulating each URM
  primitive, plus kSimDispatch combinator and
  simulateInKSim assembly.  Per Appendix A.3 of
  docs/lawvere-k-sim-hierarchy.md.

GebLean/LawvereKSimER.lean                   [step 6]
  kToER definition; kToERN; kToERFunctor; kToER_interp
  and functor laws.  (Bare name, distinct from
  LawvereKSimERDirect.lean.)

GebLean/LawvereERKSim.lean                   [step 10]
  erToK; erToKN; erToKFunctor; erToK_interp; functor laws.

GebLean/LawvereERKSimEquivalence.lean        [step 11]
  Strict iso erToKFunctor ⋙ kToERFunctor = 𝟭, and reverse.
  Mathlib Equivalence wrapper.
```

Module dependency graph:

```text
RegisterMachine ─→ URMConcrete
                       │
        ┌──────────────┼─────────────────────┐
        ↓              ↓                     ↓
 URMSubroutinesKSim  URMSubroutinesER  ERSubroutinesURM
        │              │                     │
        │              │              KSimSubroutinesURM
        │              │                     │
        │              ├──→ LawvereERKSim    │
        │              │                     │
        └─→ LawvereKSimER ←──────────────────┘

LawvereKSimER  ─┐
LawvereERKSim  ─┴─→ LawvereERKSimEquivalence
```

Re-exports updated in `GebLean.lean` per the project's policy.

---

## §12 Reuse pointers

### §12.1 Direct reuse (load-bearing path)

- **`RegisterMachineNS.RegisterMachine` (structure)** —
  used by `URMConcrete.toRegisterMachine` (§3.3).
- **`RegisterMachineNS.run`, `runFromConfig`, `runReg`** and their
  reduction lemmas — used in `URMComputes.correct` and simulator
  interp proofs (§6.3).
- **`RegisterMachineNS.ElementaryBound`** — derived from
  `URMComputes.toElementaryBound` (§3.5).
- **`Utilities/Tower.lean`'s `tower`, `tower_zero`,
  `tower_succ`** — used in `URMComputes.towerDominates` and
  in simulator value-bounds.
- **`Utilities/ComputationalComplexity.lean`'s
  `tower_succ_pow_bound`** — `urmSeq` tower arithmetic (§4.1).
- **`Utilities/ComputationalComplexity.lean`'s
  `polynomial_iter_tower_two_bound`** — `urmLoop` tower
  arithmetic (§4.3).
- **`LawvereERPolynomialBound.lean`'s `ERMor1.PolyBound` and
  builders** — certifying that `boundExpr f` is a genuine ER
  expression at level ≤ 2 (§8).
- **`LawvereERPolynomialBound.lean`'s
  `ERMor1.PolyBound.log_le_towerHeight`** — bridging ER tower
  expressions to value bounds when needed.
- **`Utilities/KSimSzudzikSimrec.lean`'s `kSimSzudzikPackList`,
  `kSimSzudzikUnpackAt`, `seqPackBound`** — encoding URM
  register vectors and PCs as a single ℕ for the simulator's
  iteration state (§6.1).
- **`Utilities/ERArith.lean`'s `pred`, `discN`, `boundedRec`** —
  the ER simulator's per-instruction subroutines and PC
  dispatch tree (§5.3, §6.1).
- **`LawvereKSim.lean`, `LawvereKSimInterp.lean`,
  `LawvereKSimQuot.lean`, `LawvereKSimCat.lean`** — Phase 1
  K^sim source / target infrastructure.
- **`LawvereERQuot.lean`, `LawvereKSimQuot.lean`** — quotient
  categories for the functor lift (§9.3).

### §12.2 Indirect reuse (cross-checks and witness validation)

- **`LawvereKSimERDirect.lean`'s
  `kToERDirect_interp_level_zero`,
  `kToERDirect_interp_level_one`** — independent witnesses that
  level-0 and level-1 K^sim functions are computable in ER;
  cross-checking the URM-route's correctness on small cases.
- **`LawvereKSimPolynomialBound.lean`'s `KMor1.linearBound`,
  `level0Shape`, `ConstantOrShiftedProj`** — cross-checking that
  the URM-runtime tower bound on level-1 K^sim agrees with the
  direct-translation linear bound on the same inputs.
- **`Phase4Investigation.lean`** — landed witnesses such as
  `addKFanOut5`, usable as test inputs for the new pipeline.

### §12.3 Test scaffolding

The K^sim primitives `addK`, `addKFanOut5`, and the level-0
/ level-1 atomic constructors all have known interpretations.
Step 4's catalogue can be tested with `#guard` on these
representatives at each cycle.

---

## §13 Citation map

The literature uses `E^n` notation (Grzegorczyk hierarchy);
our project uses `ER` directly per `GebLean/LawvereER.lean`'s
inductive (see §1.4). The references below are catalogued in
the literature's original `E^n` notation. Per §1.4, every
load-bearing claim using `E^n` in the literature is realized
in our project as a direct construction in `ERMor1`; no
proof step depends on the ER ↔ E^n equivalence.

### §13.1 Tourlakis 2018 (file `PR-complexity-topics.pdf`)

- **§0.1.0.7** — K^sim definition.
- **§0.1.0.15** — K^sim_n = L_n.
- **§0.1.0.17** (esp. clauses (c), (6)) — worked examples in
  K^sim, including the `switch` construct.
- **§0.1.0.22** — Grzegorczyk hierarchy definition.
- **§0.1.0.27** (esp. clauses (1)–(4)) — Bounding Lemma for E^n.
- **§0.1.0.34** — E^2 closed under bounded recursion; Cantor
  pairing in E^2.
- **§0.1.0.39** — Cantor pairing in E^2 (continued).
- **proof of §0.1.0.43, pp. 19-21** — Loop-to-URM translation
  with worked examples (`λx.x`, `λx.x+1`, `λxy.x·y`,
  Loop-to-URM template, bounded-recursion URM template).
- **§0.1.0.43** — Ritchie-Cobham property of E^n.
- **§0.1.0.44** — K^sim_n = E^{n+1} for n ≥ 2.

### §13.2 Tourlakis CN (file `tourlakis-Computability-Notes-ROOT.pdf`)

- **§4.2.2** — Hilbert-Bernays sequence-number coding.
- **§10.2.20** — cross-reference for K^sim_n = E^{n+1}.

### §13.3 Other literature

- **Cutland Theorem 4.1.1** (cited via Damnjanovic 1994 §1) —
  programs in standard formalisms compute exactly the
  elementary functions, with elementary time/space bounds.
- **Davis-Weyuker chapter 13** — explicit RM ↔ LOOP
  correspondences with simulators.
- **Meyer-Ritchie 1967** — original `LOOP_n = E^{n+1}` proof.
- **Damnjanovic 1994 §3 Lemma 3.1** — `f_k` tower-bound
  inequalities for LOOP programs (cross-checking material if
  the URM-runtime bound shape mirrors `f_k`).

### §13.4 Internal references

- **`docs/lawvere-k-sim-hierarchy.md` Appendix A** — erToK
  URM-simulation design (steps 7-10 mirror this).
- **`docs/research/2026-04-30-ksim-polynomial-bound-references.md`** —
  tower-bound shape rationale; Module A/B salvage list.
- **`docs/research/2026-05-02-ksim-to-er-architectural-pivot-handoff.md`** —
  the pivot decision and prior-failure catalogue.

---

## §14 Adversary's punch list for step 0

The step-0 adversarial brainstorm + sequential-thinking review
must explicitly check the following claims, each derived from a
prior-failure-mode hypothesis. The adversary is obligated to
follow literature references and either confirm or reject each
claim; rejection forces design revision.

### §14.1 Was the prior failure mode value-bound (not runtime-bound)?

Claim: The prior strategy (`kToERDirect`) tried to bound K^sim
function values pointwise by an ER expression. The new strategy
bounds URM step counts. These are different objects and the
shift removes the trap.

Adversary obligation: verify by reading `kSimTowerBound` and
`kSimTowerBound_dominates_inline` (in
`Utilities/KSimSzudzikSimrec.lean` and
`LawvereKSimPolynomialBound.lean`); confirm that the
`towerDominates` field of the new `URMComputes` structure
genuinely concerns step counts and not function values.

### §14.2 Does the URM-simulation strategy itself recreate the prior trap?

Claim: The runtime-bound shape `tower h_f (vMax v + offset_f)`
is a value-bound on the `stepBound` Lean function (which is
itself a number, not a K^sim function output). The composition
of step bounds via combinators (§4) is additive (`urmSeq`,
`urmIf`) or sums-of-iterations (`urmLoop`); none of these
introduce an exponential coefficient field analogous to the
prior `3^E`.

Adversary obligation: spot-check the §4 combinator arithmetic
table; trace whether any coefficient appears in the `stepBound`
or `towerHeight` arithmetic that would force a prior-style
absorption inequality.

### §14.3 Is K^sim_2 → URM compilation closed at level ≤ 2?

Claim: The `compileKSim` compiler, applied to a level-≤-2 K^sim
term, produces a URM whose `URMComputes.towerHeight` is bounded
by 2 + small constant. The compiler does not implicitly require
K^sim_3 features (e.g. unbounded `condJump` patterns smuggled in
via the `simrec` combinator).

Adversary obligation: trace the `simrec` case of `compileKSim`
(§7.1) to confirm the produced URM uses `condJump` only on the
recursion-counter register (a counted loop), never on
unbounded-iteration patterns. Verify that the `urmLoop`
combinator's `+1` `towerHeight` jump is the only level
contribution per simrec nesting.

### §14.4 Is the level-1-vs-level-2 asymmetry from prior plan v5 absent?

Claim: The URM-simulation strategy is uniform across K^sim levels
0, 1, 2: the catalogue entries are populated by structural
recursion on `KMor1` regardless of level; the level appears only
in `compileKSim`'s argument and in the resulting tower-height
computation. There is no level-1-only assumption (e.g.
`level0Shape.linearBound.1 ≤ 1`) that fails to lift to level-2
children.

Adversary obligation: examine the `compileKSim.simrec` case;
verify that the `KMor1.simrec` case's recursive call applies to
children at level n - 1 (where the parent is at level n) without
constraints on the children's specific structure.

### §14.5 Is the categorical iso of step 11 strict, not natural?

Claim: `kToERFunctor ⋙ erToKFunctor = 𝟭 (LawvereKSimDCat 2)` holds
strictly (functor equality), not merely up to natural
isomorphism. The argument relies on:
(a) both functors being identity on objects;
(b) interp-preservation pointwise for all morphisms;
(c) the morphism categories being quotients by interp-equality.

Adversary obligation: verify (a) by inspecting the proposed
`kToERFunctor.obj` and `erToKFunctor.obj` definitions; verify
(b) by checking the proof outlines for `kToER_interp` and
`erToK_interp` (§9.2); verify (c) by reading
`LawvereKSimQuot.lean` and `LawvereERQuot.lean`.

### §14.6 Is per-URM (not universal) construction what Tourlakis does?

Claim: Tourlakis 2018's proof of §0.1.0.43-44 constructs URMs
per function (not a single universal URM) and the simulating
function is per-URM (the phrasing "the simulating function for
the output variable of M" is M-specific). The new design adopts
per-URM construction by symmetry with Tourlakis.

Adversary obligation: verify by reading `PR-complexity-topics.pdf`
pp. 19-22 directly. Confirm the worked examples (`λx.x`,
`λx.x+1`, `λxy.x·y`, the Loop-to-URM template, the bounded-
recursion URM template) are all per-program / per-function. Check
the §0.1.0.44 ⊇ proof for the per-M phrasing.

### §14.7 Are the catalogue obligations local?

Claim: Each catalogue entry's `URMComputes` proof is local — it
references only the entry's own definition, the `tower` and
`runReg` lemmas from `RegisterMachine.lean`, and possibly
sub-catalogue entries via composition combinators. No global
dominance argument is required.

Adversary obligation: spot-check 2-3 catalogue entries (e.g.
`urmSubrKSucc`, `urmSubrKSimrec`, `erInstrCondJump`); trace the
sketch of their `URMComputes` proofs to confirm locality. If any
entry requires reasoning about other entries beyond the
combinator interface, that is a defect.

### §14.8 Is the design constructive throughout?

Claim: No use of `Classical`, `noncomputable`, or `axiom`. All
existence claims (e.g. termination of catalogue subroutines) are
witnessed by explicit Lean functions (e.g. `URMComputes.stepBound`).

Adversary obligation: review the `URMComputes` structure for any
existential field; review the proposed simulator constructions
for any Classical-dependent operation; confirm that the Szudzik
encoding, `boundedRec`, and `simrec` constructions remain
constructive.

### §14.9 Is interpretation-preservation strict?

Claim: `kToER_interp` and `erToK_interp` are equalities at the
interpretation level (`(F f).interp v = f.interp v`), not
inequalities or "dominated by" claims.

Adversary obligation: confirm the theorem statements in §9.2
and §9.4 are equalities; trace the proof outlines for absence
of inequalities at the ouput of the simulator.

### §14.10 Are the deferred halves genuinely deferred?

Claim: The erToK direction's load-bearing files
(`URMSubroutinesER.lean`, `KSimSubroutinesURM.lean`,
`LawvereERKSim.lean`) are designed in this master doc but their
internal proofs are deferred to steps 7-10. The kToER side
(steps 3-6) does not depend on any unfinished erToK content.

### §14.11 Does any proof step depend on ER ↔ E^n?

Claim: Per §1.4, this project formalizes `ER` directly per
`GebLean/LawvereER.lean` and does **not** formalize the
Grzegorczyk hierarchy. Every load-bearing step in the proof
chain uses `ER` directly (or its named composites in
`Utilities/ERArith.lean` and `LawvereERPolynomialBound.lean`).
Literature references using `E^n` notation appear only in the
citation map (§13) and in motivation prose (§1, §4.4, §5.2,
§8); none of those references is converted into a logical
dependency.

Adversary obligation: trace each `E^n` occurrence in the
document; confirm that for every occurrence, the surrounding
context either (a) is in §1, §13, or another non-load-bearing
section, or (b) restates the same claim in `ER` terms with a
direct `ERMor1` construction. Any place where the proof
chain steps from "X is in `E^n`" to "X is in `ER`" without
going through a direct `ERMor1` term is a defect.

Adversarial obligation: spot-check §8.4's "stays in ER"
argument; confirm that the construction of `boundExpr f`'s
ER expression (iterated `2^x` plus linear shift) does not
rely on a Grzegorczyk-hierarchy fact. Also spot-check §6.1's
`state_value_bound` polynomial in ER, confirming it is a
polynomial expression in `ERMor1` directly (via `bsum`/`bprod`),
not a black-box reference to "E^2's polynomial bound".

Adversary obligation: verify the dependency graph (§11) does not
contain a cycle or backward edge from kToER-load-bearing to
erToK-load-bearing modules.

---

## §15 Notes for downstream cycles

### §15.1 Cycle hand-off shape

Each per-step cycle starts by reading this master design's
relevant sections, plus any per-step refinements written during
that cycle's brainstorm. Each cycle's writing-plans output is
filed as `docs/plans/2026-MM-DD-er-ksim2-equiv-step-N-<topic>.md`,
referencing this master document by section number.

### §15.2 Citation discipline reminder

Per CLAUDE.md "Literature-citation discipline (transcription
workstreams only)": every planned function, definition, or
theorem in any cycle's plan carries a literature reference;
every implemented entity carries the same reference in its
docstring. The references in §13 are the master list; cycles
refine to specific page or proof-step numbers.

### §15.3 Bottom-up named-composite discipline reminder

Per CLAUDE.md: never add a `KMor1`/`ERMor1`/`URMInstr` constructor
or downstream consumer before its image in the target language
has been built and named as a `def` (with a `@[simp]` interp
lemma where applicable). The four catalogues are the named-
composite layers for the four URM-boundary translations; the
compilers and simulators are the consumers.

### §15.4 Failure-mode escalation

If during a per-step cycle the adversarial review identifies an
obstacle that revisits a prior-failure-mode hypothesis (§14.1-
14.10), pause and re-open this master design rather than
attempting to patch the per-step plan. The master design's
adversary-punch-list claims are the load-bearing assumptions of
the project; their invalidation is a master-level event.

---

End of master design.
