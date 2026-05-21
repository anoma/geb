# T3 — URM → K^sim simulator — design

Re-spec of master design §6 (master design at
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`;
T1/T2 spec at
`docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`)
against the actually-landed T1 (`GebLean/Utilities/ZeroTestURM.lean`)
and T2 (`GebLean/LawvereERKSim/` submodules) shapes. T3 builds a
K^sim simulator for arbitrary `URMProgram a` and proves it
interpretation-equivalent to `URMState.runFor`.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [1 Scope](#1-scope)
- [2 Inputs (binding T1/T2 artifacts)](#2-inputs-binding-t1t2-artifacts)
- [3 Architecture](#3-architecture)
  - [3.1 Public signature](#31-public-signature)
  - [3.2 `simrec` system shape](#32-simrec-system-shape)
  - [3.3 Base family `baseFamily`](#33-base-family-basefamily)
  - [3.4 Step family `stepFamily`](#34-step-family-stepfamily)
  - [3.5 PC-dispatch helper `KMor1.pcDispatch`](#35-pc-dispatch-helper-kmor1pcdispatch)
  - [3.6 Constant helper `KMor1.natK`](#36-constant-helper-kmor1natk)
- [4 Correctness theorem](#4-correctness-theorem)
  - [4.1 Statement](#41-statement)
  - [4.2 Conjunctive vector invariant](#42-conjunctive-vector-invariant)
  - [4.3 Proof outline](#43-proof-outline)
  - [4.4 Surfacing `simulate_interp` from `simulate_step_match`](#44-surfacing-simulate_interp-from-simulate_step_match)
- [5 Level analysis](#5-level-analysis)
- [6 Module layout](#6-module-layout)
  - [6.1 File placement](#61-file-placement)
  - [6.2 Dependency graph](#62-dependency-graph)
  - [6.3 File outlines](#63-file-outlines)
  - [6.4 Naming conventions](#64-naming-conventions)
- [7 Constructive discipline](#7-constructive-discipline)
- [8 Out of scope (defers to T4 / T5 / T6)](#8-out-of-scope-defers-to-t4--t5--t6)
- [9 Step decomposition](#9-step-decomposition)
- [10 Adversarial-review punch list](#10-adversarial-review-punch-list)
- [11 Citations](#11-citations)
  - [11.1 External (Tourlakis 2018, `PR-complexity-topics.pdf`)](#111-external-tourlakis-2018-pr-complexity-topicspdf)
  - [11.2 Internal repository references](#112-internal-repository-references)
- [12 References](#12-references)

<!-- END doctoc -->

## 1 Scope

T3 builds the K^sim simulator that runs an arbitrary URM program
(produced by T2's `compileER`, but T3 itself does not import the
compiler) for `y` steps and projects the resulting output register
as a `ℕ`. The simulator is the second leg of the
`erToK : ERMor1 a → KMor1 a` translation; the first leg is T2's
`compileER`, and the final composition is T5.

T3 produces:

- `KMor1.natK : ℕ → KMor1 0` and its lifted form `KMor1.natK'`,
  with interpretation and level lemmas. Level 0.
- `KMor1.pcDispatch : (size : ℕ) → (Fin size → KMor1 n) →
  KMor1 n → KMor1 (n + 1)`, with `interp_pcDispatch_match`,
  `interp_pcDispatch_default`, and `pcDispatch_level`. The
  dispatch chain stays at level 1 when branches and default are
  level ≤ 1.
- `simulate : URMProgram a → KMor1 (1 + a)`.
- `simulate_interp`: simulator output equals `URMState.runFor`
  output projected at `outputReg`.
- `simulate_level`: `(simulate P).level ≤ 2`.

The runtime bound (`boundExprK`), the `erToK` assembly, the
`erToKFunctor`, and the strict iso are out of scope; they belong
to T4, T5, and T6 respectively. See § 8.

## 2 Inputs (binding T1/T2 artifacts)

The shapes below are fixed by what T1 and T2 landed. Any change
to these would require re-spec.

| Artifact | File:line | Role in T3 |
| --- | --- | --- |
| `URMInstr r` (5 cases) | `GebLean/Utilities/ZeroTestURM.lean:89` | Each constructor maps to a `stepFamily` branch. |
| `URMProgram a` (arity-indexed) | `GebLean/Utilities/ZeroTestURM.lean:122` | T3's input. `numInputs` is the `a` type parameter. |
| `URMState P` | `GebLean/Utilities/ZeroTestURM.lean:143` | Reference structure mirrored by the `simrec` component vector. |
| `URMState.step P` | `GebLean/Utilities/ZeroTestURM.lean:155` | Case-by-case mirror target for `stepFamily`. |
| `URMState.runFor P` | `GebLean/Utilities/ZeroTestURM.lean:179` | `runFor_zero` / `runFor_succ` reduction lemmas match `simrecVec_zero` / `simrecVec_succ`. |
| `URMState.init P v` | `GebLean/Utilities/ZeroTestURM.lean:254` | Mirrored by `baseFamily`; same `List.find?` lookup. |
| `KMor1` inductive | `GebLean/LawvereKSim.lean:34` | Target type of `simulate`. |
| `KMor1.simrec` constructor | `GebLean/LawvereKSim.lean:50` | The primitive `simulate` uses. |
| `KMor1.level` | `GebLean/LawvereKSim.lean:105` | Used to discharge `simulate_level`. |
| `KMor1.interp_simrec` (`@[simp]`) | `GebLean/LawvereKSimInterp.lean:162` | Public reduction lemma for `simulate_interp`. |
| `KMor1.simrecVec_zero` / `_succ` (`@[simp]`) | `GebLean/LawvereKSimInterp.lean:180`, `:193` | Peel one iteration of the `simrec` recursion. |
| `KMor1.cond` (Tourlakis `switch`, level 1) | `GebLean/Utilities/KArith.lean:222` | Inner combinator of `pcDispatch`. |
| `KMor1.interp_cond` (`@[simp]`) | `GebLean/Utilities/KArith.lean:249` | Reduces `pcDispatch`'s nested `cond` chain. |
| `KMor1.pred` (level 1) | `GebLean/Utilities/KArith.lean:44` | Used both inside `pcDispatch` (`pred^k(I)` tests `I = k`) and inside `stepFamily` (`.dec` branch). |

T3 does not depend on `LawvereER*`, `LawvereERKSim/*`,
`LawvereKSimER*`, `LawvereKSimMajorization*`, or any CSLib URM
module. See § 6.2.

## 3 Architecture

### 3.1 Public signature

```lean
def simulate {a : ℕ} (P : URMProgram a) : KMor1 (1 + a)

theorem simulate_interp {a : ℕ} (P : URMProgram a)
    (y : ℕ) (v : Fin a → ℕ) :
    (simulate P).interp (Fin.cons y v)
      = ((URMState.init P v).runFor y).regs P.outputReg

theorem simulate_level {a : ℕ} (P : URMProgram a) :
    (simulate P).level ≤ 2
```

The simulator's context arity is `1 + a`: slot 0 carries the
time bound `y`, slots `1..a` carry the input vector `v`. The
output is the value of `P.outputReg` after `y` steps from
`URMState.init P v`.

### 3.2 `simrec` system shape

`simulate P` is a single `KMor1.simrec`:

- recursion variable: `y` (slot 0 of the outer context);
- parameters: `v` (slots `1..a`);
- system size: `P.numRegs + 1`;
- component layout: component `0` is the PC; components
  `1, …, numRegs` are register values `regs 0, …,
  regs (numRegs − 1)` (component `j + 1` ↔ register `j`);
- output index: `P.outputReg.succ : Fin (P.numRegs + 1)`.

Picking `Fin.cons y v` as the input convention matches
`interp_simrec`'s context-splitting (`ctx 0` for the recursion
variable; `Fin.succ` projection for parameters).

### 3.3 Base family `baseFamily`

```lean
def baseFamily {a : ℕ} (P : URMProgram a) :
    Fin (P.numRegs + 1) → KMor1 a
  | ⟨0,        _⟩ => KMor1.zero
  | ⟨j + 1, hj⟩  =>
      let r : Fin P.numRegs := ⟨j, by omega⟩
      match (List.finRange a).find?
            (fun i => decide (P.inputRegs i = r)) with
      | some i => KMor1.proj i
      | none   => KMor1.zero
```

Mirrors `URMState.init` syntactically: component `0` is `KMor1.zero`
(initial PC = 0); component `j + 1` for register `j` reproduces
`URMState.init`'s register-vector definition, using the same
`List.find?` lookup. Every leaf is `zero` or `proj`, so each
`baseFamily P j` is at level 0.

### 3.4 Step family `stepFamily`

```lean
def stepFamily {a : ℕ} (P : URMProgram a) :
    Fin (P.numRegs + 1) → KMor1 (a + 1 + (P.numRegs + 1))
```

Per `KMor1.interp_simrec_eq_simrecVec`, the step context layout
for one `stepFamily j` call is:

| slot | meaning |
| --- | --- |
| `0` | current iteration counter `m` (unused) |
| `1..a` | input vector `v` (used only as input slot reference) |
| `a + 1` | previous PC value `I_prev` |
| `a + 2..a + 1 + numRegs` | previous register values `v_0_prev, …, v_{numRegs−1}_prev` |

Helper projections (each is `KMor1.proj …` at level 0):

- `I_prev : KMor1 (a + 1 + (P.numRegs + 1))`
  — slot `a + 1`.
- `v_j_prev : Fin P.numRegs → KMor1 (a + 1 + (P.numRegs + 1))`
  — slot `a + 2 + j.val`.

Component `0` (PC):

```text
stepFamily P ⟨0, _⟩ := pcDispatch P.instrs.size branches_pc default_pc

branches_pc k := match P.instrs[k]'_ with
  | .stop          => I_prev                            -- identity
  | .jumpZ i l₁ l₂ => cond ∘ ⟨v_i_prev, natK' _ l₁, natK' _ l₂⟩
  | _              => succ ∘ I_prev                     -- PC + 1
default_pc       := I_prev                              -- past-end self-loop
```

Component `j + 1` (register `j`, for each `j : Fin P.numRegs`):

```text
stepFamily P (j + 1) := pcDispatch P.instrs.size branches_j default_j

branches_j k := match P.instrs[k]'_ with
  | .assign i c  => if i.val = j.val then natK' _ c     else v_j_prev
  | .inc i       => if i.val = j.val then succ ∘ v_j_prev else v_j_prev
  | .dec i       => if i.val = j.val then pred ∘ v_j_prev else v_j_prev
  | _            => v_j_prev
default_j      := v_j_prev
```

Every branch and every default is at level ≤ 1 (`cond`, `pred` are
level 1; `succ`, `proj`, `natK'` are level 0). By
`pcDispatch_level` (§ 3.5), each `stepFamily P j` is at level ≤ 1.

### 3.5 PC-dispatch helper `KMor1.pcDispatch`

```lean
def KMor1.pcDispatch {n : ℕ} (size : ℕ)
    (branches : Fin size → KMor1 n) (default : KMor1 n) :
    KMor1 (n + 1)
```

Implemented as the nested `cond` chain on `pred^k(PC)` (where
`PC = ctx (Fin.last n)` is the last context slot), recursively on
`size`:

```text
pcDispatch 0     _        default := default ∘ Fin.init
pcDispatch (k+1) branches default :=
  cond ∘ ⟨pred^k(PC), branches ⟨k, _⟩, pcDispatch k (branches ∘ castSucc) default⟩
```

The implementation choice between this top-down form (peeling the
highest `k`) and a bottom-up form (peeling `k = 0` first) is left
to implementation; either form yields the same interpretation and
level. The spec fixes the *interpretation* lemmas, not the recursion
direction.

Key lemmas:

```lean
@[simp] theorem KMor1.interp_pcDispatch_match
    {n size : ℕ} (branches : Fin size → KMor1 n)
    (default : KMor1 n) (ctx : Fin (n + 1) → ℕ)
    (k : Fin size) (h : ctx (Fin.last n) = k.val) :
    (KMor1.pcDispatch size branches default).interp ctx
      = (branches k).interp (Fin.init ctx)

@[simp] theorem KMor1.interp_pcDispatch_default
    {n size : ℕ} (branches : Fin size → KMor1 n)
    (default : KMor1 n) (ctx : Fin (n + 1) → ℕ)
    (h : ctx (Fin.last n) ≥ size) :
    (KMor1.pcDispatch size branches default).interp ctx
      = default.interp (Fin.init ctx)

theorem KMor1.pcDispatch_level {n : ℕ} (size : ℕ)
    (branches : Fin size → KMor1 n) (default : KMor1 n)
    (h_branches : ∀ k, (branches k).level ≤ 1)
    (h_default : default.level ≤ 1) :
    (KMor1.pcDispatch size branches default).level ≤ 1
```

The `+ 1` from `cond` does not raise level beyond 1 because the
`cond` is itself level 1 and is composed with level-1 children
under `comp` (which takes `max` without adding).

### 3.6 Constant helper `KMor1.natK`

```lean
def KMor1.natK : ℕ → KMor1 0
  | 0     => KMor1.zero
  | c + 1 => KMor1.comp KMor1.succ (fun _ : Fin 1 => KMor1.natK c)

@[simp] theorem KMor1.interp_natK (c : ℕ) (ctx : Fin 0 → ℕ) :
    (KMor1.natK c).interp ctx = c

theorem KMor1.natK_level (c : ℕ) : (KMor1.natK c).level = 0

def KMor1.natK' (n c : ℕ) : KMor1 n :=
  KMor1.comp (KMor1.natK c) Fin.elim0

@[simp] theorem KMor1.interp_natK' (n c : ℕ) (ctx : Fin n → ℕ) :
    (KMor1.natK' n c).interp ctx = c

theorem KMor1.natK'_level (n c : ℕ) : (KMor1.natK' n c).level = 0
```

`natK'` is the version usable inside an arbitrary-arity context;
`stepFamily`'s branches use it for the `assign` constant `c` and
for the `jumpZ` target labels `l₁`, `l₂`.

## 4 Correctness theorem

### 4.1 Statement

```lean
theorem simulate_interp {a : ℕ} (P : URMProgram a)
    (y : ℕ) (v : Fin a → ℕ) :
    (simulate P).interp (Fin.cons y v)
      = ((URMState.init P v).runFor y).regs P.outputReg
```

Total over `URMProgram a`; no `WellBounded` precondition. The K^sim
side's `default_pc = I_prev` matches `URMState.step`'s past-end
self-loop, and `runFor`'s post-halt invariant
(`URMState.runFor_halted_invariant`,
`GebLean/Utilities/ZeroTestURM.lean:213`) follows from the same
identity.

### 4.2 Conjunctive vector invariant

The induction goes through the conjunctive form

```lean
private theorem simulate_step_match {a : ℕ}
    (P : URMProgram a) (v : Fin a → ℕ) (y : ℕ) :
    KMor1.simrecVec (baseFamily P) (stepFamily P) v y ⟨0, _⟩
      = ((URMState.init P v).runFor y).pc
    ∧ ∀ j : Fin P.numRegs,
        KMor1.simrecVec (baseFamily P) (stepFamily P) v y j.succ
          = ((URMState.init P v).runFor y).regs j
```

The conjunction is necessary: each `stepFamily P j` reads the
previous values of *every* component (e.g. the PC's `jumpZ` branch
reads `v_i_prev`; each register's `branches_j k` for `k` a `jumpZ`
reads the PC), so the inductive hypothesis must cover the full
component vector.

### 4.3 Proof outline

By induction on `y`.

**Base case `y = 0`.** Both sides reduce by `simrecVec_zero` and
`runFor_zero` to the same `baseFamily P` / `URMState.init P v`
definitions. The PC component reduces to `0 = 0`; each register
component reduces to the same `List.find?` lookup that
`URMState.init` uses; closed by `rfl` after `simp` chains.

**Step case `y + 1`.** Both sides peel one iteration:

- URM side: `URMState.runFor_succ` gives
  `runFor (y + 1) = step (runFor y)`.
- K^sim side: `simrecVec_succ` gives the one-iteration unfolding
  through `stepFamily P j`.

Case-by-case on `P.instrs[(runFor y).pc]'?` (or past-end, when
`(runFor y).pc ≥ P.instrs.size`):

| URM case | K^sim side | Discharge |
| --- | --- | --- |
| past-end | `pcDispatch_default` for both `branches_pc` and `branches_j` | `default_pc = I_prev`, `default_j = v_j_prev` match the URM identity. |
| `.stop` | `pcDispatch_match` selects `I_prev` / `v_j_prev` | Match `URMState.step`'s `.stop` case (identity). |
| `.assign i c` | `pcDispatch_match`; for `j = i.val`, returns `c`; otherwise `v_j_prev` | `Function.update s.regs i c` reduces to `c` at `j = i.val`, else `s.regs j`. |
| `.inc i` | analogous | `Function.update s.regs i (s.regs i + 1)`. |
| `.dec i` | analogous, using `pred` | `Function.update s.regs i (s.regs i - 1)`. |
| `.jumpZ i l₁ l₂` | PC component: `cond` on `v_i_prev`; register components: `v_j_prev` | `URMState.step`'s `.jumpZ` updates only `pc`. |

The conjunctive IH supplies, for each branch, the equalities of
`I_prev` and each `v_j_prev` at time `y` to their URM-side
counterparts. After substituting, both sides reduce to identical
expressions over `regs j` and `pc`.

### 4.4 Surfacing `simulate_interp` from `simulate_step_match`

Project `simulate_step_match`'s register-component clause at
`j = P.outputReg`; combine with `interp_simrec`'s unfolding of
`simulate P` at the public-facing context; close by `rfl`. No
additional lemmas required.

## 5 Level analysis

```lean
theorem simulate_level {a : ℕ} (P : URMProgram a) :
    (simulate P).level ≤ 2
```

Breakdown:

- Each `baseFamily P j` is `zero` or `proj`: level 0. So
  `Finset.univ.sup (fun j => (baseFamily P j).level) = 0`.
- Each `stepFamily P j` is a `pcDispatch` whose branches and
  default are all level ≤ 1 (every constituent — `cond`, `pred`,
  `succ`, `proj`, `natK'` — has level ≤ 1). By
  `pcDispatch_level`, `(stepFamily P j).level ≤ 1`. So
  `Finset.univ.sup (fun j => (stepFamily P j).level) ≤ 1`.
- The `KMor1.level`'s `simrec` clause adds 1 to the max of base
  and step sups: `max 0 1 + 1 = 2`.

No `KMor1.eq` (level 2) or `KMor1.raise` appears in the term, so
no other level bumps occur.

## 6 Module layout

### 6.1 File placement

| File | Status | Contents |
| --- | --- | --- |
| `GebLean/Utilities/KArith.lean` | Extended | `KMor1.natK`, `KMor1.natK'`, `KMor1.interp_natK`, `KMor1.interp_natK'`, `KMor1.natK_level`, `KMor1.natK'_level`. |
| `GebLean/Utilities/KSimURMSimulator.lean` | New | `KMor1.pcDispatch`, `KMor1.interp_pcDispatch_match`, `KMor1.interp_pcDispatch_default`, `KMor1.pcDispatch_level`, `baseFamily`, `stepFamily`, `simulate`, `simulate_step_match`, `simulate_interp`, `simulate_level`. |
| `GebLean.lean` | Updated | re-export `GebLean.Utilities.KSimURMSimulator`. |

The simulator lives under `Utilities/` (not under the
`LawvereERKSim/` submodule tree) because its inputs and outputs are
independent of `LawvereER`: it consumes `URMProgram a` (from
`Utilities/ZeroTestURM.lean`) and produces `KMor1 (1 + a)` (from
`LawvereKSim.lean`). T5 will be the joining point: it imports both
`LawvereERKSim` (compiler) and `Utilities/KSimURMSimulator`
(simulator), composing them through `boundExprK e` (T4).

### 6.2 Dependency graph

```text
Utilities/KSimURMSimulator
  ├── Utilities/ZeroTestURM         -- URMProgram, URMState, step, runFor, init
  ├── LawvereKSim                   -- KMor1, simrec, level
  ├── LawvereKSimInterp             -- interp_simrec, simrecVec_zero, simrecVec_succ
  └── Utilities/KArith              -- cond, pred, natK, succ, proj wrappers
```

No import of `LawvereER*`, `LawvereERKSim*`, `LawvereKSimER*`,
`LawvereKSimMajorization*`, or any CSLib URM module.

### 6.3 File outlines

`GebLean/Utilities/KArith.lean` additions (inserted after the
existing `KMor1.cond` block, approximately line 270):

```lean
def KMor1.natK : ℕ → KMor1 0
@[simp] theorem KMor1.interp_natK (c : ℕ) (ctx : Fin 0 → ℕ) : ...
theorem KMor1.natK_level (c : ℕ) : (KMor1.natK c).level = 0

def KMor1.natK' (n c : ℕ) : KMor1 n := KMor1.comp (KMor1.natK c) Fin.elim0
@[simp] theorem KMor1.interp_natK' (n c : ℕ) (ctx : Fin n → ℕ) : ...
theorem KMor1.natK'_level (n c : ℕ) : (KMor1.natK' n c).level = 0
```

`GebLean/Utilities/KSimURMSimulator.lean` (new, approximately
350–450 LOC):

```text
imports                                  -- per § 6.2
module docstring                         -- with citations to § 11
namespace GebLean.KSimURMSimulator
open GebLean.ZeroTestURM
open GebLean

-- 1. PC-dispatch helper
def KMor1.pcDispatch ...
@[simp] theorem KMor1.interp_pcDispatch_match ...
@[simp] theorem KMor1.interp_pcDispatch_default ...
theorem KMor1.pcDispatch_level ...

-- 2. Base and step families
def baseFamily {a : ℕ} (P : URMProgram a) : ...
def stepFamily {a : ℕ} (P : URMProgram a) : ...

-- 3. The simulator
def simulate {a : ℕ} (P : URMProgram a) : KMor1 (1 + a)

-- 4. Correctness
private theorem simulate_step_match ...
theorem simulate_interp ...

-- 5. Level
theorem simulate_level ...

end GebLean.KSimURMSimulator
```

`GebLean.lean` (re-export change):

```lean
public import GebLean.Utilities.KSimURMSimulator
```

### 6.4 Naming conventions

Per mathlib `naming.html` and `.claude/rules/lean-coding.md`:

- `def`s: `lowerCamelCase` — `simulate`, `baseFamily`,
  `stepFamily`, `pcDispatch`, `natK`, `natK'`.
- `theorem`s: `snake_case` — `simulate_interp`, `simulate_level`,
  `simulate_step_match`, `interp_pcDispatch_match`,
  `interp_pcDispatch_default`, `pcDispatch_level`, `interp_natK`,
  `interp_natK'`, `natK_level`, `natK'_level`.
- Namespace `GebLean.KSimURMSimulator` parallels
  `GebLean.LawvereERKSim`.
- `KMor1.pcDispatch`, `KMor1.natK`, `KMor1.natK'` extend the
  existing `KMor1.cond`, `KMor1.pred`, `KMor1.add` etc. pattern in
  `KArith.lean`.

## 7 Constructive discipline

- No `noncomputable` declarations. `simulate` is a `def` returning
  data.
- No `Classical.choice`, `Classical.choose`, `Classical.em` in any
  T3 declaration or proof. `baseFamily` uses the same `List.find?`
  lookup as `URMState.init` (`ZeroTestURM.lean:254`).
- No `axiom`. No `admit`.
- `sorry` permitted only between commits per `CLAUDE.md`; not in
  committed code.
- Verified post-implementation by `scripts/check-axioms.sh` on
  every T3 public declaration. Allowlist excludes
  `Classical.choice`.

## 8 Out of scope (defers to T4 / T5 / T6)

- **`boundExprK` and runtime domination.** Master design §7.
  Deferred to T4.
- **`KMor1.maxK`, `KMor1.maxOver`, `KMor1.pow2_iter`.** The three
  level-2 K^sim composites that the master spec § 3.1 listed
  alongside `natK`. Their only consumer is T4's `boundExprK`;
  deferred to T4.
- **`erToK : ERMor1 a → KMor1 a`.** Master design § 8.1.
  Composition `KMor1.comp (simulate (compileER e))
  (Fin.cons (boundExprK e) (fun i => KMor1.proj i))`. Deferred to
  T5.
- **`erToK_level`, `erToK_interp`, `erToKN`, `erToKN_interp`,
  `erToKFunctor`.** Master design § 8.2 – § 8.4. Deferred to T5.
- **Strict categorical iso `LawvereERCat ≌ LawvereKSimDCat 2`.**
  Master design § 11. Deferred to T6.

T3 does not import `LawvereERKSim/Compiler.lean` or any consumer of
it. The simulator is total on every `URMProgram a`; the compiler's
`CompiledFragment a` structure is irrelevant.

## 9 Step decomposition

T3 is small enough to land in one branch with the following
internal task split (refined further during plan writing):

1. **T3-Task-1.** `KMor1.natK` and `KMor1.natK'` plus interp/level
   lemmas in `Utilities/KArith.lean`. Approximately 30 LOC.
2. **T3-Task-2.** `KMor1.pcDispatch` plus `interp_pcDispatch_match`,
   `interp_pcDispatch_default`, `pcDispatch_level` in
   `Utilities/KSimURMSimulator.lean`. Approximately 80 LOC.
3. **T3-Task-3.** `baseFamily` and `stepFamily` in
   `Utilities/KSimURMSimulator.lean`. Approximately 60 LOC
   (most of the size is in the per-instruction branches).
4. **T3-Task-4.** `simulate` (the assembly) plus the auxiliary
   helper projections `I_prev`, `v_j_prev`. Approximately 30 LOC.
5. **T3-Task-5.** `simulate_step_match` (the conjunctive
   induction). Approximately 100 LOC, with case-by-case
   instruction discharge.
6. **T3-Task-6.** `simulate_interp` and `simulate_level`.
   Approximately 30 LOC.
7. **T3-Task-7.** Axiom audit (`scripts/check-axioms.sh` on each
   public declaration); manual lint sweep (`lake build`,
   `markdownlint-cli2`). Approximately 10 LOC.

Two adversarial-review rounds expected on the plan; two more
expected on the implementation as it lands. Total approximate LOC:
340.

## 10 Adversarial-review punch list

The round-N adversary verifies each claim and reports findings in
`.review-N.md`. Most important obligation: every named construction
in §§ 3 – 6 carries a citation (Tourlakis location or
`File.lean:line`), and every cited claim is verifiable at the cited
source.

| # | Claim | Adversary obligation |
| --- | --- | --- |
| 10.1 | Constructive discipline preserved: no `Classical.*`, no `noncomputable`, no `axiom`, no `admit`, no `sorry`. | Grep new files. Confirm `List.find?` (not `Classical.choose`) inside `baseFamily`. Confirm `scripts/check-axioms.sh` passes on `simulate`, `simulate_interp`, `simulate_level`, `pcDispatch_level`, `natK`, `natK'`. |
| 10.2 | `baseFamily` mirrors `URMState.init` exactly. | Read `ZeroTestURM.lean:254` against § 3.3; flag any divergence in the `List.find?` predicate, the default value, or the PC starting value. |
| 10.3 | `stepFamily` mirrors `URMState.step` for all five `URMInstr` constructors plus the past-end branch. | Tabulate the 5 + 1 cases of `URMState.step` (`ZeroTestURM.lean:155`) against `branches_pc` / `branches_j` (§ 3.4); flag any case where the K^sim term does not match the Nat-side update. Special check: `.jumpZ` updates only `pc`, not registers. |
| 10.4 | Level claim for `pcDispatch`: chain stays at level 1 when branches and default are level ≤ 1. | Trace `KMor1.level` on the recursive `pcDispatch` body in § 3.5; confirm `comp` does not bump level beyond max of children, and the outermost `cond` is itself level 1 — so the chain stays at level 1 by induction on `size`. |
| 10.5 | Level claim for `simulate`: ≤ 2. | Trace `KMor1.level` on `simulate P`'s simrec shape; confirm base sup is 0, step sup is 1 (via 10.4), simrec adds 1 → 2. Confirm no `KMor1.eq` (level 2) or `KMor1.raise` is used. |
| 10.6 | `simulate_interp`'s proof uses the conjunctive vector IH (§ 4.2), not a per-component induction. | Read the proof; confirm the inductive hypothesis is the conjunction over all `numRegs + 1` components, and that each per-component step branch relies on the IH for *other* components (e.g. the `.jumpZ` PC branch reads `v_i_prev`). |
| 10.7 | Every named construction in §§ 3 – 6 cites either a Tourlakis location or `File.lean:line`. | Spot-check 4 – 6 citations against the cited sources. Flag any orphan construction or mis-citation. |
| 10.8 | No phantom infrastructure. | Trace `simulate_interp`'s proof obligation backwards through §§ 3 – 4; confirm every construction in §§ 3 – 6 contributes to the trace. Flag orphans. |
| 10.9 | Independence from kToER side. | Grep imports of `Utilities/KSimURMSimulator.lean` for `LawvereKSimER`, `LawvereKSimMajorization`, `LawvereER`, `LawvereERKSim`; expect zero matches. |
| 10.10 | No CSLib-URM dependency. | Grep new files for `Cslib.URM`, `import Cslib`; expect zero. |
| 10.11 | Scope match. | Read § 8 (out of scope) against the file outlines in § 6.3; flag any T4 / T5 / T6 construction that leaks into T3. |
| 10.12 | Naming conventions per mathlib `naming.html` and `.claude/rules/lean-coding.md`. | Verify `def`s in `lowerCamelCase`, theorems in `snake_case`, namespace in `UpperCamelCase`. Re-fetch `naming.html` each round. |
| 10.13 | Documentation conventions per mathlib `doc.html`. | Verify module docstring has required sections; verify every public `def` / `structure` / `theorem` has a `/-- … -/` docstring; verify no history references inside docstrings. |
| 10.14 | LOC estimate plausibility. | Sketch each helper's expected size against § 9; flag if the approximately 340 LOC total appears off by more than 2 ×. |
| 10.15 | Tourlakis 2018 § 0.1.0.37 transcription fidelity. | Tabulate § 6.1 of the master spec (the Tourlakis simulation lemma's `v_i` and `I` recursion equations) against `stepFamily` of this spec; flag any mismatch. The master spec is the intermediate-binding for what § 0.1.0.37 says. |

## 11 Citations

### 11.1 External (Tourlakis 2018, `PR-complexity-topics.pdf`)

- § 0.1.0.2 p. 1 — definition of `K_0` (initial functions). Grounds
  `natK` as a `c`-fold composition of `succ` with `zero`, both at
  level 0.
- § 0.1.0.17(4) p. 6 — `λx.x ∸ 1 ∈ K_1`. Grounds `pred` as level 1,
  used in `stepFamily`'s `.dec` branch and (in `pred^k`) inside
  `pcDispatch`.
- § 0.1.0.17(6) p. 6 — `switch ∈ K_1`. Grounds `cond` (= `switch`)
  as level 1, used inside `pcDispatch` and `stepFamily`'s `.jumpZ`
  branch.
- § 0.1.0.20 p. 7 — `λx.x = a ∈ K^sim_{1,*}`. Grounds the level-1
  predicate `pred^k(I) = 0 ⇔ I = k`, which is the dispatch
  primitive `pcDispatch` uses.
- § 0.1.0.37 pp. 15 – 16 — **simulation lemma.** The transcription
  source for `baseFamily` and `stepFamily`. The joint recursion
  on `(v_i, I)` is the inductive hypothesis of `simulate_step_match`.
  The conclusion "All the simulating functions are in K^sim_2" is
  the source of `simulate_level`.

### 11.2 Internal repository references

- `GebLean/Utilities/ZeroTestURM.lean:89` — `URMInstr` inductive
  (5 cases per § 0.1.0.37 p. 16).
- `GebLean/Utilities/ZeroTestURM.lean:122` — `URMProgram a`
  arity-indexed structure.
- `GebLean/Utilities/ZeroTestURM.lean:143` — `URMState P` structure.
- `GebLean/Utilities/ZeroTestURM.lean:155` — `URMState.step P`.
- `GebLean/Utilities/ZeroTestURM.lean:179` — `URMState.runFor P`,
  with `runFor_zero` and `runFor_succ` reduction lemmas at
  `:186` and `:192`.
- `GebLean/Utilities/ZeroTestURM.lean:213` — `runFor_halted_invariant`
  (past-end identity).
- `GebLean/Utilities/ZeroTestURM.lean:254` — `URMState.init P v`.
- `GebLean/LawvereKSim.lean:34` — `KMor1` inductive.
- `GebLean/LawvereKSim.lean:50` — `KMor1.simrec` constructor.
- `GebLean/LawvereKSim.lean:105` — `KMor1.level` recursion.
- `GebLean/LawvereKSimInterp.lean:162` — `KMor1.interp_simrec` (the
  public `@[simp]` lemma).
- `GebLean/LawvereKSimInterp.lean:180` — `KMor1.simrecVec_zero`.
- `GebLean/LawvereKSimInterp.lean:193` — `KMor1.simrecVec_succ`.
- `GebLean/Utilities/KArith.lean:44` — `KMor1.pred` (level 1).
- `GebLean/Utilities/KArith.lean:222` — `KMor1.cond` (level 1).
- `GebLean/Utilities/KArith.lean:249` — `KMor1.interp_cond`
  (`@[simp]`).

## 12 References

- Master design:
  `docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`.
- T1 / T2 spec:
  `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`
  (this T3 spec re-specs that document's § 6 against landed T1 / T2
  shapes).
- T2 plan:
  `docs/superpowers/plans/2026-05-17-step-t2-er-to-urm-compiler.md`.
- T2 partial-completion handoff:
  `docs/superpowers/plans/2026-05-18-step-t2-t11-handoff.md`.
- Post-T2 handoff (Step B framing):
  `docs/superpowers/plans/2026-05-20-post-t2-handoff.md`.
- Project process: `docs/process.md`.
- Project rules: `CLAUDE.md`, `.claude/rules/lean-coding.md`,
  `.claude/rules/markdown-writing.md`,
  `.claude/rules/fork-upstream-flow.md`.
- Tourlakis 2018 `PR-complexity-topics.pdf` — § 0.1.0.37
  (simulation lemma), § 0.1.0.17 (catalogue of K^sim primitives
  used).
