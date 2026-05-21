# T3 — URM → K^sim simulator — design

Re-spec of master design §7 ("The simulator (erToK side)", lines
1902–1943 of
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`)
and the parallel §6 of the T1/T2 spec at
`docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`,
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
- `simulate : URMProgram a → KMor1 (a + 1)`.
- `simulate_interp`: simulator output equals `URMState.runFor`
  output projected at `outputReg`.
- `simulate_level`: `(simulate P).level ≤ 2`.

The runtime bound (`boundExprK`; master design § 9) and the
level-2 K^sim composites it consumes (`maxK`, `maxOver`,
`pow2_iter`) are deferred to T4; the `erToK` assembly and the
`erToKFunctor` (master design § 10) are deferred to T5; the
strict iso (master design § 11) is deferred to T6. See § 8.

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
| `KMor1.interp_zero` (`@[simp]`) | `GebLean/LawvereKSimInterp.lean:86` | Reduces `baseFamily`'s PC component and `none`-branch register components. |
| `KMor1.interp_proj` (`@[simp]`) | `GebLean/LawvereKSimInterp.lean:98` | Reduces `baseFamily`'s `some i` branch and `stepFamily`'s helper projections. |
| `KMor1.cond` (Tourlakis `switch`, level 1) | `GebLean/Utilities/KArith.lean:222` | Inner combinator of `pcDispatch`. |
| `KMor1.interp_cond` (`@[simp]`) | `GebLean/Utilities/KArith.lean:249` | Reduces `pcDispatch`'s nested `cond` chain. |
| `KMor1.pred` (level 1) | `GebLean/Utilities/KArith.lean:44` | Used both inside `pcDispatch` (`pred^k(I) = 0` ⇔ `I ≤ k`, threaded into the bottom-up `cond` chain) and inside `stepFamily` (`.dec` branch). |

T3 does not depend on `LawvereER*`, `LawvereERKSim/*`,
`LawvereKSimER*`, `LawvereKSimMajorization*`, or any CSLib URM
module. See § 6.2.

## 3 Architecture

### 3.1 Public signature

```lean
def simulate {a : ℕ} (P : URMProgram a) : KMor1 (a + 1)

theorem simulate_interp {a : ℕ} (P : URMProgram a)
    (y : ℕ) (v : Fin a → ℕ) :
    (simulate P).interp (Fin.cons y v)
      = ((URMState.init P v).runFor y).regs P.outputReg

theorem simulate_level {a : ℕ} (P : URMProgram a) :
    (simulate P).level ≤ 2
```

The simulator's context arity is `a + 1`: slot 0 carries the
time bound `y`, slots `1..a` carry the input vector `v`. The
output is the value of `P.outputReg` after `y` steps from
`URMState.init P v`. The arity `a + 1` matches
`KMor1.simrec`'s return type (`KMor1 (a + 1)`,
`LawvereKSim.lean:50`) definitionally; `Fin.cons y v` has type
`Fin (a + 1) → ℕ`.

### 3.2 `simrec` system shape

`simulate P` is a single `KMor1.simrec`:

- recursion variable: `y` (slot 0 of the outer context);
- parameters: `v` (slots `1..a`);
- system size: `P.numRegs + 1`;
- component layout: for each `j : Fin P.numRegs`, the component
  at simrec index `j.castSucc : Fin (P.numRegs + 1)` holds
  register `j`'s value; the component at simrec index
  `Fin.last P.numRegs : Fin (P.numRegs + 1)` holds the PC;
- output index: `P.outputReg.castSucc : Fin (P.numRegs + 1)`.

Placing the PC at the last component aligns the previous-PC
step-context slot with the last slot of the step context, which
is the slot `KMor1.pcDispatch` (§ 3.5) reads.

Picking `Fin.cons y v` as the input convention matches
`interp_simrec`'s context-splitting (`ctx 0` for the recursion
variable; `Fin.succ` projection for parameters).

### 3.3 Base family `baseFamily`

Mirrors `URMState.init` syntactically, with the component layout
of § 3.2. The mathlib-idiomatic destructuring is via
`Fin.lastCases`: the PC component is `Fin.last P.numRegs`; each
register component is `(j : Fin P.numRegs).castSucc`.

```lean
def baseFamily {a : ℕ} (P : URMProgram a) :
    Fin (P.numRegs + 1) → KMor1 a :=
  Fin.lastCases
    -- PC component: initial value 0
    (KMor1.zero : KMor1 a)
    -- Register component for `r : Fin P.numRegs`
    (fun r =>
      match (List.finRange a).find?
            (fun i => decide (P.inputRegs i = r)) with
      | some i => KMor1.proj i
      | none   => KMor1.zero)
```

In the `some i` branch, `i : Fin a` is the input slot index
returned by `List.find?` (distinct from the outer-scope register
index `r : Fin P.numRegs`); `KMor1.proj i` then has type
`KMor1 a`, matching the `baseFamily` return type. Each subterm
is `KMor1.zero` or `KMor1.proj _`, so each `baseFamily P j` is
at level 0.

### 3.4 Step family `stepFamily`

```lean
def stepFamily {a : ℕ} (P : URMProgram a) :
    Fin (P.numRegs + 1) → KMor1 (a + 1 + (P.numRegs + 1))
```

Per `KMor1.interp_simrec_eq_simrecVec`, the step context for one
`stepFamily j` call has arity `a + 1 + (P.numRegs + 1) =
a + numRegs + 2`. The previous-component slots are placed at
`slot = a + 1 + i` for component index `i : Fin (P.numRegs + 1)`.
Combined with § 3.2's component layout (registers at indices
`0..numRegs − 1`, PC at index `numRegs`):

| slot | meaning |
| --- | --- |
| `0` | current iteration counter `m` (unused) |
| `1..a` | input vector `v` (used only as input slot reference) |
| `a + 1 + j` for `j : Fin P.numRegs` | previous register value `v_j_prev` |
| `a + 1 + numRegs` (the last slot, `Fin.last (a + numRegs + 1) : Fin (a + numRegs + 2)`) | previous PC value `I_prev` |

Helper projections (each is `KMor1.proj …` at level 0):

- `v_j_prev : Fin P.numRegs → KMor1 (a + 1 + (P.numRegs + 1))`
  — slot `a + 1 + j.val`.
- `I_prev : KMor1 (a + 1 + (P.numRegs + 1))`
  — last slot (`a + 1 + numRegs`).

The PC slot's coincidence with the last context slot is the
alignment that lets `pcDispatch` (§ 3.5) read it directly.

PC component (= `Fin.last P.numRegs`):

```text
stepFamily P (Fin.last P.numRegs) :=
  pcDispatch P.instrs.size branches_pc default_pc

branches_pc k := match P.instrs[k]'_ with
  | .stop          => I_prev                            -- identity
  | .jumpZ i l₁ l₂ => cond ∘ ⟨v_i_prev, natK' _ l₁, natK' _ l₂⟩
  | _              => succ ∘ I_prev                     -- PC + 1
default_pc       := I_prev                              -- past-end self-loop
```

Register-`j` component (= `j.castSucc`, for each
`j : Fin P.numRegs`):

```text
stepFamily P j.castSucc :=
  pcDispatch P.instrs.size branches_j default_j

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

The dispatcher is instantiated with `n := a + numRegs + 1` so its
return type `KMor1 (n + 1)` matches the step context arity
`a + numRegs + 2`. Explicitly,
`n + 1 = a + 1 + (numRegs + 1) = a + numRegs + 2`, so
`n = a + numRegs + 1`. Branches and default are typed at the
same arity `n + 1`, so each may read any context slot directly
(no lift required); in particular, `I_prev` and each `v_j_prev`
project at the appropriate slot of the full step context, and
their interpretations remain at the unshifted step context
throughout (per § 3.5's non-substituting recursion).

### 3.5 PC-dispatch helper `KMor1.pcDispatch`

```lean
def KMor1.pcDispatch {n : ℕ} (size : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) :
    KMor1 (n + 1)
```

Branches and default share the dispatcher's output arity `n + 1`,
giving each access to all context slots (including the last slot,
which carries the PC value being dispatched on). Branches may
ignore the PC slot if they choose, but the `default` term reads
the PC slot to realise the past-end self-loop (`default_pc :=
I_prev` in § 3.4).

Implementation is a flat fold of `cond` tests on iterated
predecessors of the PC slot, with **no substitution** applied
to branches or default. Let `PC := KMor1.proj (Fin.last n)`
and define a standalone `private def` for the `k`-fold
composition of `KMor1.pred` over `PC`:

```lean
private def KMor1.predIter (n k : ℕ) : KMor1 (n + 1) :=
  match k with
  | 0     => KMor1.proj (Fin.last n)
  | k + 1 => KMor1.comp KMor1.pred
               (fun _ : Fin 1 => KMor1.predIter n k)

@[simp] theorem KMor1.interp_predIter
    (n k : ℕ) (ctx : Fin (n + 1) → ℕ) :
    (KMor1.predIter n k).interp ctx = ctx (Fin.last n) ∸ k

theorem KMor1.predIter_level (n k : ℕ) :
    (KMor1.predIter n k).level ≤ 1
```

`KMor1.predIter n k` has level 1 for `k ≥ 1`, level 0 for
`k = 0` (since `KMor1.pred.level = 1` and `KMor1.comp` takes
`max`).

The dispatcher is then defined by recursion on `size`, building
the chain from the outside in. Critically, each `cond` sits at
the same context as its siblings; branches and default are
never wrapped in a context-substituting `KMor1.comp` along the
way:

```text
pcDispatch 0           branches default := default

pcDispatch (size + 1) branches default :=
  KMor1.comp KMor1.cond
    (fun i : Fin 3 => match i with
      | ⟨0, _⟩ => predIter 0             -- test PC = 0
      | ⟨1, _⟩ => branches ⟨0, _⟩        -- selected if PC = 0
      | ⟨2, _⟩ => pcDispatchFrom 1 size
                    (branches ∘ Fin.succ) default)
```

where `pcDispatchFrom k size branches default` is a `private`
auxiliary "test `predIter k`, then `predIter (k + 1)`, etc."
continuation:

```text
private def KMor1.pcDispatchFrom {n : ℕ} (k size : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) : KMor1 (n + 1)

pcDispatchFrom k 0           branches default := default

pcDispatchFrom k (size + 1) branches default :=
  KMor1.comp KMor1.cond
    (fun i : Fin 3 => match i with
      | ⟨0, _⟩ => KMor1.predIter n k     -- test pred^k(PC) = 0
      | ⟨1, _⟩ => branches ⟨0, _⟩        -- selected if PC = k
      | ⟨2, _⟩ => pcDispatchFrom (k + 1) size
                    (branches ∘ Fin.succ) default)
```

The branches and default appear inside `cond` without any
context-substituting `KMor1.comp` wrapping; their interpretation
contexts are identical to the surrounding context. The fall-
through semantics: `cond(predIter k, branches ⟨k, _⟩, rest)`
selects `branches ⟨k, _⟩` exactly when `pred^k(PC) = 0`
(i.e. `PC ≤ k`), and falls through to `rest` otherwise (i.e.
`PC > k`). Inside the chain, by the time the `k`-th test is
reached, every earlier test has fallen through (so `PC ≥ k`);
combined with `PC ≤ k` from the current test, this yields
`PC = k` and the correct selection of `branches ⟨k, _⟩`.

Tourlakis citation: § 0.1.0.20 p. 7 establishes
`λx.x ≤ a ∈ K_{1,*}` (predicate-on-`K_1` sub-class); chained
with § 0.1.0.8 p. 3 (`K_1 ⊆ K^sim_1`), `pred^k(I) = 0 ⇔ I ≤ k`
sits at level 1, which is what `cond`'s test slot consumes
without bumping the surrounding level.

Key lemmas:

```lean
@[simp] theorem KMor1.interp_pcDispatch_match
    {n size : ℕ} (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) (ctx : Fin (n + 1) → ℕ)
    (k : Fin size) (h : ctx (Fin.last n) = k.val) :
    (KMor1.pcDispatch size branches default).interp ctx
      = (branches k).interp ctx

@[simp] theorem KMor1.interp_pcDispatch_default
    {n size : ℕ} (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) (ctx : Fin (n + 1) → ℕ)
    (h : ctx (Fin.last n) ≥ size) :
    (KMor1.pcDispatch size branches default).interp ctx
      = default.interp ctx

theorem KMor1.pcDispatch_level {n size : ℕ}
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1))
    (h_branches : ∀ k, (branches k).level ≤ 1)
    (h_default : default.level ≤ 1) :
    (KMor1.pcDispatch size branches default).level ≤ 1
```

Both `interp_pcDispatch_match` and `interp_pcDispatch_default`
are `@[simp]` but conditionally so: their hypotheses
(`ctx (Fin.last n) = k.val` or `ctx (Fin.last n) ≥ size`)
must be in the local proof context for the rewrite to fire. In
the `simulate_step_match` step case (§ 4.3), these hypotheses
arise from the case-split on the instruction at the previous
PC: each branch of the case-split fixes the previous PC value
to a specific `k.val` (in-bounds) or witnesses `≥ size`
(past-end), and the corresponding simp lemma applies.

Level analysis (by induction on `size`, simultaneously over
`pcDispatch` and `pcDispatchFrom k`, with `k` *universally
quantified* in the inductive hypothesis on `pcDispatchFrom`):

- Base case `pcDispatch 0 _ default = default` and
  `pcDispatchFrom k 0 _ default = default` at level
  `default.level ≤ 1`.
- Recursive case: `KMor1.predIter n k` is at level ≤ 1
  (level 0 for `k = 0`, level 1 for `k ≥ 1`); each branch is at
  level ≤ 1 by hypothesis; the recursive `pcDispatchFrom
  (k + 1) size` call is at level ≤ 1 by induction (the
  universal quantification of `k` lets the IH apply at
  `k + 1`). The outer `KMor1.comp KMor1.cond [predIter n k,
  branches[0], recur]` is at level
  `max (KMor1.cond.level) (max-of-children-levels) =
  max 1 1 = 1`. Inductive step preserves the bound.

The proofs of `interp_pcDispatch_match`,
`interp_pcDispatch_default`, and `pcDispatch_level` all use
the same `size`-induction shape with `k` and `branches`
generalised. The recursive call's `branches ∘ Fin.succ` is
consumed by the IH's branch-family parameter, which the
universal quantification accommodates.

Branches and default appear inside `cond` without any
context-substituting `KMor1.comp` wrapping; their levels enter
the maximum directly, with no shift-induced bump.

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

Holds for every `URMProgram a`; no `WellBounded` precondition is
required. The K^sim side's `default_pc := I_prev` matches
`URMState.step`'s past-end self-loop, and `runFor`'s post-halt
invariant (`URMState.runFor_halted_invariant`,
`GebLean/Utilities/ZeroTestURM.lean:213`) follows from the same
identity.

### 4.2 Conjunctive vector invariant

The induction goes through the conjunctive form (using § 3.2's
component layout: PC at `Fin.last P.numRegs`, registers at
`j.castSucc` for `j : Fin P.numRegs`):

```lean
private theorem simulate_step_match {a : ℕ}
    (P : URMProgram a) (v : Fin a → ℕ) (y : ℕ) :
    KMor1.simrecVec (baseFamily P) (stepFamily P) v y
        (Fin.last P.numRegs)
      = ((URMState.init P v).runFor y).pc
    ∧ ∀ j : Fin P.numRegs,
        KMor1.simrecVec (baseFamily P) (stepFamily P) v y
            j.castSucc
          = ((URMState.init P v).runFor y).regs j
```

The conjunction is necessary because the PC step family
(`stepFamily P (Fin.last P.numRegs)`) reads previous register
values via the `.jumpZ` branch's `v_i_prev`. Each register-`j`
step family reads only the previous PC (for `pcDispatch`'s test)
and the previous register `j`; it does not read other registers'
previous values. The joint IH is therefore forced by the PC's
cross-component read, not by every step family's read pattern.

### 4.3 Proof outline

By induction on `y`.

**Base case `y = 0`.** Both sides reduce by `simrecVec_zero` and
`runFor_zero` to the same `baseFamily P` / `URMState.init P v`
definitions. The PC component reduces by `interp_zero` to `0`,
which equals `(URMState.init P v).pc = 0`. For each register
component, case-split on the `Option (Fin a)` result of
`(List.finRange a).find? (fun i => decide (P.inputRegs i = r))`:
in the `some i` branch, both sides reduce by `interp_proj` and
the `URMState.init` register definition to `v i`; in the `none`
branch, both reduce by `interp_zero` to `0`. The case-split is
explicit (not closed by `rfl` alone), but each case closes after
the relevant `simp` chain.

**Step case `y + 1`.** The URM side requires the back-peel
reduction `runFor (init P v) (y + 1) = step (runFor (init P v) y)`.
This is derived from `URMState.runFor_succ` (`:192`, front-peel)
and `URMState.runFor_add` (`:199`) by the chain:
`runFor s 1 = runFor (step s) 0 = step s` (by `runFor_succ` at
`n = 0`); then `runFor s (y + 1) = runFor (runFor s y) 1
= step (runFor s y)` (by `runFor_add` and the previous step).
Citing only `runFor_succ` is insufficient because the fixed
`s := URMState.init P v` is incompatible with `runFor_succ`'s
front-peel rewrite. Note: `runFor_succ` is `@[simp]` in the
front-peel direction; the back-peel form derived above is not
`@[simp]` and must be invoked manually inside the step case,
since adding `runFor_succ` to a `simp` set under the fixed
`s := init P v` would rewrite the wrong direction.

After the back-peel reduction:

- URM side: `runFor (y + 1) = step (runFor y)`.
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
`j = P.outputReg` (the simrec output index is
`P.outputReg.castSucc` per § 3.2); combine with `interp_simrec`'s
unfolding of `simulate P` at the public-facing context; close by
`rfl`. No additional lemmas required.

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
- The `KMor1.level`'s `.simrec` clause
  (`LawvereKSim.lean:111`) is
  `max (Finset.univ.sup (·.level over h))
   (Finset.univ.sup (·.level over g)) + 1`. With `sup_h = 0`
  and `sup_g ≤ 1`, this yields `max 0 1 + 1 = 2`.

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
`Utilities/ZeroTestURM.lean`) and produces `KMor1 (a + 1)` (from
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

/-!
# Title
brief summary
## Main definitions
## Main statements
## Notation              -- (omit if none)
## Implementation notes  -- (omit if none)
## References            -- citations per § 11
## Tags
-/

-- KMor1 namespace extensions (declared inside `namespace GebLean`
-- to match the existing `KMor1.cond` pattern in `KArith.lean`).
namespace GebLean
private def KMor1.predIter ...
@[simp] theorem KMor1.interp_predIter ...
theorem KMor1.predIter_level ...
private def KMor1.pcDispatchFrom ...
def KMor1.pcDispatch ...
@[simp] theorem KMor1.interp_pcDispatch_match ...
@[simp] theorem KMor1.interp_pcDispatch_default ...
theorem KMor1.pcDispatch_level ...
end GebLean

-- Simulator definitions (under a fresh namespace).
namespace GebLean.KSimURMSimulator
open GebLean.ZeroTestURM
open GebLean

-- 1. Base and step families
def baseFamily {a : ℕ} (P : URMProgram a) : ...
def stepFamily {a : ℕ} (P : URMProgram a) : ...

-- 2. The simulator
def simulate {a : ℕ} (P : URMProgram a) : KMor1 (a + 1)

-- 3. Correctness
private theorem simulate_step_match ...
theorem simulate_interp ...

-- 4. Level
theorem simulate_level ...

end GebLean.KSimURMSimulator
```

The module docstring follows mathlib `doc.html`'s prescribed
section ordering verbatim. The `KMor1.*` helpers and the
simulator-specific definitions sit in different namespaces so
that `KMor1.pcDispatch` is fully qualified
`GebLean.KMor1.pcDispatch`, matching `GebLean.KMor1.cond` at
`KArith.lean:222`.

`GebLean.lean` (re-export change):

```lean
import GebLean.Utilities.KSimURMSimulator
```

Plain `import` (not `public import`) matches the existing
`GebLean.lean` re-export pattern; the cited Lean source files do
not declare `module` at top, so `public import` would have no
extra effect.

### 6.4 Naming conventions

Per mathlib `naming.html` and `.claude/rules/lean-coding.md`:

- `def`s: `lowerCamelCase` — `simulate`, `baseFamily`,
  `stepFamily`, `pcDispatch`, `natK`, `natK'`.
- `theorem`s: `snake_case` — `simulate_interp`, `simulate_level`,
  `simulate_step_match`, `interp_pcDispatch_match`,
  `interp_pcDispatch_default`, `pcDispatch_level`, `interp_natK`,
  `interp_natK'`, `natK_level`, `natK'_level`.
- Namespace placement (per § 6.3): `KMor1.pcDispatch`, `KMor1.natK`,
  `KMor1.natK'` are declared inside `namespace GebLean` directly,
  yielding `GebLean.KMor1.pcDispatch` etc.; this matches the
  existing `KMor1.cond`, `KMor1.pred`, `KMor1.add` pattern in
  `KArith.lean`. The simulator-specific definitions
  (`baseFamily`, `stepFamily`, `simulate`, `simulate_step_match`,
  `simulate_interp`, `simulate_level`) are declared inside
  `namespace GebLean.KSimURMSimulator`, paralleling
  `GebLean.LawvereERKSim`.

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

- **`boundExprK` and runtime domination.** Master design § 9
  ("The runtime-bound function (erToK side)"). Deferred to T4.
- **`KMor1.maxK`, `KMor1.maxOver`, `KMor1.pow2_iter`.** The three
  level-2 K^sim composites listed alongside `natK` in the T1/T2
  spec's § 3.1. Their only consumer is T4's `boundExprK`;
  deferred to T4.
- **`erToK : ERMor1 a → KMor1 a`.** Master design § 10 ("The
  functors and interp-preservation"). Composition
  `KMor1.comp (simulate (compileER e))
  (Fin.cons (boundExprK e) (fun i => KMor1.proj i))`. Deferred to
  T5.
- **`erToK_level`, `erToK_interp`, `erToKN`, `erToKN_interp`,
  `erToKFunctor`.** Master design § 10. Deferred to T5.
- **Strict categorical iso `LawvereERCat ≌ LawvereKSimDCat 2`.**
  Master design § 11 ("The categorical isomorphism"). Deferred
  to T6.

T3 does not import `LawvereERKSim/Compiler.lean` or any consumer of
it. The simulator is total on every `URMProgram a`; the compiler's
`CompiledFragment a` structure is irrelevant.

## 9 Step decomposition

T3 is small enough to land in one branch with the following
internal task split (refined further during plan writing):

1. **T3-Task-1.** `KMor1.natK` and `KMor1.natK'` plus interp/level
   lemmas in `Utilities/KArith.lean`. Approximately 30 LOC.
2. **T3-Task-2.** `KMor1.predIter` (private), its `@[simp]`
   interp lemma, its level lemma; `KMor1.pcDispatch` plus
   `pcDispatchFrom` (private), `interp_pcDispatch_match`,
   `interp_pcDispatch_default`, `pcDispatch_level` in
   `Utilities/KSimURMSimulator.lean`. Approximately 120–150
   LOC (the joint induction over `pcDispatchFrom` with `k`
   generalised, plus the conditional-simp semantics, push the
   per-task size above the initial 80 LOC estimate).
3. **T3-Task-3.** `baseFamily` and `stepFamily` in
   `Utilities/KSimURMSimulator.lean`. Approximately 60 LOC
   (most of the size is in the per-instruction branches).
4. **T3-Task-4.** `simulate` (the assembly) plus the auxiliary
   helper projections `I_prev`, `v_j_prev`. Approximately 30 LOC.
5. **T3-Task-5.** `simulate_step_match` (the conjunctive
   induction). Approximately 150–250 LOC, with case-by-case
   instruction discharge plus per-instruction `Function.update`
   propagation between the K^sim and URM sides.
6. **T3-Task-6.** `simulate_interp` and `simulate_level`.
   Approximately 30 LOC.
7. **T3-Task-7.** Axiom audit (`scripts/check-axioms.sh` on each
   public declaration); manual lint sweep (`lake build`,
   `markdownlint-cli2`). Approximately 10 LOC.

Two adversarial-review rounds expected on the plan; two more
expected on the implementation as it lands. Total approximate
LOC: 360–500.

## 10 Adversarial-review punch list

The round-N adversary verifies each claim and reports findings in
`.review-N.md`. Primary obligation: every named construction in
§§ 3 – 6 carries a citation (Tourlakis location or
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
| 10.15 | Tourlakis 2018 § 0.1.0.37 transcription fidelity. | Tabulate master design § 7 (and Tourlakis § 0.1.0.37 pp. 15–16, the literal source of the simulation lemma's `v_i` and `I` recursion equations) against `stepFamily` of this spec; flag any mismatch. |
| 10.16 | `pcDispatch` interpretation correctness under its recursion. | Trace the recursive case of `pcDispatch (size + 1)` and `pcDispatchFrom k (size + 1)` (§ 3.5) under `KMor1.interp`; confirm that `interp_pcDispatch_match` and `interp_pcDispatch_default` are provable as stated. Specifically: that branches' and default's interpretation contexts inside the dispatcher remain identical to the surrounding context (no PC-slot substitution by the recursion structure). |

## 11 Citations

### 11.1 External (Tourlakis 2018, `PR-complexity-topics.pdf`)

- § 0.1.0.2 p. 1 — definition of `K_0` (Axt–Heinemann hierarchy
  initial set, closure of `{λx.x, λx.x+1}` under substitution).
  Grounds the level-0 closure principle under which composing
  `KMor1.succ` (level 0) with `KMor1.zero` (level 0) `c`-fold
  yields a level-0 morphism. The specific `succ ∘ zero` constant
  pattern is the internal `KArith.lean` precedent set by
  `KMor1.one` at `KArith.lean:31`, not Tourlakis's definition
  (Tourlakis's `K_0` does not contain a closed `zero`; constants
  arise from substitution on `λx.x` and `λx.x+1`). The level-0
  placement of `natK` is sound by the closure principle.
- § 0.1.0.17(4) p. 6 — `λx.x ∸ 1 ∈ K_1`. Grounds `pred` as level 1,
  used in `stepFamily`'s `.dec` branch and (in `pred^k`) inside
  `pcDispatch`. Tourlakis's `∸` is truncated decrement, matching
  Lean's `Nat.sub` clamped at zero; `KMor1.pred` realises
  `λx.x ∸ 1` as defined.
- § 0.1.0.17(6) p. 6 — `switch ∈ K_1`. Grounds `cond` (= `switch`)
  as level 1, used inside `pcDispatch` and `stepFamily`'s `.jumpZ`
  branch.
- § 0.1.0.20 p. 7 — `λx.x ≤ a, λx.x < a, λx.x = a ∈ K_{1,*}`
  (the predicate sub-class of `K_1`). Chained with § 0.1.0.8
  (`K_n ⊆ K^sim_n`, p. 3) for the `K^sim_{1,*}` containment.
  Grounds the level-1 inequality `pred^k(PC) = 0 ⇔ PC ≤ k`,
  which is the test `pcDispatch`'s bottom-up `cond` chain uses;
  the chain's nested-fall-through structure (§ 3.5) converts
  the inequality at the `k`-th level into the equality
  `PC = k`.
- § 0.1.0.37 pp. 15 – 16 — **simulation lemma.** The transcription
  source for `baseFamily` and `stepFamily`. The joint recursion
  on `(v_i, I)` is the inductive hypothesis of `simulate_step_match`.
  The conclusion "All the simulating functions are in K^sim_2" is
  the source of `simulate_level`. Note: Tourlakis's I-recursion
  (p. 16) has "otherwise = I + 1"; this spec follows the prose
  immediately preceding § 0.1.0.37 ("computation continues
  forever trivially, without changing either the V_i or the
  instruction number") and the landed `URMState.step`'s
  past-end `else s` self-loop, which matches the prose.

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
- `GebLean/LawvereKSimInterp.lean:86` — `KMor1.interp_zero`
  (`@[simp]`).
- `GebLean/LawvereKSimInterp.lean:98` — `KMor1.interp_proj`
  (`@[simp]`).
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
