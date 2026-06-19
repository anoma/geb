# Era completeness Phase 6-7 sub-plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [How to work this plan](#how-to-work-this-plan)
- [Route fidelity (why the recurrence engine, not a direct count)](#route-fidelity-why-the-recurrence-engine-not-a-direct-count)
- [File structure](#file-structure)
- [Phase map and the internal re-checkpoint](#phase-map-and-the-internal-re-checkpoint)
- [Task 0: relocate `Tm.weaken` to `Era.lean` (#916)](#task-0-relocate-tmweaken-to-eralean-916)
- [Phase 6 — `eraBSum` and `eraBProd` via the recurrence engine](#phase-6--erabsum-and-erabprod-via-the-recurrence-engine)
  - [Task 6.1: positional-coding predicates `E_Code`, `E_π` (Lemma 3)](#task-61-positional-coding-predicates-e_code-e_%CF%80-lemma-3)
  - [Task 6.2: the master trajectory relation and its solution count (Claims 3-4)](#task-62-the-master-trajectory-relation-and-its-solution-count-claims-3-4)
  - [Task 6.3: the counting identity `#solutions(E₂) = histCode` (Claim 5)](#task-63-the-counting-identity-solutionse%E2%82%82--histcode-claim-5)
  - [Task 6.4: `eraHistCode` — the history code as an `Era` term (RE-CHECKPOINT)](#task-64-erahistcode--the-history-code-as-an-era-term-re-checkpoint)
  - [Task 6.5: `eraBSum`](#task-65-erabsum)
  - [Task 6.6: `eraBProd`](#task-66-erabprod)
- [Phase 7 — capstones](#phase-7--capstones)
  - [Task 7.1: `era_complete`](#task-71-era_complete)
  - [Task 7.2: the K-sim-2 corollary](#task-72-the-k-sim-2-corollary)
- [Self-review checklist (run before adversarial review)](#self-review-checklist-run-before-adversarial-review)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps
> use checkbox (`- [x]`) syntax for tracking.

**Goal:** Build the bounded-sum and bounded-product term formers
`eraBSum`/`eraBProd` with their `eval` lemmas, then assemble
`era_complete` (every `ERMor1` elementary function is the denotation of
an `Era` term) and the K-sim-2 corollary, closing the M3b completeness
direction.

**Architecture:** Transcribe the Istrate-Prunescu-Shunia
recurrence-to-term metatheorem (arXiv:2606.09336, Theorem 2) at order
`k = 1`. Both formers are instances of one engine: a first-order
recurrence `s(m+1) = step m (s m)` becomes the closed-form term
`s(n) = ⌊H/Aⁿ⌋`, where the history code `H` is materialised as a
solution-count term via the Prunescu-Sauras-Altuzarra hypercube method
(arXiv:2407.12928, Section 4 / `count_zeros_eq`) applied to the
Diophantine encoding `diophOf` (Phase 4) of the step. `eraBSum` uses
`step m s = s + f m`; `eraBProd` uses `step m s = s · f m`. No direct
2-D lattice-point count is used: the papers represent every bounded sum
only through this recurrence engine (verified against both sources;
§ "Route fidelity"). The ℕ-level read-offs (`recurrence_readoff`,
`count_zeros_eq`, `positional_readoff`) are already proven (Phase 5);
this plan adds the trajectory-encoding glue (Claims 1-5) and the
`Era`-term realisations.

**Tech stack:** Lean 4, Mathlib (pin `v4.29.0-rc6`), `lake build` /
`lake test` / `lake lint`, `scripts/check-axioms.sh`. Constructive-only
(no `noncomputable`); axiom-clean (`propext`, `Quot.sound`,
`Classical.choice` only).

---

## How to work this plan

- **One declaration at a time** (`.claude/rules/lean-coding.md`): write a
  `def`/`theorem`, get it building with no `sorry`/underscore, then move
  on. `sorry` is an audited stand-in *between* steps only; never in a
  commit; `admit` is never permitted; use `_` for a transient hole that
  elaboration flags.

- **Numeric sanity checks** use `#eval` on plain-`ℕ` closed forms only
  (fast and safe). Do **not** `#eval`/`#guard` symbolic `Tm.eval`
  reductions — they expand the Gödel-style composite and hang (memory:
  "ER / Gödel-numbering interp not safe for `#guard`"). Test `Era` terms
  only through proven `eval` lemmas. Delete every `#eval` probe before
  committing.

- **Per-commit**: `bash scripts/pre-commit.sh` (runs `lake test` +
  `lake lint`) before every `.lean` commit. Commit subjects: imperative,
  lowercase, no trailing period, under ~72 characters; end the message
  with the
  `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`
  trailer.

- **VCS**: `jj` only; no raw mutating `git`. Each task is one or more
  `jj` commits (subagent-driven: implementers edit and verify, the
  controller commits and reviews).

- **Mathlib search** before each from-scratch proof: `lean_leansearch`,
  `lean_loogle`, `lean_local_search` (do not assume a lemma name).

- **Read the source before transcribing.** This phase transcribes
  published mathematics; the binding sources are local PDFs (§ References).
  Each ℕ-level lemma cites the exact paper claim/equation it transcribes.
  The only details to supply beyond the papers are the ones mathematicians
  skip: exact constants in bounds, the explicit majorant/width terms, and
  the strict-inequality witness discharges. Do not invent constructions
  the sources do not contain.

## Route fidelity (why the recurrence engine, not a direct count)

Both governing papers were read to settle the construction:

- arXiv:2606.09336 (the recurrence paper) represents **every** sequence,
  including running sums, only through Theorem 2 as the order-1 recurrence
  `s(m+1) = s(m) + f(m)`, giving `s(n) = ⌊H/Aⁿ⌋`. It contains no named
  `Σ`/`Π` corollary and no lattice-point-count representation of a sum.
- arXiv:2407.12928 (the count paper) counts only zero-sets `{ā : P(ā)=0}`
  of a predicate that is — or reduces (Lemma 3.5) to — a *simple-in-x̄
  exponential polynomial*, precisely so the packed `M` factorises via the
  cube-sum identity (Lemma 3.2) into geometric progressions. It represents
  a fixed list of named functions, never a general bounded sum, and makes
  no `Σ`-elimination claim.

A direct 2-D count `Σ_{i<y} f(i) = #{(i,w) : i<y ∧ w<f(i)}` would be a
divergence from both papers, and its predicate `w < f(i)` is not separable
for a general summand, so the packed `M` would not factorise. The
recurrence engine is therefore both the faithful and the only sound route,
and it is required regardless because `eraBProd` is not a count. This
**supersedes** the decision note's "`eraBSum` also admits the direct 2-D
form" remark (`docs/superpowers/notes/2026-06-14-erabsum-m3b-construction-decision.md`
§ 4.3), which is corrected by Task 0.

## File structure

- `GebLean/Era.lean` (exists): receives `Tm.weaken` and `Tm.eval_weaken`
  (relocated from `EraDiophantine.lean`; Task 0 / #916). These are
  general `Tm` combinators (`subst` of a variable renaming), no Mathlib,
  so `Era.lean` retains its no-Mathlib property.

- `GebLean/Utilities/EraRecurrence.lean` (new): the ℕ-level
  recurrence-to-term engine. The positional-coding predicates
  (`E_Code`, `E_π`; Lemma 3), the master trajectory relation and its
  solution-count characterisation (Claims 3-4), the `ω₁+ω₂+1` counting
  identity (Claim 5: `#solutions(E₂) = histCode`), and the `Era`-term
  realisation `eraHistCode` (via `count_zeros_eq` + `cubeSum_factor`) with
  its `eval` lemma, plus the general former `eraRec` with
  `eval (eraRec …) = recSeq …` (via `recurrence_readoff`). Imports
  `EraDiophantine` (for `diophOf`, `DiophEnc`, `SosSystem`) and
  `EraHypercube` (for `count_zeros_eq`, `recSeq`, `histCode`,
  `recurrence_readoff`, `cubeSum_factor`).

- `GebLean/EraCompleteness.lean` (exists): `eraBSum`/`eraBProd` as the two
  `eraRec` instances with their `eval` lemmas against `natBSum`/`natBProd`;
  the capstones `era_complete` and the K-sim-2 corollary. Imports
  `EraRecurrence`.

## Phase map and the internal re-checkpoint

Task 0 (relocation) is mechanical. Phase 6 is the dominant cost and the
principal schedule risk; its core is Task 6.4 (`eraHistCode` as a term),
which glues `diophOf` and `count_zeros_eq` through the cube-sum
factorisation. **Re-checkpoint:** before executing Task 6.4, with Tasks
6.1-6.3 landed and the exact `E₂` ℕ-shape known, re-read arXiv:2407.12928
§ 4 (the `M`/`δ`/`HW` packing) and confirm the factorisation reduces
`packM(E₂)` to `G₀/G₁/G₂` terms; if a gap appears, pause and report
(stuck-and-ask template, `.claude/rules/lean-coding.md`). Dependency
order: 0, 6.1, 6.2, 6.3, 6.4, 6.5, 6.6, 7.1, 7.2.

---

## Task 0: relocate `Tm.weaken` to `Era.lean` (#916)

This task lands as two commits: a code relocation (Steps 1-5) and a
doc reconciliation (Steps 6-7), keeping one concern per commit.

`Era.lean` is **already imported** by `EraDiophantine.lean`
(`EraDiophantine.lean:1`), so the relocation moves the two combinators
*up* the existing dependency edge — it introduces no new import and
removes one (`EraDiophantine` keeps importing `Era`). `Era.lean` is
Mathlib-free and `Tm.subst`/`Tm.eval_subst` live in its `namespace Era`
(`Era.lean:55,76,493`); the relocated bodies use only those, so the
no-Mathlib property is preserved.

**Files:**

- Modify: `GebLean/Era.lean` (insert after `Tm.eval_subst`)
- Modify: `GebLean/Utilities/EraDiophantine.lean:173-194` (remove the
  relocated block and its enclosing `namespace Era … end Era` wrapper,
  which encloses only these two declarations)
- Modify: `docs/superpowers/notes/2026-06-14-erabsum-m3b-construction-decision.md`
  (Step 6)
- Modify: `docs/superpowers/specs/2026-06-14-era-completeness-bounded-sum-design.md`
  (Step 6)

In-file users of `Tm.weaken`/`Tm.eval_weaken` the relocation must not
break (all in `EraDiophantine.lean`, which `open`s `Era`):
`SimpleMonomial.weaken` calls `mon.coeff.weaken f` (`:470`); the
`eval_weaken` proofs call `Tm.eval_weaken` (`:494`, `:507`). These resolve
`Era.Tm.weaken` via `open Era`; the `mon.coeff.weaken f` dot-notation form
is unaffected by the namespace move (method resolution is by type). Verify
them in Step 3.

- [x] **Step 1: copy the two declarations into `Era.lean`.** Insert,
  immediately after `Tm.eval_subst` (the substitution-evaluation lemma,
  currently the last `Tm.*` meta-theorem before the basis section), in the
  same namespace that contains `Tm.subst`/`Tm.eval_subst`:

```lean
/-- Re-index a term along a variable map `f : Fin m → Fin m'`, renaming
each free variable `i` to `f i`. The special case `f = id` is the identity
(`Tm.subst_id`); in general it is substitution of the variable-renaming
tuple, so it executes without `Classical.choice`. -/
def Tm.weaken {B : Type} {ar : B → Nat} {m m' : Nat} (f : Fin m → Fin m')
    (t : Tm B ar m) : Tm B ar m' :=
  t.subst (fun i => .var (f i))

/-- Re-indexing compatibility for terms: evaluating `t.weaken f` at `ρ'`
equals evaluating `t` at the precomposed context `ρ' ∘ f`. An instance of
`Tm.eval_subst` at the variable-renaming tuple. -/
theorem Tm.eval_weaken {B : Type} {ar : B → Nat}
    (I : (b : B) → (Fin (ar b) → Nat) → Nat) {m m' : Nat} (f : Fin m → Fin m')
    (t : Tm B ar m) (ρ' : Fin m' → Nat) :
    (t.weaken f).eval I ρ' = t.eval I (ρ' ∘ f) := by
  unfold Tm.weaken
  rw [Tm.eval_subst]
  rfl
```

- [x] **Step 2: remove the originals** from
  `GebLean/Utilities/EraDiophantine.lean` (the `def Tm.weaken …` and
  `theorem Tm.eval_weaken …` block, plus the enclosing `namespace Era` /
  `end Era` wrapper that encloses only them).

- [x] **Step 3: build the whole project** and confirm the in-file users
  (`SimpleMonomial.weaken:470`, the `eval_weaken` proofs `:494`, `:507`)
  still resolve `Tm.weaken`/`Tm.eval_weaken` from `Era.lean`.

Run: `lake build`
Expected: builds clean. If a `Tm.weaken` reference fails to resolve,
confirm `Era.lean`'s namespace matches (`Era.Tm.weaken`) and that
`EraDiophantine.lean` still `open`s `Era`.

- [x] **Step 4: pre-commit, axiom-check, commit the relocation.**

Run: `bash scripts/pre-commit.sh`
Run: `bash scripts/check-axioms.sh` (expect `propext`, `Quot.sound`,
`Classical.choice` only)

```bash
jj describe -m "refactor(era): relocate Tm.weaken to Era.lean

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj new
```

- [x] **Step 5: reconcile the decision note.** In
  `docs/superpowers/notes/2026-06-14-erabsum-m3b-construction-decision.md`
  § 4.3, replace the "`eraBSum` also admits the direct 2-D form … without
  the positional-coding layer" sentence with a one-line correction: the
  direct 2-D count is not used (it diverges from both papers and does not
  factorise for general summands); both formers use the recurrence engine.

- [x] **Step 6: reconcile the binding spec.** The companion spec
  (`docs/superpowers/specs/2026-06-14-era-completeness-bounded-sum-design.md`)
  § 5, § 6 still describe the superseded Marchenkov-2007 digit-sum
  construction and the 2003-monograph `2^x`-elimination, and § 8 frames the
  K-sim-2 corollary via the categorical `erKSimEquiv`. The implemented
  construction is the Istrate-Prunescu-Shunia recurrence engine
  (arXiv:2606.09336, Theorem 2) for both formers, and the corollary uses
  the term-level `erToK_interp`/`kToER_interp` faithfulness (the
  equivalence carries no semantic read-out). Add a short supersession note
  at the head of § 5 and § 8 (and a one-line pointer in § 6) recording this
  and pointing to this sub-plan and the decision note. The spec's binding
  *statements* — § 3 (`era_complete`/`era_sound_er`), § 4 (the two `eval`
  lemmas), § 7 (soundness), § 11 (acceptance), § 12 (scope) — are
  unchanged; only the § 5/§ 6/§ 8 *construction narrative* is marked
  superseded. (Specs and plans co-evolve on-branch:
  `CLAUDE.md` § Specs and plans live on the feature branch.)

- [x] **Step 7: doctoc, markdownlint, commit the doc reconciliation.**

Run (refresh the spec's TOC, then lint both edited docs):

```bash
SPEC=docs/superpowers/specs/2026-06-14-era-completeness-bounded-sum-design.md
NOTE=docs/superpowers/notes/2026-06-14-erabsum-m3b-construction-decision.md
npx doctoc --update-only "$SPEC"
npx markdownlint-cli2 "$SPEC" "$NOTE"
```

Expected: TOC unchanged or refreshed; 0 markdownlint errors.

```bash
jj describe -m "doc(era): reconcile spec and decision note with the recurrence route

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj new
```

---

## Phase 6 — `eraBSum` and `eraBProd` via the recurrence engine

The deliverables (binding, companion spec § 4):

```lean
eval (eraBSum  t) ctx = natBSum  (ctx 0) (fun i => eval t (Fin.cons i (Fin.tail ctx)))
eval (eraBProd t) ctx = natBProd (ctx 0) (fun i => eval t (Fin.cons i (Fin.tail ctx)))
```

with `eraBSum`, `eraBProd : ETm (k+1) → ETm (k+1)`; variable `0` is the
loop bound and the `Fin.cons i (Fin.tail ctx)` shape matches
`ERMor1.interp_bsum`/`interp_bprod` verbatim.

Phase-5 interfaces consumed (exact current signatures):

```lean
-- GebLean/Utilities/EraHypercube.lean
def recSeq (init : ℕ) (step : ℕ → ℕ → ℕ) : ℕ → ℕ
def histCode (init : ℕ) (step : ℕ → ℕ → ℕ) (A : ℕ) (n : ℕ) : ℕ
  -- = ∑ k ∈ Finset.range (n + 1), recSeq init step k * A ^ k
theorem recurrence_readoff (init : ℕ) (step : ℕ → ℕ → ℕ) (A : ℕ) (n : ℕ)
    (hbound : ∀ j, j ≤ n → recSeq init step j < A) :
    recSeq init step n = histCode init step A n / A ^ n
theorem count_zeros_eq (k w t : ℕ) (hw : 0 < w) (P : (Fin k → ℕ) → ℕ)
    (hP : ∀ a ∈ cubePoints k t, P a < 2 ^ w) :
    (Nat.digits 2 (packM k w t P)).sum / w - t ^ k
      = ((cubePoints k t).filter (fun a => P a = 0)).card
theorem cubeSum_factor (k : ℕ) (u vbase : Fin k → ℕ) (t : ℕ) :
    (∑ a ∈ cubePoints k t, ∏ i, (a i) ^ (u i) * (vbase i) ^ (a i))
      = ∏ i, (∑ j ∈ Finset.range t, j ^ (u i) * (vbase i) ^ j)

-- GebLean/Utilities/EraDiophantine.lean
def diophOf {n : ℕ} : ETm n → DiophEnc n
theorem diophOf_encodes {n : ℕ} (t : ETm n) :
    (diophOf t).Encodes (Tm.eval eraInterp t)
def eraMajorant {n : ℕ} : ETm n → ETm n
theorem eraMajorant_spec {n : ℕ} (t : ETm n) (ctx : Fin n → ℕ) :
    Tm.eval eraInterp t ctx < Tm.eval eraInterp (eraMajorant t) ctx
theorem eraMajorant_mono {n : ℕ} (t : ETm n) {ctx ctx' : Fin n → ℕ}
    (h : ∀ i, ctx i ≤ ctx' i) :
    Tm.eval eraInterp (eraMajorant t) ctx ≤ Tm.eval eraInterp (eraMajorant t) ctx'
```

The Phase-6 work is to realise the abstract ℕ `histCode` as an `Era`
term, then take `⌊H/Aⁿ⌋`. All new `EraRecurrence.lean` content opens with
the mandatory module docstring (title, summary, main definitions, main
statements, references, tags) before any declaration.

### Task 6.1: positional-coding predicates `E_Code`, `E_π` (Lemma 3)

**Files:**

- Create: `GebLean/Utilities/EraRecurrence.lean`

Transcribe arXiv:2606.09336, Lemma 3 (p. 8). The positional code of a
sequence `a₀,…,aₙ` with each `aₖ < A` is `x = Σ_{k≤n} aₖ Aᵏ`, and:

```text
Code(x, A, n)        ⟷  x < A^(n+1)
a = π(x, A, j, n)    ⟷  x = λ₁ + a·A^j + λ₂·A^(j+1) ∧ λ₁ < A^j ∧ a < A ∧ j ≤ n
                        (so a is the j-th base-A digit; π(x,A,n,n) = ⌊x/A^n⌋)
```

- [x] **Step 1: define the digit-extraction relation and prove the
  read-off.** Reuse Phase 5's `positional_readoff` for the top digit; for
  a general digit, define the predicate and prove it characterises
  `x / A^j % A`. Search first for an existing Mathlib `Nat.digits`/base-`A`
  digit lemma (`Nat.digits`, `Nat.ofDigits`, `Nat.div_pow_mod`).

```lean
/-- The base-`A` digit-extraction predicate of arXiv:2606.09336, Lemma 3:
`piDigit x A j n a` holds iff `a` is the `j`-th base-`A` digit of `x` and
`j ≤ n`. Equivalent to `a = x / A^j % A`. -/
def piDigit (x A j n a : ℕ) : Prop :=
  (∃ l₁ l₂, x = l₁ + a * A ^ j + l₂ * A ^ (j + 1) ∧ l₁ < A ^ j) ∧ a < A ∧ j ≤ n

theorem piDigit_iff (x A j n a : ℕ) (hA : 1 ≤ A) (hj : j ≤ n) :
    piDigit x A j n a ↔ a = x / A ^ j % A := by
  sorry
```

Strategy: forward, `Nat.add_mul_div_left`/`Nat.add_mul_mod_self_left`
extract the digit from the witnessed decomposition; backward, supply
`l₁ := x % A^j`, `l₂ := x / A^(j+1)`, with `a < A` from `Nat.mod_lt` and
`a < A` from the digit being a `% A`. This is a self-contained ℕ lemma;
budget a `lean4:sorry-filler-deep` pass if the witness algebra is fiddly.

- [x] **Step 2: build, axiom-check, commit**
  (`feat(era): transcribe the base-A digit-extraction predicate`).

### Task 6.2: the master trajectory relation and its solution count (Claims 3-4)

**Files:**

- Modify: `GebLean/Utilities/EraRecurrence.lean`

Transcribe arXiv:2606.09336, the master relation (p. 8) and Claim 4 (p. 9),
specialised to order `k = 1`. At `k = 1` the relation glues, for a
candidate code `x` and an internal index `j`:

```text
E(n, x, y₀)(j, z₀, z₁) :=
    Code(x, A, n)                  -- x codes a length-(n+1) base-A sequence
  ∧ piDigit x A 0 n y₀             -- initial value a₀ = y₀
  ∧ piDigit x A j n z₀             -- consecutive pair a_j = z₀
  ∧ piDigit x A (j+1) n z₁         --                a_{j+1} = z₁
  ∧ z₁ = step j z₀                 -- the recurrence holds at j  (E_F = diophOf step)
```

with `step` the recurrence function. Define the count `G` and prove
Claim 4: the count equals its maximum `n` exactly when `x` is the true
trajectory's code.

- [x] **Step 1: define the trajectory predicate and the per-index hit.**

```lean
/-- The recurrence-instance predicate (arXiv:2606.09336, master relation,
`k = 1`): index `j < n` "hits" for code `x` when consecutive base-`A`
digits `a_j, a_{j+1}` of `x` satisfy `a_{j+1} = step j a_j`. -/
def hitsAt (step : ℕ → ℕ → ℕ) (A x n j : ℕ) : Prop :=
  step j (x / A ^ j % A) = x / A ^ (j + 1) % A

/-- The number of recurrence instances `0 ≤ j < n` satisfied by code `x`
(arXiv:2606.09336, Claim 3, `G(n, y)(x)`). -/
def hitCount (step : ℕ → ℕ → ℕ) (A x n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun j => hitsAt step A x n j)).card
```

Note: `hitsAt step A x n j` unfolds to a `ℕ`-equality
`step j (…) = (…)`, so `DecidablePred (fun j => hitsAt step A x n j)` is
synthesised from `Nat.decEq` — `Finset.filter` takes it directly (do not
wrap in `decide … = true`), and `hitCount` is a plain computable
`Finset.card`; no `Classical`. If synthesis fails, add the instance
explicitly:

```lean
instance (step : ℕ → ℕ → ℕ) (A x n : ℕ) :
    DecidablePred (fun j => hitsAt step A x n j) :=
  fun _ => Nat.decEq _ _
```

- [x] **Step 2: state and prove Claim 4** — the count is maximal iff `x`
  codes the genuine trajectory, and then `x = histCode`.

```lean
/-- arXiv:2606.09336, Claim 4 (`k = 1`): for `A` a strict bound on the
trajectory `recSeq init step` up to `n`, the unique code with all `n`
recurrence instances satisfied is `histCode init step A n`, and it is the
unique maximiser of `hitCount`. -/
theorem hitCount_eq_max_iff (init : ℕ) (step : ℕ → ℕ → ℕ) (A n : ℕ)
    (hbound : ∀ j, j ≤ n → recSeq init step j < A)
    (x : ℕ) (hx : x < A ^ (n + 1)) :
    hitCount step A x n = n ∧ x / A ^ 0 % A = init
      ↔ x = histCode init step A n := by
  sorry
```

Strategy: (⟸) for `x = histCode`, `positional_readoff`/`piDigit_iff` give
every digit `a_k = recSeq k` (digits are below `A` by `hbound`), so every
instance `recSeq (j+1) = step j (recSeq j)` holds by `recSeq`'s defining
equation — all `n` hit, and `a₀ = init`. (⟹) each `hitsAt` forces
`a_{j+1} = step j a_j`; with `a₀ = init` and induction the digits coincide
with `recSeq k` for `k ≤ n`, so `x` and `histCode` have equal base-`A`
digits below `A^(n+1)`, hence equal (`Nat.eq_of_digits`/positional
uniqueness). This is the substantial ℕ lemma of Task 6.2; budget a
`lean4:sorry-filler-deep` pass and factor the digit-agreement induction as
its own lemma. Cite Claim 4 (p. 9). Hypothesis threading for `piDigit_iff`
(Task 6.1): its `1 ≤ A` is discharged from `hbound 0` (`recSeq … 0 < A`),
and its `j ≤ n` from `j < n` (membership in `Finset.range n`) — establish
both before each `piDigit_iff` rewrite, since `hitsAt`'s `%`-form drops
them.

- [x] **Step 3: build, axiom-check, commit**
  (`feat(era): prove the trajectory code is the unique hit maximiser`).

### Task 6.3: the counting identity `#solutions(E₂) = histCode` (Claim 5)

**Files:**

- Modify: `GebLean/Utilities/EraRecurrence.lean`

Transcribe arXiv:2606.09336, Claim 5 (p. 10). The code `C = histCode` is
re-expressed as a solution count via `x = ω₁ + ω₂ + 1`: since the
maximal-hit equation has the unique solution `x = C`, the number of pairs
`(ω₁, ω₂) ∈ ℕ²` with `ω₁ + ω₂ + 1 = C` is exactly `C`.

- [x] **Step 1: the pair-count identity (the Claim-5 core).**

```lean
/-- The number of ordered pairs `(ω₁, ω₂) ∈ ℕ²` with `ω₁ + ω₂ + 1 = C`
is `C` (arXiv:2606.09336, Claim 5: the `ω₁+ω₂+1` counting trick). -/
theorem card_pairs_succ_sum (C : ℕ) :
    ((Finset.range C ×ˢ Finset.range C).filter
        (fun p => p.1 + p.2 + 1 = C)).card = C := by
  sorry
```

Strategy: the satisfying pairs are exactly `{(i, C-1-i) : i < C}`, a graph
over `Finset.range C`; use `Finset.card_filter`/a bijection to
`Finset.range C` (`Finset.card_nbij'` with `p ↦ p.1`). Numeric-check the
statement over `C ∈ 0..6` with a throwaway `#eval` first.

- [x] **Step 2: assemble `solCount_eq_histCode`** — the solution count of
  the combined system (maximal hits ∧ `ω₁+ω₂+1 = x`) equals `histCode`.

```lean
/-- arXiv:2606.09336, Claim 5 (`k = 1`): the number of triples
`(ω₁, ω₂, …)` solving the `E₂` system equals the history code. The witness
tuple of the maximal-hit constraint is unique (Claim 4), so the count
collapses to the `ω₁+ω₂+1` pair count, which is `histCode`. -/
theorem solCount_eq_histCode (init : ℕ) (step : ℕ → ℕ → ℕ) (A n : ℕ)
    (hbound : ∀ j, j ≤ n → recSeq init step j < A) :
    -- the E₂ solution count, stated over the explicit ω₁,ω₂ cube
    sorry = histCode init step A n := by
  sorry
```

Finalise the left-hand count's exact `Finset` shape here (it ranges
`(ω₁, ω₂)` over `[0, A^(n+1))²` filtered by
`hitCount step A (ω₁+ω₂+1) n = n ∧ (ω₁+ω₂+1)/1 % A = init`), driven by the
`piDigit`/`hitCount` definitions of Tasks 6.1-6.2 and
`hitCount_eq_max_iff`. Reduce to `card_pairs_succ_sum` at `C = histCode`
(using `histCode < A^(n+1)`, provable from `hbound` and the geometric
bound, mirroring `positional_readoff`'s `hlow`).

- [x] **Step 3: build, axiom-check, commit**
  (`feat(era): prove the E2 solution count equals the history code`).

### Task 6.4: `eraHistCode` — the history code as an `Era` term (RE-CHECKPOINT)

**Files:**

- Modify: `GebLean/Utilities/EraRecurrence.lean`

> **Re-checkpoint (see "Phase map" above).** Before this task, re-read
> arXiv:2407.12928 § 4 (the `M = Σ 2^(2w·v(ā)) δ(P(ā),w)` packing, the
> `HW(M)/w − tᵏ` read-off) and arXiv:2606.09336 p. 10 (applying Section 4
> to `E₂`). Confirm that the `E₂` predicate of Task 6.3, reduced to
> simple-exponential-polynomial form via the `diophOf` `SosSystem`,
> makes `packM` factorise through `cubeSum_factor` into `G₀/G₁/G₂` terms
> (arXiv:2407.12928, Cor 3.6: only `HW, G₀, G₁, G₂` are needed). If the
> reduction has a gap, pause and report before coding.

Goal: an `Era` term `eraHistCode` (parameterised by the step's `diophOf`
encoding and the majorant-derived `A`, `w`, `t`) with

```lean
theorem eraHistCode_eval … :
    Tm.eval eraInterp (eraHistCode …) ctx = histCode init step A n
```

This realises `solCount_eq_histCode` as a term by `count_zeros_eq`: the
count `#{… = 0}` over the cube equals `HW(packM)/w − tᵏ`, and `packM`,
`HW = eraSigma`, `t`, `w` are all `Era` terms.

- [x] **Step 1: the predicate term `P_E₂`.** Build the `ETm` for the `E₂`
  sum-of-squares predicate over the cube variables from `diophOf step`'s
  `SosSystem` plus the `piDigit`/`Code` gadgets, using `Tm.weaken`
  (Task 0) to splice the step encoding into the enlarged variable context.
  Prove its `eval` is `0` exactly on the counted set (reuse
  `diophOf_encodes`).

- [x] **Step 2: reduce `δ(P_E₂, w)` to simple-exponential-polynomial
  (SEP) form (arXiv:2407.12928, Lemma 3.5 / Corollary 3.6).** This is the
  bridge `cubeSum_factor` does *not* supply: `cubeSum_factor` consumes an
  *already-separated* monomial `∏ᵢ aᵢ^{uᵢ}·vᵢ^{aᵢ}`, but `δ(P_E₂, w)` after
  expansion is a general algebraic sum whose cube-coordinate exponents may
  exceed `2`. Lemma 3.5 reduces any such expression to a sum of SEP
  monomials with non-exponential exponents `≤ 2` by introducing auxiliary
  cube variables `yᵢ`/`zᵢ` (the same auxiliary-variable device as
  `diophOf`'s `SosSystem`), and Corollary 3.6 records that only
  `{HW, G₀, G₁, G₂}` are then needed. Provide the `ℕ`-level reduction
  lemma:

```lean
/-- arXiv:2407.12928, Lemma 3.5 / Corollary 3.6: any cube summand reduces
to a sum of simple-in-x̄ exponential monomials of coordinate-degree ≤ 2,
so its cube-sum factors through `cubeSum_factor` into `G₀/G₁/G₂`. -/
theorem sep_reduce … : sorry := by
  sorry
```

  Finalise the statement against the exact `δ(P_E₂, w)` shape produced by
  Step 1 (it depends on `diophOf`'s `SosSystem` field types). If
  `diophOf`'s output is already simple-in-x̄ with coordinate-degree ≤ 2
  (it is a sum of squares of "simple" sub-terms — check the `SimpleSum`/
  `SimpleMonomial` invariants in `EraDiophantine.lean`), this lemma is the
  identity on the already-reduced form and the task is to *confirm* that,
  not re-derive Lemma 3.5; record which case holds. **This is the
  re-checkpoint deliverable** — if the `SosSystem` is not already in the
  required form and Lemma 3.5's auxiliary-variable reduction must be
  transcribed in full, pause and report the enlarged scope before
  proceeding.

- [x] **Step 3: the packed number term `packM_term`.** With Step 2's SEP
  form, apply `cubeSum_factor` so the cube-sum of `δ(P_E₂, w)·base^(v(ā))`
  becomes a product of `G₀/G₁/G₂` closed-form terms
  (`eraGeomSum`/`natLinGeomSum`/`natSqGeomSum`, Phases 1, 3). Width `w`,
  side `t`, base `A` are `eraMajorant`-derived terms; discharge
  `P_E₂(ā) < 2^w` on the cube from the majorant bound and
  `eraMajorant_spec`/`_mono`.

- [x] **Step 4: `eraHistCode` and its `eval` lemma.** Define
  `eraHistCode := etsub (ediv (eraSigma … packM_term) w_term) (epow t_term k_term)`
  (the `HW(M)/w − tᵏ` read-off as a term), and prove
  `eval eraHistCode ctx = histCode init step A n` by `count_zeros_eq`
  (giving `HW(packM)/w − tᵏ = solCount`) chained with
  `solCount_eq_histCode` (Task 6.3). This is the dominant proof; factor
  per the "factoring-out-lemmas" technique and budget the largest effort.

- [x] **Step 5: build, axiom-check, commit**
  (`feat(era): realise the recurrence history code as an Era term`).

### Task 6.5: `eraBSum`

**Files:**

- Modify: `GebLean/EraCompleteness.lean`

- [x] **Step 1: the general former `eraRec`.** In `EraRecurrence.lean`,
  package Task 6.4 into the recurrence-to-term former and its `eval` lemma
  (via `recurrence_readoff`). `eraRec` takes the bound `A` as a supplied
  `Era` term together with the `recurrence_readoff` hypothesis as a
  proof obligation, so each instance discharges its own bound:

```lean
/-- The first-order recurrence-to-term former (arXiv:2606.09336,
Theorem 2, `k = 1`): given an `Era`-term step and a bound term `A` with
`∀ j ≤ y, recSeq init step j < eval A`, `eval (eraRec …) = recSeq init
step y` at the loop bound `y = ctx 0`. -/
theorem eraRec_eval …
    (hbound : ∀ j, j ≤ ctx 0 → recSeq init step j < Tm.eval eraInterp A ctx) :
    Tm.eval eraInterp (eraRec …) ctx = recSeq init step (ctx 0) := by
  -- `recSeq … = histCode … / A^y` (recurrence_readoff) then eraHistCode_eval
  sorry
```

  Note the bound is on `recSeq j` (the running aggregate), not on the
  summand `f`. For a *sum*, `recSeq j = Σ_{i<j} f(i)` grows with `j`, so
  the pointwise summand majorant `eraMajorant t` does **not** bound it; a
  sum majorant `y·M` is needed (Step 2). For a *product* the analogous
  bound is `Mʸ` (Task 6.6).

- [x] **Step 2: build the sum-majorant term and its bound lemma.** The
  partial sum is bounded by the loop bound times the pointwise majorant:

```lean
/-- A sum majorant for the bounded-sum recurrence: `Σ_{i<j} f(i)` is
strictly below `y·(eraMajorant t) + 1` for all `j ≤ y = ctx 0`. -/
theorem sumMajorant_bound {k : ℕ} (t : ETm (k + 1)) (ctx : Fin (k + 1) → ℕ)
    (j : ℕ) (hj : j ≤ ctx 0) :
    (∑ i ∈ Finset.range j,
        Tm.eval eraInterp t (Fin.cons i (Fin.tail ctx)))
      < sorry := by
  sorry
```

  Finalise the bound term as the `eval` of the sum-majorant `Era` term
  (`emul` of the loop-bound variable with `eraMajorant t`, plus one).
  Strategy: each summand `< M` by `eraMajorant_spec`; a sum of `j ≤ y`
  terms each `< M` is `< j·M + 1 ≤ y·M + 1` (`Finset.sum_lt_sum`/
  `Finset.sum_le_card_nsmul`). Budget a `lean4:sorry-filler-deep` pass.

- [x] **Step 3: define `eraBSum`** as the `eraRec` instance with
  `step m s = s + f m`, `init = 0` (so `recSeq = natBSum`), and `A` the
  Step-2 sum majorant:

```lean
/-- Bounded summation as an `Era` term: variable `0` is the loop bound.
The `s(m+1) = s(m) + f(m)` instance of the recurrence engine. -/
def eraBSum {k : ℕ} (t : ETm (k + 1)) : ETm (k + 1) := sorry
```

- [x] **Step 4: the `eval` lemma (the deliverable).**

```lean
theorem eraBSum_eval {k : ℕ} (t : ETm (k + 1)) (ctx : Fin (k + 1) → ℕ) :
    Tm.eval eraInterp (eraBSum t) ctx =
      natBSum (ctx 0) (fun i =>
        Tm.eval eraInterp t (Fin.cons i (Fin.tail ctx))) := by
  sorry
```

Strategy: `eraRec_eval` (its bound hypothesis discharged by
`sumMajorant_bound`, Step 2) gives `recSeq 0 (fun m s => s + f m) (ctx 0)`;
prove `recSeq 0 (fun m s => s + f m) y = natBSum y f` by induction on `y`
(`natBSum`'s defining equation; `natBSum_eq_sum` / `Finset.sum_range_succ`
if helpful). Match `f i = Tm.eval eraInterp t (Fin.cons i (Fin.tail ctx))`
exactly to the `interp_bsum` shape.

- [x] **Step 5: build, axiom-check, commit**
  (`feat(era): define bounded summation as an Era term`).

### Task 6.6: `eraBProd`

**Files:**

- Modify: `GebLean/EraCompleteness.lean`

- [x] **Step 1: build the product-majorant term and its bound lemma.**
  Unlike `eraBSum`, the running product `recSeq 1 (·*f·) j = ∏_{i<j} f(i)`
  is *not* bounded by the pointwise summand majorant `eraMajorant t` — it
  grows as `Mʸ` where `M` is that majorant. So the `recurrence_readoff`
  hypothesis `∀ j ≤ y, ∏_{i<j} f(i) < A` needs a genuine product majorant
  term. Define it as `M^y · 2` (a strict bound: `∏_{i<j} f(i) ≤ Mʸ < M^y·2`
  for the loop bound `y`, using monotonicity of the pointwise majorant via
  `eraMajorant_mono`), as an `Era` `epow`/`emul` term in the loop bound and
  parameters, with its `ℕ` bound lemma:

```lean
/-- A product majorant for the bounded-product recurrence: `∏_{i<j} f(i)`
is strictly below `(eraMajorant t)ʸ · 2` for all `j ≤ y`, where `y` is the
loop bound. -/
theorem prodMajorant_bound {k : ℕ} (t : ETm (k + 1)) (ctx : Fin (k + 1) → ℕ)
    (j : ℕ) (hj : j ≤ ctx 0) :
    (∏ i ∈ Finset.range j,
        Tm.eval eraInterp t (Fin.cons i (Fin.tail ctx)))
      < sorry := by
  sorry
```

  Finalise the bound term (the `sorry` in the conclusion) as the `eval` of
  the product-majorant `Era` term. Strategy: each factor `< M` by
  `eraMajorant_spec`; the product of `j ≤ y` factors each `< M` is `≤ M^j ≤
  M^y`; `< M^y·2` since `M ≥ 1`. Budget a `lean4:sorry-filler-deep` pass.

- [x] **Step 2: define `eraBProd`** as the `eraRec` instance with
  `step m s = s · f m`, `init = 1`, and `A` the Step-1 product majorant.

```lean
/-- Bounded product as an `Era` term: variable `0` is the loop bound. The
`p(m+1) = p(m) · f(m)` instance of the recurrence engine. -/
def eraBProd {k : ℕ} (t : ETm (k + 1)) : ETm (k + 1) := sorry
```

- [x] **Step 3: the `eval` lemma.**

```lean
theorem eraBProd_eval {k : ℕ} (t : ETm (k + 1)) (ctx : Fin (k + 1) → ℕ) :
    Tm.eval eraInterp (eraBProd t) ctx =
      natBProd (ctx 0) (fun i =>
        Tm.eval eraInterp t (Fin.cons i (Fin.tail ctx))) := by
  sorry
```

Strategy: identical to Task 6.5 with the product step; `eraRec_eval`
discharges the bound hypothesis via `prodMajorant_bound` (Step 1), then
prove `recSeq 1 (fun m s => s * f m) y = natBProd y f` by induction on `y`.

- [x] **Step 4: build, axiom-check, commit**
  (`feat(era): define bounded product as an Era term`).

---

## Phase 7 — capstones

### Task 7.1: `era_complete`

**Files:**

- Modify: `GebLean/EraCompleteness.lean`

- [x] **Step 1: state.**

```lean
/-- Completeness: every `ERMor1` (elementary) function is the denotation
of some `Era` term. -/
theorem era_complete {n : ℕ} (f : ERMor1 n) :
    ∃ t : ETm n, ∀ ctx : Fin n → ℕ,
      Tm.eval eraInterp t ctx = f.interp ctx := by
  sorry
```

- [x] **Step 2: prove by structural induction on `f`** (constructors
  `zero`, `succ`, `proj`, `sub`, `comp`, `bsum`, `bprod`):

```text
zero      → ⟨Tm.zero, …⟩                       (ERMor1.interp_zero; eraInterp)
succ      → ⟨Tm.succ (Tm.var 0), …⟩            (interp_succ)
proj i    → ⟨Tm.var i, …⟩                      (interp_proj)
sub       → ⟨Tm.var 0 ∸ᵉ Tm.var 1, …⟩          (interp_sub; etsub eval)
comp f g  → substitute g-witnesses into f-witness   (Tm.eval_subst + IHs)
bsum f    → ⟨eraBSum (IH-witness of f), …⟩      (eraBSum_eval + IH)
bprod f   → ⟨eraBProd (IH-witness of f), …⟩     (eraBProd_eval + IH)
```

Strategy: `induction f`. The four base cases are immediate from the
`interp_*` and `eraInterp`/`etsub` equations. `comp f g` uses
`Tm.eval_subst` with the `Fin.cons`/`Fin.tail` context juggling matching
`ERMor1.interp_comp`. `bsum`/`bprod` apply `eraBSum_eval`/`eraBProd_eval`
to the inductive witness; the `Fin.cons i (Fin.tail ctx)` shape is
identical in `interp_bsum` and `eraBSum_eval`, so the IH applies directly.
Reuse `erOfETm`/`eraOpToER` patterns already in `EraCompleteness.lean`.

- [x] **Step 3: build, axiom-check, commit**
  (`feat(era): prove Era-term completeness for ERMor1`).

### Task 7.2: the K-sim-2 corollary

**Files:**

- Modify: `GebLean/EraCompleteness.lean`

The function-class identity comes from the existing term-level
interp-faithfulness lemmas, not the categorical `erKSimEquiv` (which has no
semantic read-out):

```lean
-- GebLean/LawvereERKSim/ErToK.lean
theorem erToK_interp {a : ℕ} (e : ERMor1 a) (v : Fin a → ℕ) :
    (erToK e).interp v = e.interp v
-- GebLean/LawvereKSimER.lean
theorem kToER_interp {a : ℕ} (f : KMor1 a) (h : f.level ≤ 2) (v : Fin a → ℕ) :
    (kToER f h).interp v = f.interp v
```

Note: `kToER_interp` is declared in source as a `∀`-quantified
pattern-matching recursion (`LawvereKSimER.lean:285`); the signature above
is its instantiated application form, which is what the corollary consumes.

- [x] **Step 1: pin the extraction.** Confirm `erToK_interp` and
  `kToER_interp` (with its load-bearing `level ≤ 2` premise) give the
  `ERMor1` ↔ K-sim-2 function-class equality directly; `erKSimEquiv` is
  not needed. State the exact corollary signature in terms of the K-sim-2
  morphism `interp`.

- [x] **Step 2: state and prove the corollary** as a thin composition of
  `era_complete` + `era_sound_er` (`Era ≃ E³` as denoted functions) with
  the `ERMor1` ↔ K-sim-2 interp faithfulness. Implement no `K-sim` scheme
  over the basis (spec § 12). The exact statement (both inclusions, as
  function-class equality at `interp`) is finalised here from the available
  lemmas; keep it a composition, no new arithmetic.

- [x] **Step 3: build, axiom-check, commit**
  (`feat(era): derive the K-sim-2 corollary`). This commit closes M3b.

---

## Self-review checklist (run before adversarial review)

- [x] **Spec coverage.** Companion spec § 3 (statements) → Tasks 7.1, 7.2;
  § 4 (the two `eval` lemmas, the induction) → Tasks 6.5, 6.6, 7.1; § 7
  (soundness) → already `era_sound_er` (not redone); § 11 acceptance (no
  `sorry`/`admit`/underscore in commits, 100-char, axiom-clean, `Era.lean`
  only gains the two relocated `Tm` combinators) → per-task gates and
  Task 0; § 12 (`Era.lean` basis unmodified, no `K-sim` scheme) → Task 0
  changes only the term-combinator layer, Task 7.2 is composition-only.
- [x] **Superseded spec sections (construction narrative).** Spec § 5, § 6
  (the Marchenkov digit-sum / `2^x`-elimination construction) are
  superseded by the recurrence engine (Phase 6); spec § 8's `erKSimEquiv`
  framing is superseded by the term-level `erToK_interp`/`kToER_interp`
  route (Task 7.2). Task 0 Step 6 records the supersession in the spec
  itself; the *statements* of § 3/§ 4/§ 7/§ 8/§ 11/§ 12 remain binding and
  unchanged.
- [x] **Route fidelity.** Both formers use the recurrence engine
  (arXiv:2606.09336 Theorem 2); no direct 2-D count anywhere; the decision
  note is corrected (Task 0 Step 4).
- [x] **Transcription citations.** Tasks 6.1-6.4 cite the exact paper
  claims/lemmas (Lemma 3; master relation; Claims 3-5; arXiv:2407.12928
  § 4 / Cor 3.6). The local PDF paths are in § References.
- [x] **Type consistency.** `eraBSum`/`eraBProd : ETm (k+1) → ETm (k+1)`;
  the `eval`-lemma RHS `natBSum (ctx 0) (fun i => Tm.eval … (Fin.cons i
  (Fin.tail ctx)))` matches `ERMor1.interp_bsum`/`interp_bprod` verbatim;
  `eraRec_eval`/`eraHistCode_eval` names consistent across Tasks 6.4-6.6;
  `recSeq`/`histCode`/`count_zeros_eq`/`cubeSum_factor` signatures used as
  quoted above.
- [x] **Computability.** `hitsAt` decidable; `hitCount` a plain
  `Finset.card`; `card_pairs_succ_sum` over explicit `Finset`s; no
  `noncomputable`, no `Classical` in computational content.
- [x] **De-cycling.** No `eraIlog2`/fast-`ν₂`/`⌊log₂⌋` term; `HW` is
  `eraSigma` (slow `ν₂`); the width `w` is an `eraMajorant`-derived term,
  not a logarithm.
- [x] **Lemma-name hygiene.** `Nat.add_eq_zero_iff` (not deprecated
  `Nat.add_eq_zero`); `Finset.sum_range_succ`; `Nat.add_mul_div_left`;
  digit lemmas via `Nat.digits`/`Nat.ofDigits` checked against the pin.
- [x] **Commit subjects** under 72 characters, imperative, lowercase, no
  trailing period.
- [x] **Markdownlint + doctoc.** `markdownlint-cli2` clean; run
  `doctoc --update-only` on this file before the first commit (the TOC
  markers are present at the top).

## References

Binding local PDFs (also referenced by arXiv ID throughout `docs/`):

- `/home/terence/wingeb/undecidability-chaos-universality-arithmetic-terms.pdf`
  — Istrate, Prunescu, Shunia, arXiv:2606.09336. Theorem 2 / Corollary 2
  (recurrence→term, `a(n) = ⌊H/Aⁿ⌋`); Lemma 2 (term→Diophantine, = Phase 4
  `diophOf`); Lemma 3 (positional coding, `Code`/`π`, p. 8); the master
  trajectory relation (p. 8); Claims 1-5 (pp. 9-10: range bound `t`, width
  `w` via minus→plus, count `G`, the maximal-hit code `C`, and
  `#solutions(E₂) = C`). Tasks 6.1-6.6.
- `/home/terence/wingeb/representation-number-theoretic-functions-arithmetic-terms.pdf`
  — Prunescu, Sauras-Altuzarra, arXiv:2407.12928. Section 4: the packed
  number `M = Σ 2^(2w·v(ā)) δ(P(ā),w)`, the `δ` indicator (Lemma 3.1), the
  cube-sum factorisation (Lemma 3.2 = `cubeSum_factor`), the `HW(M)/w − tᵏ`
  read-off (Lemma 3.3 / Theorem 3.4 = `count_zeros_eq`), Cor 3.6 (only
  `HW, G₀, G₁, G₂` needed). Task 6.4.
- `/home/terence/wingeb/minimal-substitution-basis-kalmar-elementary.pdf`
  — Prunescu, Sauras-Altuzarra, Shunia, arXiv:2505.23787. The Era basis
  (`Era.lean`).
- `/home/terence/wingeb/arithmetic-term-representations-gcd.pdf`
  — Prunescu, Shunia, arXiv:2411.06430. The gcd term (`eraGcd`, Phase 3),
  the base-5 form reused by the count engine.
- `/home/terence/wingeb/superpositions-elementary-arithmetic-functions-marchenkov.pdf`
  — Marchenkov 2007. The superseded digit-sum route (background only; not
  transcribed here).
- `/home/terence/wingeb/logic-free-formalization-recursive-arithmetic.pdf`
  — Goodstein 1954. Background for the deferred object-level workstream.

Repository:

- Companion spec:
  `docs/superpowers/specs/2026-06-14-era-completeness-bounded-sum-design.md`
  (§ 3, § 4, § 7, § 8, § 11, § 12 binding).
- Construction decision (corrected by Task 0 Step 4):
  `docs/superpowers/notes/2026-06-14-erabsum-m3b-construction-decision.md`.
- M3b plan (Phase 6-7 task list this sub-plan refines):
  `docs/superpowers/plans/2026-06-14-era-completeness-m3b-plan.md`.
- Phase-4/5 sub-plan (the interfaces this consumes):
  `docs/superpowers/plans/2026-06-15-era-completeness-phase4-5-subplan.md`.
- Source modules: `GebLean/Era.lean` (`ETm`, `Tm.eval`, `Tm.subst`,
  `Tm.eval_subst`, `eraInterp`); `GebLean/Utilities/EraDiophantine.lean`
  (`diophOf`, `DiophEnc`, `SosSystem`, `eraMajorant`);
  `GebLean/Utilities/EraHypercube.lean` (`count_zeros_eq`, `cubeSum_factor`,
  `recSeq`, `histCode`, `recurrence_readoff`, `positional_readoff`);
  `GebLean/LawvereER.lean` (`ERMor1`, `natBSum`, `natBProd`, `interp_*`);
  `GebLean/EraCompleteness.lean` (`era_sound_er`, `eraSigma`, `eraDelta`,
  `eraGeomSum`, `erOfETm`); `GebLean/LawvereERKSim/ErToK.lean`
  (`erToK_interp`); `GebLean/LawvereKSimER.lean` (`kToER_interp`).
