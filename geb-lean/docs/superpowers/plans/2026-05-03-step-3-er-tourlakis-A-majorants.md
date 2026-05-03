# Step 3 — Tourlakis A_n^r majorant family in ER — Implementation Plan

> **For agentic workers:** Required sub-skill: use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Land `ERMor1.A_one`, `ERMor1.A_one_iter`, and
`ERMor1.A_two_iter` as Lean named composites realizing
Tourlakis 2018 page 22 (proof of §0.1.0.44 ⊆ direction)
majorant family for K^sim level 2, with closed-form `@[simp]`
interp lemmas and `PolyBound` builders for the A_1
variants.  One new module: `ERAMajorants.lean`.

**Architecture:** Three named composites plus three interp
simp lemmas plus two PolyBound builders.  `A_one` is built
from `addN(succ(proj 0), succ(proj 0))`.  `A_one_iter r` is
r-fold composition `A_1 ∘ A_1^r`, with closed-form interp
`2^r * x + (2^{r+1} − 2)` proved by induction on `r`.
`A_two_iter r` aliases `ERMor1.towerER r` with interp
routing through `interp_towerER`.  PolyBound builders cover
only the linear A_1 variants; `A_two_iter` is tower-fast
and has no PolyBound by design (level-2 chain consumes a
Nat-level dominance hypothesis at step 4 instead).

**Tech Stack:** Lean 4 + mathlib4.  Build via `lake build`,
test via `lake test`.  Existing infrastructure consumed:
ER constructors (`ERMor1.succ`, `ERMor1.proj`, `ERMor1.comp`)
and their interp simp lemmas in `LawvereER.lean`;
`ERMor1.addN` and `interp_addN` in `Utilities/ERArith.lean`;
`ERMor1.towerER` and `interp_towerER` in
`LawvereERBoundComputable.lean`; `ERMor1.PolyBound` in
`LawvereERPolynomialBound.lean`; `tower` and its monotonicity
lemmas in `Utilities/Tower.lean`.

**Spec:**
`docs/superpowers/specs/2026-05-03-step-3-er-tourlakis-A-majorants-design.md`
(approved after 4 rounds of adversarial review; round 4
empirically Lean-verified all five proofs close cleanly).

**Master design:**
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`
§3.3 (Lean entities, polynomial-bound certification, the
no-PolyBound-for-`A_two_iter` decision).

---

## File structure

**Created (implementation):**

- `GebLean/Utilities/ERAMajorants.lean` — three named
  composites (`A_one`, `A_one_iter`, `A_two_iter`), three
  interp `@[simp]` theorems, two `PolyBound` builders
  (`ofA_one`, `ofA_one_iter`).  Imports
  `GebLean.LawvereER`, `GebLean.Utilities.ERArith`,
  `GebLean.LawvereERBoundComputable`,
  `GebLean.LawvereERPolynomialBound`,
  `GebLean.Utilities.Tower`.

**Created (tests):**

- `GebLeanTests/Utilities/ERAMajorants.lean` — ER-side
  `#guard` tests at safe inputs.

**Modified:**

- `GebLean.lean` — add public export of the new module.
- `GebLeanTests.lean` — add import of the new test module.

---

## Style and discipline reminders (from steps 1 and 2)

Each task's code must follow CLAUDE.md:

- Lines ≤ 80 characters.
- Spaces around binary operators in source: write
  `Fin (k + 1)` not `Fin (k+1)`, `(2 ^ k)` not `(2^k)`.
- Every implemented function/definition/theorem carries a
  literature reference in its docstring (Tourlakis 2018
  page 22 for `A_1`/`A_1^r`/`A_2^r`; §0.1.0.17 (c) for the
  underlying `2^x ∈ ER`; master design §3.3).
- Use `simp only [...]` not bare `simp [...]`.
- Use `change` not `show` when the goal text differs from
  what Lean has after reduction.
- No `sorry`, `admit`, `Classical`, `noncomputable`,
  `axiom`, or warnings (lakefile sets `warningAsError =
  true`).
- No banned words from CLAUDE.md's list.
- `markdownlint-cli2` clean on any new docs.

### Import-at-skeleton-creation rule

Add the import to `GebLean.lean` (and the test counterpart
to `GebLeanTests.lean`) the moment you create the skeleton
file, before adding any code.  This is verified during the
skeleton task itself.

### Forced re-elaboration before commit

After each task that touches a `.lean` file, force
re-elaboration to catch latent linter errors masked by
incremental cache:

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERAMajorants.olean
lake build GebLean.Utilities.ERAMajorants 2>&1 | tail -5
```

Inspect output for `error:` AND `warning:` lines (do not
stop at "Build completed successfully" — that line is
unreliable when the module was already cached).

### ER-side `.interp` test discipline (Gödel numbering)

Per steps 1 and 2's lessons: `#guard` on
`ERMor1.<X>.interp` for `X` involving `tuplePack` /
`tupleAt` / `boundedRec` / `boundedSearch` / `expER` /
`towerER` is impractical even for tiny inputs.  `A_one`
and `A_one_iter` are bsum-based via `mulN` (= `boolAnd`)
inside `addN`, but `bsum` size scales linearly with input,
so small-input `#guard`s terminate quickly.  `A_two_iter`
at `r ≥ 1` aliases `towerER` (which uses `expER`'s
`bprod`); ER-side `#guard`s on `A_two_iter` are restricted
to `r = 0` (which definitionally reduces to `proj 0`).

### `Fin 1` index convention

Per spec §3-§5: use `0` (relying on `OfNat (Fin 1) 0`) in
proof goals and lemma RHSs; use `(0 : Fin 1)` with explicit
type ascription in constructions where Lean cannot infer
the `Fin` from context.  This matches the existing
`interp_towerER` convention (`ctx 0` on the RHS).

---

## Task 1 — Module skeleton + `GebLean.lean` import

**Files:**

- Create: `GebLean/Utilities/ERAMajorants.lean`
- Modify: `GebLean.lean` (add import per the skeleton rule)

- [ ] **Step 1.1: Create the module skeleton**

```lean
import GebLean.LawvereER
import GebLean.Utilities.ERArith
import GebLean.LawvereERBoundComputable
import GebLean.LawvereERPolynomialBound
import GebLean.Utilities.Tower

/-!
# Tourlakis A_n^r majorant family in ER

Lean-side realization of Tourlakis 2018 page 22 (proof of
§0.1.0.44 ⊆ direction) majorant family for K^sim level 2:

- `ERMor1.A_one : ERMor1 1` (interp `λx. 2x + 2`).
- `ERMor1.A_one_iter : ℕ → ERMor1 1`
  (interp `λx. 2^r * x + (2^{r+1} - 2)`).
- `ERMor1.A_two_iter : ℕ → ERMor1 1` (alias of
  `ERMor1.towerER`, interp `λx. tower r x`).

`A_one` and `A_one_iter` carry `PolyBound` builders
(linear in the input).  `A_two_iter` does not: `tower r x`
for `r ≥ 1` is not polynomially bounded in `x`, and
`ERMor1.PolyBound` is the bprod-free polynomial fragment
per `LawvereERPolynomialBound.lean`'s structural-towerHeight
section.  Downstream consumers (step 4 majorization,
step 5 `kToER` simrec at level 2) reason about
`A_two_iter`'s growth via `interp_A_two_iter` plus
`Utilities/Tower.lean`'s monotonicity lemmas (`tower_mono_right`,
`tower_mono_left`, `self_le_tower`,
`mul_tower_le_tower_add_two`,
`tower_pow_le_tower_add_three`), and feed the resulting
Nat-level dominance hypothesis into
`simultaneousBoundedRec_interp_correct` directly — no
`PolyBound` builder is invoked at level 2.

See
`docs/superpowers/specs/2026-05-03-step-3-er-tourlakis-A-majorants-design.md`
and master design §3.3 in
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`.
Cross-reference network:
`docs/research/2026-04-30-ksim-polynomial-bound-references.md`
for the polynomial-bound infrastructure context.
-/

namespace GebLean

namespace ERMor1

end ERMor1

end GebLean
```

- [ ] **Step 1.2: Register the import in `GebLean.lean` immediately**

Open `GebLean.lean`.  Add (in alphabetical order, near the
existing `import GebLean.Utilities.ERSimultaneousBoundedRec`
line):

```lean
import GebLean.Utilities.ERAMajorants
```

- [ ] **Step 1.3: Verify the empty skeleton builds**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERAMajorants.olean
lake build GebLean.Utilities.ERAMajorants 2>&1 | tail -3
```

Expected: clean build of the empty skeleton (only the
imports and module docstring).

- [ ] **Step 1.4: Commit**

```bash
git add GebLean/Utilities/ERAMajorants.lean GebLean.lean
git commit -m "Step 3 task 1: ERAMajorants skeleton + GebLean.lean import

Module skeleton for Tourlakis 2018 page 22 majorant family
for K^sim level 2 (kToER side, master design §3.3).
Per the import-at-skeleton-creation rule, GebLean.lean's
import is registered as part of this same commit."
```

---

## Task 2 — `ERMor1.A_one` definition

**Files:**

- Modify: `GebLean/Utilities/ERAMajorants.lean` (append
  inside `namespace ERMor1`)

- [ ] **Step 2.1: Define `ERMor1.A_one`**

Inside `namespace ERMor1`:

```lean
/-- Tourlakis 2018 page 22 majorant `A_1 = λx. 2x + 2`,
realized as an ER named composite.  Master design §3.3.

Construction: `addN(succ(proj 0), succ(proj 0))`, i.e.
`(x + 1) + (x + 1) = 2x + 2`. -/
def A_one : ERMor1 1 :=
  ERMor1.comp ERMor1.addN fun i => match i with
    | ⟨0, _⟩ => ERMor1.comp ERMor1.succ
                  (fun _ : Fin 1 =>
                    ERMor1.proj (0 : Fin 1))
    | ⟨1, _⟩ => ERMor1.comp ERMor1.succ
                  (fun _ : Fin 1 =>
                    ERMor1.proj (0 : Fin 1))
```

- [ ] **Step 2.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERAMajorants.olean
lake build GebLean.Utilities.ERAMajorants 2>&1 | tail -5
```

Expected: clean build, no warnings.

```bash
git add GebLean/Utilities/ERAMajorants.lean
git commit -m "Step 3 task 2: ERMor1.A_one definition

Tourlakis 2018 page 22 majorant A_1 = λx. 2x + 2 as an ER
named composite, built from addN(succ(proj 0), succ(proj 0)).
Master design §3.3."
```

---

## Task 3 — `interp_A_one` `@[simp]` theorem

**Files:**

- Modify: `GebLean/Utilities/ERAMajorants.lean` (append
  after `A_one` inside `namespace ERMor1`)

- [ ] **Step 3.1: State and prove `interp_A_one`**

```lean
/-- Closed-form interpretation of `A_one`:
`A_one.interp ![x] = 2 * x + 2` (Tourlakis 2018 page 22,
`A_1`).  Master design §3.3. -/
@[simp] theorem interp_A_one (ctx : Fin 1 → ℕ) :
    A_one.interp ctx = 2 * (ctx 0) + 2 := by
  unfold A_one
  simp only [ERMor1.interp_comp, ERMor1.interp_addN,
    ERMor1.interp_succ, ERMor1.interp_proj]
  omega
```

Note: `ring` does not close — `simp only` produces a
residual goal containing `Nat.succ`-shaped terms that
`ring` cannot normalize on `Nat`.  `omega` closes
immediately.

- [ ] **Step 3.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERAMajorants.olean
lake build GebLean.Utilities.ERAMajorants 2>&1 | tail -5
```

Expected: clean build, no warnings.

```bash
git add GebLean/Utilities/ERAMajorants.lean
git commit -m "Step 3 task 3: interp_A_one closed-form simp lemma

Closed-form interpretation A_one.interp ![x] = 2 * x + 2,
proved via simp through the constructor interp lemmas plus
omega.  Tourlakis 2018 page 22, A_1.  Master design §3.3."
```

---

## Task 4 — `ERMor1.A_one_iter` definition

**Files:**

- Modify: `GebLean/Utilities/ERAMajorants.lean` (append
  after `interp_A_one` inside `namespace ERMor1`)

- [ ] **Step 4.1: Define `ERMor1.A_one_iter`**

```lean
/-- Tourlakis 2018 page 22 iterated majorant
`A_1^r = λx. 2^r * x + (2^{r+1} − 2)`, realized as r-fold
composition of `A_one` with itself.  Master design §3.3.

Recursion direction: `A_1 ∘ A_1^r` (apply r-fold first,
then one more `A_one`).  At `r = 0` returns the
identity-on-1, realized as `proj 0`. -/
def A_one_iter : ℕ → ERMor1 1
  | 0     => ERMor1.proj (0 : Fin 1)
  | r + 1 => ERMor1.comp A_one
              (fun _ : Fin 1 => A_one_iter r)
```

- [ ] **Step 4.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERAMajorants.olean
lake build GebLean.Utilities.ERAMajorants 2>&1 | tail -5
```

Expected: clean build, no warnings.

```bash
git add GebLean/Utilities/ERAMajorants.lean
git commit -m "Step 3 task 4: ERMor1.A_one_iter definition

r-fold composition of A_one with itself, with the recursion
direction A_1 ∘ A_1^r (apply r-fold first, then one more).
At r = 0, returns proj 0 (the identity on Fin 1).
Tourlakis 2018 page 22, A_1^r.  Master design §3.3."
```

---

## Task 5 — `interp_A_one_iter` closed-form `@[simp]` theorem

**Files:**

- Modify: `GebLean/Utilities/ERAMajorants.lean` (append
  after `A_one_iter` inside `namespace ERMor1`)

- [ ] **Step 5.1: State and prove `interp_A_one_iter`**

```lean
/-- Closed-form interpretation of `A_one_iter`:
`(A_one_iter r).interp ![x] = 2^r * x + (2^{r+1} − 2)`
(Tourlakis 2018 page 22, `A_1^r` r-fold composition closed
form).  Master design §3.3.

Proof outline: induction on `r`.  Base case unfolds
`A_one_iter 0 = proj 0` and reduces by `omega`.  Successor
case unfolds one layer of `A_one_iter (r + 1)`, applies the
`@[simp] interp_A_one` rewrite to collapse the outer
`A_one`, rewrites by the IH, and closes via `omega` after
introducing explicit `pow_succ`-derived equalities for
`2^(r+1)` and `2^(r+2)`, a positivity hypothesis
`Nat.one_le_pow _ _` for the `Nat`-subtraction guard, and
a multiplicative bridge
`2^(r+1) * ctx 0 = 2 * (2^r * ctx 0)` (without which omega
treats the two `* ctx 0` products as independent atoms;
see spec §9.6). -/
@[simp] theorem interp_A_one_iter (r : ℕ)
    (ctx : Fin 1 → ℕ) :
    (A_one_iter r).interp ctx
      = 2 ^ r * (ctx 0) + (2 ^ (r + 1) - 2) := by
  induction r with
  | zero =>
      unfold A_one_iter
      simp only [ERMor1.interp_proj, pow_zero, one_mul]
      omega
  | succ r ih =>
      unfold A_one_iter
      simp only [ERMor1.interp_comp, interp_A_one]
      rw [ih]
      have h_succ1 : 2 ^ (r + 1) = 2 * 2 ^ r := by
        rw [pow_succ]; ring
      have h_succ2 : 2 ^ (r + 2) = 2 * 2 ^ (r + 1) := by
        rw [pow_succ]; ring
      have h_pow_ge_two : 2 ≤ 2 ^ (r + 1) := by
        rw [h_succ1]
        have h_pow_pos_r : 1 ≤ 2 ^ r :=
          Nat.one_le_pow _ _ (by omega)
        omega
      have h_mul_bridge :
          2 ^ (r + 1) * ctx 0 = 2 * (2 ^ r * ctx 0) := by
        rw [h_succ1]; ring
      omega
```

This proof was empirically verified during round-4
adversarial review by transcribing into a fresh module and
running `lake build` with no errors or warnings.

- [ ] **Step 5.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERAMajorants.olean
lake build GebLean.Utilities.ERAMajorants 2>&1 | tail -5
```

Expected: clean build, no warnings.

```bash
git add GebLean/Utilities/ERAMajorants.lean
git commit -m "Step 3 task 5: interp_A_one_iter closed-form simp lemma

Closed-form 2^r * x + (2^{r+1} - 2) for the r-fold composition
of A_one with itself.  Proved by induction on r; the succ
case requires explicit pow_succ-derived equalities, a Nat
positivity hypothesis, and a multiplicative bridge so omega
can close the linear arithmetic over the atoms 2^r and
2^(r+1) * x.  Tourlakis 2018 page 22, A_1^r.  Master design
§3.3."
```

---

## Task 6 — `ERMor1.A_two_iter` definition + `interp_A_two_iter`

**Files:**

- Modify: `GebLean/Utilities/ERAMajorants.lean` (append
  after `interp_A_one_iter` inside `namespace ERMor1`)

- [ ] **Step 6.1: Define `ERMor1.A_two_iter`**

```lean
/-- Tourlakis 2018 page 22 iterated majorant
`A_2^r = λx. tower r x`, realized as the existing named
composite `def ERMor1.towerER` in
`LawvereERBoundComputable.lean`.  Underlying construction
iterates `expER` with base `2`, citing Tourlakis 2018
§0.1.0.17 (c) `λx. 2^x ∈ ER`.  Master design §3.3.

No `PolyBound` builder is provided: `tower r x` for
`r ≥ 1` is not polynomially bounded in `x`, and
`ERMor1.PolyBound` is the bprod-free polynomial fragment
per `LawvereERPolynomialBound.lean`'s structural-towerHeight
section.  See the module docstring for how downstream
consumers handle this. -/
def A_two_iter (r : ℕ) : ERMor1 1 := ERMor1.towerER r
```

- [ ] **Step 6.2: State and prove `interp_A_two_iter`**

```lean
/-- Closed-form interpretation of `A_two_iter`:
`(A_two_iter r).interp ![x] = tower r x` (Tourlakis 2018
page 22, `A_2^r = tower r x`).  Routes through the existing
`interp_towerER` simp lemma.  Master design §3.3. -/
@[simp] theorem interp_A_two_iter (r : ℕ)
    (ctx : Fin 1 → ℕ) :
    (A_two_iter r).interp ctx
      = tower r (ctx 0) := by
  unfold A_two_iter
  exact ERMor1.interp_towerER r ctx
```

- [ ] **Step 6.3: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERAMajorants.olean
lake build GebLean.Utilities.ERAMajorants 2>&1 | tail -5
```

Expected: clean build, no warnings.

```bash
git add GebLean/Utilities/ERAMajorants.lean
git commit -m "Step 3 task 6: ERMor1.A_two_iter alias + interp lemma

A_two_iter r aliases ERMor1.towerER r; interp_A_two_iter
routes through the existing interp_towerER simp lemma to
expose the closed-form tower r (ctx 0).  No PolyBound
builder is provided (tower-fast).  Tourlakis 2018 page 22,
A_2^r = tower r.  Master design §3.3."
```

---

## Task 7 — `ERMor1.PolyBound.ofA_one`

**Files:**

- Modify: `GebLean/Utilities/ERAMajorants.lean` (append
  after `interp_A_two_iter` inside `namespace ERMor1`,
  switching to sub-namespace `PolyBound`)

- [ ] **Step 7.1: Open `namespace PolyBound` and define `ofA_one`**

```lean
namespace PolyBound

/-- Polynomial bound for `A_one`: linear with leading
coefficient `2` and zero constant.

The bound shape `2 * (sup ctx + 1)^1 + 0` evaluates to
`2 * (sup + 1) = 2 * sup + 2 ≥ 2 * (ctx 0) + 2`, since
`ctx 0 ≤ sup ctx`.  Master design §3.3 amended
polynomial-bound certification subsection. -/
def ofA_one : PolyBound A_one where
  degree      := 1
  coefficient := 2
  constant    := 0
  bounds      := fun ctx => by
    rw [interp_A_one]
    simp only [pow_one, Nat.add_zero]
    have h_ctx0_le_sup :
        ctx 0
          ≤ (Finset.univ : Finset (Fin 1)).sup ctx :=
      Finset.le_sup
        (s := (Finset.univ : Finset (Fin 1)))
        (f := ctx) (b := (0 : Fin 1))
        (Finset.mem_univ _)
    omega
```

This proof was empirically verified during round-4
adversarial review.

- [ ] **Step 7.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERAMajorants.olean
lake build GebLean.Utilities.ERAMajorants 2>&1 | tail -5
```

Expected: clean build, no warnings.

```bash
git add GebLean/Utilities/ERAMajorants.lean
git commit -m "Step 3 task 7: ERMor1.PolyBound.ofA_one builder

PolyBound for A_one (degree 1, coefficient 2, constant 0).
Tightness: 2 * (sup + 1) = 2 * sup + 2 ≥ 2 * (ctx 0) + 2.
Master design §3.3 amended polynomial-bound certification
subsection."
```

---

## Task 8 — `ERMor1.PolyBound.ofA_one_iter`

**Files:**

- Modify: `GebLean/Utilities/ERAMajorants.lean` (append
  after `ofA_one` inside `namespace PolyBound`)

- [ ] **Step 8.1: Define `ofA_one_iter`**

```lean
/-- Polynomial bound for `A_one_iter r`: linear with
leading coefficient `2^r` and constant `2^{r+1} − 2`.

The chosen `(degree, coefficient, constant)` triple
matches the closed-form `interp_A_one_iter` literally:
the closed form `2^r * (ctx 0) + (2^{r+1} − 2)` is
dominated by `2^r * (sup ctx + 1) + (2^{r+1} − 2)`
because `ctx 0 ≤ sup ctx ≤ sup ctx + 1`, so the bounds
proof reduces to a `Nat.mul_le_mul_left` step on the
leading-coefficient slot.  The constant slot is matched
exactly.

Master design §3.3 amended polynomial-bound
certification subsection. -/
def ofA_one_iter (r : ℕ) : PolyBound (A_one_iter r) where
  degree      := 1
  coefficient := 2 ^ r
  constant    := 2 ^ (r + 1) - 2
  bounds      := fun ctx => by
    rw [interp_A_one_iter]
    simp only [pow_one]
    have h_ctx0_le_sup :
        ctx 0
          ≤ (Finset.univ : Finset (Fin 1)).sup ctx :=
      Finset.le_sup
        (s := (Finset.univ : Finset (Fin 1)))
        (f := ctx) (b := (0 : Fin 1))
        (Finset.mem_univ _)
    have h_ctx0_le_succ :
        ctx 0
          ≤ (Finset.univ : Finset (Fin 1)).sup ctx + 1 := by
      omega
    have h_mul :
        2 ^ r * ctx 0
          ≤ 2 ^ r *
              ((Finset.univ : Finset (Fin 1)).sup ctx + 1) :=
      Nat.mul_le_mul_left _ h_ctx0_le_succ
    omega
```

This proof was empirically verified during round-4
adversarial review.

- [ ] **Step 8.2: Close namespaces and build**

After the `ofA_one_iter` definition, the file should end with
both namespace closers in place.  Verify the file's tail
reads:

```lean
end PolyBound

end ERMor1

end GebLean
```

Then build:

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERAMajorants.olean
lake build GebLean.Utilities.ERAMajorants 2>&1 | tail -5
```

Expected: clean build, no warnings.

- [ ] **Step 8.3: Commit**

```bash
git add GebLean/Utilities/ERAMajorants.lean
git commit -m "Step 3 task 8: ERMor1.PolyBound.ofA_one_iter builder

PolyBound for A_one_iter r (degree 1, coefficient 2^r,
constant 2^{r+1} - 2).  The constant slot matches the
closed-form interp_A_one_iter literally; the bounds proof
reduces to Nat.mul_le_mul_left on the leading-coefficient
slot.  Master design §3.3 amended polynomial-bound
certification subsection."
```

---

## Task 9 — Test module skeleton + ER-side `#guard`s

**Files:**

- Create: `GebLeanTests/Utilities/ERAMajorants.lean`
- Modify: `GebLeanTests.lean` (add import per the skeleton
  rule)

- [ ] **Step 9.1: Create the test-module skeleton**

```lean
import GebLean.Utilities.ERAMajorants

/-!
# Tests for `GebLean.Utilities.ERAMajorants`

Per the project's ER-side `.interp` test discipline:
`#guard`s are restricted to bprod-free composites at small
inputs.  `A_one` and `A_one_iter` use `bsum` via `mulN`
inside `addN`, but `bsum` size scales linearly with input
so small-input `#guard`s terminate quickly.  `A_two_iter`
at `r ≥ 1` aliases `towerER` (which uses `expER`'s `bprod`)
and is excluded except at `r = 0` (definitionally
`proj 0`).

Closed-form correctness for all `r` is captured by the
`@[simp]` interp lemmas
(`ERMor1.interp_A_one`, `ERMor1.interp_A_one_iter`,
`ERMor1.interp_A_two_iter`); these `#guard`s are sanity
backstops, not the primary correctness witness.
-/

namespace GebLean

end GebLean
```

- [ ] **Step 9.2: Register the test import in `GebLeanTests.lean` immediately**

Open `GebLeanTests.lean`.  Add (in alphabetical order, near
the existing
`import GebLeanTests.Utilities.ERSimultaneousBoundedRec`
line):

```lean
import GebLeanTests.Utilities.ERAMajorants
```

- [ ] **Step 9.3: Verify the empty test skeleton builds**

```bash
rm -f .lake/build/lib/lean/GebLeanTests/Utilities/ERAMajorants.olean
lake test 2>&1 | tail -5
```

Expected: clean build, no warnings.

- [ ] **Step 9.4: Add ER-side `#guard`s**

Inside `namespace GebLean`, append:

```lean
-- A_one: shallow, with bsum reductions only at small bounds
-- via mulN (= boolAnd = bsum ...).  No bprod, no boundedRec;
-- bsum-via-mulN size scales linearly with input, so
-- small-input #guards terminate fast.
#guard ERMor1.A_one.interp ![0] = 2
#guard ERMor1.A_one.interp ![3] = 8
#guard ERMor1.A_one.interp ![5] = 12

-- A_one_iter at small r: bsum sizes <= 9 at r = 2, x = 3.
#guard (ERMor1.A_one_iter 0).interp ![3] = 3
#guard (ERMor1.A_one_iter 1).interp ![3] = 8
#guard (ERMor1.A_one_iter 2).interp ![0] = 6
#guard (ERMor1.A_one_iter 2).interp ![3] = 18

-- A_two_iter at r = 0 reduces definitionally to proj 0;
-- safe to #guard.
#guard (ERMor1.A_two_iter 0).interp ![5] = 5

-- No #guard on A_two_iter at r ≥ 1: kernel reduction
-- explodes through expER's bprod.  Closed-form correctness
-- is captured by interp_A_two_iter + the existing
-- interp_towerER lemma.
```

- [ ] **Step 9.5: Run the tests and observe timing**

```bash
rm -f .lake/build/lib/lean/GebLeanTests/Utilities/ERAMajorants.olean
time lake test 2>&1 | tail -5
```

Expected: clean test run.  If any individual `A_one_iter 2`
`#guard` is observed to dominate the runtime (e.g. takes
more than a couple of seconds), drop that line — the
closed-form `interp_A_one_iter` simp lemma already proves
correctness for all `r`, so the `#guard`s are sanity
backstops only.

- [ ] **Step 9.6: Commit**

```bash
git add GebLeanTests/Utilities/ERAMajorants.lean GebLeanTests.lean
git commit -m "Step 3 task 9: ERAMajorants test module + ER-side #guards

Test skeleton + GebLeanTests.lean import (per the
import-at-skeleton-creation rule), plus ER-side #guards for
A_one (3 inputs), A_one_iter (4 inputs at r ≤ 2), and
A_two_iter (1 input at r = 0).  No #guards at r ≥ 1 for
A_two_iter (kernel reduction explodes through expER's
bprod); closed-form correctness is captured by the
@[simp] interp_A_two_iter lemma."
```

---

## Task 10 — Final verification

**Files:** No code changes.  Verification only.

- [ ] **Step 10.1: Forced-rebuild verification (whole project)**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERAMajorants.olean
rm -f .lake/build/lib/lean/GebLeanTests/Utilities/ERAMajorants.olean
lake build 2>&1 | tail -10
```

Expected output: no `error:` lines, no `warning:` lines,
ending with "Build completed successfully" (do NOT trust
that line in isolation — verify by inspection of the full
output that no errors or warnings appear).

- [ ] **Step 10.2: Run the full test suite**

```bash
lake test 2>&1 | tail -10
```

Expected: clean test run; no `#guard` failures.

- [ ] **Step 10.3: Verify acceptance criteria**

Open `GebLean/Utilities/ERAMajorants.lean` and confirm:

- [ ] `def ERMor1.A_one : ERMor1 1` is present.
- [ ] `def ERMor1.A_one_iter : ℕ → ERMor1 1` is present.
- [ ] `def ERMor1.A_two_iter : ℕ → ERMor1 1` is present
      (alias of `ERMor1.towerER`).
- [ ] `@[simp] theorem ERMor1.interp_A_one`,
      `interp_A_one_iter`, `interp_A_two_iter` are present
      with closed forms per spec §4.
- [ ] `def ERMor1.PolyBound.ofA_one : PolyBound A_one` is
      present.
- [ ] `def ERMor1.PolyBound.ofA_one_iter (r : ℕ) :
      PolyBound (A_one_iter r)` is present.
- [ ] Module docstring cites Tourlakis 2018 page 22 and
      master design §3.3, includes the polynomial-vs-tower
      split paragraph that explicitly documents the absence
      of `ofA_two_iter`, and contains pointers to
      `docs/research/2026-04-30-ksim-polynomial-bound-references.md`
      and master design §3.3.
- [ ] Each public def/theorem carries a per-entity
      docstring with the citations from spec §7.

Open `GebLean.lean` and confirm:

- [ ] `import GebLean.Utilities.ERAMajorants` is present.

Open `GebLeanTests.lean` and confirm:

- [ ] `import GebLeanTests.Utilities.ERAMajorants` is
      present.

- [ ] **Step 10.4: Update `.session/workstreams/er-ksim2-equiv-via-urm.md`**

Append a "Step 3 complete" entry to the Progress section
mirroring the step-2 entry.  Example:

```markdown
- Step 3 (Tourlakis A_n^r majorant family in ER):
  complete.  Lands `ERMor1.A_one`, `ERMor1.A_one_iter`,
  `ERMor1.A_two_iter` named composites; closed-form
  `@[simp]` interp lemmas; `ERMor1.PolyBound.ofA_one` and
  `ERMor1.PolyBound.ofA_one_iter` builders.  No PolyBound
  for `A_two_iter` (tower-fast; level-2 chain consumes
  Nat-level dominance via `simultaneousBoundedRec_interp_correct`
  at step 5).  Plan at
  `docs/superpowers/plans/2026-05-03-step-3-er-tourlakis-A-majorants.md`.
  Spec at
  `docs/superpowers/specs/2026-05-03-step-3-er-tourlakis-A-majorants-design.md`.
  4 rounds adversarial review; round 4 empirically
  Lean-verified all five spec proofs.
```

Update the "Next steps" section to point to step 4
(`LawvereKSimMajorization.lean`).

- [ ] **Step 10.5: `markdownlint-cli2` clean on docs**

```bash
markdownlint-cli2 \
  docs/superpowers/plans/2026-05-03-step-3-er-tourlakis-A-majorants.md \
  docs/superpowers/specs/2026-05-03-step-3-er-tourlakis-A-majorants-design.md \
  docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md \
  docs/research/2026-05-03-step-3-spec-adversarial-review-round-1.md \
  docs/research/2026-05-03-step-3-spec-adversarial-review-round-2.md \
  docs/research/2026-05-03-step-3-spec-adversarial-review-round-3.md \
  docs/research/2026-05-03-step-3-spec-adversarial-review-round-4.md \
  2>&1 | tail -3
```

Expected: 0 errors.

- [ ] **Step 10.6: Final commit**

```bash
git add .session/workstreams/er-ksim2-equiv-via-urm.md
git commit -m "Step 3 task 10: final verification + workstream update

All acceptance criteria from spec §10 verified.  Clean lake
build and lake test (no errors, no warnings, no sorry).
Module exports and per-entity docstrings confirmed.
Workstream notes updated.  Step 3 complete."
```

- [ ] **Step 10.7: Cycle-end code review (delegated)**

Dispatch a fresh code-review subagent covering the entire
diff of step 3 (`origin/terence/develop..HEAD` after the
spec/plan commits land):

- The subagent should read every line of
  `GebLean/Utilities/ERAMajorants.lean`,
  `GebLeanTests/Utilities/ERAMajorants.lean`, and the
  diffs in `GebLean.lean` and `GebLeanTests.lean`.
- It should verify the spec §10 acceptance criteria
  against the actual code, not the plan.
- It should produce a finding list at
  `docs/research/2026-05-03-step-3-cycle-end-review.md`.
- Address its substantive findings before declaring step 3
  done.

(This step is the final per-cycle review step described in
the procedure document; do not skip it.)

---

## Out of scope for this plan (step 4 owes)

Per spec §8, the following are NOT part of this plan and
will be implemented in step 4
(`LawvereKSimMajorization.lean`):

1. `linearBound_le_A_one_iter` translation lemma.
2. Cross-family translation lemmas relating `A_1^k` to
   `A_2^?`.
3. `KMor1.majorize_r f h` (explicit Lean-`Nat` `r` as a
   function of K^sim term structure).
4. `KMor1.majorize_by_A_one_iter` for `f.level ≤ 1`.
5. `KMor1.majorize_by_A_two_iter` for `f.level ≤ 2`.
6. All level-2 iteration arithmetic (the
   `M_n ≤ A_1^{r_H + n · r_G}(...)` closed-form bound and
   its inductive proof on `n`).
7. The Nat hypothesis fed to
   `simultaneousBoundedRec_interp_correct`'s dominance
   slot at step 5's level-2 simrec case.
8. Module file `GebLean/LawvereKSimMajorization.lean`.

`tower r x` monotonicity lemmas already in
`Utilities/Tower.lean` (`tower_mono_right`,
`tower_mono_left`, `self_le_tower`,
`mul_tower_le_tower_add_two`, `tower_pow_le_tower_add_three`)
are consumed as-is by step 4; this plan does not extend
`Utilities/Tower.lean`.
