# Step 3 — Tourlakis A_n^r majorant family in ER

Spec for cycle 3 of the ER ↔ K^sim_2 categorical-equivalence
formalization (master design:
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`).
This cycle lands the ER named composites realizing
Tourlakis 2018 page-22 majorant family (`A_1`, `A_1^r`,
`A_2^r`) plus their closed-form interp lemmas and
`PolyBound` builders for the `A_1` variants.  The level-2
member `A_2^r` is tower-fast and ships without a
`PolyBound`; downstream majorization (step 4) reasons about
it via the closed-form `tower r x` Nat function.

## §1 Status and motivation

### §1.1 Goal

Realize Tourlakis 2018 page 22 (proof of §0.1.0.44 ⊆
direction) majorant family as ER named composites, with
closed-form `@[simp]` interp lemmas suitable for direct
`Nat`-arithmetic reasoning, and `PolyBound` builders where
the family member admits a polynomial bound.  Downstream
consumers:

- Step 4 majorization (master design §3.4):
  `linearBound_le_A_one_iter` translation, level-1 and
  level-2 `KMor1.majorize_by_A_n_iter` theorems, all
  consume `interp_A_one`, `interp_A_one_iter`,
  `interp_A_two_iter`.  The `PolyBound` builders are
  consumed where the level chain stays polynomial.
- Step 5 `kToER` (master design §3.5): the simrec case at
  level 2 uses `A_two_iter r` as the `componentBound`
  argument to `simultaneousBoundedRec`, with the dominance
  hypothesis supplied by step 4's
  `KMor1.majorize_by_A_two_iter`.

### §1.2 Scope

In scope:

- `GebLean/Utilities/ERAMajorants.lean` (ER-level):
  `ERMor1.A_one`, `ERMor1.A_one_iter`, `ERMor1.A_two_iter`
  named composites; closed-form `@[simp]` interp lemmas;
  `ERMor1.PolyBound.ofA_one`,
  `ERMor1.PolyBound.ofA_one_iter`.
- Tests: `GebLeanTests/Utilities/ERAMajorants.lean`.

Out of scope (step 4 owns; see §8 below for the explicit
list):

- `linearBound_le_A_one_iter` translation lemma.
- Cross-family translation lemmas relating `A_1^k` to
  `A_2^?`.
- `KMor1.majorize_r`, `KMor1.majorize_by_A_one_iter`,
  `KMor1.majorize_by_A_two_iter` structural-induction
  theorems.
- All level-2 iteration arithmetic.

Out of scope and not anyone's job:

- `PolyBound` for `A_two_iter`: does not exist.
  `tower r x` for `r ≥ 1` is not polynomially bounded in
  `x`, and `ERMor1.PolyBound` is the bprod-free polynomial
  fragment per `LawvereERPolynomialBound.lean`'s
  structural-towerHeight section.  The level-2 chain
  consumes `interp_A_two_iter` + Nat-level dominance from
  step 4 directly; no `PolyBound` is needed.  Master
  design §3.3 was amended to remove this deliverable.
- A unary `ERMor1.A_two : ERMor1 1` definition.  The
  literature's `A_2 = λx. 2^x` is exactly `A_two_iter 1`
  (since `tower 1 x = 2^x`); no separate name is warranted.
- K^sim-side `A_n` composites.  Master design §3.3 builds
  the `A_n` family on the ER side only; K^sim-side
  majorization (step 4) consumes the ER `A_n` via
  `(ERMor1.A_n_iter r).interp` on the bound side.

### §1.3 Implementation flexibility vs literature contract

Per CLAUDE.md "Non-negotiable interfaces for categories
formalizing pre-existing mathematical objects": the
mathematical content is fixed by literature; Lean
representation choices may flex.

**Literature-fixed (non-negotiable):**

- `A_one`'s interp is `λx. 2x + 2` (Tourlakis 2018 page
  22, `A_1`).
- `A_one_iter r`'s interp is `λx. 2^r * x + (2^{r+1} − 2)`
  (Tourlakis 2018 page 22, `A_1^r`; r-fold composition of
  `A_1` with itself, closed form).
- `A_two_iter r`'s interp is `λx. tower r x`
  (= `A_2^r(x)` per Tourlakis 2018 page 22).
- All three are in `ERMor1` directly, not in some E^n
  surrogate.
- Polynomial-bound shape inherits from
  `LawvereERPolynomialBound.lean`'s `PolyBound`
  structure (`coefficient * (max+1)^degree + constant`).

**Lean-side flexible:**

- Exact construction of `A_one` from atomic generators
  (`addN(succ(proj 0), succ(proj 0))` is one option;
  `succ(succ(addN(proj 0, proj 0)))` is another;
  `comp addN [...]` exact slot routing).
- Recursion direction in `A_one_iter` (`A_1 ∘ A_1^r` or
  `A_1^r ∘ A_1`).
- Choice of tactic for arithmetic steps (`omega`, `ring`,
  explicit chains).
- Whether `interp_A_one_iter`'s closed-form constant is
  written as `2 ^ (r + 1) − 2` or `2 * 2^r − 2` (same
  Nat).

The implementer may revise any Lean-side representation
during implementation if proofs reveal a cleaner path,
provided the literature contract is preserved.

## §2 Architecture and module layout

One new module under `GebLean/Utilities/`:

### §2.1 `GebLean/Utilities/ERAMajorants.lean`

- Imports:
  - `GebLean.LawvereERArith` (for `ERMor1.addN`,
    `ERMor1.succ`, `ERMor1.proj`, and their interp simp
    lemmas).
  - `GebLean.LawvereERBoundComputable` (for
    `ERMor1.towerER`, `ERMor1.interp_towerER`).
  - `GebLean.LawvereERPolynomialBound` (for
    `ERMor1.PolyBound`).
  - `GebLean.Utilities.Tower` (transitively pulled in;
    direct import for clarity).
- Namespace: `GebLean`, with definitions under
  `ERMor1` and the `PolyBound` builders under
  `ERMor1.PolyBound`.

### §2.2 Tests

- `GebLeanTests/Utilities/ERAMajorants.lean`.

### §2.3 Imports at skeleton-creation time

Per discipline-1 (step 1 task 4.5 lesson): each new
module's import is registered in `GebLean.lean` (or
`GebLeanTests.lean` for tests) immediately when the
skeleton file is created, before any code is added to it.
This guarantees `lake build` re-elaborates the new module
on every subsequent task, catching linter regressions in
real time.

### §2.4 Dependency graph

```text
LawvereERArith                              (existing)
  ↓
LawvereERBoundComputable                    (existing)
  ↓
LawvereERPolynomialBound                    (existing)
  ↓
ERAMajorants.lean                           [step 3, this cycle]
  ↓
LawvereKSimMajorization.lean                [step 4]
  ↓
LawvereKSimER.lean                          [step 5]
```

ER-side step 3 sits parallel to the
`ERSimultaneousBoundedRec.lean` chain landed in step 2;
the two contribute independently to step 4's input.

## §3 ER named composites

All in `namespace GebLean.ERMor1`.

### §3.1 `A_one : ERMor1 1`

```lean
/-- Tourlakis 2018 page 22 majorant `A_1 = λx. 2x + 2`,
realized as an ER named composite.  Master design §3.3.

Construction: `addN(succ(proj 0), succ(proj 0))`, i.e.
`(x + 1) + (x + 1) = 2x + 2`. -/
def A_one : ERMor1 1 :=
  ERMor1.comp ERMor1.addN fun i => match i with
    | ⟨0, _⟩ => ERMor1.comp ERMor1.succ
                  (fun _ : Fin 1 =>
                    ERMor1.proj ⟨0, by decide⟩)
    | ⟨1, _⟩ => ERMor1.comp ERMor1.succ
                  (fun _ : Fin 1 =>
                    ERMor1.proj ⟨0, by decide⟩)
```

Citation: Tourlakis 2018 page 22 (proof of §0.1.0.44 ⊆),
`A_1` definition; master design §3.3.

### §3.2 `A_one_iter : ℕ → ERMor1 1`

```lean
/-- Tourlakis 2018 page 22 iterated majorant
`A_1^r = λx. 2^r * x + (2^{r+1} − 2)`, realized as r-fold
composition of `A_one` with itself.  Master design §3.3.

Recursion direction: `A_1 ∘ A_1^r` (apply r-fold first,
then one more `A_one`).  At `r = 0` returns the identity
on `Fin 1`, realized as `proj 0`. -/
def A_one_iter : ℕ → ERMor1 1
  | 0     => ERMor1.proj ⟨0, by decide⟩
  | r + 1 => ERMor1.comp A_one
              (fun _ : Fin 1 => A_one_iter r)
```

Citation: Tourlakis 2018 page 22, `A_1^r` notation; master
design §3.3 lines 192-193 (closed form
`2^r · x + (2^{r+1} − 2)` for `r`-fold composition).

### §3.3 `A_two_iter : ℕ → ERMor1 1`

```lean
/-- Tourlakis 2018 page 22 iterated majorant
`A_2^r = λx. tower r x`, realized as the existing named
composite `ERMor1.towerER r` (`LawvereERBoundComputable.lean`
line 230).  Underlying construction iterates `expER` with
base `2`, citing Tourlakis 2018 §0.1.0.17 (c)
`λx. 2^x ∈ ER`.  Master design §3.3. -/
def A_two_iter (r : ℕ) : ERMor1 1 := ERMor1.towerER r
```

Citation: Tourlakis 2018 page 22, `A_2^r = tower r`; master
design §3.3.

## §4 Closed-form interp lemmas

### §4.1 `interp_A_one`

```lean
@[simp] theorem interp_A_one (ctx : Fin 1 → ℕ) :
    A_one.interp ctx = 2 * (ctx ⟨0, by decide⟩) + 2 := by
  unfold A_one
  simp only [ERMor1.interp_comp, ERMor1.interp_addN,
    ERMor1.interp_succ, ERMor1.interp_proj]
  ring
```

(Tactic shape; final implementation may use `omega` if
`ring` does not close the residual `Nat`-arithmetic goal.)

### §4.2 `interp_A_one_iter`

```lean
@[simp] theorem interp_A_one_iter (r : ℕ)
    (ctx : Fin 1 → ℕ) :
    (A_one_iter r).interp ctx
      = 2 ^ r * (ctx ⟨0, by decide⟩)
          + (2 ^ (r + 1) - 2) := by
  induction r with
  | zero =>
      unfold A_one_iter
      simp only [ERMor1.interp_proj, pow_zero, one_mul,
        pow_one]
      omega
  | succ r ih =>
      unfold A_one_iter
      simp only [ERMor1.interp_comp, interp_A_one]
      rw [show (fun _ : Fin 1 =>
                  (A_one_iter r).interp ctx) ⟨0, by decide⟩
              = (A_one_iter r).interp ctx from rfl, ih]
      have h_pow_ge_two : 2 ^ (r + 1) ≥ 2 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      ring_nf
      omega
```

Proof outline (tactic shape; implementation may streamline):

- Base `r = 0`: `A_one_iter 0 = proj 0`, so interp =
  `ctx 0 = 2^0 * ctx 0 + 0 = 2^0 * ctx 0 + (2^1 - 2)`.
- Step `r + 1`: by IH, `(A_one_iter r).interp ctx
  = 2^r * ctx 0 + (2^{r+1} - 2)`.  Then
  `(A_one_iter (r+1)).interp ctx = A_one.interp [previous]
  = 2 * (2^r * ctx 0 + (2^{r+1} - 2)) + 2
  = 2^{r+1} * ctx 0 + 2^{r+2} - 4 + 2
  = 2^{r+1} * ctx 0 + (2^{r+2} - 2)`.
  The `Nat`-subtraction step needs a `2^{r+1} ≥ 2` lemma
  for `omega`.

### §4.3 `interp_A_two_iter`

```lean
@[simp] theorem interp_A_two_iter (r : ℕ)
    (ctx : Fin 1 → ℕ) :
    (A_two_iter r).interp ctx
      = tower r (ctx ⟨0, by decide⟩) := by
  unfold A_two_iter
  exact ERMor1.interp_towerER r ctx
```

Pure routing through the existing
`ERMor1.interp_towerER` lemma.

## §5 PolyBound builders

All in `namespace GebLean.ERMor1.PolyBound`.

### §5.1 `ofA_one`

```lean
/-- Polynomial bound for `A_one`: linear with leading
coefficient `2` and zero constant.  The bound
`2 * (sup ctx + 1) + 0` exactly matches `A_one`'s closed
form `2 * ctx 0 + 2` when `ctx 0 = sup ctx`.

Master design §3.3 amended polynomial-bound certification
subsection. -/
def ofA_one : PolyBound A_one where
  degree      := 1
  coefficient := 2
  constant    := 0
  bounds      := fun ctx => by
    rw [interp_A_one]
    simp only [pow_one, Nat.add_zero]
    have h_ctx0 : ctx ⟨0, by decide⟩
                    ≤ (Finset.univ : Finset (Fin 1)).sup ctx
                  + 0 := by
      have := Finset.le_sup
        (s := (Finset.univ : Finset (Fin 1)))
        (f := ctx) (b := ⟨0, by decide⟩)
        (by simp)
      omega
    omega
```

(Tactic shape; implementation will adjust the
`Finset.le_sup` invocation to match the existing
`PolyBound.bounds` field's exact statement, mirroring
`ofAddN` at `LawvereERPolynomialBound.lean` line 448.)

### §5.2 `ofA_one_iter`

```lean
/-- Polynomial bound for `A_one_iter r`: linear with
leading coefficient `2^r` and constant `2^{r+1} − 2`,
matching the closed-form `interp_A_one_iter` literally so
the bounds proof reduces to `ctx 0 ≤ sup ctx`.

The bound is loose by `2^r` at the constant slot if
compared to the tightest possible `Nat` constant
(`max(0, 2^r − 2)`); the looser choice is preferred for
proof brevity.  Master design §3.3 amended
polynomial-bound certification subsection. -/
def ofA_one_iter (r : ℕ) : PolyBound (A_one_iter r) where
  degree      := 1
  coefficient := 2 ^ r
  constant    := 2 ^ (r + 1) - 2
  bounds      := fun ctx => by
    rw [interp_A_one_iter]
    simp only [pow_one]
    have h_ctx0 : ctx ⟨0, by decide⟩
                    ≤ (Finset.univ : Finset (Fin 1)).sup ctx
                  := Finset.le_sup
        (s := (Finset.univ : Finset (Fin 1)))
        (f := ctx) (b := ⟨0, by decide⟩) (by simp)
    have h_pow_pos : 1 ≤ 2 ^ r := Nat.one_le_pow _ _ (by omega)
    nlinarith
```

(Tactic shape; if `nlinarith` does not close the residual
multiplicative goal, the implementer will fall back to a
manual `Nat.mul_le_mul_left` chain after a
`Nat.add_le_add_right` step.)

### §5.3 No `PolyBound.ofA_two_iter`

Per §1.2: `tower r x` for `r ≥ 1` is not polynomially
bounded in `x`, and `ERMor1.PolyBound` is the bprod-free
polynomial fragment per `LawvereERPolynomialBound.lean`'s
structural-towerHeight section.  Step 3 ships nothing for
`A_two_iter` beyond the named composite and its
`interp_A_two_iter` simp lemma.  Downstream consumers
reason about `A_two_iter`'s growth via `interp_A_two_iter`
combined with `Utilities/Tower.lean`'s monotonicity lemmas
(`tower_mono_right`, `tower_mono_left`, `self_le_tower`,
`mul_tower_le_tower_add_two`,
`tower_pow_le_tower_add_three`).

The module docstring includes a paragraph explaining the
absence of `ofA_two_iter` so that downstream readers
encountering the module surface do not search for it.

## §6 Tests

### §6.1 `GebLeanTests/Utilities/ERAMajorants.lean`

ER-side `#guard`s at the safe end of the kernel-reduction
discipline (per discipline-3 from the kickoff prompt:
ER-side `.interp` `#guard`s are practical only for
bprod-free composites at small inputs).

```lean
import GebLean.Utilities.ERAMajorants

namespace GebLean

-- A_one: 7-generator-deep, no bprod / no boundedRec.
#guard ERMor1.A_one.interp ![0] = 2
#guard ERMor1.A_one.interp ![3] = 8
#guard ERMor1.A_one.interp ![5] = 12

-- A_one_iter at small r: still bprod-free.
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

end GebLean
```

If any `A_one_iter r=2` `#guard` proves slow, drop it; the
closed-form `interp_A_one_iter` simp lemma already proves
correctness for all `r`.

### §6.2 No separate Nat-side tests

`A_one_iter`'s closed form `2^r * x + (2^{r+1} − 2)`
reduces to a pure `Nat` expression once
`interp_A_one_iter` fires.  Anything we'd `#guard` on the
`Nat` side is `decide`-trivial (e.g.
`#guard 2 ^ 2 * 3 + (2 ^ 3 - 2) = 18`); we do not add
such tests because they exercise nothing beyond
`Nat`-arithmetic.

`tower r x` (which is `A_two_iter`'s interp) is exercised
by `Utilities/Tower.lean`'s existing test surface (if any);
step 3 does not extend it.

### §6.3 Re-exports

Both done at skeleton-creation time:

- `GebLean.lean`: `import GebLean.Utilities.ERAMajorants`
  near the other Utilities imports.
- `GebLeanTests.lean`: `import GebLeanTests.Utilities.ERAMajorants`
  near the other test imports.

## §7 Citations

Per CLAUDE.md transcription discipline.  Each public
`def`/`theorem` carries the literature reference in its
docstring.

Master-design reference for all entities below: §3.3.
Literature reference for all entities below:
Tourlakis 2018 page 22 (proof of §0.1.0.44 ⊆ direction).

- **Module docstring** — majorant family for K^sim level 2.
- **`A_one`** — `A_1 = λx. 2x + 2`.
- **`A_one_iter`** — `A_1^r`, r-fold composition of `A_1`.
- **`A_two_iter`** — `A_2^r = tower r`.  Underlying
  `towerER` additionally cites Tourlakis 2018
  §0.1.0.17 (c) (`λx. 2^x ∈ ER`).
- **`interp_A_one`**, **`interp_A_one_iter`**,
  **`interp_A_two_iter`** — same citations as the
  corresponding named composite.  `interp_A_one_iter`'s
  closed form `2^r · x + (2^{r+1} − 2)` matches master
  design §3.3.
- **`PolyBound.ofA_one`**, **`PolyBound.ofA_one_iter`** —
  master design §3.3 amended polynomial-bound
  certification subsection.

The transcription discipline's "research document
cross-reference network" pointer is to
`docs/research/2026-04-30-ksim-polynomial-bound-references.md`
(for the polynomial-bound infrastructure context) and
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`
§3.3 (for the per-entity master-design source).

## §8 Out of scope (step 4 owes)

The following are NOT part of step 3 and will be owned by
step 4 (`LawvereKSimMajorization.lean`):

1. **`linearBound_le_A_one_iter`** translation lemma:
   `∀ x. c * x + d ≤ (A_one_iter r).interp ![x]` with
   explicit `r := max ⌈log_2 (c + 1)⌉ ⌈log_2 (d + 2)⌉`.
   Master design §3.4 lines 838-869.  Consumes
   step 3's `interp_A_one_iter` closed form on the right.

2. **Cross-family translation lemmas** relating `A_1^k` to
   `A_2^?`, used in the level-2 case of
   `KMor1.majorize_by_A_two_iter`.  Exact statement
   determined by step 4's level-2 prose proof in master
   design §3.4 lines 894-958 (the "iteration arithmetic"
   closed-form bound on `M_n`).  Consumes both
   `interp_A_one_iter` and `interp_A_two_iter`.

3. **`KMor1.majorize_r f h`**: explicit Lean-`Nat` `r` as a
   function of `f`'s K^sim term structure.  Master design
   §3.4 lines 871-892.

4. **`KMor1.majorize_by_A_one_iter`**: `f.interp v
   ≤ (A_one_iter r).interp ![vMax v]` for `f.level ≤ 1`,
   with explicit `r`.  Master design §3.4 line 887-889.

5. **`KMor1.majorize_by_A_two_iter`**: `f.interp v
   ≤ (A_two_iter r).interp ![vMax v]` for `f.level ≤ 2`,
   with explicit `r`.  Master design §3.4 lines 881-885.

6. **All level-2 iteration arithmetic** (the
   `M_n ≤ A_1^{r_H + n · r_G}(...)` closed-form bound and
   its inductive proof on `n`).  Master design §3.4 lines
   940-958.

7. **The Nat hypothesis fed to
   `simultaneousBoundedRec_interp_correct`'s dominance
   slot** at step 5's level-2 simrec case.  This is the
   downstream consumer of items 5 and 6 above.

8. **Module file**: `GebLean/LawvereKSimMajorization.lean`,
   distinct from step 3's `Utilities/ERAMajorants.lean`.

`tower r x` monotonicity lemmas (already in
`Utilities/Tower.lean`) are consumed as-is by step 4; step
3 does not extend `Utilities/Tower.lean`.

## §9 Risks and mitigations

### §9.1 `Nat`-subtraction in `interp_A_one_iter`'s closed form

The constant `2 ^ (r + 1) − 2` uses `Nat`-subtraction.
This is well-defined for all `r ≥ 0` because
`2 ^ (r + 1) ≥ 2`, but `omega` will demand a manual
`have h : 2 ^ (r + 1) ≥ 2 := ...` before closing the
inductive step.  Mitigation: include the lemma explicitly
in the `succ` case of the proof, as shown in §4.2.

### §9.2 `nlinarith` failure on `ofA_one_iter`'s bounds proof

The PolyBound's `bounds` goal is
`2^r * x + (2^{r+1} - 2) ≤ 2^r * (sup + 1) + (2^{r+1} - 2)`
which reduces to `2^r * x ≤ 2^r * (sup + 1)`, i.e.
`x ≤ sup + 1`.  `nlinarith` should handle this, but if it
times out, the implementer will fall back to a manual
`Nat.mul_le_mul_left h_pow_pos` chain.  Mitigation:
explicit fallback path in §5.2.

### §9.3 ER-side `#guard` cost for `A_one_iter r=2`

`A_one_iter 2` is `comp A_one (comp A_one (proj 0))` —
roughly 21 generators deep.  Kernel reduction at `ctx ![3]`
should terminate quickly (no bprod), but if it slows the
build, drop those `#guard`s; the closed-form simp lemma
covers correctness.  Mitigation: `#guard`s are cheap to
remove; closed form is canonical proof.

### §9.4 Master-design line-number drift

The §3.3 amended text and master-design line numbers cited
here may shift when later cycles edit the master design.
Mitigation: section-number references (e.g. "§3.3 amended
polynomial-bound certification subsection") are robust to
line-number drift; line numbers are best-effort
convenience.

### §9.5 Recursion direction choice for `A_one_iter`

Two equivalent definitions: `A_1 ∘ A_1^r` (chosen) vs
`A_1^r ∘ A_1`.  The chosen direction makes the `succ` case
of `interp_A_one_iter` reduce to `A_one.interp [previous]
= 2 * previous + 2`, which is the cleanest form for
`omega` after substituting the IH.  If the implementer
prefers the other direction, the closed-form proof
restructures slightly (the IH is used inside `A_one`'s
argument rather than around it); both are valid.
Mitigation: choice documented in §3.2; flexibility allowed
by §1.3.

### §9.6 No `PolyBound` for `A_two_iter` triggers downstream confusion

Step 4 readers expecting a uniform `PolyBound`-shaped
interface across `A_n` may search for `ofA_two_iter` and
not find it.  Mitigation: §5.3 documents the absence
explicitly, and the module docstring leads with a
paragraph explaining the polynomial-vs-tower split.

## §10 Acceptance criteria

A clean build (`lake build` and `lake test`) with no
warnings, no `sorry`, no `admit`, after which:

1. `GebLean/Utilities/ERAMajorants.lean` exists with:
   - `ERMor1.A_one : ERMor1 1` named composite.
   - `ERMor1.A_one_iter : ℕ → ERMor1 1` named composite.
   - `ERMor1.A_two_iter : ℕ → ERMor1 1` named composite
     (alias of `towerER`).
   - `@[simp] theorem interp_A_one`, `interp_A_one_iter`,
     `interp_A_two_iter` with closed forms per §4.
   - `def PolyBound.ofA_one : PolyBound A_one`.
   - `def PolyBound.ofA_one_iter (r) : PolyBound
     (A_one_iter r)`.
   - Module docstring citing Tourlakis 2018 page 22 and
     master design §3.3, with the polynomial-vs-tower split
     paragraph.
   - Per-entity docstrings carrying the citations from §7.
2. `GebLeanTests/Utilities/ERAMajorants.lean` exists with
   the `#guard`s from §6.1.
3. `GebLean.lean` imports `GebLean.Utilities.ERAMajorants`.
4. `GebLeanTests.lean` imports
   `GebLeanTests.Utilities.ERAMajorants`.
5. No regressions in existing test surface.
6. `markdownlint-cli2` clean on the spec, plan, and any
   docs touched.
