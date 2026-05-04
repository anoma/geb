# Step 1 — Foundational ER-side tupling — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Land the foundational fixed-length k-tuple Szudzik
pairing infrastructure on the ER side: `Nat.tuplePack`,
`Nat.tupleAt`, polynomial-bound theorem, ER-side named
composites, PolyBound builders, ERMorN-quotient round-trip
lemmas, and (gated) decorative `LawvereERCat.tupleIso`.

**Architecture:** Two new modules under
`GebLean/Utilities/`: `Tupling.lean` (Nat-level, depending
only on `Mathlib.Data.Nat.Pairing` and
`Mathlib.Data.Fin.Tuple.Basic`) and `ERTupling.lean` (ER
layer, depending on `Tupling`, `ERArith`, and
`LawvereERPolynomialBound`). Definitions follow Tourlakis
2018 §0.1.0.34, p. 14's left-fold k-tuple coding scheme
`[[z_1,…,z_k]]^{(k)}` with Szudzik pairing replacing
Cantor's J. Indexing convention: parameter `k : ℕ` indexes
a `(k+1)`-tuple via `Fin (k+1)`.

**Tech Stack:** Lean 4 + mathlib4. Build via `lake build`,
test via `lake test`. Existing infrastructure consumed:
`Nat.pair`, `Nat.unpair`, `Nat.pair_le_sq`, `ERMor1.proj`,
`ERMor1.natPair`, `ERMor1.natUnpairFst`,
`ERMor1.natUnpairSnd`, `ERMor1.comp`, `ERMor1.PolyBound`,
`erMorNSetoid`, `ERMorN`, `ERMorN.comp`, `ERMorN.id`,
`LawvereERCat`.

**Spec:**
`docs/superpowers/specs/2026-05-02-step-1-er-tupling-design.md`
(v3 after three rounds of adversarial review). The spec is
the source of truth for all literature citations and
docstring text; this plan transcribes implementation steps.

**Master design:**
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`
§3.1 (entities), §3.2 (downstream consumer), §3.7 (module
layout), §15.12 (punch-list claim).

---

## File structure

**Created:**

- `GebLean/Utilities/Tupling.lean` — Nat-level definitions,
  bijection theorems, polynomial bound. Imports
  `Mathlib.Data.Nat.Pairing` and
  `Mathlib.Data.Fin.Tuple.Basic`.
- `GebLean/Utilities/ERTupling.lean` — ER-side named
  composites, interp lemmas, PolyBound builders,
  `ERMorN.lift` / `ERMorN.ofVec` helpers, ERMorN-quotient
  round-trip lemmas, optional `LawvereERCat.tupleIso`.
  Imports `GebLean.Utilities.Tupling`,
  `GebLean.Utilities.ERArith`,
  `GebLean.LawvereERPolynomialBound`,
  `GebLean.LawvereERQuot`.
- `GebLeanTests/Tupling.lean` — Nat-side smoke tests +
  boundary `example` lemmas.
- `GebLeanTests/ERTupling.lean` — ER-side smoke tests +
  boundary `example` lemmas.

**Modified:**

- `GebLean.lean` — add public exports of
  `GebLean.Utilities.Tupling` and
  `GebLean.Utilities.ERTupling`.
- `GebLeanTests.lean` — add imports of
  `GebLeanTests.Tupling` and `GebLeanTests.ERTupling`.

---

## Style and discipline reminders

Each task's code must follow CLAUDE.md:

- Lines ≤ 80 characters.
- Spaces around binary operators in source: write
  `Fin (k + 1)` not `Fin (k+1)`, especially in binder
  positions (the project's mathlibStandardSet linter
  enforces this).
- Every implemented function/definition/theorem carries a
  literature reference in its docstring (Tourlakis 2018
  §0.1.0.34, p. 14, or master design §3.1).
- Use `simp only [...]` not bare `simp [...]` — the
  project's flexible-tactic linter rejects `simp [...]`
  modifying `⊢` (per `linter.flexible`). Use `simp` alone
  only when no rewrite list is needed.
- Use `change` not `show` when the goal text differs from
  what Lean has after reduction (`linter.style.show`).
- No `sorry`, no `admit`, no warnings (the lakefile sets
  `warningAsError = true`).
- No banned words from CLAUDE.md's list.
- `markdownlint-cli2` clean on any new docs.

### Import-at-skeleton-creation rule

**Add the import to `GebLean.lean` (and the test
counterpart to `GebLeanTests.lean`) the moment you create
the skeleton file**, before adding any code. Reason: this
guarantees `lake build` always re-elaborates the new file
on every subsequent task, so the lakefile's
`warningAsError = true` catches every linter error in real
time. Otherwise `lake build` may incrementally cache the
new file as `.olean` after the first task and never
re-lint it on later tasks, masking errors until a
later cleanup pass forces a re-elaboration.

### Verifying a clean build

To force re-elaboration of a single module without the
incremental cache short-circuiting:

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/<Module>.olean
lake build GebLean.Utilities.<Module>
```

After each task, before committing, run this command for
the module touched in the task. The implementer must
inspect the full output for `error:` lines and not stop
at "Build completed successfully (N jobs)" — that line is
unreliable when the module is already cached.

### Test discipline for ER-side `.interp` (Gödel numbering)

ER's named composites for primitive operations (`natPair`,
`natUnpairFst`, `natUnpairSnd`, `tuplePack`, `tupleAt`) are
witnesses that the operations are elementary recursive.
They are built from atomic ER constructors via composition,
`boundedRec`, `boundedSearch`, etc. When kernel-reduced via
`#guard` / `decide`:

- `natPair x y` evaluates `(x+y)*(x+y) + x` (or Szudzik's
  branch) via `mulN` → `boundedRec` over `addN`, which
  itself unfolds into iterated reductions.
- `natUnpairFst n` runs `boundedSearch` (bounded
  μ-operator) up to `n`, checking each candidate by
  re-reducing `natPair`.
- `tuplePack k v` for `k ≥ 1` triggers nested `natPair`
  calls.
- `tupleAt k i n` for `k ≥ 1` triggers nested `natUnpair*`
  calls.

The cumulative kernel-reduction cost is impractical even
for tiny inputs: `(ERMor1.tuplePack 1).interp ![3, 5]`
already exceeds reasonable build time. Therefore, in test
files:

- **Do not** write `#guard (ERMor1.<X>).interp <ctx> = <value>`
  for `X` involving `tuplePack k` / `tupleAt k` /
  `natPair` / `natUnpair*` / `boundedRec` / `boundedSearch`
  / `expER` / `towerER` etc., except at trivial arity
  (`k = 0`, where `tuplePack 0 = proj 0` and no `natPair`
  is invoked).
- **Do** rely on the proven universal `@[simp]` interp
  lemmas (`interp_tuplePack`, `interp_tupleAt`) for
  higher-arity correctness — they cover all inputs by
  induction.
- If a concrete higher-arity `example` is wanted for
  documentation, use `:= by simp [interp_*]` to rewrite
  the goal to the Nat level first; but be aware that
  `simp` may not fully reduce `Fin.lastCases` on
  literal `Fin (k+1)` indices and may leave residual
  goals like `Nat.tupleAt 1 (Nat.pair 3 5) 0 = 3` that
  themselves require manual `Fin.cases` dispatch. In
  practice, dropping such examples is cleaner — the
  universal proof subsumes them.

---

## Task 1 — `Nat.tuplePack`, `Nat.tupleAt`, `Nat.tuplePackCoef`

**Files:**

- Create: `GebLean/Utilities/Tupling.lean`

- [ ] **Step 1.1: Create the module skeleton**

```lean
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Fixed-length k-tuple Szudzik pairing

Foundational tupling infrastructure for the ER ↔ K^sim_2
categorical equivalence.  Realizes Tourlakis 2018
§0.1.0.34, p. 14's k-tuple coding scheme
`[[z_1,…,z_k]]^{(k)}` with Szudzik pairing
(`Nat.pair x y = if x < y then y² + x else x² + x + y`)
replacing Cantor's `J = (x+y)² + x`.  Both are bijections
`ℕ × ℕ → ℕ` polynomially bounded by `(x+y+1)²`.

The parameter `k : ℕ` of `tuplePack` and `tupleAt` indexes
a tuple of length `k + 1`; using `Fin (k+1)` makes the
empty tuple unrepresentable, since the bijection
`(Fin (k+1) → ℕ) ↔ ℕ` is only meaningful for non-empty
products.

See `docs/superpowers/specs/2026-05-02-step-1-er-tupling-design.md`
and master design §3.1 in
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`.
-/

namespace Nat

end Nat
```

- [ ] **Step 1.2: Verify mathlib lemma names**

Before writing the recursive-case lemmas, verify the exact
mathlib names. Add these `#check`s temporarily at the bottom
of the file:

```lean
#check @Fin.lastCases_last
#check @Fin.lastCases_castSucc
#check @Fin.init
```

Run: `lake build`

If a `#check` fails, the lemma name has drifted in the
pinned mathlib commit. Update Tasks 2, 3, 5, 6 accordingly
(replace the `simp` lemma references) before proceeding.

After verification, delete the `#check`s.

- [ ] **Step 1.3: Define `Nat.tuplePack`**

Inside `namespace Nat`:

```lean
/-- Pack a `(k+1)`-tuple of naturals into a single natural
via iterated left-associated Szudzik pairing.  Realizes
Tourlakis 2018 §0.1.0.34, p. 14's `[[z_1,…,z_{k+1}]]^{(k+1)}`
(with Szudzik replacing Cantor's J).  See master design
§3.1. -/
def tuplePack : (k : ℕ) → (Fin (k+1) → ℕ) → ℕ
  | 0,     v => v 0
  | k + 1, v =>
      Nat.pair (tuplePack k (Fin.init v))
        (v (Fin.last (k+1)))
```

- [ ] **Step 1.4: Define `Nat.tupleAt`**

```lean
/-- Extract the `i`-th component from a packed
`(k+1)`-tuple.  Inverse of `tuplePack`.  Realizes Tourlakis
2018 §0.1.0.34, p. 14's `Π^{k+1}_i` projections (with
index orientation matched to the left-fold recurrence;
`Nat.unpair.fst` plays the role of Tourlakis's K and
`Nat.unpair.snd` plays L).  See master design §3.1. -/
def tupleAt : (k : ℕ) → ℕ → Fin (k+1) → ℕ
  | 0,     n, _ => n
  | k + 1, n, i =>
      Fin.lastCases (motive := fun _ : Fin (k+2) => ℕ)
        ((Nat.unpair n).2)
        (fun j : Fin (k+1) => tupleAt k (Nat.unpair n).1 j)
        i
```

- [ ] **Step 1.5: Define `Nat.tuplePackCoef`**

```lean
/-- Closed-form coefficient witnessing the polynomial
bound `tuplePack k v ≤ tuplePackCoef k * (M+1)^(2^k)`,
where `M = sup v` over `Fin (k+1)`.  Recurrence derived
from `Nat.pair_le_sq` per master design §3.1. -/
def tuplePackCoef : ℕ → ℕ
  | 0     => 1
  | k + 1 => (tuplePackCoef k + 2)^2
```

- [ ] **Step 1.6: Build and commit**

Run: `lake build`
Expected: clean build, no warnings.

Run: `lake test`
Expected: all tests pass.

```bash
git add GebLean/Utilities/Tupling.lean
git commit -m "Step 1 task 1: Nat.tuplePack, Nat.tupleAt, Nat.tuplePackCoef

Foundational definitions for the (k+1)-tuple Szudzik pairing
infrastructure.  Realizes Tourlakis 2018 §0.1.0.34, p. 14's
k-tuple coding scheme [[z_1,...,z_k]]^(k) with Szudzik
replacing Cantor's J, and the closed-form coefficient
recurrence per master design §3.1.

Master design §3.1 entity batch 1 of 5 for step 1."
```

---

## Task 2 — `@[simp]` interp lemmas for `tuplePack` and `tupleAt`

**Files:**

- Modify: `GebLean/Utilities/Tupling.lean` (append)

- [ ] **Step 2.1: Add `tuplePack_zero` and `tuplePack_succ`**

Append in `namespace Nat`:

```lean
@[simp] theorem tuplePack_zero (v : Fin 1 → ℕ) :
    tuplePack 0 v = v 0 := rfl

@[simp] theorem tuplePack_succ (k : ℕ)
    (v : Fin (k+2) → ℕ) :
    tuplePack (k+1) v
      = Nat.pair (tuplePack k (Fin.init v))
          (v (Fin.last (k+1))) := rfl
```

- [ ] **Step 2.2: Add `tupleAt_zero`**

```lean
@[simp] theorem tupleAt_zero (n : ℕ) (i : Fin 1) :
    tupleAt 0 n i = n := rfl
```

- [ ] **Step 2.3: Add `tupleAt_succ_last` and
  `tupleAt_succ_castSucc`**

```lean
/-- `tupleAt` reduction at the last index: peels one
`Nat.unpair` step on the right. -/
@[simp] theorem tupleAt_succ_last (k n : ℕ) :
    tupleAt (k+1) n (Fin.last (k+1))
      = (Nat.unpair n).2 := by
  simp [tupleAt, Fin.lastCases_last]

/-- `tupleAt` reduction at a non-last index: peels one
`Nat.unpair` step on the left and recurses at depth `k`. -/
@[simp] theorem tupleAt_succ_castSucc (k n : ℕ)
    (j : Fin (k+1)) :
    tupleAt (k+1) n j.castSucc
      = tupleAt k (Nat.unpair n).1 j := by
  simp [tupleAt, Fin.lastCases_castSucc]
```

- [ ] **Step 2.4: Build and commit**

Run: `lake build`
Expected: clean build.

```bash
git add GebLean/Utilities/Tupling.lean
git commit -m "Step 1 task 2: @[simp] interp lemmas for Nat.tuplePack/tupleAt

Five simp lemmas: tuplePack_zero, tuplePack_succ, tupleAt_zero,
tupleAt_succ_last, tupleAt_succ_castSucc.  These reduce
downstream bijection-theorem proofs to clean
'induction k; · rfl; · simp [Nat.unpair_pair, ...]' shape
rather than manual Fin.lastCases dispatch.

Master design §3.1 entity batch 2 of 5 for step 1."
```

---

## Task 3 — `Nat.tupleAt_le`

**Files:**

- Modify: `GebLean/Utilities/Tupling.lean` (append)

- [ ] **Step 3.1: Add `tupleAt_le`**

```lean
/-- Every component extracted from a packed natural is
bounded by the packed natural itself.  Mirrors existing
`Nat.seqAt_le` in `Utilities/SzudzikSeq.lean`; underlying
mathlib lemmas: `Nat.unpair_left_le`,
`Nat.unpair_right_le`. -/
theorem tupleAt_le : ∀ (k n : ℕ) (i : Fin (k+1)),
    tupleAt k n i ≤ n
  | 0,     n, _ => by
      simp [tupleAt]
  | k + 1, n, i => by
      refine Fin.lastCases ?_ ?_ i
      · -- last branch
        simp [tupleAt, Fin.lastCases_last]
        exact Nat.unpair_right_le n
      · -- castSucc branch
        intro j
        simp [tupleAt, Fin.lastCases_castSucc]
        exact le_trans (tupleAt_le k (Nat.unpair n).1 j)
          (Nat.unpair_left_le n)
```

If the proof structure resists (e.g. `Fin.lastCases`
inside a `refine` is awkward), fall back to:

```lean
theorem tupleAt_le : ∀ (k n : ℕ) (i : Fin (k+1)),
    tupleAt k n i ≤ n
  | 0,     n, _ => le_refl n
  | k + 1, n, ⟨i, h⟩ => by
      by_cases hi : i = k + 1
      · subst hi
        have hlast : (⟨k+1, h⟩ : Fin (k+2))
            = Fin.last (k+1) := by
          ext; rfl
        rw [hlast]
        simp
        exact Nat.unpair_right_le n
      · have hi' : i < k + 1 := by omega
        have hcast :
            (⟨i, h⟩ : Fin (k+2))
              = (⟨i, hi'⟩ : Fin (k+1)).castSucc := by
          ext; rfl
        rw [hcast]
        simp
        exact le_trans
          (tupleAt_le k (Nat.unpair n).1 ⟨i, hi'⟩)
          (Nat.unpair_left_le n)
```

- [ ] **Step 3.2: Build and commit**

Run: `lake build`
Expected: clean build.

```bash
git add GebLean/Utilities/Tupling.lean
git commit -m "Step 1 task 3: Nat.tupleAt_le

Linear bound: every component extracted from a packed
natural is bounded by the packed natural itself.  Mirrors
existing Nat.seqAt_le in Utilities/SzudzikSeq.lean.

Master design §3.1 entity batch 3 of 5 for step 1."
```

---

## Task 4 — Bijection theorems `tupleAt_tuplePack` and `tuplePack_tupleAt`

**Files:**

- Modify: `GebLean/Utilities/Tupling.lean` (append)

- [ ] **Step 4.1: Add `tupleAt_tuplePack`**

```lean
/-- Round-trip: extracting component `i` from a packed
tuple returns the original component.  Realizes Tourlakis
2018 §0.1.0.34, p. 14's
`Π^k_i [[z_1,…,z_k]]^{(k)} = z_i`. -/
theorem tupleAt_tuplePack :
    ∀ (k : ℕ) (v : Fin (k+1) → ℕ) (i : Fin (k+1)),
      tupleAt k (tuplePack k v) i = v i
  | 0,     v, i => by
      simp [tupleAt_zero]
      exact congrArg v (Subsingleton.elim _ i)
  | k + 1, v, i => by
      refine Fin.lastCases ?_ ?_ i
      · -- last branch: i = Fin.last (k+1)
        simp [tuplePack_succ, tupleAt_succ_last,
              Nat.unpair_pair]
      · -- castSucc branch: i = j.castSucc, j : Fin (k+1)
        intro j
        simp [tuplePack_succ, tupleAt_succ_castSucc,
              Nat.unpair_pair]
        exact tupleAt_tuplePack k (Fin.init v) j
```

- [ ] **Step 4.2: Add `tuplePack_tupleAt`**

```lean
/-- Round-trip: packing the components extracted from a
packed natural returns the original natural. -/
theorem tuplePack_tupleAt :
    ∀ (k n : ℕ),
      tuplePack k (tupleAt k n) = n
  | 0,     n => by
      simp [tuplePack_zero, tupleAt_zero]
  | k + 1, n => by
      simp [tuplePack_succ, tupleAt_succ_last]
      have h_init :
          Fin.init (tupleAt (k+1) n)
            = tupleAt k (Nat.unpair n).1 := by
        funext j
        show tupleAt (k+1) n j.castSucc
          = tupleAt k (Nat.unpair n).1 j
        exact tupleAt_succ_castSucc k n j
      rw [h_init]
      rw [tuplePack_tupleAt k (Nat.unpair n).1]
      exact Nat.pair_unpair n
```

- [ ] **Step 4.3: Build and commit**

Run: `lake build`
Expected: clean build.

```bash
git add GebLean/Utilities/Tupling.lean
git commit -m "Step 1 task 4: bijection theorems for Nat.tuplePack/tupleAt

tupleAt_tuplePack and tuplePack_tupleAt establish the
(Fin (k+1) → ℕ) ↔ ℕ bijection.  Realizes Tourlakis 2018
§0.1.0.34, p. 14's Π^k_i [[z_1,…,z_k]]^{(k)} = z_i.
Underlying single-step bijection: mathlib's Nat.unpair_pair
and Nat.pair_unpair.

Master design §3.1 entity batch 4 of 5 for step 1."
```

---

## Task 5 — Polynomial bound `Nat.tuplePack_le`

**Files:**

- Modify: `GebLean/Utilities/Tupling.lean` (append)

- [ ] **Step 5.1: Add a small helper for sup over `Fin.init`**

```lean
/-- The sup of `Fin.init v` is at most the sup of `v`. -/
private theorem Finset.sup_init_le_sup
    {k : ℕ} (v : Fin (k+2) → ℕ) :
    (Finset.univ : Finset (Fin (k+1))).sup (Fin.init v)
      ≤ (Finset.univ : Finset (Fin (k+2))).sup v := by
  apply Finset.sup_le
  intro i _
  show v i.castSucc ≤ _
  exact Finset.le_sup (f := v) (Finset.mem_univ _)
```

(If the namespace nesting causes a conflict with mathlib's
`Finset.sup_init_le_sup`, name it
`Nat.tuplePack_sup_init_le_sup` instead.)

- [ ] **Step 5.2: Add `tuplePack_le`**

```lean
/-- Polynomial value bound on `tuplePack`.  At parameter
`k` (packing `(k+1)`-tuples), `tuplePack k v` is bounded
by `tuplePackCoef k * (M + 1)^(2^k)` where `M = sup v` over
`Fin (k+1)`.  Cites Tourlakis 2018 §0.1.0.34, p. 14 (proof
that pairing stays in E²); master design §3.1. -/
theorem tuplePack_le :
    ∀ (k : ℕ) (v : Fin (k+1) → ℕ),
      tuplePack k v ≤
        tuplePackCoef k *
          ((Finset.univ : Finset (Fin (k+1))).sup v + 1)^(2^k)
  | 0, v => by
      simp [tuplePack_zero, tuplePackCoef]
      have hv0 : v 0
          ≤ (Finset.univ : Finset (Fin 1)).sup v :=
        Finset.le_sup (f := v) (Finset.mem_univ 0)
      omega
  | k + 1, v => by
      set M' :=
        (Finset.univ : Finset (Fin (k+2))).sup v
      set Mi :=
        (Finset.univ : Finset (Fin (k+1))).sup
          (Fin.init v)
      have hMi : Mi ≤ M' := Finset.sup_init_le_sup v
      have hlast : v (Fin.last (k+1)) ≤ M' :=
        Finset.le_sup (f := v) (Finset.mem_univ _)
      have ih := tuplePack_le k (Fin.init v)
      have ih' :
          tuplePack k (Fin.init v)
            ≤ tuplePackCoef k * (M' + 1)^(2^k) := by
        apply le_trans ih
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_left
        omega
      have hpair :
          tuplePack (k+1) v
            ≤ (tuplePack k (Fin.init v)
                + v (Fin.last (k+1)) + 1)^2 := by
        rw [tuplePack_succ]
        exact Nat.pair_le_sq _ _
      have hsum :
          tuplePack k (Fin.init v)
              + v (Fin.last (k+1)) + 1
            ≤ (tuplePackCoef k + 2) * (M' + 1)^(2^k) := by
        have hC : 1 ≤ (M' + 1)^(2^k) := by
          apply Nat.one_le_pow
          omega
        have hM'1 :
            v (Fin.last (k+1)) + 1 ≤ M' + 1 := by omega
        have hM'pow :
            (M' + 1) ≤ (M' + 1)^(2^k) := by
          have h2k : 1 ≤ 2^k := Nat.one_le_pow _ _ (by omega)
          calc M' + 1
              = (M' + 1)^1 := by ring
            _ ≤ (M' + 1)^(2^k) :=
                Nat.pow_le_pow_right (by omega) h2k
        calc tuplePack k (Fin.init v)
              + v (Fin.last (k+1)) + 1
            ≤ tuplePackCoef k * (M' + 1)^(2^k)
                + (M' + 1) := by omega
          _ ≤ tuplePackCoef k * (M' + 1)^(2^k)
                + (M' + 1)^(2^k) := by
              have := hM'pow; omega
          _ = (tuplePackCoef k + 1) * (M' + 1)^(2^k) := by
              ring
          _ ≤ (tuplePackCoef k + 2) * (M' + 1)^(2^k) := by
              apply Nat.mul_le_mul_right; omega
      have hsq :
          (tuplePack k (Fin.init v)
              + v (Fin.last (k+1)) + 1)^2
            ≤ ((tuplePackCoef k + 2)
                * (M' + 1)^(2^k))^2 :=
        Nat.pow_le_pow_left hsum 2
      have hexpand :
          ((tuplePackCoef k + 2) * (M' + 1)^(2^k))^2
            = (tuplePackCoef k + 2)^2 * (M' + 1)^(2*2^k) :=
        by
          rw [Nat.mul_pow, ← pow_mul]
      have h2k1 : 2 * 2^k = 2^(k+1) := by
        rw [pow_succ]; ring
      have hcoef :
          tuplePackCoef (k+1) = (tuplePackCoef k + 2)^2 :=
        rfl
      calc tuplePack (k+1) v
          ≤ (tuplePack k (Fin.init v)
              + v (Fin.last (k+1)) + 1)^2 := hpair
        _ ≤ ((tuplePackCoef k + 2) * (M' + 1)^(2^k))^2 :=
            hsq
        _ = (tuplePackCoef k + 2)^2 * (M' + 1)^(2*2^k) :=
            hexpand
        _ = tuplePackCoef (k+1) * (M' + 1)^(2^(k+1)) := by
            rw [h2k1, hcoef]
```

If `Nat.le_self_pow` is the canonical mathlib name for
"`a ≤ a^n` when `n ≥ 1`", you can replace the `hM'pow`
chain with a one-liner. Verify by `#check @Nat.le_self_pow`;
the `calc` chain above does not depend on the name.

- [ ] **Step 5.3: Build and commit**

Run: `lake build`
Expected: clean build.

```bash
git add GebLean/Utilities/Tupling.lean
git commit -m "Step 1 task 5: Nat.tuplePack_le polynomial value bound

tuplePack k v ≤ tuplePackCoef k * (M + 1)^(2^k) where M = sup v
over Fin (k+1).  Multiplicative-coefficient form per master
design §3.1 (corrected formulation in commit 9c806cb8;
the earlier additive form (M + c_k)^(2^k) does not hold as
a literal Lean inequality for any constant c_k once k ≥ 1).

Cites Tourlakis 2018 §0.1.0.34, p. 14 (proof that pairing
stays in E²); underlying quadratic single-step bound is
Nat.pair_le_sq from Utilities/ComputationalComplexity.lean.

Master design §3.1 entity batch 5 of 5 for step 1, Nat-side
complete."
```

---

## Task 6 — Nat-side tests in `GebLeanTests/Tupling.lean`

**Files:**

- Create: `GebLeanTests/Tupling.lean`
- Modify: `GebLeanTests.lean` (add import)

- [ ] **Step 6.1: Create the test module**

```lean
import GebLean.Utilities.Tupling

namespace GebLeanTests.Tupling

-- §6.1 smoke #guards (orientation, identity, round-trip)

#guard Nat.tuplePack 1 ![3, 5] = Nat.pair 3 5
#guard Nat.tupleAt 1 (Nat.pair 3 5) 0 = 3
#guard Nat.tupleAt 1 (Nat.pair 3 5) 1 = 5

#guard Nat.tuplePack 0 ![7] = 7
#guard Nat.tupleAt 0 17 0 = 17

#guard Nat.tupleAt 2 (Nat.tuplePack 2 ![3, 5, 7]) 0 = 3
#guard Nat.tupleAt 2 (Nat.tuplePack 2 ![3, 5, 7]) 1 = 5
#guard Nat.tupleAt 2 (Nat.tuplePack 2 ![3, 5, 7]) 2 = 7

-- §6.2 boundary examples (recurrence + bound corner cases)

example (v : Fin 1 → ℕ) : Nat.tuplePack 0 v ≤ v 0 := by
  simp [Nat.tuplePack]

example : Nat.tuplePackCoef 0 = 1 := rfl

example : Nat.tuplePackCoef 1 = 9 := rfl

example : Nat.tuplePackCoef 2 = 121 := rfl

example :
    Nat.tuplePack 1 ![0, 0]
      ≤ Nat.tuplePackCoef 1 * 1^(2^1) := by
  decide

example :
    Nat.tuplePack 1 ![3, 5]
      ≤ Nat.tuplePackCoef 1 * (5 + 1)^(2^1) := by
  decide

end GebLeanTests.Tupling
```

- [ ] **Step 6.2: Register the test module**

Edit `GebLeanTests.lean` to add the import in alphabetical
order (after `Phase4Investigation` if present, or at an
appropriate location):

```lean
import GebLeanTests.Tupling
```

- [ ] **Step 6.3: Build and test**

Run: `lake build`
Expected: clean build.

Run: `lake test`
Expected: all `#guard`s pass.

- [ ] **Step 6.4: Commit**

```bash
git add GebLeanTests/Tupling.lean GebLeanTests.lean
git commit -m "Step 1 task 6: Nat-side tests for Tupling

Smoke #guards locking encoding orientation, identity case
(k = 0), and small-tuple round-trips.  Boundary example
lemmas verifying the tuplePackCoef recurrence at k = 0, 1, 2
and the bound at corner cases (M = 0, small concrete input).

The k = 1 #guard locks head/tail orientation: prefix-pack
on the LEFT, new last element on the RIGHT, matching
Tourlakis's left-fold scheme.

Master design §3.1 spec §6.1 + §6.2 transcribed."
```

---

## Task 7 — `ERMor1.tuplePack` and `ERMor1.tupleAt`

**Files:**

- Create: `GebLean/Utilities/ERTupling.lean`

- [ ] **Step 7.1: Create the module skeleton**

```lean
import GebLean.Utilities.Tupling
import GebLean.Utilities.ERArith
import GebLean.LawvereERPolynomialBound
import GebLean.LawvereERQuot

/-!
# ER-side fixed-length k-tuple Szudzik pairing

ER-level named composites mirroring `Nat.tuplePack` and
`Nat.tupleAt` in `Utilities/Tupling.lean`.  Bottom-up
construction from existing atomic ER generators (`proj`,
`natPair`, `natUnpairFst`, `natUnpairSnd`, `comp`) per
CLAUDE.md "bottom-up named-composite discipline".

See master design §3.1 (Lean entities, ER layer) and
the spec at
`docs/superpowers/specs/2026-05-02-step-1-er-tupling-design.md`.
-/

namespace GebLean
namespace ERMor1

end ERMor1
end GebLean
```

- [ ] **Step 7.1.1: Register the import in `GebLean.lean` immediately**

Per the import-at-skeleton-creation rule (top of this
plan), open `GebLean.lean` and add the import
alphabetically next to `import GebLean.Utilities.Tupling`:

```lean
import GebLean.Utilities.ERTupling
```

Run:

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERTupling.olean
lake build GebLean.Utilities.ERTupling
```

Expected: clean build of the empty skeleton (the module has
no definitions yet, so this just confirms imports resolve).

- [ ] **Step 7.2: Define `ERMor1.tuplePack`**

Inside the namespaces:

```lean
/-- ER named composite for fixed-length `(k+1)`-tuple
Szudzik pack.  Built bottom-up from `proj`, `natPair`,
`comp` per CLAUDE.md "bottom-up named-composite
discipline".  Mirrors `Nat.tuplePack`'s left-fold
recurrence (master design §3.1; Tourlakis 2018 §0.1.0.34,
p. 14). -/
def tuplePack : (k : ℕ) → ERMor1 (k + 1)
  | 0     => ERMor1.proj 0
  | k + 1 =>
      ERMor1.comp ERMor1.natPair
        ![ ERMor1.comp (tuplePack k)
             (fun i : Fin (k + 1) =>
               ERMor1.proj i.castSucc)
         , ERMor1.proj (Fin.last (k + 1)) ]
```

- [ ] **Step 7.3: Define `ERMor1.tupleAt`**

```lean
/-- ER named composite extracting component `i` from a
packed `(k+1)`-tuple.  Built bottom-up from `proj`,
`natUnpairFst`, `natUnpairSnd`, `comp`.  Mirrors
`Nat.tupleAt`'s left-fold recurrence (master design §3.1). -/
def tupleAt : (k : ℕ) → Fin (k + 1) → ERMor1 1
  | 0,     _ => ERMor1.proj 0
  | k + 1, i =>
      Fin.lastCases (motive := fun _ : Fin (k+2) => ERMor1 1)
        ERMor1.natUnpairSnd
        (fun j : Fin (k+1) =>
          ERMor1.comp (tupleAt k j) ![ERMor1.natUnpairFst])
        i
```

- [ ] **Step 7.4: Build and commit**

Run: `lake build`
Expected: clean build (no `interp` lemmas yet — types
only).

```bash
git add GebLean/Utilities/ERTupling.lean
git commit -m "Step 1 task 7: ERMor1.tuplePack and ERMor1.tupleAt

ER named composites mirroring Nat.tuplePack and Nat.tupleAt.
Built bottom-up from proj, natPair, natUnpairFst,
natUnpairSnd, comp per CLAUDE.md 'bottom-up named-composite
discipline'.  Master design §3.1 entity batch 1 of 5 for
ER side."
```

---

## Task 8 — `@[simp]` interp lemmas for ER-side composites

**Files:**

- Modify: `GebLean/Utilities/ERTupling.lean` (append)

- [ ] **Step 8.1: Add `interp_tuplePack`**

```lean
@[simp] theorem interp_tuplePack :
    ∀ (k : ℕ) (v : Fin (k+1) → ℕ),
      (tuplePack k).interp v = Nat.tuplePack k v
  | 0, v => by
      simp [tuplePack, Nat.tuplePack]
  | k + 1, v => by
      simp only [tuplePack, ERMor1.interp_comp,
        ERMor1.interp_natPair, ERMor1.interp_proj]
      have ih := interp_tuplePack k
        (fun i : Fin (k+1) => v i.castSucc)
      simp only [ERMor1.interp_comp,
        ERMor1.interp_proj] at ih ⊢
      -- The IH gives interp on the shifted vector;
      -- match it against `Fin.init v`.
      have hshift :
          (fun i : Fin (k+1) => v i.castSucc)
            = Fin.init v := by
        funext i
        rfl
      rw [hshift] at ih
      simp only [Nat.tuplePack_succ]
      rw [← ih]
      rfl
```

If `simp` doesn't close the recursive case, fall back to a
`rfl`-style proof that walks the `comp` / `natPair`
unfoldings step-by-step. The goal at the recursive case
reduces to:

```text
Nat.pair (tuplePack k).interp (v ∘ Fin.castSucc)
         (v (Fin.last (k+1)))
  = Nat.pair (Nat.tuplePack k (Fin.init v))
             (v (Fin.last (k+1)))
```

which closes by `rw [interp_tuplePack k]` and the `Fin.init`
identity.

- [ ] **Step 8.2: Add `interp_tupleAt`**

```lean
@[simp] theorem interp_tupleAt :
    ∀ (k : ℕ) (i : Fin (k+1)) (n : ℕ),
      (tupleAt k i).interp ![n] = Nat.tupleAt k n i
  | 0, _, n => by
      simp [tupleAt, Nat.tupleAt]
  | k + 1, i, n => by
      refine Fin.lastCases ?_ ?_ i
      · -- last branch
        simp [tupleAt, Nat.tupleAt,
          Fin.lastCases_last]
      · -- castSucc branch
        intro j
        simp only [tupleAt, Fin.lastCases_castSucc,
          ERMor1.interp_comp, ERMor1.interp_natUnpairFst]
        rw [interp_tupleAt k j]
        simp [Nat.tupleAt, Fin.lastCases_castSucc]
```

- [ ] **Step 8.3: Build and commit**

Run: `lake build`
Expected: clean build.

```bash
git add GebLean/Utilities/ERTupling.lean
git commit -m "Step 1 task 8: @[simp] interp lemmas for ER-side composites

interp_tuplePack and interp_tupleAt align ERMor1.tuplePack
and ERMor1.tupleAt with their Nat-level Nat.tuplePack /
Nat.tupleAt reductions.  Master design §3.1 entity batch
2 of 5 for ER side."
```

---

## Task 9 — `PolyBound` builders `ofTuplePack` and `ofTupleAt`

**Files:**

- Modify: `GebLean/Utilities/ERTupling.lean` (append)

- [ ] **Step 9.1: Add `ofTuplePack`**

```lean
namespace PolyBound

/-- PolyBound builder for `tuplePack k`.  Cites master
design §3.1: `tuplePack k v ≤ tuplePackCoef k * (M+1)^(2^k)`. -/
def ofTuplePack (k : ℕ) :
    PolyBound (tuplePack k) where
  degree      := 2^k
  coefficient := Nat.tuplePackCoef k
  constant    := 0
  bounds      := fun ctx => by
    rw [interp_tuplePack]
    simpa using Nat.tuplePack_le k ctx
```

- [ ] **Step 9.2: Add `ofTupleAt`**

```lean
/-- PolyBound builder for `tupleAt k i`.  Linear bound
from `Nat.tupleAt_le` (single-arity context); master
design §3.1. -/
def ofTupleAt (k : ℕ) (i : Fin (k+1)) :
    PolyBound (tupleAt k i) where
  degree      := 1
  coefficient := 1
  constant    := 0
  bounds      := fun ctx => by
    rw [interp_tupleAt]
    have h := Nat.tupleAt_le k (ctx 0) i
    have hsup :
        ctx 0 ≤ (Finset.univ : Finset (Fin 1)).sup ctx :=
      Finset.le_sup (f := ctx) (Finset.mem_univ 0)
    omega

end PolyBound
```

- [ ] **Step 9.3: Build and commit**

Run: `lake build`
Expected: clean build.

```bash
git add GebLean/Utilities/ERTupling.lean
git commit -m "Step 1 task 9: PolyBound.ofTuplePack and .ofTupleAt

PolyBound builders certifying the polynomial value bounds.
ofTuplePack: degree = 2^k, coefficient = Nat.tuplePackCoef k,
constant = 0.  ofTupleAt: linear (degree 1, coefficient 1,
constant 0), built from Nat.tupleAt_le.

Master design §3.1 entity batch 3 of 5 for ER side; §15.12
punch-list claim now satisfied."
```

---

## Task 10 — `ERMorN.lift`, `ERMorN.ofVec` helpers

**Files:**

- Modify: `GebLean/Utilities/ERTupling.lean` (append, before
  the round-trip lemmas in Task 11)

- [ ] **Step 10.1: Switch namespaces and add helpers**

After the closing `end ERMor1`, add:

```lean
namespace ERMorN

/-- One-element vector view of a single-output ER term.
`ERMorN.lift f i = f` for the unique `i : Fin 1`.
Auxiliary helper supporting the `ERMorN`-quotient
round-trip lemmas named in master design §3.1; bridges
single-output `ERMor1.tuplePack` to the multi-output
`ERMorN` interface on which the round-trip equation is
stated. -/
def lift {n : ℕ} (f : ERMor1 n) : ERMorN n 1 :=
  fun _ => f

/-- Named identity coercion from a vector of single-output
ER terms to the multi-output `ERMorN`.  Definitionally
`g`, since `ERMorN n m := Fin m → ERMor1 n`.  Auxiliary
helper supporting the round-trip lemmas named in master
design §3.1; gives the `Fin (k+1) → ERMor1 1` family of
`tupleAt` projections a stable `ERMorN 1 (k+1)` interface
for the quotient-level lemma signatures. -/
def ofVec {n m : ℕ} (g : Fin m → ERMor1 n) :
    ERMorN n m := g

@[simp] theorem lift_apply {n : ℕ} (f : ERMor1 n)
    (i : Fin 1) :
    ERMorN.lift f i = f := rfl

@[simp] theorem ofVec_apply {n m : ℕ}
    (g : Fin m → ERMor1 n) (i : Fin m) :
    ERMorN.ofVec g i = g i := rfl

end ERMorN
```

- [ ] **Step 10.2: Build and commit**

Run: `lake build`
Expected: clean build.

```bash
git add GebLean/Utilities/ERTupling.lean
git commit -m "Step 1 task 10: ERMorN.lift and ERMorN.ofVec helpers

Auxiliary named composites supporting the ERMorN-quotient
round-trip lemmas: lift wraps a single-output ERMor1 term
into ERMorN n 1, ofVec is a named identity coercion from
Fin m → ERMor1 n to ERMorN n m.  Both have rfl @[simp]
apply lemmas.

Master design §3.1 entity batch 4 of 5 for ER side."
```

---

## Task 11 — ERMorN-quotient round-trip lemmas

**Files:**

- Modify: `GebLean/Utilities/ERTupling.lean` (append)

- [ ] **Step 11.1: Re-enter `ERMorN` namespace and add the
  first round-trip lemma**

```lean
namespace ERMorN

/-- Round-trip at the ERMorN-quotient level: first packing,
then component-wise unpacking, is extensionally equal to
the identity at arity `(k+1)`.  Restates
`Nat.tupleAt_tuplePack` at the morphism-quotient level.
Master design §3.1. -/
theorem tupleAt_tuplePack (k : ℕ) :
    (erMorNSetoid (k+1) (k+1)).r
      (ERMorN.comp
        (ERMorN.lift (ERMor1.tuplePack k))
        (ERMorN.ofVec
           (fun i : Fin (k+1) => ERMor1.tupleAt k i)))
      (ERMorN.id (k+1)) := by
  intro ctx
  funext i
  -- LHS: (comp (lift tuplePack) (ofVec tupleAt)).interp ctx i
  --    = (ofVec tupleAt i).interp ((lift tuplePack).interp ctx)
  --    = (tupleAt k i).interp ![Nat.tuplePack k ctx]
  --    = Nat.tupleAt k (Nat.tuplePack k ctx) i
  --    = ctx i  (by Nat.tupleAt_tuplePack)
  -- RHS: (ERMorN.id (k+1)).interp ctx i = ctx i
  simp only [ERMorN.interp_comp, ERMorN.interp_id,
    ERMorN.lift, ERMorN.ofVec, ERMorN.interp,
    ERMor1.interp_tupleAt]
  -- Reduce the inner application to a single-component vector.
  have h_inner :
      (fun _ : Fin 1 => Nat.tuplePack k ctx) 0
        = Nat.tuplePack k ctx := rfl
  -- Final step: bijection
  exact Nat.tupleAt_tuplePack k ctx i
```

If the simp chain doesn't close, fall back to expanding by
hand:

```lean
theorem tupleAt_tuplePack (k : ℕ) :
    (erMorNSetoid (k+1) (k+1)).r
      (ERMorN.comp
        (ERMorN.lift (ERMor1.tuplePack k))
        (ERMorN.ofVec
           (fun i : Fin (k+1) => ERMor1.tupleAt k i)))
      (ERMorN.id (k+1)) := by
  intro ctx
  funext i
  show (ERMor1.comp (ERMor1.tupleAt k i)
          (ERMorN.lift (ERMor1.tuplePack k))).interp ctx
    = ctx i
  rw [ERMor1.interp_comp]
  show (ERMor1.tupleAt k i).interp
        (fun j => ((ERMor1.tuplePack k).interp ctx))
    = ctx i
  -- Single-component context: the inner function is constantly
  -- `(ERMor1.tuplePack k).interp ctx`.  But `ERMor1.tupleAt k i`
  -- is a 1-arity ER term, and only `j = 0` is reached.
  have heq :
      (fun _ : Fin 1 => (ERMor1.tuplePack k).interp ctx)
        = ![(ERMor1.tuplePack k).interp ctx] := by
    funext j; fin_cases j; rfl
  rw [heq, ERMor1.interp_tupleAt, ERMor1.interp_tuplePack]
  exact Nat.tupleAt_tuplePack k ctx i
```

- [ ] **Step 11.2: Add the second round-trip lemma**

```lean
/-- Round-trip in the other direction: first component-wise
unpacking, then packing, is extensionally equal to the
identity at arity `1`.  Restates `Nat.tuplePack_tupleAt`. -/
theorem tuplePack_tupleAt (k : ℕ) :
    (erMorNSetoid 1 1).r
      (ERMorN.comp
        (ERMorN.ofVec
           (fun i : Fin (k+1) => ERMor1.tupleAt k i))
        (ERMorN.lift (ERMor1.tuplePack k))) (ERMorN.id 1) := by
  intro ctx
  funext i
  fin_cases i
  -- The single index in `Fin 1` is 0.
  show (ERMor1.comp (ERMor1.tuplePack k)
          (ERMorN.ofVec
            (fun j : Fin (k+1) => ERMor1.tupleAt k j))).interp
              ctx
    = ctx 0
  rw [ERMor1.interp_comp, ERMor1.interp_tuplePack]
  -- Now LHS = Nat.tuplePack k (fun j => (tupleAt k j).interp ctx)
  --        = Nat.tuplePack k (fun j => Nat.tupleAt k (ctx 0) j)
  --        = ctx 0  by Nat.tuplePack_tupleAt
  have hext :
      (fun j : Fin (k+1) =>
        (ERMor1.tupleAt k j).interp ctx)
        = Nat.tupleAt k (ctx 0) := by
    funext j
    rw [ERMor1.interp_tupleAt]
    -- ctx : Fin 1 → ℕ, so ctx = ![ctx 0].
    have hctx :
        ctx = ![ctx 0] := by
      funext j'; fin_cases j'; rfl
    rw [hctx]
  rw [hext]
  exact Nat.tuplePack_tupleAt k (ctx 0)

end ERMorN
```

- [ ] **Step 11.3: Build and commit**

Run: `lake build`
Expected: clean build.

```bash
git add GebLean/Utilities/ERTupling.lean
git commit -m "Step 1 task 11: ERMorN-quotient round-trip lemmas

ERMorN.tupleAt_tuplePack and ERMorN.tuplePack_tupleAt
restate the Nat-level bijection theorems at the
ERMorN-quotient level using the explicit-setoid form
(erMorNSetoid n m).r — matches the codebase convention
since erMorNSetoid is declared as def, not instance.

Master design §3.1 entity batch 5 of 5 for ER side."
```

---

## Task 12 — ER-side tests in `GebLeanTests/ERTupling.lean`

**Files:**

- Create: `GebLeanTests/ERTupling.lean`
- Modify: `GebLeanTests.lean` (add import)

- [ ] **Step 12.1: Create the test module**

```lean
import GebLean.Utilities.ERTupling

namespace GebLeanTests.ERTupling

open GebLean

-- §6.1 ER-side smoke #guards (mirroring Nat side)

#guard (ERMor1.tuplePack 1).interp ![3, 5] = Nat.pair 3 5
#guard (ERMor1.tupleAt 2 1).interp
         ![Nat.tuplePack 2 ![3, 5, 7]] = 5

-- §6.2 ER-side boundary examples (PolyBound shape)

example :
    (ERMor1.PolyBound.ofTuplePack 1).degree = 2 := rfl

example :
    (ERMor1.PolyBound.ofTuplePack 1).coefficient = 9 := rfl

example :
    (ERMor1.PolyBound.ofTuplePack 1).constant = 0 := rfl

end GebLeanTests.ERTupling
```

- [ ] **Step 12.2: Register the test module**

Edit `GebLeanTests.lean` to add the import (alphabetical
order):

```lean
import GebLeanTests.ERTupling
```

- [ ] **Step 12.3: Build and test**

Run: `lake build`
Expected: clean build.

Run: `lake test`
Expected: all `#guard`s pass.

- [ ] **Step 12.4: Commit**

```bash
git add GebLeanTests/ERTupling.lean GebLeanTests.lean
git commit -m "Step 1 task 12: ER-side tests for ERTupling

Smoke #guards mirroring the Nat-side orientation locks
plus PolyBound shape examples (degree, coefficient,
constant for ofTuplePack at k = 1).

Spec §6.1 + §6.2 ER-side transcribed."
```

---

## Task 13 — Categorical iso `LawvereERCat.tupleIso` (gated)

**Files:**

- Modify: `GebLean/Utilities/ERTupling.lean` (append) — only
  if the gate passes
- Modify: `docs/superpowers/specs/2026-05-02-step-1-er-tupling-design.md`
  — either delete §8.3 (gate passes) or fill it (gate fails)

- [ ] **Step 13.1: Read `GebLean/LawvereERQuot.lean` and check
  the gate (§5.2 of the spec)**

Open `GebLean/LawvereERQuot.lean`. Check:

- [ ] **G1: Object indexing.** `LawvereERCat` is `ℕ` (line
      143), with `OfNat` instance (line 145), so
      `(k + 1 : LawvereERCat)` and `(1 : LawvereERCat)`
      resolve directly. Tick.
- [ ] **G2: Hom-set shapes.**
      `instance : CategoryStruct LawvereERCat` (line 152)
      defines `Hom := ERMorNQuo`, where
      `ERMorNQuo n m := Quotient (erMorNSetoid n m)`.
      `(k+1) ⟶ 1` is `Quotient (erMorNSetoid (k+1) 1)`;
      `1 ⟶ (k+1)` is `Quotient (erMorNSetoid 1 (k+1))`.
      Wrapping via `Quotient.mk (erMorNSetoid · ·) (lift …)`
      / `Quotient.mk (erMorNSetoid · ·) (ofVec …)` matches
      shape. Tick.
- [ ] **G3: Iso laws via Quotient.sound.** The §5.3
      construction reduces the iso laws to
      `Quotient.sound (s := erMorNSetoid · ·)` applied to
      Task 11's round-trip lemmas, plus standard category
      boilerplate. Verify by walking through the iso law
      goal (after `simp` on `≫` reduction) — does it match
      the round-trip lemma's `.r` form? Tick if yes.

- [ ] **Step 13.2: If any gate fails, fill §8.3 of the spec
  and stop**

Edit `docs/superpowers/specs/2026-05-02-step-1-er-tupling-design.md`
§8.3:

```markdown
### §8.3 Categorical iso deferral diagnosis

Failed condition: G[1|2|3]
Obstruction: <1–2 sentence reading of the relevant
            LawvereERCat construct, with line reference>
Proposed Step 1.5 cycle scope: <what infrastructure would
            need to land before the iso is reachable>
```

Skip Steps 13.3–13.5 and proceed directly to Task 14.

- [ ] **Step 13.3: If all gates pass, add `tupleIso`**

Append in `GebLean/Utilities/ERTupling.lean`:

```lean
namespace LawvereERCat

/-- Decorative iso: in `LawvereERCat`, the `(k+1)`-fold
product of the generator is isomorphic to the generator,
witnessed by `ERMor1.tuplePack` and the tuple of
`ERMor1.tupleAt`s.  Master design §3.1. -/
def tupleIso (k : ℕ) : (k + 1 : LawvereERCat) ≅ 1 where
  hom        := Quotient.mk (erMorNSetoid (k+1) 1)
                  (ERMorN.lift (ERMor1.tuplePack k))
  inv        := Quotient.mk (erMorNSetoid 1 (k+1))
                  (ERMorN.ofVec
                    (fun i : Fin (k+1) => ERMor1.tupleAt k i))
  hom_inv_id := by
    -- Reduce LHS to `Quotient.mk _ (ERMorN.comp ...)` then apply
    -- Quotient.sound on the round-trip lemma.
    show
      (Quotient.mk (erMorNSetoid (k+1) 1) _) ≫
        (Quotient.mk (erMorNSetoid 1 (k+1)) _)
        = 𝟙 _
    -- The category's ≫ on quotient classes:
    -- look up the existing definition in LawvereERQuot.lean
    -- and apply Quotient.sound on tupleAt_tuplePack.
    sorry  -- fill from the actual ≫ unfolding once visible
  inv_hom_id := by
    sorry  -- symmetric to hom_inv_id

end LawvereERCat
```

> WARNING: the `sorry`s above are placeholders. CLAUDE.md
> forbids `sorry`. Once the implementer has read
> `LawvereERQuot.lean`'s `≫` definition (lines 50-65,
> 100-135), they should write out the actual proof. The
> proof structure is:
>
> 1. Unfold `≫` to its `Quotient.lift₂`/`Quotient.map₂`
>    form (depending on the category's setup).
> 2. Reduce to a goal of the form
>    `Quotient.mk _ (ERMorN.comp f g) = Quotient.mk _ (id _)`.
> 3. Apply `Quotient.sound (s := erMorNSetoid · ·)` with
>    `ERMorN.tupleAt_tuplePack k` (or
>    `ERMorN.tuplePack_tupleAt k`).

If the iso law reduction is non-trivial (e.g., the `≫` is
not a clean `Quotient.lift₂`), pause and consult the
existing `LawvereERQuot.lean` proofs (`comp_id`, `id_comp`)
for the unfolding pattern.

- [ ] **Step 13.4: Build and verify the iso compiles
  without `sorry`**

Run: `lake build`
Expected: clean build, no `sorry` warnings, no other
warnings.

If `sorry`s remain, the gate has effectively failed at G3
even though G1 and G2 passed: surface this as a finding,
fill §8.3 with the diagnosis, remove the `tupleIso` def,
and proceed to Task 14.

- [ ] **Step 13.5: If the iso lands cleanly, delete §8.3
  from the spec**

Edit `docs/superpowers/specs/2026-05-02-step-1-er-tupling-design.md`
to remove §8.3 (since the iso is no longer deferred).

Verify the spec still lints clean:

Run: `markdownlint-cli2 docs/superpowers/specs/2026-05-02-step-1-er-tupling-design.md`
Expected: 0 errors.

- [ ] **Step 13.6: Commit**

If gate passed and iso lands:

```bash
git add GebLean/Utilities/ERTupling.lean \
        docs/superpowers/specs/2026-05-02-step-1-er-tupling-design.md
git commit -m "Step 1 task 13: LawvereERCat.tupleIso lands cleanly

Decorative categorical iso (k+1) ≅ 1 in LawvereERCat,
witnessing that products of the generator collapse via
Szudzik pairing in the morphism quotient.  All three gate
conditions (G1 object indexing, G2 hom-set shapes,
G3 Quotient.sound) pass directly.

Spec §8.3 deferral diagnosis section deleted since not
needed.  Master design §3.1 categorical packaging
complete."
```

If gate failed:

```bash
git add docs/superpowers/specs/2026-05-02-step-1-er-tupling-design.md
git commit -m "Step 1 task 13: LawvereERCat.tupleIso deferral diagnosis

Gate condition G[?] failed; spec §8.3 fills in the
diagnosis with the obstruction reading and proposed
Step 1.5 cycle scope.  The iso is decorative and the
deferral is itself a diagnostic signal per the spec's
intent (Q4 design choice)."
```

---

## Task 14 — Re-export modules and final verification

**Files:**

- Modify: `GebLean.lean` (add public exports)

- [ ] **Step 14.1: Verify `GebLeanTests.lean` registrations
  (Task 6 + Task 12)**

Open `GebLeanTests.lean`. Confirm both lines are present:

```lean
import GebLeanTests.Tupling
import GebLeanTests.ERTupling
```

- [ ] **Step 14.2: Add public exports to `GebLean.lean`**

Open `GebLean.lean`. Add (in alphabetical order in the
`Utilities` section):

```lean
import GebLean.Utilities.ERTupling
import GebLean.Utilities.Tupling
```

- [ ] **Step 14.3: Citation cross-check (spec §9 step 5)**

Open the two new modules
(`GebLean/Utilities/Tupling.lean` and
`GebLean/Utilities/ERTupling.lean`). For each public
`def` / `theorem`, verify the docstring contains the
literature citation listed in §7 of the spec verbatim
(not a paraphrase). Specifically:

- `Nat.tuplePack` — Tourlakis 2018 §0.1.0.34, p. 14;
  master design §3.1.
- `Nat.tupleAt` — Tourlakis 2018 §0.1.0.34, p. 14;
  master design §3.1.
- `Nat.tuplePackCoef` — master design §3.1
  (corrected formulation per commit `9c806cb8`);
  underlying bound `Nat.pair_le_sq` in
  `Utilities/ComputationalComplexity.lean`.
- `Nat.tupleAt_tuplePack`, `Nat.tuplePack_tupleAt` —
  Tourlakis 2018 §0.1.0.34, p. 14
  (`Π^k_i [[z_1,…,z_k]]^{(k)} = z_i`).
- `Nat.tupleAt_le` — mirrors existing `Nat.seqAt_le` in
  `Utilities/SzudzikSeq.lean`; `Nat.unpair_left_le`,
  `Nat.unpair_right_le`.
- `Nat.tuplePack_le` — Tourlakis 2018 §0.1.0.34, p. 14;
  master design §3.1.
- `ERMor1.tuplePack`, `ERMor1.tupleAt` — master design
  §3.1; CLAUDE.md "bottom-up named-composite discipline".
- `ERMor1.interp_tuplePack`, `ERMor1.interp_tupleAt` —
  master design §3.1.
- `ERMor1.PolyBound.ofTuplePack`,
  `ERMor1.PolyBound.ofTupleAt` — master design §3.1
  (PolyBound builders) and §15.12 (punch-list claim).
- `ERMorN.lift`, `ERMorN.ofVec` — master design §3.1
  (auxiliary helpers for ERMorN-level round-trip
  lemmas).
- `ERMorN.tupleAt_tuplePack`,
  `ERMorN.tuplePack_tupleAt` — master design §3.1.
- `LawvereERCat.tupleIso` (if landed) — master design
  §3.1 (categorical packaging).

If any docstring is missing or paraphrased, fix it. This
is a pure docstring-edit pass.

- [ ] **Step 14.4: Final build + test + lint**

Run: `lake build`
Expected: clean build, no warnings.

Run: `lake test`
Expected: all `#guard`s pass, all theorems compile.

Run `markdownlint-cli2` on the spec and on this plan; both
must report 0 errors.

Run a banned-word grep against the four new Lean files
(`Tupling.lean`, `ERTupling.lean`, and the two test
modules) covering the CLAUDE.md banned-words list. No
matches in prose; only inside technical-term contexts like
`Nat.pair` or `ComputationalComplexity` are acceptable.

Run: `git diff --check`
Expected: no whitespace errors.

- [ ] **Step 14.5: Commit**

```bash
git add GebLean.lean
git commit -m "Step 1 task 14: re-export Tupling and ERTupling from GebLean

Adds GebLean.Utilities.Tupling and GebLean.Utilities.ERTupling
to the library's public surface.  GebLeanTests.lean
registrations were committed alongside their respective
test modules in tasks 6 and 12.

Step 1 of the ER ↔ K^sim_2 categorical-equivalence
formalization complete; foundational fixed-length k-tuple
Szudzik pairing infrastructure is in place for step 2's
ERMor1.simultaneousBoundedRec consumer."
```

---

## Self-review (post-completion of Task 14)

- [ ] **Spec coverage check**: Skim each section of the
  spec (§3.1, §3.2, §3.3, §3.4, §4.1, §4.2, §4.3, §4.4,
  §5.3) and verify each entity it lists has a
  corresponding implementation in either Tasks 1–5
  (Nat side) or Tasks 7–11/13 (ER side). Tests covered by
  Tasks 6 + 12.

- [ ] **Tower-height + degree consistency**: At any point
  in Tasks 8/9/11, did any ER expression's PolyBound
  end up with a tower-height field instead of a polynomial
  degree? (No — `ERMor1.PolyBound` shape is
  `coefficient * (max+1)^degree + constant`, no tower
  field.)

- [ ] **Fin (k+1) consistency**: Confirm no slot uses
  `Fin k` where `Fin (k+1)` was promised by the
  indexing-convention rules in §1.3 of the spec.

- [ ] **Citation drift check**: Run grep to verify each
  module's docstrings include the master-design
  reference and (for Nat side) the Tourlakis §0.1.0.34,
  p. 14 reference.

- [ ] **Update `.session/`**: Once Task 14 is committed,
  add a one-paragraph note to `.session/workstreams/`
  for the er-ksim2-equiv-via-urm cycle progress (step 1
  complete, step 2 unblocked).

---

## Notes for the implementer

- **`lake env lean` is forbidden** — always use
  `lake build` and `lake test`. See CLAUDE.md.
- **`lake clean` is forbidden** — never use it; mathlib
  rebuild costs are prohibitive.
- **Underscores `_` for holes** — when stuck on a step,
  use `_` to surface the goal type via the resulting
  "unsolved goals" error. Never use `sorry`.
- **One definition at a time** — if Task 8's
  `interp_tuplePack` proof resists, do not paste the
  fallback and move on; pause and isolate the failing
  step into a smaller helper lemma per CLAUDE.md
  "Workflow" §13.
- **Spec is the source of truth for citations and naming**;
  this plan is the source of truth for execution
  sequencing. If a discrepancy arises, fix the spec
  inline and continue.
- **Adversarial review history**: rounds 1, 2, 3 are at
  `docs/research/2026-05-02-step-1-spec-adversarial-review-round-{1,2,3}.md`.
  Round 3's clean bill of health is the basis for this
  plan.
