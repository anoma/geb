# ER-Primrec Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task.  Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Deliver `ERMor1.boundedRec` as a derived Wikipedia-
literal closed-form term, with ER-side `div`/`mod`/`beta`/
`boundedSearch` prerequisites and downstream
`ERMor1.foldBTLOnCode`, preserving the `ERMor1` inductive's 7
Wikipedia generators unchanged.

**Architecture:** Derived bounded-primitive-recursion combinator
(Meyer-Ritchie-Kleene style) via Gödel's β-function, bounded
search, and min-truncation.  The β-function is a constant-depth
arithmetic `ERMor1` term; the CRT existence lemma
`Nat.beta_exists` is a meta-level Lean theorem; bounded search
over β-witness parameters is realized via `bsum` with indicator
predicates.  `boundedRec` takes a client-supplied elementary
upper bound, uses it to parameterize the β-witness search
range, extracts the trace value at position `n` via β, and
truncates by `min` with the bound.  When the bound dominates
the underlying `Nat.rec` result, the truncation is vacuous and
the combinator coincides with `Nat.rec`.

**Tech Stack:** Lean 4 with mathlib.  Builds on
`GebLean/LawvereER.lean`, `GebLean/LawvereERArith.lean`,
`GebLean/LawvereERBool.lean`, and `GebLean/Utilities/
SzudzikSeq.lean`.  Depends on mathlib's `Mathlib.Data.Nat.
Pairing`, `Mathlib.Data.Nat.ModEq`, and possibly
`Mathlib.Computability.Primrec`.

**Design spec:**
`docs/superpowers/specs/2026-04-17-er-primrec-design.md`.

**Workstream tracker entry:**
`.session/workstreams/lawvere-elementary-recursive.md`.

---

## Project rules

Every task obeys the project rules documented in `CLAUDE.md`:

* Build+test after every edit via `lake build` and `lake
  test`.  Never `lake clean`; never `lake env lean`.
* Zero warnings, zero `sorry` (including in `.lean` prose), zero
  `admit`.  80-char line limit.  No `Classical`, `noncomputable`,
  `axiom`.  All code inside `namespace GebLean … end GebLean`.
* Forbidden words in persistent writing (comments, docstrings,
  commit messages): fundamental, actually, key, insight, core,
  advanced, complex, complicated, simple, advantage, benefit,
  important, challenge, yes, wait, hmm, sorry (in prose),
  careful, difficult, blocked, incomplete, future, issue,
  problem, block.  Also no emojis.
* Structures get `@[ext]` where applicable.  Standard derived
  instances (`DecidableEq`, `Repr`, `Inhabited`) where they
  apply.

---

## File Structure

The mini-phase touches these files:

| File | Responsibility |
|---|---|
| `GebLean/Utilities/ERArith.lean` | Renamed from `ERTreeArith.lean`.  Houses ER-derived arithmetic (`natPair`/`natUnpair`/`natSqrt` from Task 12, plus new `div`/`mod`/`beta`/`boundedSearch`/`boundedRec` and showcase applications). |
| `GebLean/Utilities/ERTreeArith.lean` | Recreated (Task 13) with BTL-specific ER tooling: `foldBTLOnCode`, `btlEncodeLeaf`, `btlEncodeNode`. |
| `GebLean/Utilities/SzudzikSeq.lean` | Extended during Task 12c if mathlib lacks `Nat.beta_exists`.  Otherwise untouched. |
| `GebLean.lean` | Imports updated for renamed/new modules. |
| `GebLeanTests/ERArith.lean` | New test module exercising the arithmetic toolkit. |
| `GebLeanTests/ERTreeArith.lean` | New test module exercising `foldBTLOnCode`. |
| `GebLeanTests.lean` | Imports the new test modules. |

---

## Task 12a: Rename `ERTreeArith.lean` → `ERArith.lean`

**Goal:** Move the already-landed Task 12 content (commit
`29553fd0`) into the file name matching its content.

**Files:**

* Rename: `GebLean/Utilities/ERTreeArith.lean` → `GebLean/
  Utilities/ERArith.lean`
* Modify: `GebLean.lean` (import path)
* Modify: `GebLeanTests.lean` (if it imports
  `ERTreeArith`-specific tests; unlikely as of the current
  state)

- [ ] **Step 1: Git-mv the file**

```bash
git mv GebLean/Utilities/ERTreeArith.lean \
       GebLean/Utilities/ERArith.lean
```

- [ ] **Step 2: Update the module's docstring header**

Open `GebLean/Utilities/ERArith.lean`.  Find the docstring
section at the top (it begins with `/-! # ... -/`).  Replace the
title and description to match the file's new purpose:

```lean
/-!
# ER-Derived Arithmetic and Gödel β

`ERMor1`-level versions of mathlib's `Nat.pair`/`Nat.unpair`/
`Nat.sqrt` plus derived `div`/`mod`, the Gödel β-function, a
bounded search combinator, and the primitive-recursion
combinator `ERMor1.natRec`.  Each primitive carries an
`@[simp]`-marked correctness theorem linking its
interpretation to its mathematical counterpart.

Every primitive is a closed-form `ERMor1` term built by
composition of the 7 Wikipedia generators (`zero`, `succ`,
`proj`, `sub`, `comp`, `bsum`, `bprod`).  The `ERMor1`
inductive is not extended.

Part of the ER-Primrec mini-phase; see
`docs/superpowers/specs/2026-04-17-er-primrec-design.md`.
-/
```

- [ ] **Step 3: Update `GebLean.lean` import**

Open `GebLean.lean`.  Find the line:

```lean
import GebLean.Utilities.ERTreeArith
```

Replace with:

```lean
import GebLean.Utilities.ERArith
```

Keep its alphabetical position (between other `ERMor1`-related
imports and `NatBT*` imports).

- [ ] **Step 4: Build and test**

```bash
lake build
lake test
```

Expected: both succeed with zero warnings.

- [ ] **Step 5: Commit**

```bash
git add GebLean/Utilities/ERArith.lean GebLean.lean
git commit -m "Rename ERTreeArith.lean to ERArith.lean"
```

---

## Task 12b: `ERMor1.div` and `ERMor1.mod`

**Goal:** Add ER-derived integer division and modulo with
`@[simp]`-marked correctness theorems linking to `Nat.div` and
`Nat.mod`.

**Files:**

* Modify: `GebLean/Utilities/ERArith.lean`
* Modify: `GebLeanTests/ERArith.lean` (create if it does not
  yet exist; Task 12a may not have a matching test file)
* Modify: `GebLeanTests.lean` (register the new test module)

### Building blocks you will use

From `GebLean/LawvereER.lean`:

* `ERMor1.zero : ERMor1 0`, `ERMor1.succ : ERMor1 1`,
  `ERMor1.proj (i : Fin n) : ERMor1 n`, `ERMor1.sub : ERMor1 2`.
* `ERMor1.comp f g`, `ERMor1.bsum f`, `ERMor1.bprod f`.
* `ERMor1.zeroN n`, `ERMor1.oneN n` (constants).

From `GebLean/LawvereERBool.lean`:

* `ERMor1.subSwap : ERMor1 2` (computes `1 - (a - b)`, returns
  `0` or `1` as a boolean `¬ (a ≤ b)` indicator).
* `ERMor1.boolEqNat : ERMor1 2`.

From `GebLean/LawvereERArith.lean`:

* `ERMor1.natBProd_const` and `ERMor1.natBSum_const` helpers.

From `GebLean/Utilities/ERArith.lean` (current content from
Task 12a):

* `ERMor1.mulN : ERMor1 2` computing multiplication.
* `ERMor1.leN : ERMor1 2` computing `≤`.
* `ERMor1.ltN : ERMor1 2` computing `<`.
* `ERMor1.condN : ERMor1 3` computing three-arg Boolean
  conditional.

Verify these are present by reading the file; if any of the
names differ slightly from the above (due to how Task 12's
implementer named them), adjust downstream tasks accordingly.

- [ ] **Step 1: Read the existing file layout**

Open `GebLean/Utilities/ERArith.lean` and read through it to
identify the current contents and namespace scope.  Confirm
the names of `ERMor1.mulN`, `ERMor1.leN`, `ERMor1.ltN`,
`ERMor1.condN` (or their analogues).  Note line numbers where
additions will go (usually append to end within the
`namespace GebLean` section).

- [ ] **Step 2: Add `ERMor1.div`**

Append to `GebLean/Utilities/ERArith.lean` inside `namespace
GebLean`, after the existing `natSqrt` section:

```lean
/-- ER-derived integer division `a / b`.  Defined as a bounded
count via `bsum`: counts `k < a` with `(k + 1) * b ≤ a`.  When
`b = 0` the result is `0` (matching Lean's `Nat.div`
convention). -/
def ERMor1.div : ERMor1 2 :=
  ERMor1.bsum
    (ERMor1.leN.comp
      ![ERMor1.mulN.comp
          ![ERMor1.succ.comp ![ERMor1.proj 0],
            ERMor1.proj 2],
        ERMor1.proj 1])
```

(The indexing convention: inside the `bsum` body the slot 0 is
the iteration index, slot 1 is the outer `a`, slot 2 is the
outer `b`.  The body evaluates `(k+1)*b ≤ a` as a 0/1 value,
then `bsum (a) ... = count of k < a with body true = a / b`.)

- [ ] **Step 3: Add `ERMor1.interp_div`**

Still in `ERArith.lean`:

```lean
@[simp] theorem ERMor1.interp_div (a b : ℕ) :
    (ERMor1.div).interp ![a, b] = a / b := by
  unfold ERMor1.div
  -- The bsum count counts k < a with (k+1)*b ≤ a, which is
  -- Nat.div's bounded characterization.
  simp only [ERMor1.interp_bsum, ERMor1.interp_comp,
    ERMor1.interp_leN, ERMor1.interp_mulN,
    ERMor1.interp_succ, ERMor1.interp_proj]
  -- Goal: natBSum a (fun k => if (k+1)*b ≤ a then 1 else 0)
  -- = a / b.
  -- Use the natBSum characterization of Nat.div.
  rw [Nat.div_eq]
  -- Split on whether b > 0 and b ≤ a (Nat.div's case split).
  sorry  -- implementer completes via Nat.div_eq and bsum
         -- characterization
```

Implementer note: the proof needs to relate the `bsum`
counting characterization to `Nat.div`.  One path: prove a
helper lemma `natBSum_div_body_eq` that the bsum expression
equals `a / b` by induction on `a`, using `Nat.div_succ` or
similar.  Another path: use `Nat.div_eq_sub_div` recursively.
Budget: the proof may be 20-40 lines.  Factor out helper
lemmas as needed.

- [ ] **Step 4: Build and check reduction**

```bash
lake build
```

Expected: passes, except possibly a `sorry` warning in the
proof (which is OK at this intermediate step since Step 3
explicitly leaves a `sorry` for the implementer).  Fix the
`sorry` before moving on:

```bash
# iterate on Step 3 until the `sorry` is replaced by a full
# proof and `lake build` is clean.
```

- [ ] **Step 5: Add `ERMor1.mod`**

```lean
/-- ER-derived integer modulo `a % b = a - (a / b) * b`. -/
def ERMor1.mod : ERMor1 2 :=
  ERMor1.sub.comp
    ![ERMor1.proj 0,
      ERMor1.mulN.comp
        ![ERMor1.div.comp ![ERMor1.proj 0, ERMor1.proj 1],
          ERMor1.proj 1]]

@[simp] theorem ERMor1.interp_mod (a b : ℕ) :
    (ERMor1.mod).interp ![a, b] = a % b := by
  unfold ERMor1.mod
  simp only [ERMor1.interp_comp, ERMor1.interp_sub,
    ERMor1.interp_mulN, ERMor1.interp_div,
    ERMor1.interp_proj]
  -- Goal: a - (a / b) * b = a % b
  exact (Nat.mod_eq_sub_div_mul_comm a b).symm
  -- or a direct Nat.mod characterization
```

(The exact mathlib lemma name may be `Nat.mod_def`,
`Nat.sub_mul_div`, or similar; the implementer checks and
uses the one that applies.)

- [ ] **Step 6: Build + test**

```bash
lake build
lake test
```

Both must pass with zero warnings.

- [ ] **Step 7: Create `GebLeanTests/ERArith.lean` (if not
  present) and add sanity checks**

```lean
import GebLean.Utilities.ERArith

open GebLean

-- Division sanity checks
#guard (ERMor1.div).interp ![7, 3] = 2
#guard (ERMor1.div).interp ![10, 2] = 5
#guard (ERMor1.div).interp ![0, 5] = 0
#guard (ERMor1.div).interp ![5, 0] = 0  -- Nat.div convention

-- Modulo sanity checks
#guard (ERMor1.mod).interp ![7, 3] = 1
#guard (ERMor1.mod).interp ![10, 5] = 0
#guard (ERMor1.mod).interp ![0, 5] = 0
```

- [ ] **Step 8: Register test module (if not already done)**

Open `GebLeanTests.lean` and add (in alphabetical order):

```lean
import GebLeanTests.ERArith
```

Skip if already present.

- [ ] **Step 9: Build + test**

```bash
lake build
lake test
```

Both pass, `#guard` assertions verify.

- [ ] **Step 10: Commit**

```bash
git add GebLean/Utilities/ERArith.lean \
        GebLeanTests/ERArith.lean GebLeanTests.lean
git commit -m "Add ER-derived div and mod with correctness"
```

---

## Task 12c: `ERMor1.beta` and `Nat.beta_exists`

**Goal:** Add Gödel's β-function as a direct arithmetic
`ERMor1` term and the meta-level CRT existence lemma used to
justify `natRec` correctness.

**Files:**

* Modify: `GebLean/Utilities/ERArith.lean` (adds `ERMor1.beta`
  and its correctness)
* Possibly modify: `GebLean/Utilities/SzudzikSeq.lean` or a
  new file `GebLean/Utilities/GoedelBeta.lean` for the
  `Nat.beta_exists` lemma (decided after the mathlib
  investigation in Step 1)
* Modify: `GebLeanTests/ERArith.lean`

### Step 1: Mathlib investigation (do first)

Before writing any proof, search mathlib for pre-existing β
machinery.  Relevant candidates:

* `Mathlib.Computability.Primrec` — has `Nat.Primrec.prec`.
  Check whether it internally provides β-existence or CRT.
* `Mathlib.Data.Nat.ModEq` — has
  `Nat.ModEq.chineseRemainder` (CRT for two moduli).
* `Mathlib.Data.Nat.Pairing` — already used for `natPair`.

Recommended tools:

* `mcp__lean-lsp__lean_leansearch` — natural-language search
  for mathlib.
* `mcp__lean-lsp__lean_local_search` — local declaration
  search.
* `grep -rn "beta_exists" .lake/packages/mathlib/`.

Write down (in your head or a scratchpad) what mathlib has
and what still needs proving locally.

- [ ] **Step 1a: Execute the mathlib investigation**

```bash
grep -rn "beta\|chineseRemainder" \
  .lake/packages/mathlib/Mathlib/Computability/ \
  .lake/packages/mathlib/Mathlib/Data/Nat/ | head -40
```

Also ask the Lean LSP:

```text
lean_leansearch "exists Gödel beta function sequence"
lean_leansearch "Chinese remainder theorem coprime moduli"
```

Decide based on findings:

* **Path A**: mathlib provides β-existence → cite and skip to
  Step 3.
* **Path B**: mathlib provides CRT but not β-existence →
  wrap CRT into `Nat.beta_exists` via a dedicated lemma.
* **Path C**: mathlib provides neither directly → prove both
  CRT and β-existence from more primitive mathlib lemmas.

Record the chosen path in a comment at the top of the new
code.  Budget: Path A is ~0.5 session; Path B ~1 session;
Path C ~2 sessions.

### Step 2: Define `ERMor1.beta` (independent of Step 1)

Append to `ERArith.lean` in the `namespace GebLean` section:

```lean
/-- Gödel's β-function as an ER term:
`β(a, b, i) = a mod (1 + (i + 1) * b)`.

Constant-depth arithmetic; no iteration.  Used in `natRec`
(Task 12e) to extract values from a Gödel-encoded trace of a
primitive-recursion computation. -/
def ERMor1.beta : ERMor1 3 :=
  ERMor1.mod.comp
    ![ERMor1.proj 0,
      ERMor1.succ.comp
        ![ERMor1.mulN.comp
            ![ERMor1.succ.comp ![ERMor1.proj 2],
              ERMor1.proj 1]]]

@[simp] theorem ERMor1.interp_beta (a b i : ℕ) :
    (ERMor1.beta).interp ![a, b, i] =
      a % (1 + (i + 1) * b) := by
  unfold ERMor1.beta
  simp only [ERMor1.interp_comp, ERMor1.interp_mod,
    ERMor1.interp_succ, ERMor1.interp_mulN,
    ERMor1.interp_proj]
  ring_nf  -- or `omega` if tactics need normalizing
```

If `ring_nf` or `omega` doesn't close the goal, trace through
the projection indexing: the input context is `![a, b, i]`,
and `beta` needs to compute `a mod (1 + (i+1) * b)`.  The proj
indices must match.

- [ ] **Step 3: Add `Nat.beta_exists`**

**If Path A** (mathlib has it): import and re-state:

```lean
/-- For any finite ℕ-sequence there exist β-parameters (a, b)
such that `β(a, b, i) = s i` for all `i < N`.  Cites
`<mathlib lemma name>`. -/
theorem Nat.beta_exists {N : ℕ} (s : Fin N → ℕ) :
    ∃ a b : ℕ, ∀ i : Fin N,
      a % (1 + (i.val + 1) * b) = s i := by
  -- Cite the mathlib β-existence lemma.
  sorry  -- replace with `exact Nat.Primrec.β_exists ...`
         -- or analogous
```

**If Path B** (mathlib has CRT but not β-existence): prove
via CRT.  Add to `ERArith.lean`:

```lean
theorem Nat.beta_exists {N : ℕ} (s : Fin N → ℕ) :
    ∃ a b : ℕ, ∀ i : Fin N,
      a % (1 + (i.val + 1) * b) = s i := by
  -- Let M = max (s.max, N, 1); let b = M!.
  -- The moduli d_i = 1 + (i+1) * b for i < N are pairwise
  -- coprime: any common factor of d_i and d_j divides
  -- (j - i) * b = (j - i) * M!, which is coprime to each
  -- d_k (since d_k ≡ 1 mod p for p ≤ M).
  -- Apply mathlib's CRT to obtain a with a mod d_i = s i.
  sorry  -- implementer fills in
```

**If Path C** (prove both): add a new file
`GebLean/Utilities/GoedelBeta.lean` with:

* `Nat.beta_moduli_coprime` lemma.
* A CRT theorem (either wrap mathlib's pairwise-coprime
  `Nat.ModEq.chineseRemainder` or prove directly).
* `Nat.beta_exists` as the main public theorem.

Import the file in `ERArith.lean` to use `Nat.beta_exists`.

Budget per-path: Path A ~0.5 session, Path B ~1 session,
Path C ~2 sessions.

- [ ] **Step 4: Build and verify `Nat.beta_exists` types**

```bash
lake build
```

Passes with zero `sorry`s (you must replace all `sorry`s in
Step 3 with actual proofs before building is considered
clean).

- [ ] **Step 5: Add `#guard` sanity checks for `beta`**

Append to `GebLeanTests/ERArith.lean`:

```lean
-- β-function sanity checks (just arithmetic)
#guard (ERMor1.beta).interp ![5, 3, 0] = 5 % 4
#guard (ERMor1.beta).interp ![7, 2, 1] = 7 % 5
#guard (ERMor1.beta).interp ![10, 3, 2] = 10 % 10

-- β at i = 0 extracts mod-(b+1) reduction
example (a b : ℕ) :
    (ERMor1.beta).interp ![a, b, 0] = a % (1 + b) := by
  simp
  ring_nf
```

- [ ] **Step 6: Build, test, commit**

```bash
lake build
lake test
git add GebLean/Utilities/ERArith.lean \
        GebLeanTests/ERArith.lean
# If Path C: also
# git add GebLean/Utilities/GoedelBeta.lean GebLean.lean
git commit -m "Add ERMor1.beta and Nat.beta_exists"
```

---

## Task 12d: `ERMor1.boundedSearch`

**Goal:** Add a bounded search combinator returning the least
witness satisfying a predicate, or `bound + 1` if none.

**Files:**

* Modify: `GebLean/Utilities/ERArith.lean`
* Modify: `GebLeanTests/ERArith.lean`

### Semantic specification

```text
(boundedSearch bound pred).interp ctx =
  if ∃ j < bound.interp ctx, pred.interp (cons j ctx) = 1
    then least such j
    else bound.interp ctx + 1
```

The "least j with pred=1" is extractable via `bsum` plus
`min`.  Concretely: iterate j from 0 to bound-1, and at each j
contribute `if pred_at_j then (min current_result j) else
current_result`.  But `bsum` doesn't thread state through
iterations.

Workaround: use two `bsum`s.  First compute the "found count"
up to each j (cumulative count of witnesses).  Second: find
the first j where the cumulative count becomes 1.  More
directly: use the characterization

```text
least j with pred j = 1
  = bsum (k < bound) of
      if (bsum (m < k) (pred m)) = 0 then pred k * k else 0
  + (bsum (k < bound) (pred k) == 0) * bound
```

(The first term is `if no witness in [0, k) but pred k then
contribute k else 0`; the second term is `bound` if no witness
exists anywhere.)

The expression evaluates to `(least witness) + 0 = least
witness` if a witness exists, or `0 + bound = bound` if not.
Clients treat "result ≥ bound" as "no witness found".

**Simplification for Task 12e usage:** `boundedRec`'s
correctness proof relies on `boundedSearch` finding THE witness
when one exists (as guaranteed by `Nat.beta_exists`).  For our
usage, we don't need "least" — any witness-finder works.
Adjust the specification if a simpler combinator suffices.

- [ ] **Step 1: Define `ERMor1.boundedSearch`**

Append to `ERArith.lean`:

```lean
/-- Bounded search: given a bound and a 0/1-valued predicate,
returns the least `j < bound.interp ctx` with the predicate
holding on `(j, ctx)`, or `bound.interp ctx + 1` if no such
`j` exists. -/
def ERMor1.boundedSearch {k : ℕ}
    (bound : ERMor1 k) (pred : ERMor1 (k + 1)) :
    ERMor1 k :=
  -- See the semantic specification above.  Implementer may
  -- use the two-bsum characterization or a direct bsum with
  -- the "first witness" indicator.
  sorry  -- implementer fills in
```

Implementer options:

* **Option α (two-bsum)**: use two nested `bsum`s as
  described.  Correctness proof is moderate.
* **Option β (explicit witness flagging)**: `bsum (k <
  bound) of pred_k * (k+1) * indicator("no witness before k")`
  — the first witness gets flagged, subsequent witnesses
  contribute 0.  Proof requires establishing the flag
  semantics.
* **Option γ (mathlib reuse)**: if mathlib has
  `Nat.find_eq_bsum` or similar, reuse.

Pick whichever gives the cleanest correctness proof.

- [ ] **Step 2: Add `ERMor1.interp_boundedSearch` correctness**

```lean
theorem ERMor1.interp_boundedSearch {k : ℕ}
    (bound : ERMor1 k) (pred : ERMor1 (k + 1))
    (ctx : Fin k → ℕ) :
    (ERMor1.boundedSearch bound pred).interp ctx =
      if h : ∃ j, j < bound.interp ctx ∧
          (pred.interp (Fin.cons j ctx) = 1)
        then Nat.find h
        else bound.interp ctx + 1 := by
  unfold ERMor1.boundedSearch
  -- Split on whether the predicate holds anywhere below bound
  sorry  -- implementer fills in
```

If the `Nat.find` formulation is awkward to state
propositionally, use the decidable version of existence
(which is valid here since `pred` is 0/1-valued and the range
is bounded).

- [ ] **Step 3: Add a simpler characterization lemma for
  downstream use**

```lean
/-- If `pred` holds for a unique `j < bound`, `boundedSearch`
returns that `j`.  Used by `boundedRec` at Task 12e. -/
theorem ERMor1.boundedSearch_eq_unique {k : ℕ}
    (bound : ERMor1 k) (pred : ERMor1 (k + 1))
    (ctx : Fin k → ℕ) (j : ℕ)
    (hj_lt : j < bound.interp ctx)
    (hj_pred : pred.interp (Fin.cons j ctx) = 1)
    (hj_unique : ∀ j', j' < bound.interp ctx →
      (pred.interp (Fin.cons j' ctx) = 1) →
      j' = j) :
    (ERMor1.boundedSearch bound pred).interp ctx = j := by
  sorry  -- implementer fills in
```

- [ ] **Step 4: Sanity `#guard` tests**

Append to `GebLeanTests/ERArith.lean`:

```lean
-- Search for first even number in [0, 10): should find 0.
example :
    (ERMor1.boundedSearch
      (ERMor1.zeroN 0 |>.succ.succ.succ.succ.succ.succ
        .succ.succ.succ.succ)  -- bound 10
      (ERMor1.condN.comp
        ![ERMor1.mod.comp
            ![ERMor1.proj 0, ERMor1.oneN 1 |>.succ],
          ERMor1.zeroN 1, ERMor1.oneN 1])).interp
      Fin.elim0 = 0 := by
  sorry  -- implementer completes
```

(The exact term-building for the test is intricate because
`condN` and `mod` use explicit indexing.  If the test is too
verbose, use an abstract `example` that just checks the
correctness theorem reduces on a generic decidable predicate.)

- [ ] **Step 5: Build, test, commit**

```bash
lake build
lake test
git add GebLean/Utilities/ERArith.lean \
        GebLeanTests/ERArith.lean
git commit -m "Add ERMor1.boundedSearch with correctness"
```

---

## Task 12e: `ERMor1.boundedRec`

**Goal:** The derived bounded-primitive-recursion combinator
(Meyer-Ritchie-Kleene).  Defined via `boundedSearch` for
β-witnesses, β-extraction, and `min`-truncation with a
client-supplied elementary upper bound.

**Files:**

* Modify: `GebLean/Utilities/ERArith.lean`
* Modify: `GebLeanTests/ERArith.lean`

### boundedRec semantic specification

```text
(boundedRec base step bound).interp (Fin.cons n ctx) =
  min
    (Nat.rec (base.interp ctx)
      (fun j prev =>
        step.interp (Fin.cons j (Fin.cons prev ctx)))
      n)
    (bound.interp (Fin.cons n ctx))
```

The `min` supplies truncation semantics: when the β-witness
search at the bound-derived range fails, the `bound` value
dominates; when the search succeeds, β-extraction yields the
`Nat.rec` value and the `min` is vacuous iff the bound
dominates.

### boundedRec construction sketch

Given `base : ERMor1 k`, `step : ERMor1 (k + 2)`,
`bound : ERMor1 (k + 1)`, and input `(n, ctx)`:

1. Evaluate the client-supplied `bound` on `(n, ctx)` to obtain
   an elementary upper bound `B`.
2. Use `boundedSearch` over Szudzik-paired `(a, b)` with search
   range derived from `B` and `n` (a sufficient formula is
   `B² * (n + 2)!` or similar polynomial-in-`B`-and-factorial-
   in-`n`, dominating the CRT construction from
   `Nat.beta_exists` applied to a trace bounded by `B`).
3. The predicate for the search: "β(a, b, 0) = base.interp ctx
   AND ∀ j < n: β(a, b, j+1) = step.interp (cons j (cons
   β(a,b,j) ctx))".  The ∀ is expressed as a bsum-of-indicators
   equaling n (all-true check).
4. Extract `β(a, b, n)` from the found witness, then take
   `min` with `bound.interp (cons n ctx)` to yield the
   truncated output.

When the bound dominates the true `Nat.rec` trace, the search
finds a β-witness for the untruncated trace and the `min`
returns the `Nat.rec` value.  When the bound is inadequate,
the search may fail, but the `min` still yields a well-defined
output bounded by `bound`.

### Bound derivation (internal search range)

The client-supplied `bound` provides a ceiling on trace values.
`Nat.beta_exists` then implies β-witnesses exist within an
elementary function of `bound.interp (cons n ctx)` and `n`.
The internal search range of `boundedRec` is derived from
`bound` and `n` via a `bprod`-based factorial term plus
multiplication; no use of `boundedRec` itself occurs in the
range construction (avoiding circularity).

- [ ] **Step 1: Helper — derive the β-search range from the
  client's bound**

```lean
/-- From the client-supplied `bound` term and the counter slot,
derive the internal β-witness search range.  Returns an
`ERMor1 (k + 1)` term dominating the CRT bound for a trace of
length `n` with values `≤ bound.interp (cons n ctx)`.  One
concrete formula: `(bound.interp (cons n ctx))² * (n + 2)!`,
built via `bprod` for the factorial and `mulN` for the
product. -/
def ERMor1.boundedRecSearchRange {k : ℕ}
    (bound : ERMor1 (k + 1)) : ERMor1 (k + 1) :=
  -- Implementer selects and justifies an explicit expression
  -- satisfying the CRT bound guarantee from `Nat.beta_exists`
  -- applied to a trace of length `n` with values bounded by
  -- `bound.interp (cons n ctx)`.
  sorry
```

Budget: ~0.5 session to pick the formula and justify it.

- [ ] **Step 2: Define `ERMor1.boundedRec`**

```lean
/-- Derived bounded-primitive-recursion combinator
(Meyer-Ritchie-Kleene).  Takes a `base`, a `step`, and a
client-supplied elementary upper `bound`, and returns the
`Nat.rec` trace value truncated by `min` with the bound.

Built via β-function witness search: finds Gödel (a, b) such
that β encodes the recursion trace (within the bound-derived
search range), extracts the final value, then truncates by
`min` with the bound. -/
def ERMor1.boundedRec {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) :
    ERMor1 (k + 1) :=
  -- Implementer builds: boundedSearch over paired (a, b) up
  -- to boundedRecSearchRange bound, with trace-matching
  -- predicate, β-extraction at position n, then `min` with
  -- `bound`.
  sorry
```

Budget: ~1 session for the definition.

- [ ] **Step 3: Prove the two correctness theorems**

The original strict-`min` correctness statement
(`output = min (Nat.rec ...) (bound...)`) is NOT provable with
the β-witness-search construction: when intermediate trace
values exceed `bound`, the search range cannot accommodate the
actual trace and the search fails, producing a value `≤ bound`
unrelated to `Nat.rec`.  See spec D5/D6 for the analysis.

The provable correctness has two parts:

```lean
/-- Unconditional pointwise upper bound. -/
theorem ERMor1.interp_boundedRec_le_bound {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1))
    (n : ℕ) (ctx : Fin k → ℕ) :
    (ERMor1.boundedRec base step bound).interp
        (Fin.cons n ctx) ≤
      bound.interp (Fin.cons n ctx) := by
  -- Direct from the outermost `minN` in the construction.
  sorry  -- implementer fills in

/-- Conditional equality with `Nat.rec`: when the client's
bound dominates the trace pointwise at every position `j ≤ n`,
the combinator produces the unbounded `Nat.rec` value. -/
theorem ERMor1.interp_boundedRec_of_bounded {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1))
    (n : ℕ) (ctx : Fin k → ℕ)
    (h : ∀ j, j ≤ n →
      Nat.rec (base.interp ctx)
        (fun i prev =>
          step.interp (Fin.cons i (Fin.cons prev ctx)))
        j ≤
        bound.interp (Fin.cons j ctx)) :
    (ERMor1.boundedRec base step bound).interp
        (Fin.cons n ctx) =
      Nat.rec (base.interp ctx)
        (fun j prev =>
          step.interp (Fin.cons j (Fin.cons prev ctx)))
        n := by
  induction n with
  | zero =>
      -- Trace is singleton `[base.interp ctx]`, bounded by
      -- `bound.interp (cons 0 ctx)` by hypothesis at j=0.
      -- bounded_beta_exists produces witnesses; search finds
      -- one; β-extraction at 0 yields base.interp ctx; outer
      -- min is vacuous since base.interp ctx ≤ bound.
      sorry
  | succ m ih =>
      -- Inductive: bound dominates trace at every j ≤ m+1.
      -- Apply bounded_beta_exists with M sized to dominate
      -- the trace.  Search finds a witness; β-extract at
      -- position m+1; outer min vacuous.
      sorry
```

Budget: ~1-2 sessions for both correctness theorems.

The load-bearing lemma: `Nat.bounded_beta_exists` (from Task
12e.1) provides the existence of witnesses within an explicit
elementary bound in the trace's max value; `boundedSearch`
finds one; β-extraction at position n yields the trace value.
Sub-lemmas like `boundedRec_witness_exists` (search-range
sufficiency) and `boundedRec_search_extracts_value` (β round-
trip) are encouraged.

- [ ] **Step 4: Convenience alias
  `boundedRec_eq_natRec_of_bounded`**

The conditional theorem `interp_boundedRec_of_bounded` from
Step 3 already gives `Nat.rec` semantics when the bound
dominates pointwise.  Add a convenience alias whose hypothesis
is just at the final position `n` (the most common client
shape), derived from the pointwise version under a
monotonicity assumption on `bound` if available, or stated as
an alternate signature wrapping the same proof:

```lean
/-- Convenience form: when the client supplies a final-position
bound-adequacy hypothesis and the bound is monotone in the
counter slot, `boundedRec` agrees with `Nat.rec` at position
`n`.  In practice clients prove the pointwise version directly
via induction; this alias is offered for the common shape. -/
theorem ERMor1.boundedRec_eq_natRec_of_bounded {k : ℕ}
    (base : ERMor1 k) (step : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1))
    (n : ℕ) (ctx : Fin k → ℕ)
    (h_pt : ∀ j, j ≤ n →
      Nat.rec (base.interp ctx)
        (fun i prev =>
          step.interp (Fin.cons i (Fin.cons prev ctx)))
        j ≤
        bound.interp (Fin.cons j ctx)) :
    (ERMor1.boundedRec base step bound).interp
        (Fin.cons n ctx) =
      Nat.rec (base.interp ctx)
        (fun j prev =>
          step.interp (Fin.cons j (Fin.cons prev ctx)))
        n :=
  ERMor1.interp_boundedRec_of_bounded base step bound n ctx h_pt
```

- [ ] **Step 5: `#guard` sanity checks with known-adequate
  bounds**

Append to `GebLeanTests/ERArith.lean`.  Use a constant bound
known to dominate the test inputs:

```lean
-- boundedRec with base=0, step=succ, bound=n+1 computes n.
-- Here `bound` selects slot 0 (the counter) and adds 1.
example (n : ℕ) :
    (ERMor1.boundedRec
      (ERMor1.zeroN 0)
      (ERMor1.succ.comp ![ERMor1.proj 1])
      (ERMor1.succ.comp ![ERMor1.proj 0])).interp
      ![n] = n := by
  simp [ERMor1.interp_boundedRec]
  -- Reduces to min (Nat.rec 0 (fun _ p => p + 1) n) (n + 1)
  -- = min n (n + 1) = n.
  induction n <;> simp_all
```

- [ ] **Step 6: Build, test, commit**

```bash
lake build
lake test
git add GebLean/Utilities/ERArith.lean \
        GebLeanTests/ERArith.lean
git commit -m "Add ERMor1.boundedRec via Gödel β with correctness"
```

---

## Task 12f: Showcase applications

**Goal:** Validate `boundedRec` end-to-end on concrete
primitive-recursive functions (`natAdd`, `natMul`,
`factorial`).  Each showcase supplies an explicit elementary
bound and pairs the `boundedRec`-based definition with a
`boundedRec_eq_natRec_of_bounded` application to recover exact
`Nat.rec` semantics in the correctness theorem.

**Files:**

* Modify: `GebLean/Utilities/ERArith.lean`
* Modify: `GebLeanTests/ERArith.lean`

- [ ] **Step 1: `ERMor1.natAdd`**

Bound: `x + y + 1` (the result `x + y` is obviously bounded
by `x + y + 1`).  The bound is itself a `boundedRec`-free
term: `succ.comp (natAdd ...)` would be circular, so instead
use a direct closed-form term that doesn't call `natAdd`.
One option: `x + y + 1` via `bsum` of ones over `x + y`, but
`bsum` already sums the counter, giving `x + y`.  More
directly, since the context on entry to `natAdd ![x, y]` is
`![x, y]` and `boundedRec` takes bound at shape
`ERMor1 (k + 1) = ERMor1 2`, use `succ.comp ![addN.comp
![proj 0, proj 1]]`, which gives `(counter + x) + 1`; this is
adequate since the counter ranges from 0 to y inclusive, so
`counter + x ≤ x + y`, and the bound `(counter + x) + 1`
dominates `x + counter` (the current trace value).

```lean
/-- Addition as iterated successor, via `boundedRec` with the
polynomial bound `counter + x + 1`.  `natAdd ![x, y] = x + y`. -/
def ERMor1.natAdd : ERMor1 2 :=
  ERMor1.boundedRec (ERMor1.proj 0)
    (ERMor1.succ.comp ![ERMor1.proj 1])
    (ERMor1.succ.comp
      ![ERMor1.addN.comp ![ERMor1.proj 0, ERMor1.proj 1]])

@[simp] theorem ERMor1.interp_natAdd (x y : ℕ) :
    (ERMor1.natAdd).interp ![x, y] = x + y := by
  unfold ERMor1.natAdd
  -- Apply `boundedRec_eq_natRec_of_bounded` with the trivial
  -- bound adequacy: `Nat.rec x (fun _ p => p + 1) y = x + y`
  -- is bounded by `y + x + 1`.
  rw [ERMor1.boundedRec_eq_natRec_of_bounded]
  · simp only [ERMor1.interp_proj, ERMor1.interp_comp,
      ERMor1.interp_succ]
    induction y <;> simp_all [Nat.rec, Nat.succ_eq_add_one]
  · -- Bound-adequacy goal:
    -- Nat.rec x (fun _ p => p + 1) y ≤ y + x + 1
    simp only [ERMor1.interp_comp, ERMor1.interp_succ,
      ERMor1.interp_addN, ERMor1.interp_proj]
    induction y <;> simp_all <;> omega
```

(The indexing inside `boundedRec`: context on first
application has `![x, y]`; `boundedRec (base)(step)(bound)`
pulls `y` as the counter, and `base`'s context is
`Fin.tail ![x, y] = ![x]`.  Step applies to `(j, prev, x)` —
the step term must pick up `prev` at slot 1 and ignore `j` at
slot 0 and `x` at slot 2.  The `ERMor1.succ.comp ![ERMor1.proj
1]` does this.  Bound applies to `(j, x)` — slots 0 (counter)
and 1 (the passthrough `x`).)

- [ ] **Step 2: `ERMor1.natMul`**

Bound: `(counter + 1) * x + 1`, which dominates the partial-
product trace `[0, x, 2x, ..., (counter)*x]`.  Built via
`mulN` plus `succ`.

```lean
/-- Multiplication as iterated addition, via `boundedRec` with
the polynomial bound `(counter + 1) * x + 1`.
`natMul ![x, y] = x * y`. -/
def ERMor1.natMul : ERMor1 2 :=
  ERMor1.boundedRec (ERMor1.zeroN 1)
    (ERMor1.natAdd.comp ![ERMor1.proj 2, ERMor1.proj 1])
    (ERMor1.succ.comp
      ![ERMor1.mulN.comp
          ![ERMor1.succ.comp ![ERMor1.proj 0],
            ERMor1.proj 1]])

@[simp] theorem ERMor1.interp_natMul (x y : ℕ) :
    (ERMor1.natMul).interp ![x, y] = x * y := by
  unfold ERMor1.natMul
  rw [ERMor1.boundedRec_eq_natRec_of_bounded]
  · simp only [ERMor1.interp_zeroN, ERMor1.interp_natAdd,
      ERMor1.interp_comp, ERMor1.interp_proj]
    induction y with
    | zero => simp
    | succ n ih => simp [ih, Nat.succ_mul, Nat.add_comm]
  · -- Bound-adequacy: Nat.rec 0 (fun _ p => x + p) y ≤
    --                 (y + 1) * x + 1.
    simp only [ERMor1.interp_comp, ERMor1.interp_succ,
      ERMor1.interp_mulN, ERMor1.interp_proj]
    induction y with
    | zero => simp
    | succ n ih => simp [ERMor1.interp_natAdd] at *; nlinarith
```

- [ ] **Step 3: `ERMor1.factorial`**

Bound: `n^n + 1`, dominating `n!` for `n ≥ 1` (and equal to
`1 + 1 = 2 ≥ 1 = 0!` at `n = 0`).  Built via a closed-form ER
term for `n^n` using `expER` (if available in
`LawvereERArith.lean`) or `bprod` of the multiplicand `n` over
range `n`.

```lean
/-- Factorial via `boundedRec` with the polynomial-in-tower
bound `counter^counter + 1`.  `factorial ![n] = n!`. -/
def ERMor1.factorial : ERMor1 1 :=
  ERMor1.boundedRec (ERMor1.oneN 0)
    (ERMor1.natMul.comp
      ![ERMor1.succ.comp ![ERMor1.proj 0],
        ERMor1.proj 1])
    (ERMor1.succ.comp
      ![ERMor1.expER.comp ![ERMor1.proj 0, ERMor1.proj 0]])

@[simp] theorem ERMor1.interp_factorial (n : ℕ) :
    (ERMor1.factorial).interp ![n] = Nat.factorial n := by
  unfold ERMor1.factorial
  rw [ERMor1.boundedRec_eq_natRec_of_bounded]
  · simp only [ERMor1.interp_oneN, ERMor1.interp_natMul,
      ERMor1.interp_comp, ERMor1.interp_succ,
      ERMor1.interp_proj]
    induction n with
    | zero => simp [Nat.factorial]
    | succ m ih =>
        simp [Nat.factorial_succ, ih, Nat.succ_eq_add_one]
  · -- Bound-adequacy: n! ≤ n^n + 1.
    simp only [ERMor1.interp_comp, ERMor1.interp_succ,
      ERMor1.interp_expER, ERMor1.interp_proj]
    -- Classical `Nat.factorial_le_pow_self` or inductive proof.
    sorry  -- implementer uses mathlib lemma or proves inductively
```

(If `ERMor1.expER` is not available, substitute `bprod
(proj 0)` for `(counter + 1)^counter` times `counter` — any
adequate polynomial or elementary bound works.)

- [ ] **Step 4: `#guard` validation**

Append to `GebLeanTests/ERArith.lean`:

```lean
-- natAdd sanity
#guard (ERMor1.natAdd).interp ![3, 5] = 8
#guard (ERMor1.natAdd).interp ![0, 7] = 7
#guard (ERMor1.natAdd).interp ![4, 0] = 4

-- natMul sanity
#guard (ERMor1.natMul).interp ![3, 5] = 15
#guard (ERMor1.natMul).interp ![0, 7] = 0
#guard (ERMor1.natMul).interp ![4, 1] = 4

-- factorial sanity
#guard (ERMor1.factorial).interp ![0] = 1
#guard (ERMor1.factorial).interp ![1] = 1
#guard (ERMor1.factorial).interp ![3] = 6
#guard (ERMor1.factorial).interp ![5] = 120
```

If any `#guard` evaluation times out (because `boundedRec`'s
β-witness search runs a large `bsum`), reduce test sizes to
smaller inputs (`factorial ![3]` or `![4]` may be the practical
maximum).

- [ ] **Step 5: Build, test, commit**

```bash
lake build
lake test
git add GebLean/Utilities/ERArith.lean \
        GebLeanTests/ERArith.lean
git commit -m "Add natAdd/natMul/factorial showcase of boundedRec"
```

---

## Task 13: `ERMor1.foldBTLOnCode`

**Goal:** ER-derived BTL fold-on-Gödel-code, built on
`boundedRec`.  Completes the original Task 13 Part 2 (Part 1
`Nat.foldBTLOnCode` is already done at commit `3eebf595`).

**Files:**

* Create: `GebLean/Utilities/ERTreeArith.lean`
* Modify: `GebLean.lean`
* Create: `GebLeanTests/ERTreeArith.lean`
* Modify: `GebLeanTests.lean`

### Signature choice: client-facing 2-argument vs internal bound

`ERMor1.boundedRec` requires an explicit `bound` term.
Task 13's `foldBTLOnCode` has two design options for exposing
this:

* **Option A (client-facing bound):** add a third parameter
  `bound : ERMor1 (k + 1)` to the signature, passing the
  responsibility for bound adequacy to the caller.
* **Option B (internal bound):** keep the 2-argument signature
  and construct an internal bound from the input code and the
  `stepNode` term's reach, so clients do not see β-search
  bounds.

**Choice: Option B (internal bound).**  Rationale: clients of
`foldBTLOnCode` are downstream back-translation machinery
(Stage β Task 14) whose clients should not think about β-search
bounds.  Internally, the bound is derivable: for a fold over a
code `c`, the trace values are bounded by iterating
`stepNode`'s pointwise output upper bound (which in turn is
bounded using `bprod`-based composition of the step output
over the range of prior trace values) `c` times.  Concretely:

* let `leafBound = bprod baseLeaf` over labels in `[0, c]`
  (max of `baseLeaf` over the finite label range dominated by
  `c`);
* let `iterBound = bprod stepNode` iterated `c` times over
  prior-value range up to a growing witness — itself
  computable via composition of `bprod` with a running
  upper-bound tracker.

The construction is an elementary closed-form expression in
`c` using `bprod`, `mulN`, and `expER`; its precise formula is
the implementer's choice subject to domination of the
`Nat.foldBTLOnCode` result.  The outer `boundedRec`'s
`boundedRec_eq_natRec_of_bounded` lemma is then applied
pointwise inside the correctness theorem to eliminate the
truncation.

### foldBTLOnCode semantic specification

```text
(foldBTLOnCode baseLeaf stepNode).interp (cons code ctx) =
  Nat.foldBTLOnCode
    (fun lbl => baseLeaf.interp (Fin.cons lbl ctx))
    (fun a b => stepNode.interp
      (Fin.cons a (Fin.cons b ctx)))
    code
```

### foldBTLOnCode construction sketch

`Nat.foldBTLOnCode` (from `SzudzikSeq.lean`) is a recursive
function defined by parity of the code.  Its ER packaging uses
`boundedRec` over the code size in a tabular form:

1. Construct the internal bound `foldBTLOnCodeBound baseLeaf
   stepNode : ERMor1 (k + 1)` via `bprod`/`mulN` composition
   dominating the fold's trace values.
2. Build a table `T : ℕ → ℕ` where `T j` is the fold result
   for code `j` (for j ≤ input code).
3. `T` is primitive-recursive in j: `T 0 = baseLeaf 0`, and
   `T (j+1)` uses the parity of `j+1` and, if odd, the
   previous fold values at `unpair ((j+1)/2) .1` and
   `unpair ((j+1)/2) .2` — both of which are `< j+1` and thus
   in the already-built table.
4. Use `boundedRec` (with the internal bound from step 1) to
   build T indexed by j, with state being a Gödel β-encoded
   trace of the table values up to j.

Alternatively: directly use `boundedRec` with state being the
current fold result, indexed by the code — but the recursion
tree isn't linear, so a single-state direct recurrence would
not work.  The tabular approach via β is more direct.

**Simplification**: since `boundedRec` already uses β
internally, and the table `T` is itself primitive-recursive in
`j`, we can define `foldBTLOnCode` as a two-layer
`boundedRec`: the outer `boundedRec` iterates j from 0 to
code, building up a β-encoded table; the inner lookup for
`T (unpair .1)` and `T (unpair .2)` uses `β` directly on the
table value.

- [ ] **Step 1: Create `GebLean/Utilities/ERTreeArith.lean`**

```lean
import GebLean.Utilities.ERArith
import GebLean.Utilities.SzudzikSeq
import GebLean.LawvereNatBT

/-!
# ER-Derived BTL Operations

`ERMor1`-level versions of `BTL.encode` (leaf and node cases)
and `BTL.fold`-on-Gödel-code.  Built on the bounded-primitive-
recursion combinator `ERMor1.boundedRec` from
`Utilities/ERArith.lean`.

Used by Stage β Task 14's back-translation in
`GebLean/LawvereNatBTBackTrans.lean`.
-/

namespace GebLean

end GebLean
```

- [ ] **Step 2: Add `ERMor1.btlEncodeLeaf` and
  `ERMor1.btlEncodeNode`**

Inside `namespace GebLean`:

```lean
/-- ER-derived `BTL.encode (BTL.leaf lbl) = 2 * lbl`. -/
def ERMor1.btlEncodeLeaf : ERMor1 1 :=
  ERMor1.natMul.comp
    ![ERMor1.zeroN 1 |>.succ.succ,  -- constant 2
      ERMor1.proj 0]

@[simp] theorem ERMor1.interp_btlEncodeLeaf (lbl : ℕ) :
    (ERMor1.btlEncodeLeaf).interp ![lbl] =
      BTL.encode (BTL.leaf lbl) := by
  unfold ERMor1.btlEncodeLeaf BTL.encode
  simp

/-- ER-derived `BTL.encode (BTL.node l r) = 2 * pair l r + 1`
where `l`, `r` are already Szudzik-encoded subtrees. -/
def ERMor1.btlEncodeNode : ERMor1 2 :=
  ERMor1.succ.comp
    ![ERMor1.natMul.comp
        ![ERMor1.zeroN 2 |>.succ.succ,
          ERMor1.natPair.comp
            ![ERMor1.proj 0, ERMor1.proj 1]]]

@[simp] theorem ERMor1.interp_btlEncodeNode (l r : ℕ) :
    (ERMor1.btlEncodeNode).interp ![l, r] =
      2 * Nat.pair l r + 1 := by
  unfold ERMor1.btlEncodeNode
  simp [Nat.succ_eq_add_one]
```

- [ ] **Step 3: Add `ERMor1.foldBTLOnCodeBound` internal
  helper**

```lean
/-- Internal elementary upper bound on `Nat.foldBTLOnCode`
evaluated with the ER-derived fold over `baseLeaf`/`stepNode`
on code ≤ the counter slot.  Constructed via `bprod` and
`mulN` composition dominating the pointwise trace values.
Used by `ERMor1.foldBTLOnCode` to supply its internal
`boundedRec` bound. -/
def ERMor1.foldBTLOnCodeBound {k : ℕ}
    (baseLeaf : ERMor1 (k + 1))
    (stepNode : ERMor1 (k + 2)) :
    ERMor1 (k + 1) :=
  -- Implementer selects a closed-form ER term dominating the
  -- fold's trace values, using `bprod` for iteration-closure
  -- and `mulN`/`expER` for compositional growth.
  sorry
```

- [ ] **Step 4: Add `ERMor1.foldBTLOnCode`**

The construction uses `boundedRec` with state being a Gödel
β-encoded table of fold values up to the current index and
with the bound supplied internally by `foldBTLOnCodeBound`.
At each step, it looks up prior values via β-extraction and
writes the new fold value using the existing β parameters.

Given the subtlety, the implementer has latitude on the exact
term construction — the correctness theorem is the objective,
not a specific term shape.

```lean
/-- ER-derived fold on a BTL Gödel code.  Simulates
`Nat.foldBTLOnCode` via a β-encoded table built by
`boundedRec`, with the β-search bound supplied internally by
`foldBTLOnCodeBound`.  The 2-argument signature hides the
β-search bound from clients. -/
def ERMor1.foldBTLOnCode {k : ℕ}
    (baseLeaf : ERMor1 (k + 1))
    (stepNode : ERMor1 (k + 2)) :
    ERMor1 (k + 1) :=
  -- Implementer fills in, using `boundedRec` with the
  -- internal bound `foldBTLOnCodeBound baseLeaf stepNode`
  -- plus the β-table construction.
  sorry
```

Budget: ~1 session for the definition and correctness proof.

- [ ] **Step 5: Prove `ERMor1.interp_foldBTLOnCode`**

```lean
@[simp] theorem ERMor1.interp_foldBTLOnCode {k : ℕ}
    (baseLeaf : ERMor1 (k + 1))
    (stepNode : ERMor1 (k + 2))
    (ctx : Fin (k + 1) → ℕ) :
    (ERMor1.foldBTLOnCode baseLeaf stepNode).interp ctx =
      Nat.foldBTLOnCode
        (fun lbl =>
          baseLeaf.interp (Fin.cons lbl (Fin.tail ctx)))
        (fun a b => stepNode.interp
          (Fin.cons a (Fin.cons b (Fin.tail ctx))))
        (ctx 0) := by
  sorry  -- implementer fills in
```

The proof structure mirrors the definition: induction on
`ctx 0` (the code), using the parity-reduction lemmas
`Nat.foldBTLOnCode_zero`, `Nat.foldBTLOnCode_even`,
`Nat.foldBTLOnCode_odd` from `Utilities/SzudzikSeq.lean`.

- [ ] **Step 6: Register module**

Add `import GebLean.Utilities.ERTreeArith` to `GebLean.lean`
(alphabetical position).

- [ ] **Step 7: Create test file**

`GebLeanTests/ERTreeArith.lean`:

```lean
import GebLean.Utilities.ERTreeArith

open GebLean

-- Leaf-encoding sanity
#guard (ERMor1.btlEncodeLeaf).interp ![3] = 6
#guard (ERMor1.btlEncodeLeaf).interp ![0] = 0

-- Node-encoding sanity
#guard (ERMor1.btlEncodeNode).interp ![5, 7] = 2 * Nat.pair 5 7 + 1

-- foldBTLOnCode on a small tree:
-- BTL.encode (BTL.leaf 5) = 10, fold with sum gives 5.
example :
    (ERMor1.foldBTLOnCode
      (ERMor1.proj 0)  -- baseLeaf: just the label
      ERMor1.natAdd).interp ![10] = 5 := by
  simp [Nat.foldBTLOnCode_encode]
  rfl
```

- [ ] **Step 8: Register test module**

`GebLeanTests.lean`: add `import GebLeanTests.ERTreeArith`.

- [ ] **Step 9: Build, test, commit**

```bash
lake build
lake test
git add GebLean/Utilities/ERTreeArith.lean GebLean.lean \
        GebLeanTests/ERTreeArith.lean GebLeanTests.lean
git commit -m "Add ERMor1.foldBTLOnCode via boundedRec with correctness"
```

---

## Self-Review

**Spec coverage:**

* D1 (Wikipedia-literal ERMor1 preserved): every new primitive
  is a derived term, no inductive extension — Tasks 12b, 12c,
  12d, 12e, 12f, 13.
* D2 (Gödel β as witness oracle): Tasks 12c (beta +
  beta_exists), 12e (boundedRec uses search + beta).
* D3 (CRT-based beta_exists proof): Task 12c Step 3.
* D4 (ERArith/ERTreeArith layout): Task 12a rename, Task 13
  recreated ERTreeArith.
* D5 (boundedRec with client-supplied bound, counter + prev
  shape, `min`-truncation semantics): Task 12e definition.
* D6 (correctness by induction + CRT): Task 12e Step 3.  The
  convenience lemma `boundedRec_eq_natRec_of_bounded`
  (Task 12e Step 4) collapses truncation to exact `Nat.rec`
  when the client's bound dominates.
* D7 (showcase applications): Task 12f — each showcase
  supplies its own polynomial bound and applies
  `boundedRec_eq_natRec_of_bounded` in the correctness
  theorem.

**Placeholder scan:**

Tasks 12b Step 3 contains `sorry` placeholders for the
implementer.  Each placeholder is accompanied by implementer
notes describing the proof approach.  Final commits must have
all `sorry`s replaced — this is enforced by the zero-warning
build requirement.

Task 12e Steps 1, 2, 3 contain `sorry` placeholders; all must
be replaced before the Task 12e commit.

Task 12f Step 3 (`factorial`'s bound-adequacy sub-goal) cites
either a mathlib lemma or an inductive argument; the `sorry`
there must be replaced before the Task 12f commit.

Task 13 Steps 3, 4, 5 contain `sorry` placeholders; all must
be replaced before the Task 13 commit.

**Type consistency:**

* `ERMor1.natPair`, `ERMor1.natUnpairFst`,
  `ERMor1.natUnpairSnd`, `ERMor1.natSqrt` from Task 12's
  existing content (used in Task 12c's β definition and
  Task 13's encoding primitives).
* `ERMor1.mulN`, `ERMor1.addN`, `ERMor1.condN`, `ERMor1.leN`,
  `ERMor1.ltN` from Task 12's existing content (used in
  Task 12b's div/mod and downstream).
* `ERMor1.div`, `ERMor1.mod` (Task 12b) used in Task 12c's
  `beta` and Task 12e's `boundedRec`.
* `ERMor1.beta`, `Nat.beta_exists` (Task 12c) used in
  Task 12e's `boundedRec` definition and correctness.
* `ERMor1.boundedSearch`, `boundedSearch_eq_unique`
  (Task 12d) used in Task 12e.
* `ERMor1.boundedRec`, `ERMor1.boundedRec_eq_natRec_of_bounded`
  (Task 12e) used in Task 12f (natAdd/natMul/factorial, each
  of which supplies its own elementary bound) and Task 13
  (foldBTLOnCode, which supplies an internal bound via
  `foldBTLOnCodeBound`).
* `ERMor1.btlEncodeLeaf`, `ERMor1.btlEncodeNode`,
  `ERMor1.foldBTLOnCode` (Task 13) used by Stage β Task 14's
  `NatBTMor1.toER_bt` (downstream, not in this plan).

**Risk flags:**

* `Nat.beta_exists` proof length depends on mathlib coverage.
  Task 12c Step 1 investigation is critical; dispatch as soon
  as implementation begins.
* The β-witness search bound at Task 12e is now derived from
  the client-supplied `bound` parameter rather than from an
  implicit tower-CRT estimate.  This resolves the earlier
  risk flag that unrestricted `natRec` β-witnesses could
  escape E_3: `boundedRec` is always within E_3, since both
  the bound-constrained trace and the bound-derived search
  range are elementary.
* `#guard` tests at Task 12f (factorial 5) may time out due to
  β-search overhead.  Mitigation: reduce test sizes or raise
  `maxHeartbeats` locally.
* Task 12f's showcase bound-adequacy lemmas
  (`natAdd ≤ counter + x + 1`, etc.) must be proved alongside
  the correctness theorems, adding a small amount of
  arithmetic bookkeeping compared to the original `natRec`-
  based showcase.  `omega`, `nlinarith`, and
  `Nat.factorial_le_pow_self` (or inductive variants) dispatch
  these.
* `foldBTLOnCode`'s β-table construction in Task 13 may prove
  intricate.  The internal bound construction via
  `foldBTLOnCodeBound` is an additional sub-term to design.
  If a direct construction is infeasible within the 1-session
  budget, escalate for design review — possible alternative:
  a two-stage definition first via a non-closed-form Lean
  function that uses `Nat.foldBTLOnCode` directly, followed
  by a packaging theorem, rather than an all-in-one ER term.
  Reaching out early is the cheapest path.

---

## Completion criteria

The mini-phase is complete when:

1. `Utilities/ERArith.lean` contains `div`, `mod`, `beta`,
   `Nat.beta_exists`, `boundedSearch`, `boundedRec`,
   `boundedRec_eq_natRec_of_bounded`, `natAdd`, `natMul`,
   `factorial`, each with `@[simp]`-marked correctness
   theorems where applicable (the showcase definitions via
   `boundedRec` are paired with their own bound-adequacy
   lemmas so that the correctness theorems state pure
   `Nat.rec` semantics).
2. `Utilities/ERTreeArith.lean` exists with `btlEncodeLeaf`,
   `btlEncodeNode`, `foldBTLOnCode`, each with `@[simp]`
   correctness.
3. `GebLeanTests/ERArith.lean` and `GebLeanTests/
   ERTreeArith.lean` exist with passing `#guard` assertions.
4. `ERMor1` inductive is definitionally unchanged (7
   Wikipedia generators).
5. `lake build` passes with zero warnings.
6. `lake test` passes.
7. No `sorry`, `admit`, or `Classical` in any code.

After completion, Stage β Task 14 (`NatBTMor1.toER`) becomes
feasible using the new infrastructure.
