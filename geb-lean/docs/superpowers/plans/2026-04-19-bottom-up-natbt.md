# Bottom-Up NatBT Implementation Plan

> Use `superpowers:subagent-driven-development` to execute
> task-by-task.

**Design spec**:
`docs/superpowers/specs/2026-04-19-bottom-up-natbt-design.md`.

**Supersedes**:
`docs/superpowers/plans/2026-04-18-option-e-bounded-natbt.md`.

---

## Project rules (from CLAUDE.md)

* `lake build` and `lake test` after every change.  Never `lake
  clean` or `lake env lean`.
* Zero warnings; no `sorry` / `admit` / `Classical` /
  `noncomputable` / `axiom`.  80-char lines.
* Forbidden words in persistent writing: fundamental, actually,
  key, insight, core, advanced, complex, complicated, simple,
  advantage, benefit, important, challenge, yes, wait, hmm,
  sorry, careful, difficult, blocked, incomplete, future, issue,
  problem, block.
* `Co-Authored-By: Claude Opus 4.7 (1M context)
  <noreply@anthropic.com>` trailer on every commit.

---

## Phase A: drop `@[reducible]` from ℕ-aliased category defs

### Task A.1: Edit four files

Files to modify, each with the `@[reducible] def := ℕ` form:

* `GebLean/LawvereERQuot.lean` line 143: `LawvereERCat`.
* `GebLean/LawvereBTQuot.lean` line 145: `LawvereBTQuotCat`.
* `GebLean/LawvereBT.lean` line 2043: `LawvereBTCat`.
* `GebLean/LawvereTreeERQuot.lean` line 159: `LawvereTreeERCat`.

Drop the `@[reducible]` attribute.  Keep the `def Foo := ℕ` body.

### Task A.2: Build and fix breakage

Run `lake build`; fix any errors.  Common patterns that may break:

* Code that did `(n : LawvereERCat) + 1` (relying on ℕ-arithmetic
  through reduction).  Fix: cast explicitly via `(n : ℕ)`.
* `decide` or `simp` calls that needed reducibility to unfold.
  Fix: explicit unfolds via `show` / `change`.

If breakage is extensive (e.g., > 20 fixes), report a
`DONE_WITH_CONCERNS` describing the scope; we may revert and use
`@[irreducible]` instead.

### Task A.3: Build, test, commit

```bash
lake build && lake test
git add (modified files)
git commit -m "Make Lawvere category aliases non-reducible"
```

---

## Phase C: `LawvereNatBTV2.lean` — inductive + toER + interp

### Task C.1: File skeleton + import inventory

Create `GebLean/LawvereNatBTV2.lean`.  Inventory the named ER
implementations to be referenced:

* `Utilities/ERArith.lean`: `addN`, `mulN`, `boundedRec`,
  `ERMor1.zeroN`, `ERMor1.oneN`, etc.
* `Utilities/ERTreeArith.lean`: `btlEncodeLeaf`, `btlEncodeNode`,
  `foldBTLOnCode`, `twoN`, etc.
* `Utilities/SzudzikSeq.lean`: encoding helpers.
* `LawvereERBoundComputable.lean`: `towerHeight`, `towerER`,
  `sumCtxER`, `towerBound`.

Header docstring should note: this is the bottom-up NatBT
theory.  Each constructor has a named ER implementation; interp
is derived via `(toER).interp`.

### Task C.2: `BTL` and `NatBTSort` reuse

Decide: import from existing `LawvereNatBT.lean`, or extract to
a utility file.

Recommendation: add `import GebLean.LawvereNatBT` and reuse the
existing `BTL`, `NatBTSort` types directly.  No copy.

### Task C.3: `NatBTMor1` inductive (foundational constructors)

Define the NatBT inductive with the foundational ER-direct
constructors: `zero`, `succ`, `natProj`, `sub`, `compNat`,
`bsum`, `bprod`.  These are the 7 ER generators lifted into
two-sort form.  No BT-related constructors yet.

Build, commit `Define LawvereNatBTV2 inductive (ER-direct
constructors)`.

### Task C.4: Add BT structural constructors

Extend the inductive with: `leafBT`, `nodeBT`, `btProj`,
`compBT`, `encodeBT`, `decodeBT`.  Each maps to a named ER
implementation:

* `leafBT` → `ERMor1.btlEncodeLeaf`.
* `nodeBT` → `ERMor1.btlEncodeNode`.
* `btProj`, `encodeBT`, `decodeBT` → identity at the encoded
  level (the BT slots are encoded as ℕ in the ER side).

Build, commit `Add BT structural constructors to LawvereNatBTV2`.

### Task C.5: Add bounded recursive constructors

Extend the inductive with: `foldBTNat`, `foldBTBT`,
`boundedNatRec`.  Each takes a `bound` parameter and maps to a
named ER implementation:

* `foldBTNat` → `ERMor1.foldBTLOnCode`.
* `foldBTBT` → `ERMor1.foldBTLOnCode` (with sort-aware decoding
  at interp).
* `boundedNatRec` → `ERMor1.boundedRec`.

Build, commit `Add bounded recursive constructors to
LawvereNatBTV2`.

### Task C.6: `NatBTMor1.toER` definition

Define `toER : NatBTMor1 nm σ → ERMor1 (nm.1 + nm.2)`
structurally.  Each constructor maps to its named ER
implementation, with appropriate slot permutations.

`foldBTBT` requires careful slot reordering: ER's
`foldBTLOnCode`'s `stepNode` puts β-extracted prev values at
slots 0-1; NatBT's structural slot order puts BT context slots
at the end.  Insert a permutation via `comp` + `proj`.

Build, commit `Add NatBTMor1.toER structural translation`.

### Task C.7: `NatBTMor1.interp` derived from `toER`

```lean
def NatBTMor1.interp {nm : ℕ × ℕ} {σ : NatBTSort}
    (t : NatBTMor1 nm σ)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    σ.carrier :=
  let combinedCtx : Fin (nm.1 + nm.2) → ℕ :=
    Fin.append ctxN (fun i => (ctxB i).encode)
  let v := t.toER.interp combinedCtx
  match σ with
  | .nat => v
  | .bt => BTL.decode v
```

Per-constructor `@[simp]` lemmas: each gives the structural
form of interp (e.g., `interp_zero = 0`,
`interp_succ x = (interp x) + 1`).  Each lemma's proof unfolds
`toER` for that constructor and uses ER's interp simp set.

Build + test, commit `Add NatBTMor1.interp via toER plus simp
lemmas`.

---

## Phase D: quotient + category + products + interp functor

### Task D.1: Tuples + quotient

Create `GebLean/LawvereNatBTV2Quot.lean` mirroring the existing
`LawvereNatBTQuot.lean` for the new inductive.

Build, commit.

### Task D.2: `Category` instance + `HasChosenFiniteProducts`

In the same file.  Standard categorical machinery.

Build + test, commit.

### Task D.3: Interp functor

Create `GebLean/LawvereNatBTV2Interp.lean` with
`natBTV2InterpFunctor : LawvereNatBTV2Cat ⥤ Type`, prove
`Faithful`.

Build + test, commit.

---

## Phase E: equivalence

### Task E.1: Forward functor `F : LawvereERCat ⥤ LawvereNatBTV2Cat`

Create `GebLean/LawvereERNatBTV2Equiv.lean`.  Define
`ERMor1.toNatBTV2 : ERMor1 n → NatBTMor1 (n, 0) .nat` mapping
each ER constructor to its NatBT analog.  Lift to tuples,
quotient, define functor.

Build + test, commit.

### Task E.2: Back functor `G : LawvereNatBTV2Cat ⥤ LawvereERCat`

Use `NatBTMor1.toER` from Task C.6.  At the morphism level
(`(n, 0)` arity restriction for now): each NatBTMorN at `(n, 0)
(m, 0)` lifts to `ERMorN n m` via componentwise `toER`.

Build + test, commit.

### Task E.3: Equivalence assembly

Prove `F ∘ G ≃ id` and `G ∘ F ≃ id` extensionally.  Both reduce
to interp-agreement, which holds by construction (interp is
defined via `toER`).

Build + test, commit.

---

## Phase F: Layer 1 + tests + tracker

### Task F.1: Layer 1 combinators (initial set)

Add `foldBTNatAuto`, `boundedNatRecAuto` etc. as `def`s with
auto-derived bounds via `towerER ∘ towerHeight`.  Each comes
with an `@[simp]` correctness lemma reducing to clean
structural semantics.

Build + test, commit.

### Task F.2: Test suite

Create `GebLeanTests/LawvereNatBTV2.lean` and
`GebLeanTests/LawvereERNatBTV2Equiv.lean` with `#guard`s
exercising each layer.

Build + test, commit.

### Task F.3: Tracker update

Update `.session/workstreams/lawvere-elementary-recursive.md`
with completion of Phases A, C, D, E, F.

Build, commit.

---

## Completion criteria

1. Phase A: aliases non-reducible; build clean.
2. Phase C: `LawvereNatBTV2.lean` with all constructors,
   `toER`, derived `interp`, simp lemmas.
3. Phase D: categorical machinery + faithful interp functor.
4. Phase E: `LawvereERCat ≃ LawvereNatBTV2Cat` proved on the
   nose.
5. Phase F: Layer 1 combinators + tests + tracker.
6. All builds clean; all tests pass.
