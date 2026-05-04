# Option E: Bounded NatBT with ER-on-the-Nose Equivalence

**Goal**: build `LawvereERCat ≃ LawvereNatBTBounded` as a single
on-the-nose categorical equivalence, with a layered API
separating the raw bounded constructors from programmer-friendly
auto-bound combinators.

**Supersedes**:
`2026-04-18-lawvere-natramified-two-stage-design.md` (NatRamified
intermediate, abandoned after analysis showed first-order
ramified recurrence is PR-strength, not E_3).

---

## Architecture

```text
LawvereERCat
   ≃                 (single equivalence, on-the-nose)
LawvereNatBTBounded
   ↑
   Layer 1 combinators (foldBTNatAuto, primRecAuto, ...)
   ↑
   Layer 0 raw constructors (foldBTNat, foldBTBT, boundedNatRec)
   ↑
   Nat-level ER-style helpers
   (Nat.foldBTLOnCodeERStyle, Nat.boundedRecERStyle)
```

The equivalence is at the raw-constructor level; Layer 1
combinators are pure `def`s that emit raw constructors with
auto-derived bounds.  Programmers use Layer 1 (no proof
content); the equivalence is proven once at Layer 0.

---

## Design decisions

### D1.  Bounded constructors at constructor sites

`foldBTNat`, `foldBTBT`, and `boundedNatRec` carry explicit
`bound` parameters.  Interp is total via Option E semantics:
return the trace value when bound is adequate-monotonic, else
some witness-search-fallback value.

**Why**: bounded recursion is the Wikipedia-standard E_3
characterization (Meyer-Ritchie limited primitive recursion).
First-order tier discipline isn't strong enough to reach E_3
(it gives PR or weaker depending on what's allowed in step).
Bounded recursion at the constructor level *is* the
E_3-bounded-by-construction discipline.

### D2.  Option E semantics: mirror ER's witness search at Nat level

The bounded interp clauses delegate to Nat-level helpers
`Nat.foldBTLOnCodeERStyle` and `Nat.boundedRecERStyle` that
mirror `ERMor1.foldBTLOnCode` and `ERMor1.boundedRec`'s
witness-search construction at the Nat level.  These helpers
have the same input/output behavior on every input as the ER
combinators' interp.

A soundness theorem
`ERMor1.interp_foldBTLOnCode_eq_natFoldBTLOnCodeERStyle` (and
analog for boundedRec) connects the two.

**Why**: this makes NatBTBounded.interp = ER.interp on the back-
translated term *on every input* — no off-conditions case-split,
no adequacy hypotheses leaking into the categorical layer.  Stage
5's equivalence becomes mechanical.

### D3.  Layer 1 auto-bound combinators

Pure `def`s that pick adequate-monotonic bounds programmatically
via `towerER ∘ towerHeight(step) ∘ sumCtxER`:

```lean
def NatBTMor1.foldBTNatAuto (baseLeaf stepNode tree) :=
  NatBTMor1.foldBTNat baseLeaf stepNode tree
    (NatBTMor1.deriveTraceBound stepNode)
```

`@[simp]` correctness lemmas reduce these to the structural
`BTL.fold` / `Nat.rec` semantics:

```lean
@[simp] theorem interp_foldBTNatAuto :
    (foldBTNatAuto base step tree).interp ctxN ctxB
      = BTL.fold (...) (...) (tree.interp ...) := ...
```

**Why**: programmers writing `foldBTNatAuto base step tree`
don't see Option E's witness-search machinery.  At the
proof level, `simp` lemmas reduce to clean `BTL.fold` /
`Nat.rec` equations.  The auto-derived bound is adequate-
monotonic by construction (per Phase 4f.2 / Task 14.5-minimal
analysis), so the witness search succeeds, the trace is
returned, and the proof goes through.

### D4.  Naming: keep existing LawvereNatBT* unchanged

The existing `LawvereNatBT*` files (the unbounded "non-
ramified" two-sort theory) are kept under their current
names as a parallel development.  The new bounded theory uses
`LawvereNatBTBounded*` filenames to distinguish them.

**Why**: minimal disruption; no rename required.  The bounded
theory is the equivalent-to-ER one (the canonical "E_3 NatBT"),
but the unbounded theory is also useful for demonstrating the
unbounded-fold escape from E_3.

If renaming is desired later, the swap can be done as a
mechanical pass after the bounded theory ships.

### D5.  Single equivalence; no intermediate category

The bounded NatBT theory IS programmer-friendly via Layer 1
combinators.  No additional ramified intermediate is needed.
Stage 5's equivalence is direct: `LawvereERCat ≃
LawvereNatBTBounded`.

---

## File structure

### New utility files

| File | Role |
|---|---|
| `GebLean/Utilities/NatERStyle.lean` | `Nat.foldBTLOnCodeERStyle`, `Nat.boundedRecERStyle`, plus their soundness theorems linking to ER. |

### New theory files

| File | Role |
|---|---|
| `GebLean/LawvereNatBTBounded.lean` | `BTL` (or import from existing), `NatBTSort`, `NatBTMor1` inductive with bounded constructors, `interp` via Layer 0 helpers, per-constructor `@[simp]` lemmas. |
| `GebLean/LawvereNatBTBoundedQuot.lean` | Quotient, `Category LawvereNatBTBoundedCat`, `HasChosenFiniteProducts`. |
| `GebLean/LawvereNatBTBoundedInterp.lean` | Faithful interp functor `LawvereNatBTBoundedCat ⥤ Type`. |
| `GebLean/LawvereNatBTBounded0.lean` | `m = 0` `FullSubcategory` for the equivalence. |
| `GebLean/LawvereNatBTBoundedAuto.lean` | Layer 1 auto-bound combinators + their `@[simp]` correctness lemmas. |

### Equivalence file

| File | Role |
|---|---|
| `GebLean/LawvereERNatBTBoundedEquiv.lean` | Forward `F : ER → NatBTBounded` (using Layer 1 combinators), back-translation `G : NatBTBounded → ER`, equivalence assembly, transport of Phase 4f non-fullness. |

### Test files

| File | Role |
|---|---|
| `GebLeanTests/LawvereNatBTBounded.lean` | Stage 2-3 tests. |
| `GebLeanTests/LawvereNatBTBoundedAuto.lean` | Stage 4 combinator tests. |
| `GebLeanTests/LawvereERNatBTBoundedEquiv.lean` | Stage 5 round-trip tests. |

### Reuse from existing infrastructure

* `GebLean/LawvereNatBT.lean` — provides `BTL`, `BTL.encode`,
  `BTL.decode`, round-trip lemmas.  Imported by the new theory
  files.
* `GebLean/Utilities/ERArith.lean` — provides
  `ERMor1.boundedRec`, `interp_boundedRec_of_bounded`.
* `GebLean/Utilities/ERTreeArith.lean` — provides
  `ERMor1.foldBTLOnCode`, `interp_foldBTLOnCode_of_bounded`.
* `GebLean/LawvereERBoundComputable.lean` — provides
  `ERMor1.towerHeight`, `towerER`, `sumCtxER`, `towerBound`.

---

## Stage layout

* **Stage 1**: Layer 0 — `Nat.foldBTLOnCodeERStyle`,
  `Nat.boundedRecERStyle`, soundness theorems.
* **Stage 2**: Bounded NatBT inductive + interp + simp lemmas.
* **Stage 3**: Quotient + Category + products + interp functor +
  `m = 0` subcategory.
* **Stage 4**: Layer 1 auto-bound combinators + `@[simp]`
  correctness lemmas.
* **Stage 5**: `LawvereERCat ≃ LawvereNatBTBounded` equivalence.
* **Stage 6**: Phase 4f transport + tests + tracker.

---

## Risks

* **Stage 1's soundness theorems**: the existing
  `interp_foldBTLOnCode_of_bounded` covers the adequate case;
  we additionally need the off-conditions case (search returns
  sentinel ⇒ specific Gödel-arithmetic fallback value).  The
  proof traces the existing theorem's β-witness-search analysis
  but unconditionally — non-trivial but tractable.
* **Stage 4's `deriveTraceBound`**: requires `towerHeight` and
  `towerER` machinery from `LawvereERBoundComputable.lean`;
  also requires the back-translation `toERUniform` since
  `towerHeight` is on ER terms, not NatBT terms.  Resolution:
  derive bound at the NatBT level by mirroring `towerHeight`'s
  recursion structure on NatBT (without going through
  `toERUniform`).
* **Stage 5's natural-iso**: should be mechanical given Layer 0
  soundness, but depends on Layer 1's correctness lemmas
  reducing cleanly under `simp`.

---

## Completion criteria

1. Stage 1 helpers + soundness theorems committed.
2. Stage 2 inductive + interp + simp lemmas committed.
3. Stage 3 categorical machinery committed; interp functor
   faithful.
4. Stage 4 combinators + `@[simp]` correctness lemmas committed.
5. Stage 5 `LawvereERCat ≃ LawvereNatBTBounded` equivalence
   proved on-the-nose.
6. Stage 6 Phase 4f transported; tests pass; tracker updated.
7. All builds clean (zero warnings); all tests pass.
