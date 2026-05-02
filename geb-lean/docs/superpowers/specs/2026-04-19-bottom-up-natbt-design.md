# Bottom-Up NatBT Design

**Goal**: build a programmer-friendly two-sort NatBT category as
a strict extension of `LawvereERCat`, where every new constructor
has a pre-built named ER implementation and the categorical
equivalence with `LawvereERCat` is preserved by construction.

**Supersedes**: `2026-04-18-option-e-bounded-natbt-design.md`
(top-down design that kept hitting "this constructor isn't
back-translatable" obstructions).

---

## Architecture

```text
LawvereERCat ≃ LawvereNatBTCat   (equivalence by construction)
                  ↑
                  Each constructor has a named ER implementation;
                  the back-translation is a case-split lookup.
```

Both directions of the equivalence are direct:

* Forward `F : ER → NatBT`: each ER constructor maps to its NatBT
  analog (zero → zero, succ → succ, etc.).
* Back `G : NatBT → ER`: each NatBT constructor maps to its named
  ER implementation.

The equivalence holds on the nose because every NatBT constructor
IS a named ER expression — interp matches definitionally.

---

## Design discipline

### D1.  ER implementations come first

Before adding a constructor `c` to the NatBT inductive, an ER
term `c_impl : ERMor1 (computed_arity)` must already exist as a
named `def` in the codebase, with proven semantic properties.

If we can't write `c_impl`, we don't add `c`.  This forces the
NatBT theory to stay within ER's expressive power by
construction; we never design around an obstruction we then
can't implement.

### D2.  `interp` is derived, not parallel

`NatBTMor1.interp` is defined as `(t.toER).interp combinedCtx`
with sort-aware decoding.  No parallel Nat-level helpers; no
soundness theorems linking parallel constructions.  Interp goes
through ER directly.

`toER : NatBTMor1 nm σ → ERMor1 (nm.1 + nm.2)` is defined
structurally (no interp dependency).  BT context slots are
encoded as ℕ slots in the wider ER arity.

### D3.  Aliases are non-reducible

`LawvereERCat`, `LawvereBTQuotCat`, `LawvereBTCat`,
`LawvereTreeERCat` lose their `@[reducible]` attribute.  They
remain `def := ℕ` for the carrier, but Lean no longer unifies
them with each other through reduction.  This eliminates the
typeclass conflict that previously required a `LawvereERWrap`
workaround.

### D4.  Programmer-friendly = ER + named extensions

The NatBT category is `LawvereERCat` plus additional named
constructors for two-sort programming convenience.  No
"different category" — just ER with a richer surface vocabulary.
Mathematically the same; syntactically more ergonomic.

### D5.  Layer 1 is incremental

After the basic equivalence ships, additional combinators
(auto-bound folds, recursion patterns, etc.) can be added
incrementally — each one is a `def` over the existing surface,
backed by ER, with `@[simp]` correctness lemmas reducing to
clean structural semantics.  The category itself is stable; the
combinator library grows.

---

## File structure

### Modified files

| File | Change |
|---|---|
| `GebLean/LawvereERQuot.lean` | Drop `@[reducible]` from `LawvereERCat`. |
| `GebLean/LawvereBTQuot.lean` | Drop `@[reducible]` from `LawvereBTQuotCat`. |
| `GebLean/LawvereBT.lean` | Drop `@[reducible]` from `LawvereBTCat`. |
| `GebLean/LawvereTreeERQuot.lean` | Drop `@[reducible]` from `LawvereTreeERCat`. |

Anything that breaks is fixed in-place.  Expectation: minimal
breakage since the reducibility was used incidentally, not
load-bearing.

### New files

| File | Role |
|---|---|
| `GebLean/LawvereNatBTV2.lean` | `BTL`, `NatBTSort`, `NatBTMor1` inductive (full set of constructors), `toER` defined structurally, `interp` derived via `(toER).interp`, per-constructor `@[simp]` lemmas. |
| `GebLean/LawvereNatBTV2Quot.lean` | Quotient, `Category LawvereNatBTV2Cat`, `HasChosenFiniteProducts`. |
| `GebLean/LawvereNatBTV2Interp.lean` | Faithful interp functor `LawvereNatBTV2Cat ⥤ Type`. |
| `GebLean/LawvereERNatBTV2Equiv.lean` | Forward `F : LawvereERCat ⥤ LawvereNatBTV2Cat`, back `G : LawvereNatBTV2Cat ⥤ LawvereERCat`, equivalence assembly. |

### Test files

| File | Role |
|---|---|
| `GebLeanTests/LawvereNatBTV2.lean` | Phase C-D tests. |
| `GebLeanTests/LawvereERNatBTV2Equiv.lean` | Equivalence round-trip tests. |

### Reuse

* `BTL` and `NatBTSort` are extracted from the existing
  `LawvereNatBT.lean` (the unbounded theory) — either via
  import or by a small refactor moving them to a utility file.
  Decided during Phase C.
* The existing unbounded `LawvereNatBT*` files remain as a
  parallel development.  Renaming is deferred.

### Naming note

Files use the `V2` suffix to avoid clashing with the existing
`LawvereNatBT*` files during development.  After the equivalence
ships, the naming can be re-evaluated (e.g., promoting `V2` to
the canonical name and renaming the existing files to
`LawvereNatBTUnramified*`).

---

## Phase layout

* **Phase A** (1-3 tasks): housekeeping — drop `@[reducible]`
  from the four ℕ-aliased Lawvere categories; fix any breakage.
* **Phase B** (already done): revert the Option E scaffolding.
* **Phase C** (4-6 tasks): build `LawvereNatBTV2.lean` —
  inductive, structural `toER`, derived `interp`, per-constructor
  `@[simp]` lemmas.  Each constructor's `toER` references a
  named ER implementation already in the codebase.
* **Phase D** (3-4 tasks): quotient, category, products, interp
  functor.
* **Phase E** (3-4 tasks): equivalence — forward functor (direct
  lift of ER constructors), back functor (case-split on
  constructors, look up `toER`), equivalence assembly (trivial
  by construction).
* **Phase F** (2-3 tasks): Layer 1 combinators (incremental, as
  needed) + tests + tracker.

---

## Risks

* **Phase A breakage scope**: removing `@[reducible]` may
  surface code paths that depended on definitional unfolding.
  If extensive, may need `@[irreducible]` instead, or wrapping
  in `structure`s.  Expect minor breakage, not major.
* **Phase C `toER` for `foldBTBT` slot ordering**: ER's
  `foldBTLOnCode` puts the β-extracted previous values at slots
  0-1 of `stepNode`; NatBT's structural slot order puts BT
  context slots at the END (after ℕ slots).  `toER` will need
  to compose with a permutation to align.  Mechanical but
  verbose.
* **Equivalence proofs**: by construction trivial in spirit, but
  the interp-equality proofs require careful unfolding of `toER`
  through each constructor.  Should be clean since interp is
  defined as `(toER).interp`.

---

## Completion criteria

1. Phase A: all four `@[reducible]` removed; build clean.
2. Phase C: `LawvereNatBTV2.lean` complete with all constructors,
   `toER`, `interp`, `@[simp]` lemmas; build clean.
3. Phase D: categorical machinery; interp functor faithful.
4. Phase E: `LawvereERCat ≃ LawvereNatBTV2Cat` proved on the nose.
5. Phase F: Layer 1 combinators + tests + tracker updated.
6. All builds clean; all tests pass.

---

## Why this works

Every NatBT constructor we add MUST have a corresponding named
ER implementation.  The functor `G : NatBT → ER` is then a
syntactic case-split that returns the named implementation.
The functor `F : ER → NatBT` is the obvious lift.  By
construction, `(F (G (t))).interp = t.interp` (since interp goes
through `toER`, and `toER (F (t)) = some lift of t` whose interp
matches), and similarly `(G (F (e))).interp = e.interp`.

There is no design space for "what NatBT should expose" — there
is only the space of ER terms, and we expose the ones we find
useful.  The categorical equivalence is preserved at every
incremental step because we only ever add constructors that ARE
ER expressions.
