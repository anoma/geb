# LawvereNatRamified Two-Stage Equivalence: Design

**Goal**: build `LawvereERCat ≃ LawvereNatBTRamified` via the
clean intermediate `LawvereNatRamified` (Nat-only, tier-disciplined
fold, no bounded intermediate).

**Supersedes**:
`2026-04-18-lawvere-natbt-two-stage-design.md` (bounded
intermediate, abandoned after design analysis identified
irreducible impedance mismatch with ER's witness-search
fallback).

---

## Architecture

```text
LawvereERCat
   ≃         (Stage B: bound-derivation in back-translation)
LawvereNatRamified
   ≃         (Stage D: BT.encode/decode in back-translation)
LawvereNatBTRamified
```

Both equivalences are constructive, on-the-nose, with no
adequacy hypotheses leaking into the categorical layer.

---

## Design decisions

### D1.  No user-supplied bounds

Neither intermediate exposes bound parameters at constructor
sites.  `foldMutNat` and `foldMutBT` use unbounded `Nat.rec` and
`BTL.fold` respectively.  Bounds appear only inside
back-translation functions, where they are constructed
programmatically from `towerHeight` of the step term.

**Why**: user-supplied bounds force the theory to define
semantics off-conditions (when bound is inadequate), and that
off-condition value must agree with ER's witness-search
fallback (which is genuinely garbage).  No clean choice exists.
Eliminating user-supplied bounds eliminates the off-conditions
case entirely.

### D2.  Tier discipline

Each ramified theory carries a `Tier` index (`NonRec` or
`MayRec`) on its morphism inductive.  Recursive constructors
(`foldMutNat`, `foldMutBT`) have `MayRec` tier.  Recursive
sub-arguments (the `step`) must be tier `NonRec`, ensuring step
functions are non-recursive primitives.  Composition uses
`Tier.max` to propagate.

**Why**: this is Leivant's tier-2 ramified recurrence.  Without
tier discipline, nested folds give `step` whose `towerHeight`
is unbounded — escapes E_3 — and back-translation fails (no
ER bound exists).  Tier discipline guarantees `towerHeight(step)`
is a fixed structural quantity, so the back-translation's
`siteBound = towerER ∘ towerHeight(step)` is ER-expressible
and adequate-monotonic by construction.

### D3.  Two intermediate theories

`LawvereNatRamified` (Nat-sort only) and `LawvereNatBTRamified`
(adds BT sort) are separated.  Two equivalences chain into the
final result.

**Why**: each stage handles exactly one orthogonal change:

* Stage B handles "add ramified fold" (introduces `Nat.rec`-style
  recursion alongside ER's `bsum`/`bprod`).
* Stage D handles "add BT sort" (introduces structural BT ops and
  the `BTL.encode`/`decode` bridge).

Each back-translation has a smaller invariant.  Stage B's
back-translation deals only with `Nat.rec`-ish unfolding;
Stage D's deals only with BTL Gödel encoding.  Each is
independently auditable.

A single direct equivalence (`ER ≃ NatBTRamified`) is also
viable but conflates the two concerns into one larger
back-translation.

### D4.  Reuse existing infrastructure

* `ERMor1.boundedRec` and `ERMor1.foldBTLOnCode` (from
  `Utilities/ERArith.lean` and `Utilities/ERTreeArith.lean`)
  serve as the back-translation targets.
* `ERMor1.towerHeight`, `ERMor1.towerER`, `ERMor1.towerBound`
  (from `LawvereERBoundComputable.lean`) provide the
  bound-derivation primitives.
* `BTL`, `BTL.encode`, `BTL.decode`,
  `BTL.decode_encode` / `BTL.encode_decode` (from existing
  `LawvereNatBT.lean`, kept and renamed to
  `LawvereNatBTUnramified.lean` as a final cleanup pass) provide
  the encoding bridge for Stage D.

### D5.  Existing two-sort theory: rename, not delete

The existing `LawvereNatBT*` files (the non-ramified two-sort
theory escaping E_3) are kept as a "parallel development"
documenting the failure mode that motivated the ramified design.
They are renamed to `LawvereNatBTUnramified*` in a final
cleanup pass after the new equivalence chain is built and
tested.

---

## Stage A: `LawvereNatRamified` definition

New files:

| File | Role |
|---|---|
| `GebLean/LawvereNatRamified.lean` | `Tier`, `NatRamifiedMor1` inductive, `interp`, per-constructor `@[simp]` lemmas. |
| `GebLean/LawvereNatRamifiedQuot.lean` | `NatRamifiedMorN`, quotient, `Category`, `HasChosenFiniteProducts`. |
| `GebLean/LawvereNatRamifiedInterp.lean` | Faithful interp functor `LawvereNatRamifiedCat ⥤ Type`. |
| `GebLeanTests/LawvereNatRamified.lean` | Stage A tests. |

Inductive sketch:

```lean
inductive Tier : Type
  | nonRec | mayRec
  deriving DecidableEq, Repr, Inhabited

def Tier.max : Tier → Tier → Tier := ...

inductive NatRamifiedMor1 :
    (n : ℕ) → Tier → Type
  | zero {n : ℕ} : NatRamifiedMor1 n .nonRec
  | succ {n : ℕ} : NatRamifiedMor1 (n + 1) .nonRec
  | proj {n : ℕ} (i : Fin n) : NatRamifiedMor1 n .nonRec
  | sub {n : ℕ} : NatRamifiedMor1 (n + 2) .nonRec
  | add {n : ℕ} : NatRamifiedMor1 (n + 2) .nonRec
  | mul {n : ℕ} : NatRamifiedMor1 (n + 2) .nonRec
  | comp {a b : ℕ} {t1 t2 : Tier}
      (f : NatRamifiedMor1 b t1)
      (g : Fin b → NatRamifiedMor1 a t2) :
      NatRamifiedMor1 a (Tier.max t1 t2)
  | natMatch {n : ℕ} {t1 t2 : Tier}
      (zeroCase : NatRamifiedMor1 n t1)
      (succCase : NatRamifiedMor1 (n + 2) t2)
      (k : NatRamifiedMor1 (n + 1) .nonRec) :
      NatRamifiedMor1 (n + 1) (Tier.max t1 t2)
  | foldMutNat {n : ℕ} {tb : Tier}
      (base : NatRamifiedMor1 n tb)
      (step : NatRamifiedMor1 (n + 2) .nonRec)
      (k : NatRamifiedMor1 n .nonRec) :
      NatRamifiedMor1 n .mayRec
```

Interp uses `Nat.rec` directly; total; no off-conditions.

---

## Stage B: `LawvereERCat ≃ LawvereNatRamified`

New files:

| File | Role |
|---|---|
| `GebLean/LawvereERNatRamifiedEquiv.lean` | Forward functor, back-translation with `siteBound`, equivalence assembly. |

Forward `F : ER → NatRamified`:

```lean
| ERMor1.zero => NatRamifiedMor1.zero
| ERMor1.succ => NatRamifiedMor1.succ
| ERMor1.proj i => NatRamifiedMor1.proj i
| ERMor1.sub => NatRamifiedMor1.sub
| ERMor1.comp f g => NatRamifiedMor1.comp f.toRamified
    (fun i => (g i).toRamified)
| ERMor1.bsum f =>
    -- bsum f n = sum_{i<n} f(i, ctx) via foldMutNat
    NatRamifiedMor1.foldMutNat
      NatRamifiedMor1.zero
      (NatRamifiedMor1.add.comp ![f.toRamified.comp
        ![NatRamifiedMor1.proj 0, ...projN+1...],
        NatRamifiedMor1.proj 1])
      (NatRamifiedMor1.proj 0)
| ERMor1.bprod f =>
    -- bprod f n = prod_{i<n} f(i, ctx) via foldMutNat with mul/1
    ...
```

Back-translation `G : NatRamified → ER`:

```lean
| NatRamifiedMor1.zero => ERMor1.zero
| NatRamifiedMor1.succ => ERMor1.succ
...
| NatRamifiedMor1.add =>
    -- add a b = bsum_{i<b} 1 + a -- expressible
    ERMor1.comp ERMor1.bsum (...)
| NatRamifiedMor1.mul =>
    -- mul a b = bsum_{i<b} a -- expressible via bsum
    ERMor1.comp ERMor1.bsum (...)
| NatRamifiedMor1.foldMutNat base step k =>
    -- Use boundedRec with siteBound
    let b := step.toER.siteBound k.toER  -- adequate-monotonic
    ERMor1.boundedRec base.toER step.toER b
| NatRamifiedMor1.natMatch zc sc k =>
    -- one-level pattern: k = 0 or k = succ k', via boundedRec
    -- with bound = max(zc.bound, sc.bound).siteBound
    ...
```

Where `siteBound : ERMor1 (k+1)` for a step `s : ERMor1 (k+2)`
is constructed via `towerER (s.towerHeight)` composed with
`sumCtxER + 2` to ensure pointwise adequacy plus monotonicity.

Correctness theorems by structural induction; both directions
preserve interp on the nose (using
`interp_boundedRec_of_bounded` discharge for the `foldMutNat`
case).

---

## Stage C: `LawvereNatBTRamified` definition

New files:

| File | Role |
|---|---|
| `GebLean/LawvereNatBTRamified.lean` | `NatBTSort`, `NatBTRamifiedMor1` inductive, `interp`, simp lemmas. |
| `GebLean/LawvereNatBTRamifiedQuot.lean` | Quotient, category, products. |
| `GebLean/LawvereNatBTRamifiedInterp.lean` | Faithful interp functor. |
| `GebLeanTests/LawvereNatBTRamified.lean` | Tests. |

Reuses `BTL` from `LawvereNatBT.lean` (renamed to
`LawvereNatBTUnramified.lean` in cleanup).

Inductive extends `LawvereNatRamified`'s pattern with two-sort
indexing `(n, m) : ℕ × ℕ` and adds:

```lean
  | leafBT {nm : ℕ × ℕ} :
      NatBTRamifiedMor1 (nm.1 + 1, nm.2) .bt .nonRec
  | nodeBT {nm : ℕ × ℕ} :
      NatBTRamifiedMor1 (nm.1, nm.2 + 2) .bt .nonRec
  | btProj {nm : ℕ × ℕ} (i : Fin nm.2) :
      NatBTRamifiedMor1 nm .bt .nonRec
  | btMatch {nm σ t1 t2}
      (leafCase : NatBTRamifiedMor1 (nm.1 + 1, nm.2) σ t1)
      (nodeCase : NatBTRamifiedMor1 (nm.1, nm.2 + 2) σ t2)
      (tree : NatBTRamifiedMor1 nm .bt .nonRec) :
      NatBTRamifiedMor1 nm σ (Tier.max t1 t2)
  | foldMutBT {nm σ tb ts}
      (base : NatBTRamifiedMor1 (nm.1 + 1, nm.2) σ tb)
      (step : NatBTRamifiedMor1 (nm.1, nm.2 + 2) σ .nonRec)
      (tree : NatBTRamifiedMor1 nm .bt ts) :
      NatBTRamifiedMor1 nm σ .mayRec
  | encodeBT {nm} (t : NatBTRamifiedMor1 nm .bt _) :
      NatBTRamifiedMor1 nm .nat _
  | decodeBT {nm} (k : NatBTRamifiedMor1 nm .nat _) :
      NatBTRamifiedMor1 nm .bt _
```

Interp uses `BTL.fold` directly for `foldMutBT`; total.

---

## Stage D: `LawvereNatRamified ≃ LawvereNatBTRamified`

New files:

| File | Role |
|---|---|
| `GebLean/LawvereNatRamifiedNatBTRamifiedEquiv.lean` | Forward inclusion + back-translation via `BTL.encode`/`decode` + equivalence. |

Forward `H : NatRamified → NatBTRamified`: structural inclusion
sending object `n` to `(n, 0)`, each Nat-only constructor to its
NatBT counterpart.

Back-translation `K : NatBTRamified → NatRamified` (restricted
to `(n, 0)` objects, i.e., the m=0 subcategory):

* `leafBT`/`nodeBT`/`btProj`/`btMatch`/`foldMutBT` translate via
  `BTL.encode`/`decode` round-trip.  E.g., `foldMutBT base step
  tree` becomes `NatRamifiedMor1.foldMutNat (toRamified base
  encoded) (toRamified step encoded) (toRamified (encode tree))`.
* `encodeBT`/`decodeBT` become identities (since the Nat
  representation already encodes BT structure).

Stage D's equivalence holds at the m=0 subcategory; for general
(n, m) → (n', m') morphisms, the equivalence requires a
Szudzik-pack object iso (analogous to the original plan's Task
16).  This sub-detail can ship after the main chain.

---

## Stage E: Compose and finalize

| File | Role |
|---|---|
| `GebLean/LawvereERNatBTRamifiedEquiv.lean` | Composed chain `LawvereERCat ≃ LawvereNatBTRamified`, transport of Phase 4f non-fullness. |

Plus tracker update and final rename pass:

```bash
git mv GebLean/LawvereNatBT.lean GebLean/LawvereNatBTUnramified.lean
# ... update imports
```

---

## Risks and open issues

* **Stage B's `bsum`/`bprod` translation**: needs careful
  formula.  `bsum f n = Nat.rec 0 (fun i prev => prev + f(i,
  ctx)) n` — straightforward but requires plumbing the context
  correctly across the `comp`.
* **Stage D's general (n, m) handling**: deferred to a
  sub-detail; main chain works at m=0.
* **Tier-discipline preservation under composition**: requires
  `Tier.max` to behave correctly across nested `comp`/`natMatch`
  /`btMatch`.  Standard but tedious.
* **Build performance**: the existing
  `LawvereERBoundComputable.lean` builds slowly due to
  heartbeat-bound proofs.  New work should keep individual
  theorems under the default heartbeat where possible.

---

## Completion criteria

1. Stage A: `LawvereNatRamified` defined, builds clean,
   interp functor faithful.
2. Stage B: `LawvereERCat ≃ LawvereNatRamified` proved.
3. Stage C: `LawvereNatBTRamified` defined, builds clean.
4. Stage D: `LawvereNatRamified ≃ LawvereNatBTRamified` proved
   at m=0 subcategory.
5. Stage E: Composed `LawvereERCat ≃ LawvereNatBTRamified`
   proved; Phase 4f non-fullness transported.
6. All tests pass; `lake build` clean; tracker updated;
   `LawvereNatBT*` renamed to `LawvereNatBTUnramified*`.
