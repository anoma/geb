# T5 — categorical equivalence `LawvereERCat ≌ LawvereKSimDCat 2`

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [1 Scope and goal](#1-scope-and-goal)
- [2 Inputs and prerequisites](#2-inputs-and-prerequisites)
- [3 File layout](#3-file-layout)
- [4 Public API surface](#4-public-api-surface)
  - [4.1 T5-A: extensions to `ErToKFunctor.lean`](#41-t5-a-extensions-to-ertokfunctorlean)
  - [4.2 T5-B: contents of `Equivalence.lean` (round-trips)](#42-t5-b-contents-of-equivalencelean-round-trips)
  - [4.3 T5-C: contents of `Equivalence.lean` (packaging)](#43-t5-c-contents-of-equivalencelean-packaging)
  - [4.4 Naming rationale](#44-naming-rationale)
- [5 Step decomposition](#5-step-decomposition)
- [6 Proof shapes](#6-proof-shapes)
  - [6.1 `erToKFunctor_map_interp`](#61-ertokfunctor_map_interp)
  - [6.2 `erToKFunctor_comp_kInterpFunctor`](#62-ertokfunctor_comp_kinterpfunctor)
  - [6.3 `erToKFunctor_comp_kToERFunctor`](#63-ertokfunctor_comp_ktoerfunctor)
  - [6.4 `kToERFunctor_comp_erToKFunctor`](#64-ktoerfunctor_comp_ertokfunctor)
  - [6.5 `erToKKToErIso` and `kToErErToKIso`](#65-ertokktoeriso-and-ktoerertokiso)
  - [6.6 `erKSimEquiv`](#66-erksimequiv)
  - [6.7 `IsEquivalence` instances](#67-isequivalence-instances)
- [7 Axiom budget](#7-axiom-budget)
- [8 Test plan](#8-test-plan)
- [9 Scope guardrails](#9-scope-guardrails)
- [10 Implementation operational notes](#10-implementation-operational-notes)
- [11 Adversarial-review punch list](#11-adversarial-review-punch-list)
  - [11.1 Mathlib upstream guides honoured](#111-mathlib-upstream-guides-honoured)
  - [11.2 Mirror-precedent faithful](#112-mirror-precedent-faithful)
  - [11.3 Faithfulness chain sound](#113-faithfulness-chain-sound)
  - [11.4 Citations complete](#114-citations-complete)
  - [11.5 Axiom budget table sound](#115-axiom-budget-table-sound)
  - [11.6 Mathlib API names verified](#116-mathlib-api-names-verified)
  - [11.7 Scope guardrails complete](#117-scope-guardrails-complete)
  - [11.8 Triangle identity assumption verified](#118-triangle-identity-assumption-verified)
  - [11.9 No development-history references in docstrings](#119-no-development-history-references-in-docstrings)
  - [11.10 LOC estimates plausible](#1110-loc-estimates-plausible)
- [12 References](#12-references)

<!-- END doctoc -->

## 1 Scope and goal

T5 is the final phase of the ER ↔ K^sim_2 equivalence project.
It packages the categorical equivalence

```text
LawvereERCat ≌ LawvereKSimDCat 2
```

from the now-landed `erToKFunctor` (T4, PR #201) and the
previously-landed `kToERFunctor` (kToER work). This is the
categorical-equivalence statement of Tourlakis 2018 §0.1.0.44 at
`n = 2`, the headline result the ER ↔ K^sim_2 workstream has
been building toward.

The mathematical content T5 delivers is in fact strictly
stronger than the master-spec §11 obligation: T5 proves the two
round-trip composites
`erToKFunctor ⋙ kToERFunctor = 𝟙 LawvereERCat` and
`kToERFunctor ⋙ erToKFunctor = 𝟙 (LawvereKSimDCat 2)` as
strict equalities of functors (an isomorphism of categories,
not merely a categorical equivalence). The natural isomorphisms
the master spec requires are then derived as `eqToIso` of these
strict equalities, and the `Equivalence` packaging consumes
those isos.

The proof technique that makes the strict-equality strengthening
free is faithfulness of the two interpretation functors
`erInterpFunctor` and `kInterpFunctor`, combined with the two
landed functor-level interp-preservation equalities. Section 6
gives the recipe.

T5 decomposes into three sub-phases, executed in order:

- **T5-A — Two named-composite interp-preservation theorems.**
  Per the bottom-up named-composite discipline
  (`.claude/rules/lean-coding.md` § Bottom-up named-composite
  discipline for categorical equivalences), the equivalence
  cannot be built without both functors' interp preservation
  theorems available as named composites at both the quotient
  and functor levels. The K → ER direction landed these in
  `LawvereKSimER.lean:488` (`kToERFunctor_map_interp`) and
  `LawvereKSimER.lean:538` (`kToERFunctor_comp_erInterpFunctor`)
  during the original kToER work. T5-A produces the ER → K
  counterparts.
- **T5-B — Round-trip strict equalities and their isomorphisms.**
  Two strict functor equalities for the round-trip composites,
  proved via faithfulness; their `eqToIso` images supply the
  natural isomorphisms the master spec calls for.
- **T5-C — Equivalence packaging.** The `CategoryTheory.Equivalence`
  term plus `Functor.IsEquivalence` typeclass instances for
  both functors.

## 2 Inputs and prerequisites

Binding inputs for the T5 spec and implementation phases:

- Master research design:
  [`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`](../../research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md).
- Master ER-to-K spec (T1 + T2 + T3 + T4):
  [`docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`](2026-05-16-er-to-k-via-cslib-urm-design.md),
  §11 commits to the T5 surface.
- T4 spec (5-round adversarial-converged):
  [`docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`](2026-05-22-step-t4-runtime-bound-design.md).
- T4 plan (5-round adversarial-converged):
  [`docs/superpowers/plans/2026-05-22-step-t4-runtime-bound-plan.md`](../plans/2026-05-22-step-t4-runtime-bound-plan.md).
- Post-T4 handoff:
  [`docs/superpowers/plans/2026-05-25-post-t4-handoff.md`](../plans/2026-05-25-post-t4-handoff.md).
- Mirror code: `GebLean/LawvereKSimER.lean` lines 336–571,
  especially `kToERN`, `kToERN_compat_extEq`,
  `kToERFunctor_map_interp` (line 488), and
  `kToERFunctor_comp_erInterpFunctor` (line 538).
- Two interp functors:
  `kInterpFunctor` at `GebLean/LawvereKSimDCatInterp.lean:67–79`
  (faithful by the instance at line 84);
  `erInterpFunctor` at `GebLean/LawvereERInterp.lean:64–73`
  (faithful by the instance at line 80).
- T4 landed surface as documented in
  [`docs/superpowers/plans/2026-05-25-post-t4-handoff.md`](../plans/2026-05-25-post-t4-handoff.md)
  § T4 actually-landed surface.
- Tourlakis 2018, *Topics in PR Complexity*, §0.1.0.44 (the
  equivalence statement):
  [`.claude/docs/arithmetic-hierarchies/PR-complexity-topics.pdf`](../../../.claude/docs/arithmetic-hierarchies/PR-complexity-topics.pdf).
- Bottom-up named-composite discipline rule:
  [`.claude/rules/lean-coding.md`](../../../.claude/rules/lean-coding.md)
  § Bottom-up named-composite discipline for categorical
  equivalences.

T5 transcribes Tourlakis §0.1.0.44 as a categorical equivalence
at `n = 2`; T5 itself introduces no novel mathematics, only
categorical packaging of already-landed proofs.

## 3 File layout

T5 touches three Lean files: it extends one, creates one, and
adds an import to the umbrella.

| File | Change | Approx LOC delta |
| --- | --- | --- |
| `GebLean/LawvereERKSim/ErToKFunctor.lean` | Add `import GebLean.LawvereKSimDCatInterp`; add T5-A's two theorems at end of `namespace GebLean` | +35 |
| `GebLean/LawvereERKSim/Equivalence.lean` (new) | T5-B and T5-C content: strict round-trip equalities, their `eqToIso` natural isomorphisms, and the `Equivalence` packaging plus `IsEquivalence` instances | ≈ 140 |
| `GebLean/LawvereERKSim.lean` (umbrella) | Add `import GebLean.LawvereERKSim.Equivalence`; extend the module docstring's bulleted submodule list to mention `Equivalence` | +6 |

No other file is touched. No `lakefile.toml` change. No CI or
script change.

The new module `GebLean/LawvereERKSim/Equivalence.lean` follows
the project's mandatory module-docstring template (see
§ Documentation in `.claude/rules/lean-coding.md`):

```text
/-!
# Equivalence — categorical equivalence LawvereERCat ≌ LawvereKSimDCat 2
...
## Main definitions
...
## Main statements
...
## References
...
## Tags
...
-/
```

The `Equivalence.lean` module sits at the same level as
`ErToK.lean` and `ErToKFunctor.lean` under
`GebLean/LawvereERKSim/`; it imports `ErToKFunctor` (for
`erToKFunctor`), `LawvereKSimER` (for `kToERFunctor`,
`kToERFunctor_comp_erInterpFunctor`), `LawvereERInterp` (for
`erInterpFunctor` and its `Faithful` instance), and
`LawvereKSimDCatInterp` (for `kInterpFunctor` and its
`Faithful` instance), plus mathlib's
`CategoryTheory.Equivalence`.

## 4 Public API surface

All declarations live under `namespace GebLean`.

### 4.1 T5-A: extensions to `ErToKFunctor.lean`

| Name | Type |
| --- | --- |
| `erToKFunctor_map_interp` | `∀ {n m : ℕ} (e : ERMorNQuo n m), (erToKFunctor_map e).hom.interp = e.interp` |
| `erToKFunctor_comp_kInterpFunctor` | `erToKFunctor ⋙ kInterpFunctor = erInterpFunctor` |

Both are `theorem`s. Both mirror their kToER counterparts:

- `erToKFunctor_map_interp` mirrors `kToERFunctor_map_interp`
  (`LawvereKSimER.lean:488–520`).
- `erToKFunctor_comp_kInterpFunctor` mirrors
  `kToERFunctor_comp_erInterpFunctor`
  (`LawvereKSimER.lean:538–547`).

### 4.2 T5-B: contents of `Equivalence.lean` (round-trips)

| Name | Type |
| --- | --- |
| `erToKFunctor_comp_kToERFunctor` | `erToKFunctor ⋙ kToERFunctor = 𝟙 LawvereERCat` |
| `kToERFunctor_comp_erToKFunctor` | `kToERFunctor ⋙ erToKFunctor = 𝟙 (LawvereKSimDCat 2)` |
| `erToKKToErIso` | `erToKFunctor ⋙ kToERFunctor ≅ 𝟙 LawvereERCat` |
| `kToErErToKIso` | `kToERFunctor ⋙ erToKFunctor ≅ 𝟙 (LawvereKSimDCat 2)` |

The two equalities are `theorem`s; the two isomorphisms are
`def`s (each a one-line `eqToIso` of its corresponding equality).

### 4.3 T5-C: contents of `Equivalence.lean` (packaging)

| Name | Type |
| --- | --- |
| `erKSimEquiv` | `LawvereERCat ≌ LawvereKSimDCat 2` |
| `instance` | `erToKFunctor.IsEquivalence` |
| `instance` | `kToERFunctor.IsEquivalence` |

`erKSimEquiv` is a `def`; the two `IsEquivalence` instances are
anonymous `instance` declarations referring to
`erKSimEquiv.isEquivalence_functor` and the symmetric form.

### 4.4 Naming rationale

- `erKSimEquiv` over `lawvereERKSimDCat2Equiv` or
  `erToKKToErEquivalence`: the short form is unambiguous given
  the type annotation `LawvereERCat ≌ LawvereKSimDCat 2`, reads
  cleanly inline, and matches the existing project preference
  for compact names (`kToERFunctor`, `erToKFunctor`,
  `erInterpFunctor`, `kInterpFunctor`).
- Round-trip strict-equality lemmas use the mirror's
  `<lhs-functor>_comp_<rhs-functor>` pattern (cf.
  `kToERFunctor_comp_erInterpFunctor`).
- Natural isomorphisms are named `<lhs>KToErIso` /
  `<lhs>ErToKIso` (handoff convention), with the iso direction
  reading left-to-right on the LHS of the iso.

## 5 Step decomposition

Six commits on the topic branch `feat/t5-equivalence` (or
`feat/equivalence`; chosen at branch-creation time).

| Task | Deliverable | Approx LOC | File(s) |
| --- | --- | --- | --- |
| T5.0 | Baseline verification: `lake build`, `scripts/check-axioms.sh`, `markdownlint-cli2`, doctoc-check clean on fresh branch | 0 | — |
| T5.A.1 | `erToKFunctor_map_interp` (quotient-level interp preservation) | ≈ 18 | `ErToKFunctor.lean` |
| T5.A.2 | `erToKFunctor_comp_kInterpFunctor` (functor-level strict equality) | ≈ 15 | `ErToKFunctor.lean` |
| T5.B.1 | New `Equivalence.lean`; strict round-trip equalities `erToKFunctor_comp_kToERFunctor` and `kToERFunctor_comp_erToKFunctor` | ≈ 60 | `Equivalence.lean` |
| T5.B.2 | Named natural isomorphisms `erToKKToErIso`, `kToErErToKIso` as `eqToIso` of T5.B.1 | ≈ 12 | `Equivalence.lean` |
| T5.C | `erKSimEquiv`; `instance erToKFunctor.IsEquivalence`; `instance kToERFunctor.IsEquivalence`; umbrella update | ≈ 60 | `Equivalence.lean`, `LawvereERKSim.lean` |

T5.0 produces no code commit; verification only. Commits start
at T5.A.1.

Critical path: T5.0 → T5.A.1 → T5.A.2 → T5.B.1 → T5.B.2 → T5.C.
T5.B.1 depends on both T5.A.2 (the ER → K functor equality)
and the landed `kToERFunctor_comp_erInterpFunctor` (the
K → ER functor equality, `LawvereKSimER.lean:538`).

## 6 Proof shapes

Each declaration's proof recipe is given here in full; the
implementation phase consumes these directly. Tactic identifiers
are illustrative — minor reorderings or `simp` set adjustments
are acceptable as long as the proof shape is preserved and the
axiom budget (§7) is honoured.

### 6.1 `erToKFunctor_map_interp`

```lean
theorem erToKFunctor_map_interp {n m : ℕ}
    (e : ERMorNQuo n m) :
    (erToKFunctor_map e).hom.interp = e.interp := by
  unfold erToKFunctor_map
  refine Quotient.inductionOn
    (motive := fun (e : ERMorNQuo n m) =>
      KMorNQuo.interp
        (Quotient.liftOn (s := erMorNSetoid n m) e _ _).hom
      = ERMorNQuo.interp e) e ?_
  intro rec
  funext ctx; funext j
  change (erToKN rec j).interp ctx = (rec j).interp ctx
  exact erToKN_interp rec ctx j
```

Mirror: `kToERFunctor_map_interp` at
`LawvereKSimER.lean:488–520`. The motive-shape detail (the
`Quotient.liftOn` placeholders) is identical to the mirror's
form, with K/ER swapped.

### 6.2 `erToKFunctor_comp_kInterpFunctor`

```lean
theorem erToKFunctor_comp_kInterpFunctor :
    erToKFunctor ⋙ kInterpFunctor = erInterpFunctor := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro n m e
  funext ctx
  simp only [CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.comp_map]
  change (erToKFunctor_map e).hom.interp ctx = e.interp ctx
  rw [erToKFunctor_map_interp]
```

Mirror: `kToERFunctor_comp_erInterpFunctor` at
`LawvereKSimER.lean:538–547`. The obj equality `(_ ⥤ _).obj n =
n` is `rfl` for both functors (both are identity on objects);
this collapses `Functor.ext`'s `eqToHom` transports trivially.

### 6.3 `erToKFunctor_comp_kToERFunctor`

```lean
theorem erToKFunctor_comp_kToERFunctor :
    erToKFunctor ⋙ kToERFunctor = 𝟙 LawvereERCat := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro n m e
  simp only [CategoryTheory.Functor.id_obj,
    CategoryTheory.Functor.comp_obj,
    eqToHom_refl, Category.comp_id, Category.id_comp,
    CategoryTheory.Functor.id_map,
    CategoryTheory.Functor.comp_map]
  -- goal: kToERFunctor.map (erToKFunctor.map e) = e
  apply erInterpFunctor.map_injective
  -- goal: erInterpFunctor.map (kToERFunctor.map
  --         (erToKFunctor.map e)) = erInterpFunctor.map e
  change (kToERFunctor ⋙ erInterpFunctor).map
            (erToKFunctor.map e)
       = erInterpFunctor.map e
  rw [kToERFunctor_comp_erInterpFunctor]
  change (erToKFunctor ⋙ kInterpFunctor).map e
       = erInterpFunctor.map e
  rw [erToKFunctor_comp_kInterpFunctor]
```

The two `change` steps exploit `Functor.comp_map`'s definitional
equality: `(F ⋙ G).map f` reduces to `G.map (F.map f)` by `rfl`,
so each `change` is type-checking sugar. This lets the
`rw [kToERFunctor_comp_erInterpFunctor]` rewrite the *functor*
equality on a *map* term without invoking `Functor.congr_hom`
(which would introduce unwanted `eqToHom` transports).

Faithfulness of `erInterpFunctor` (instance at
`LawvereERInterp.lean:80`) is consumed via `map_injective`. The
proof closes because, after the two `rw`s, the goal reduces to
`erInterpFunctor.map e = erInterpFunctor.map e`, closed by
`rfl` from the last `rw`.

### 6.4 `kToERFunctor_comp_erToKFunctor`

```lean
theorem kToERFunctor_comp_erToKFunctor :
    kToERFunctor ⋙ erToKFunctor = 𝟙 (LawvereKSimDCat 2) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro n m f
  simp only [CategoryTheory.Functor.id_obj,
    CategoryTheory.Functor.comp_obj,
    eqToHom_refl, Category.comp_id, Category.id_comp,
    CategoryTheory.Functor.id_map,
    CategoryTheory.Functor.comp_map]
  apply kInterpFunctor.map_injective
  change (erToKFunctor ⋙ kInterpFunctor).map (kToERFunctor.map f)
       = kInterpFunctor.map f
  rw [erToKFunctor_comp_kInterpFunctor]
  change (kToERFunctor ⋙ erInterpFunctor).map f
       = kInterpFunctor.map f
  rw [kToERFunctor_comp_erInterpFunctor]
```

Symmetric to 6.3 with `er` and `k` swapped. Consumes
faithfulness of `kInterpFunctor` (instance at
`LawvereKSimDCatInterp.lean:84`).

### 6.5 `erToKKToErIso` and `kToErErToKIso`

```lean
def erToKKToErIso : erToKFunctor ⋙ kToERFunctor ≅ 𝟙 LawvereERCat :=
  eqToIso erToKFunctor_comp_kToERFunctor

def kToErErToKIso :
    kToERFunctor ⋙ erToKFunctor ≅ 𝟙 (LawvereKSimDCat 2) :=
  eqToIso kToERFunctor_comp_erToKFunctor
```

`eqToIso` of strict functor equality. No further proof needed.

### 6.6 `erKSimEquiv`

```lean
def erKSimEquiv : LawvereERCat ≌ LawvereKSimDCat 2 :=
  CategoryTheory.Equivalence.mk
    erToKFunctor
    kToERFunctor
    erToKKToErIso.symm
    kToErErToKIso
```

The `Equivalence.mk` signature in mathlib takes:
`(F : C ⥤ D) (G : D ⥤ C) (η : 𝟙 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟙 D)`
plus an autoparam `functor_unitIso_comp : ∀ X, F.map (η.hom.app X)
≫ ε.hom.app (F.obj X) = 𝟙 (F.obj X) := by aesop_cat`.

The triangle identity is expected to reduce trivially:
`η.hom.app X` and `ε.hom.app X` are both `eqToHom rfl = 𝟙 X`
(both obj equalities `(erToKFunctor ⋙ kToERFunctor).obj X = X`
and `(kToERFunctor ⋙ erToKFunctor).obj X = X` are `rfl`), so the
composite reduces to `𝟙 X ≫ 𝟙 X = 𝟙 X` by `Category.id_comp`.
`aesop_cat` is expected to close this; if not, the manual
discharge is `intro X; simp` or `intro X; dsimp; rfl`.

The implementation phase verifies the autoparam closes; if a
manual discharge is needed, it is added as a `(by ...)`
argument to `Equivalence.mk`.

### 6.7 `IsEquivalence` instances

```lean
instance : erToKFunctor.IsEquivalence :=
  erKSimEquiv.isEquivalence_functor

instance : kToERFunctor.IsEquivalence :=
  erKSimEquiv.symm.isEquivalence_functor
```

Each is a one-liner. The mathlib accessor name
`isEquivalence_functor` versus `isEquivalenceFunctor` (or any
similar variant under mathlib's current pin) is verified during
T5.C implementation; the dispatch structure is fixed.

The K-side instance routes through `erKSimEquiv.symm` (the
`Equivalence` reverses by swapping `functor` and `inverse`),
producing the `IsEquivalence` for `kToERFunctor` from the same
packaging.

## 7 Axiom budget

Every T5 declaration is transitively downstream of `erToK_interp`,
which carries `AXIOM_ALLOW: Classical.choice` via mathlib's
`Fin.lastCases_castSucc` equation lemma. This is the standing
project exception per `.claude/rules/lean-coding.md` § Accepted
exceptions.

| Declaration | AXIOM_ALLOW comment? | Transitive Classical.choice via |
| --- | --- | --- |
| `erToKFunctor_map_interp` | yes | `erToKN_interp` → `erToK_interp` |
| `erToKFunctor_comp_kInterpFunctor` | yes | `erToKFunctor_map_interp` |
| `erToKFunctor_comp_kToERFunctor` | yes | T5-A.2 + landed `kToERFunctor_comp_erInterpFunctor` |
| `kToERFunctor_comp_erToKFunctor` | yes | symmetric |
| `erToKKToErIso`, `kToErErToKIso` | yes (each) | `eqToIso` of strict equalities |
| `erKSimEquiv` | yes | both isos |
| `instance erToKFunctor.IsEquivalence`, `instance kToERFunctor.IsEquivalence` | yes (each) | `erKSimEquiv` |

The AXIOM_ALLOW comment immediately precedes each declaration
(or sits inside its `/-- … -/` docstring), matching the
convention established in `ErToKFunctor.lean` (see lines 55,
65, 73, 88, 116, 139). Suggested wording:

```text
-- AXIOM_ALLOW: Classical.choice (transitively via
-- `erToK_interp`; see .claude/rules/lean-coding.md § Accepted
-- exceptions).
```

The exact wording per declaration may name the closer
transitive predecessor (e.g. `erToKFunctor_map_interp` for
declarations downstream of it) for traceability.

Expected post-T5 `scripts/check-axioms.sh` envelope:
`[propext, Quot.sound]` — no Classical.choice visible in CI
output after suppression. T5 introduces no new axiom beyond
what `erToK_interp` already brings: `CategoryTheory.Equivalence`,
`eqToIso`, `Faithful.map_injective`, and the `IsEquivalence`
typeclass have no Classical.choice content of their own
(verified by the mirror's clean envelope on
`LawvereKSimER.lean`).

## 8 Test plan

No `#guard` or runtime tests at this layer.

**Rationale.** Per project memory
`feedback_godel_interp_not_decidable_in_tests`, the ER /
Gödel-numbering composite tree (`natPair`, `tupleAt`,
`boundedRec`, `boundedSearch`) expands symbolically under
`#guard` and hangs the elaborator. Every T5 declaration is
functorial or categorical and routes through `erToK_interp`
transitively; no concrete numerical computation surfaces at this
layer.

Correctness verification reduces to:

- Type-checking the equivalence: `lake build` must succeed.
- The faithfulness-driven proofs in T5-B.1 themselves rely on
  `erToK_interp` and `kToER_interp`, already proven and audited.
- The mirror's `kToERFunctor_*` lemmas being already-landed and
  axiom-audited.
- The axiom envelope inspection in §7: `scripts/check-axioms.sh`
  reports `[propext, Quot.sound]` after suppression.

## 9 Scope guardrails

Explicitly out of T5:

- **No modification of the kToER side.** `LawvereKSimER.lean`,
  `LawvereKSimDCatInterp.lean`, and all kToER-side dependencies
  are consumed but not edited. T5 is additive only.
- **No modification of the T4 surface.** `RuntimeBound.lean`,
  `ErToK.lean`, and the existing content of `ErToKFunctor.lean`
  are consumed but not edited (T5-A only appends).
- **No modification of interp functors.** `erInterpFunctor` and
  `kInterpFunctor` and their `Faithful` instances are consumed
  unchanged.
- **No standalone `Full` or `EssSurj` instances.** Those are
  derivable from `IsEquivalence` on demand; emitting them
  separately duplicates surface for no gain.
- **No fullness claim about interp functors.**
  `erInterpFunctor_not_full` at `LawvereERInterp.lean:102`
  remains the standing "K^sim ⊊ recursive functions at level
  3" boundary; T5 does not perturb it.
- **No work on followup branch #654.** The existing pending
  sub-tasks G–L on that branch are independent refactoring;
  T5 does not consume or amend them.
- **No new `#guard` / runtime tests.** Per §8.
- **No bare `Equivalence` instance for either category in
  isolation.** The packaging is `LawvereERCat ≌ LawvereKSimDCat 2`,
  consumed as a whole; no `instance : LawvereERCat ≌ _` global
  instance.
- **No transferring categorical structure beyond the equivalence
  packaging.** Mathlib already provides API for transferring
  limits, colimits, monoidal structure, etc. along
  `Equivalence`; T5 does not pre-emptively invoke any of it.
- **Renames are out of scope.** T5 introduces new names; it
  does not rename existing T4 or kToER-side names.

## 10 Implementation operational notes

- **Working directory.** `/home/terence/git-workspaces/geb/geb-lean`.
- **Topic branch.** Single branch `feat/t5-equivalence` (or
  `feat/equivalence`; the implementation phase chooses, the
  spec does not bind). One concern per branch per
  `CLAUDE.md` § Rules.
- **Per-task commit.** `jj commit -m '<commit message>'` exactly
  per task; the T4 execution session documented a pitfall with
  `jj describe @-` (error-prone when `@` is non-empty). Six
  commits total (T5.0 baseline produces no code change and
  hence no commit; commits start at T5.A.1).
- **Commit message conventions.** All-lowercase subject;
  imperative present tense; no trailing period; ≤ 72 chars.
  Suggested subjects:
  - T5.A.1: `feat(equivalence): add erToKFunctor_map_interp`
  - T5.A.2: `feat(equivalence): add erToKFunctor_comp_kInterpFunctor`
  - T5.B.1: `feat(equivalence): add round-trip strict equalities`
  - T5.B.2: `feat(equivalence): add eqToIso natural isomorphisms`
  - T5.C: `feat(equivalence): package LawvereERCat ≌ LawvereKSimDCat 2`
- **Verification before each commit.**
  1. `lake build` succeeds.
  2. `scripts/check-axioms.sh` reports `[propext, Quot.sound]`.
  3. `markdownlint-cli2 '**/*.md'` clean if any `.md` changed.
  4. `doctoc '**/*.md'` regenerated where any `.md` with more
     than one `##` heading changed.
  5. `lake test` succeeds (only formality at this layer; no new
     tests in T5 per §8).
- **Umbrella update.** After T5.B.1 creates
  `Equivalence.lean`, the umbrella file
  `GebLean/LawvereERKSim.lean` adds
  `import GebLean.LawvereERKSim.Equivalence` and extends the
  module-docstring bulleted submodule list with an
  `Equivalence` entry. This change rides on the T5.C commit
  (since the umbrella has nothing to import until T5.C lands
  the `Equivalence` value used by downstream callers).
- **No `jj git push` without user line-by-line review.**
  Per `CLAUDE.md` § Rules.
- **No raw mutating `git` subcommands.** `jj` is the
  state-mutating interface; `scripts/hooks/block-mutating-git.sh`
  enforces this.
- **No bash process substitution.** Per project memory
  `feedback_no_bash_process_substitution`. Intermediate output
  goes to `/tmp` files.
- **Build with `lake build`.** Never `lake env lean`; never
  `lake clean` (would force mathlib rebuild).
- **AXIOM_ALLOW comments must match §7's table.** The
  adversarial review checks each declaration carries its
  exception comment.

## 11 Adversarial-review punch list

The round-N adversary (per
[`docs/process.md`](../../process.md) § Adversarial review)
verifies each claim below and reports findings in
`docs/superpowers/specs/2026-05-25-step-t5-equivalence-design.review-N.md`.

### 11.1 Mathlib upstream guides honoured

Claim: every named declaration in the spec respects the four
mathlib guides (commit, style, naming, doc).

Adversary obligation: re-fetch the four guides at
[`leanprover-community.github.io/contribute/index.html`](https://leanprover-community.github.io/contribute/index.html);
check each declaration name (case, snake/camel, `_iff_` suffix
where relevant), each suggested commit-message subject (lowercase
first letter, imperative, no trailing period), each docstring
placeholder for required sections; flag every violation.

### 11.2 Mirror-precedent faithful

Claim: T5-A.1 and T5-A.2 are line-for-line mirrors of
`kToERFunctor_map_interp` (`LawvereKSimER.lean:488–520`) and
`kToERFunctor_comp_erInterpFunctor`
(`LawvereKSimER.lean:538–547`) with K and ER swapped.

Adversary obligation: open `LawvereKSimER.lean` at the cited
lines and §6.1 and §6.2 here; verify each tactic step has its
mirror counterpart; flag any divergence in proof shape.

### 11.3 Faithfulness chain sound

Claim: §6.3 and §6.4's proof of strict round-trip equality via
`Faithful.map_injective` + `Functor.comp_map`'s definitional
equality + the two functor-level interp-preservation equalities
is complete and produces an axiom-clean proof.

Adversary obligation: trace the proof steps line-by-line;
verify that `Functor.comp_map` is `rfl` in Lean 4 (it is — see
mathlib `CategoryTheory.Functor.Basic`); verify that
`Faithful.map_injective` is the correct member-of-typeclass
identifier; verify that the two `rw`s commute with the surface
`(F ⋙ G).map _` rewriting; flag any gap.

### 11.4 Citations complete

Claim: every named construction carries at least one citation
in its docstring — to the mirror lemma, to the master spec, to
Tourlakis 2018 §0.1.0.44, or to the post-T4 handoff.

Adversary obligation: enumerate every declaration in §4;
confirm a citation will appear in its `/-- … -/` block; flag
any that lacks one.

### 11.5 Axiom budget table sound

Claim: §7's table accurately reflects which declarations
transit `Classical.choice` through which predecessors, and the
expected envelope after AXIOM_ALLOW suppression is
`[propext, Quot.sound]`.

Adversary obligation: trace each entry's "transitive Classical.choice
via" column against the actual T4 / kToER-side AXIOM_ALLOW
content; verify the suppression mechanism in
`scripts/check-axioms.sh` recognises the comment pattern; flag
any mismatch.

### 11.6 Mathlib API names verified

Claim: `Equivalence.mk` takes the four-argument shape used in
§6.6 plus the autoparam `functor_unitIso_comp` defaulted to
`by aesop_cat`; the typeclass `Functor.IsEquivalence` and the
accessor `Equivalence.isEquivalence_functor` (or its current
mathlib name) exist under the current pin.

Adversary obligation: open mathlib (via the lean-lsp MCP or a
direct file lookup) and verify the signatures and names; flag
any divergence and propose the correct invocation.

### 11.7 Scope guardrails complete

Claim: §9 enumerates everything that could reasonably creep
into T5 but should not, with a clear "out of scope" framing.

Adversary obligation: brainstorm three plausible scope creeps
not currently in §9 (e.g., adding NatTrans lemmas, transferring
limits along the equivalence, adding simp lemmas for the
round-trip composites); flag whether they should be added to
the guardrails list, deferred to a follow-up, or are already
implicit.

### 11.8 Triangle identity assumption verified

Claim: `aesop_cat` will close the `functor_unitIso_comp`
autoparam in `Equivalence.mk` because both unit and counit
isomorphism components reduce to `𝟙`.

Adversary obligation: verify the claim by tracing
`erToKKToErIso.symm.hom.app X` and `kToErErToKIso.hom.app
(erToKFunctor.obj X)` to `eqToHom rfl = 𝟙 _` step-by-step. If
the trace finds that `aesop_cat` may not close it (e.g., due to
unfolding control of `eqToIso` or `Equivalence.mk` autoparam
elaboration), the spec must commit explicitly to the manual
fallback (`intro X; simp` or `intro X; dsimp; rfl`) as the
discharge, not as a fallback.

### 11.9 No development-history references in docstrings

Claim: every `/-! … -/` and `/-- … -/` placeholder in this
spec, when rendered into the implementation, will contain only
persistent content per `.claude/rules/lean-coding.md` § Comment
and docstring rules; no "previously …", "now uses …", "after
T4 …" content.

Adversary obligation: scan §3 and §6 for development-history
phrasing; flag any phrase that would migrate into a docstring
verbatim.

### 11.10 LOC estimates plausible

Claim: §5's LOC estimates (T5.A.1 ≈ 18; T5.A.2 ≈ 15; T5.B.1
≈ 60; T5.B.2 ≈ 12; T5.C ≈ 60) are within ±50% of what the
proof shapes in §6 produce when written out as proper Lean.

Adversary obligation: count lines for each proof shape in §6
(including docstring + AXIOM_ALLOW + signature + proof body);
compare against §5; flag any estimate off by more than 50%.

## 12 References

- Tourlakis 2018, *Topics in PR Complexity*, §0.1.0.44:
  [`.claude/docs/arithmetic-hierarchies/PR-complexity-topics.pdf`](../../../.claude/docs/arithmetic-hierarchies/PR-complexity-topics.pdf).
- Master research design:
  [`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`](../../research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md).
- Master ER-to-K spec:
  [`docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`](2026-05-16-er-to-k-via-cslib-urm-design.md).
- T4 spec:
  [`docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`](2026-05-22-step-t4-runtime-bound-design.md).
- T4 plan:
  [`docs/superpowers/plans/2026-05-22-step-t4-runtime-bound-plan.md`](../plans/2026-05-22-step-t4-runtime-bound-plan.md).
- Post-T4 handoff:
  [`docs/superpowers/plans/2026-05-25-post-t4-handoff.md`](../plans/2026-05-25-post-t4-handoff.md).
- Mirror code: `GebLean/LawvereKSimER.lean` lines 336–571.
- Interp functors: `GebLean/LawvereKSimDCatInterp.lean:67–79`
  (`kInterpFunctor`) and `GebLean/LawvereERInterp.lean:64–73`
  (`erInterpFunctor`); their `Faithful` instances at lines 84
  and 80 respectively.
- T4 surface (`erToKFunctor` and dependencies):
  `GebLean/LawvereERKSim/RuntimeBound.lean`,
  `GebLean/LawvereERKSim/ErToK.lean`,
  `GebLean/LawvereERKSim/ErToKFunctor.lean`.
- Mathlib `CategoryTheory.Equivalence`:
  [`Mathlib.CategoryTheory.Equivalence`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Equivalence.html).
- Mathlib `CategoryTheory.Functor.FullyFaithful`:
  [`Mathlib.CategoryTheory.Functor.FullyFaithful`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/FullyFaithful.html).
- Project rules: [`CLAUDE.md`](../../../CLAUDE.md),
  [`.claude/rules/lean-coding.md`](../../../.claude/rules/lean-coding.md),
  [`.claude/rules/markdown-writing.md`](../../../.claude/rules/markdown-writing.md),
  [`docs/process.md`](../../process.md).
