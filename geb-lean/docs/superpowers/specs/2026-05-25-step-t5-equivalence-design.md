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
  - [11.8 Triangle identity discharge verified](#118-triangle-identity-discharge-verified)
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
categorical-equivalence statement of Tourlakis 2018 Corollary
0.1.0.44 at `n = 2`.

T5 proves the two round-trip composites
`erToKFunctor ⋙ kToERFunctor = 𝟙 LawvereERCat` and
`kToERFunctor ⋙ erToKFunctor = 𝟙 (LawvereKSimDCat 2)` as
strict equalities of functors (theorem-level, conditional on
the proof shapes in §6.3/§6.4 going through under the current
mathlib pin). The natural isomorphisms the master spec requires
are then `eqToIso` of these strict equalities; the
`CategoryTheory.Equivalence` packaging consumes those isos via
the raw structure constructor `Equivalence.mk'` (see §6.6) so
that the stored `unitIso` and `counitIso` are the user-supplied
`eqToIso`s, not the adjointified forms that the smart
constructor `Equivalence.mk` would produce.

The proof technique that yields the strict-equality strengthening
without additional proof effort beyond what faithfulness supplies
is faithfulness of the two interpretation functors
`erInterpFunctor` and `kInterpFunctor`, combined with the two
landed functor-level interp-preservation equalities. Section 6
gives the recipe. T5.0 (baseline verification) includes a
type-check of a stub form of §6.3's proof shape so that the
spec's "strict equality" claim is verified before T5-B proper
begins. See §5 for the stub's operational semantics (scratch
file, removed before T5.B.1 commits; failure pauses
implementation and triggers spec revision).

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
- **T5-C — Equivalence packaging.** The
  `CategoryTheory.Equivalence` term via the raw structure
  constructor `Equivalence.mk'`, plus two explicit
  `Functor.IsEquivalence` instances on `erToKFunctor` and
  `kToERFunctor` (see §6.7 for why explicit instances are
  required rather than relying on typeclass search through
  mathlib's globals).

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
- Tourlakis 2018, *Topics in PR Complexity*, Corollary 0.1.0.44
  (the equivalence statement):
  [`.claude/docs/arithmetic-hierarchies/PR-complexity-topics.pdf`](../../../.claude/docs/arithmetic-hierarchies/PR-complexity-topics.pdf).
- Bottom-up named-composite discipline rule:
  [`.claude/rules/lean-coding.md`](../../../.claude/rules/lean-coding.md)
  § Bottom-up named-composite discipline for categorical
  equivalences.

T5 transcribes Tourlakis Corollary 0.1.0.44 as a categorical equivalence
at `n = 2`; T5 itself introduces no novel mathematics, only
categorical packaging of already-landed proofs.

## 3 File layout

T5 touches three Lean files: it extends one, creates one, and
adds an import to the umbrella.

| File | Change | Approx LOC delta |
| --- | --- | --- |
| `GebLean/LawvereERKSim/ErToKFunctor.lean` | Add `import GebLean.LawvereKSimDCatInterp`; add T5-A's two theorems at end of `namespace GebLean` | +35 |
| `GebLean/LawvereERKSim/Equivalence.lean` (new) | T5-B and T5-C content: strict round-trip equalities, their `eqToIso` natural isomorphisms, the `Equivalence` packaging via `Equivalence.mk'`, and two explicit `IsEquivalence` instances | ≈ 130 |
| `GebLean/LawvereERKSim.lean` (umbrella) | Add `import GebLean.LawvereERKSim.Equivalence`; extend the module docstring's bulleted submodule list to mention `Equivalence` | +6 |

No other file is touched. No `lakefile.toml` change. No CI or
script change.

The new module `GebLean/LawvereERKSim/Equivalence.lean` follows
the project's mandatory module-docstring template (see
§ Documentation in `.claude/rules/lean-coding.md`). The module
docstring's sections will be: `# Title`, brief summary,
`## Main definitions`, `## Main statements`, `## Implementation
notes` (commits to the `Equivalence.mk'` constructor choice and
the `cat_disch` triangle discharge per §6.6), `## References`,
and `## Tags`. The optional `## Notation` section is omitted as
no new notation is introduced.

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

`erKSimEquiv` is a `def`. The two `IsEquivalence` instances are
explicit (typeclass search cannot bridge from `def`-bound
`erKSimEquiv` to an `IsEquivalence` goal on the named functors;
see §6.7). Each instance is a one-line projection
`erKSimEquiv.isEquivalence_functor` / `.isEquivalence_inverse`
of mathlib's global instance applied to `erKSimEquiv`.

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
| T5.0 | Baseline verification: `lake build`, `scripts/check-axioms.sh`, `markdownlint-cli2`, doctoc-check, plus stub type-check of §6.3's proof shape and §6.7's typeclass-search assumption — all clean on fresh branch | 0 | — |
| T5.A.1 | `erToKFunctor_map_interp` (quotient-level interp preservation) | ≈ 18 | `ErToKFunctor.lean` |
| T5.A.2 | `erToKFunctor_comp_kInterpFunctor` (functor-level strict equality) | ≈ 15 | `ErToKFunctor.lean` |
| T5.B.1 | New `Equivalence.lean`; strict round-trip equalities `erToKFunctor_comp_kToERFunctor` and `kToERFunctor_comp_erToKFunctor` | ≈ 60 | `Equivalence.lean` |
| T5.B.2 | Named natural isomorphisms `erToKKToErIso`, `kToErErToKIso` as `eqToIso` of T5.B.1 | ≈ 12 | `Equivalence.lean` |
| T5.C | `erKSimEquiv` via `Equivalence.mk'`; two `IsEquivalence` instances (`erToKFunctor` and `kToERFunctor`) as projections of mathlib globals; umbrella update | ≈ 60 | `Equivalence.lean`, `LawvereERKSim.lean` |

T5.0 produces no code commit; verification only. Commits start
at T5.A.1.

T5.0's stub-verification step has the following operational
semantics:

- The stub lives in a scratch file at
  `/tmp/t5-equivalence-stubs.lean` (or equivalent), outside the
  committed Lean source tree.
- The stub contains: one `example` block implementing §6.3's
  proof shape against axiomatised placeholders for the two
  functor-level interp-preservation equalities; one `example`
  block for §6.1's `Quotient.inductionOn` motive-elaboration
  shape. (The §6.7 instance declarations are not stubbed
  separately because they are one-liners against the concrete
  `erKSimEquiv` value; their elaboration is verified directly
  at T5.C `lake build` time.)
- If any `example` fails to elaborate, T5.0 reports the
  divergence and the implementation phase pauses. The spec is
  revised (a follow-up adversarial round is dispatched) before
  any T5.A / T5.B / T5.C commit lands. T5.0 does not patch the
  spec mid-flight; the implementer does not attempt local
  workarounds.
- The scratch file is not committed; it lives only as a check
  artifact for the T5.0 baseline run.

LOC estimates above include docstring, AXIOM_ALLOW comment,
signature, and proof body. The post-T4 handoff's smaller "Lean
lines" figures (T5-A.1 ≈ 15, T5-A.2 ≈ 10) count only the proof
body; the spec's envelope is canonical.

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
        (Quotient.liftOn (s := erMorNSetoid n m) e
          (fun rec =>
            ({ hom := Quotient.mk (kMorNSetoid n m) (erToKN rec),
               depth_witness := Quotient.mk _
                 { rep := erToKN rec,
                   rep_level := fun i => erToKN_level rec i,
                   rep_eq := rfl } } : KSimMor 2 n m))
          _).hom
      = ERMorNQuo.interp e) e ?_
  intro rec
  funext ctx; funext j
  change (erToKN rec j).interp ctx = (rec j).interp ctx
  exact erToKN_interp rec ctx j
```

Mirror: `kToERFunctor_map_interp` at
`LawvereKSimER.lean:488–520`. The proof shape mirrors the K-side
structurally, with three asymmetries:

- The mirror destructures `f : KSimMor 2 n m` via `rcases f
  with ⟨fh, fdw⟩` and applies `Quotient.inductionOn` to the
  depth-witness `fdw`, because `KSimMor` is a sigma over a
  depth witness. T5-A.1 applies `Quotient.inductionOn` directly
  to `e : ERMorNQuo n m`, since `LawvereERCat`'s morphisms are
  a bare quotient (no depth witness wrapping).
- The mirror's RHS extracts `.hom.interp` from `f : KSimMor 2`;
  the spec's signature places `.hom.interp` on the LHS, from
  `(erToKFunctor_map e).hom : KMorNQuo n m`. Both sides have
  the same type `(Fin n → ℕ) → (Fin m → ℕ)`; the dot-notation
  resolution `.hom.interp` uses `KSimMor.hom` then
  `KMorNQuo.interp` (defined at
  `LawvereKSimDCatInterp.lean:25`).
- The mirror's inner `change` reduces to comparing two
  `ERMor1`-level interps; T5-A.1's inner `change` compares two
  `KMor1`-level interps via `erToKN`, since `erToKN rec` returns
  `KMorN n m` (not `ERMorN n m`).

The motive spells out the lift function explicitly (the
`KSimMor`-valued `{ hom, depth_witness }` builder); the
well-definedness proof remains as a single underscore, matching
the mirror's pattern at `LawvereKSimER.lean:497–501` (which
spells out its lift function and leaves the well-definedness
underscore for elaboration to fill from the post-`unfold` goal).
The reason for spelling out the lift function rather than
leaving it as a second underscore: elaboration of two
underscores in the motive's `Quotient.liftOn` application
position can fail under the current pin (the engine cannot infer
both the lift function and its well-definedness compatibility
proof from the expected motive type alone). Spelling out the
lift function unambiguously fixes the elaboration; T5.0
baseline verifies this.

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
this collapses `Functor.ext`'s `eqToHom` transports to `𝟙 _`,
which `simp only [eqToHom_refl, Category.id_comp,
Category.comp_id]` discharges before the inner `change`/`rw`
chain begins.

### 6.3 `erToKFunctor_comp_kToERFunctor`

```lean
theorem erToKFunctor_comp_kToERFunctor :
    erToKFunctor ⋙ kToERFunctor = 𝟭 LawvereERCat := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro n m e
  apply heq_of_eq
  apply erInterpFunctor.map_injective
  change erInterpFunctor.map
            (kToERFunctor.map (erToKFunctor.map e))
       = erInterpFunctor.map e
  have h1 :
      erInterpFunctor.map (kToERFunctor.map (erToKFunctor.map e))
        = kInterpFunctor.map (erToKFunctor.map e) :=
    eq_of_heq
      (CategoryTheory.Functor.hcongr_hom
        kToERFunctor_comp_erInterpFunctor
        (erToKFunctor.map e))
  have h2 :
      kInterpFunctor.map (erToKFunctor.map e)
        = erInterpFunctor.map e :=
    eq_of_heq
      (CategoryTheory.Functor.hcongr_hom
        erToKFunctor_comp_kInterpFunctor e)
  rw [h1, h2]
```

The proof routes through `CategoryTheory.Functor.hext` (the
heterogeneous-equality variant of `Functor.ext`) rather than
`Functor.ext`. The reason: `Functor.ext` with `h_obj := fun _ =>
rfl` still leaves `eqToHom`-laden goals on the morphism side
because the obj-side proofs are not literally `Eq.refl` after
beta-reduction; `simp [eqToHom_refl, Category.id_comp,
Category.comp_id]` cannot collapse them. `Functor.hext`
delivers a `HEq` obligation on maps; since obj-agreement is
`rfl`, the `HEq` reduces to plain equality via `heq_of_eq`
without any `eqToHom` introduction.

`CategoryTheory.Functor.hcongr_hom` is mathlib's HEq companion
of `Functor.congr_hom`: it takes a functor equality `F = G` and
a morphism `f`, producing `F.map f ≍ G.map f`. Wrapped with
`eq_of_heq` (applicable here because the obj parts of `F` and
`G` agree by `rfl` on `f`'s endpoints), each `hcongr_hom`
yields an ordinary `Eq` rewrite that composes cleanly via `rw`.

Faithfulness of `erInterpFunctor` (instance at
`LawvereERInterp.lean:80`) is consumed via `map_injective`. The
proof closes because, after the two `rw`s, the goal reduces to
`erInterpFunctor.map e = erInterpFunctor.map e`, closed by
`rfl` from the last `rw`.

### 6.4 `kToERFunctor_comp_erToKFunctor`

```lean
theorem kToERFunctor_comp_erToKFunctor :
    kToERFunctor ⋙ erToKFunctor = 𝟭 (LawvereKSimDCat 2) := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro n m f
  apply heq_of_eq
  apply kInterpFunctor.map_injective
  change kInterpFunctor.map
            (erToKFunctor.map (kToERFunctor.map f))
       = kInterpFunctor.map f
  have h1 :
      kInterpFunctor.map (erToKFunctor.map (kToERFunctor.map f))
        = erInterpFunctor.map (kToERFunctor.map f) :=
    eq_of_heq
      (CategoryTheory.Functor.hcongr_hom
        erToKFunctor_comp_kInterpFunctor
        (kToERFunctor.map f))
  have h2 :
      erInterpFunctor.map (kToERFunctor.map f)
        = kInterpFunctor.map f :=
    eq_of_heq
      (CategoryTheory.Functor.hcongr_hom
        kToERFunctor_comp_erInterpFunctor f)
  rw [h1, h2]
```

Symmetric to 6.3 with `er` and `k` swapped. Consumes
faithfulness of `kInterpFunctor` (instance at
`LawvereKSimDCatInterp.lean:84`), and `Functor.hcongr_hom`
applied to the two functor-level interp-preservation equalities
in the opposite order from §6.3.

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

Mathlib's `CategoryTheory.Equivalence` (at
`Mathlib/CategoryTheory/Equivalence.lean:85–105`) is declared
with `where mk' ::`, exposing two constructors:

- `Equivalence.mk'` (the raw structure constructor): takes the
  four data fields plus the triangle identity
  `functor_unitIso_comp` as an autoparam defaulting to
  `by cat_disch`. Stores the user-supplied `unitIso` and
  `counitIso` verbatim.
- `Equivalence.mk` (the smart constructor at line 351): takes
  the same four data fields without the triangle, and stores
  `adjointifyη η ε` in the `unitIso` slot. This corrects the
  user-supplied unit so that the triangle identity holds by
  construction, but the stored `unitIso` differs from the input.

T5 uses `Equivalence.mk'` so that
`erKSimEquiv.unitIso = erToKKToErIso.symm` and
`erKSimEquiv.counitIso = kToErErToKIso` definitionally. This
preserves the strict-equality strengthening at the packaging
level (downstream `rfl`-rewrites against `erKSimEquiv.unitIso`
collapse to `eqToIso _ |>.symm` directly).

The triangle identity is supplied as an explicit fifth
argument rather than left to the `cat_disch` autoparam: under
the current mathlib pin, `cat_disch` (which dispatches to
`aesop_cat`) cannot reduce `eqToIso _ |>.symm.hom.app X` to
`𝟙 _` because the relevant unfold lemmas (`eqToIso.hom`,
`eqToIso.inv`) are not in `aesop_cat`'s safe-rules set. The
working discharge invokes `simp` with the two natural-iso
definitions and the two `Iso`-projection lemmas:

```lean
def erKSimEquiv : LawvereERCat ≌ LawvereKSimDCat 2 :=
  CategoryTheory.Equivalence.mk'
    erToKFunctor
    kToERFunctor
    erToKKToErIso.symm
    kToErErToKIso
    (by intro X;
        simp [erToKKToErIso, kToErErToKIso,
              eqToIso.hom, eqToIso.inv])
```

Tracing the discharge: `simp` unfolds `erToKKToErIso` and
`kToErErToKIso` (the two `def`-bound natural isos from §6.5)
to their `eqToIso _ |>.symm` and `eqToIso _` forms. The
`eqToIso.hom` and `eqToIso.inv` lemmas (at
`Mathlib/CategoryTheory/EqToHom.lean:197` and `:201`
respectively, *with* the dot prefix) reduce the `.hom.app X`
projections to `eqToHom (Functor.congr_obj _ X)` and
`eqToHom (Functor.congr_obj _ X).symm`. Since both functors
are identity on objects (`(erToKFunctor ⋙ kToERFunctor).obj X
= X` and dual are both `rfl`), the `eqToHom`s reduce to
`𝟙 _`. The triangle LHS becomes
`erToKFunctor.map (𝟙 X) ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _ = 𝟙 _`, closed by
mathlib's standard category simp set. MCP-verified.

### 6.7 `IsEquivalence` instances

Mathlib provides two global `instance`s at
`Mathlib/CategoryTheory/Equivalence.lean:630` and `:632`:

```lean
instance isEquivalence_functor (e : C ≌ D) : e.functor.IsEquivalence
instance isEquivalence_inverse (e : C ≌ D) : e.inverse.IsEquivalence
```

These give `IsEquivalence` for `e.functor` and `e.inverse` of a
**specific** equivalence value `e`. Typeclass search cannot
discover this from a goal of shape `IsEquivalence erToKFunctor`
on its own: even though `erKSimEquiv.functor` reduces
definitionally to `erToKFunctor`, the search engine has no way
to invert that equality and identify the bridging `Equivalence`
value. T5 therefore emits explicit named instances, each a
one-line projection of the global instance pre-applied to
`erKSimEquiv`:

```lean
instance : erToKFunctor.IsEquivalence :=
  erKSimEquiv.isEquivalence_functor

instance : kToERFunctor.IsEquivalence :=
  erKSimEquiv.isEquivalence_inverse
```

Each instance is a direct dot-notation projection (verified to
typecheck under the current mathlib pin in the T5.0 baseline; see
§5). The instances depend transitively on `erKSimEquiv` and
hence on `erToK_interp`, so each carries the AXIOM_ALLOW comment
(§7).

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
`eqToIso`, `Faithful.map_injective`, and the mathlib global
`isEquivalence_functor` / `isEquivalence_inverse` instances have
no Classical.choice content of their own (verified by the
mirror's clean envelope on `LawvereKSimER.lean`).

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
  imperative present tense; no trailing period; ≤ 72 chars
  (subject including prefix). The scope `(ertok)` is used for
  T5.A commits (which extend `ErToKFunctor.lean`, an `ertok`-
  scoped file); `(equivalence)` is used for T5.B and T5.C
  commits (which create and populate `Equivalence.lean`).
  Suggested subjects:
  - T5.A.1: `feat(ertok): add erToKFunctor_map_interp`
  - T5.A.2: `feat(ertok): add erToKFunctor_comp_kInterp`
  - T5.B.1: `feat(equivalence): add round-trip strict equalities`
  - T5.B.2: `feat(equivalence): add eqToIso natural isos`
  - T5.C: `feat(equivalence): package LawvereERCat ≌ LawvereKSimDCat 2`
- **Verification before each commit.**
  1. `lake build` succeeds.
  2. `scripts/check-axioms.sh` reports `[propext, Quot.sound]`.
  3. `markdownlint-cli2 '**/*.md'` clean if any `.md` changed.
  4. `doctoc '**/*.md'` regenerated where any `.md` with more
     than one `##` heading changed.
  5. `lake test` succeeds (the pre-T5 test suite runs unchanged;
     §8 commits T5 to add no new tests, so this check safeguards
     against accidental breakage of existing tests, not against
     new T5 content).
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
`Functor.hext` + `Faithful.map_injective` + `Functor.hcongr_hom`
applied to the two functor-level interp-preservation equalities
is complete and produces an axiom-clean proof.

Adversary obligation: trace the proof steps line-by-line;
verify that `CategoryTheory.Functor.hext` is the correct
heterogeneous-equality `Functor.ext` variant under the current
mathlib pin; verify that `CategoryTheory.Functor.hcongr_hom`
exists and has the signature
`(h : F = G) (f : X ⟶ Y) → F.map f ≍ G.map f`; verify that
the `eq_of_heq` wrapping is sound (it is because the obj-parts
of `F` and `G` agree by `rfl` on `f`'s endpoints, so the HEq
reduces to plain Eq); flag any gap. The fully verified working
proofs are recorded in `.review-2.md` and its follow-up
.review-3.md`.

### 11.4 Citations complete

Claim: every named construction carries at least one citation
in its docstring — to the mirror lemma, to the master spec, to
Tourlakis 2018 Corollary 0.1.0.44, or to the post-T4 handoff.

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

Claim: `Equivalence.mk'` is the raw structure constructor and
takes four data arguments plus the autoparam
`functor_unitIso_comp` defaulted to `by cat_disch`; the typeclass
`Functor.IsEquivalence` and the global instances
`Equivalence.isEquivalence_functor` /
`Equivalence.isEquivalence_inverse` exist under the current
mathlib pin and project the named-functor `IsEquivalence` for a
specific equivalence value.

Adversary obligation: open mathlib (via the lean-lsp MCP or a
direct file lookup) and verify each name and signature against
`Mathlib/CategoryTheory/Equivalence.lean` (the `mk' ::`
structure declaration, the smart `mk` at line 351, and the
global instances at lines 630 / 632); flag any divergence and
propose the correct invocation.

### 11.7 Scope guardrails complete

Claim: §9 enumerates the candidate scope creeps into T5 and
their disposition (in / out / follow-up).

Adversary obligation: list three additional plausible scope
creeps not currently in §9 (e.g., adding NatTrans lemmas,
transferring limits along the equivalence, adding simp lemmas
for the round-trip composites); for each, indicate whether it
should be added to the guardrails list, deferred to a follow-up,
or is already implicit.

### 11.8 Triangle identity discharge verified

Claim: the explicit fifth argument
`(by intro X; simp [erToKKToErIso, kToErErToKIso,
eqToIso.hom, eqToIso.inv])` discharges the
`functor_unitIso_comp` obligation in `Equivalence.mk'`. The
`cat_disch` autoparam alone is insufficient because mathlib's
`aesop_cat`-based safe-rules set does not unfold
`eqToIso.hom` / `eqToIso.inv` on `eqToIso _ |>.symm`-shaped
inputs.

Adversary obligation: verify under the current mathlib pin
via `mcp__lean-lsp__lean_run_code` that the explicit
fifth-argument form closes the triangle in a stand-in
elaboration with axiomatised
`erToKFunctor_comp_kToERFunctor` and
`kToERFunctor_comp_erToKFunctor`. If `aesop_cat`'s safe-rules
set has expanded under a newer pin so that `cat_disch` alone
suffices, the spec can be amended to drop the explicit fifth
argument — but the default position is that the explicit
discharge is load-bearing.

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

- Tourlakis 2018, *Topics in PR Complexity*, Corollary 0.1.0.44:
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
