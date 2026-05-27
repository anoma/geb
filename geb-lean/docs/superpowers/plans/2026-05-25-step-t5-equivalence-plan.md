# T5 Equivalence Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Package the categorical equivalence
`LawvereERCat ≌ LawvereKSimDCat 2` (Tourlakis 2018
Corollary 0.1.0.44 at `n = 2`) by extending
`GebLean/LawvereERKSim/ErToKFunctor.lean` with two
interp-preservation theorems and creating a new
`GebLean/LawvereERKSim/Equivalence.lean` containing the
strict round-trip equalities, their `eqToIso` natural
isomorphisms, the `Equivalence` value via `Equivalence.mk'`,
and two explicit `IsEquivalence` instances.

**Architecture:** Faithfulness of the two interpretation
functors (`erInterpFunctor`, `kInterpFunctor`) plus the two
landed functor-level interp-preservation equalities
(`kToERFunctor_comp_erInterpFunctor`, new
`erToKFunctor_comp_kInterpFunctor`) yield strict round-trip
equalities of functors via `Faithful.map_injective` +
`Functor.comp_map`-as-`rfl`. The `Equivalence` packaging
consumes `eqToIso` of those strict equalities via mathlib's
raw structure constructor `Equivalence.mk'` so that
`erKSimEquiv.unitIso = erToKKToErIso.symm` and
`erKSimEquiv.counitIso = kToErErToKIso` hold by `rfl`.

**Tech Stack:** Lean 4, mathlib `CategoryTheory.Equivalence`,
`CategoryTheory.Functor.FullyFaithful`, `CategoryTheory.EqToHom`;
project-internal `GebLean.LawvereKSimER`,
`GebLean.LawvereERKSim.ErToKFunctor`,
`GebLean.LawvereERInterp`, `GebLean.LawvereKSimDCatInterp`.

**Spec:**
[`docs/superpowers/specs/2026-05-25-step-t5-equivalence-design.md`](../specs/2026-05-25-step-t5-equivalence-design.md)
(3-round adversarial-converged).

---

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [File structure](#file-structure)
- [Topic branch](#topic-branch)
- [Common verification commands](#common-verification-commands)
- [Task 0 (T5.0): Baseline verification](#task-0-t50-baseline-verification)
- [Task 1 (T5.A.1): `erToKFunctor_map_interp`](#task-1-t5a1-ertokfunctor_map_interp)
- [Task 2 (T5.A.2): `erToKFunctor_comp_kInterpFunctor`](#task-2-t5a2-ertokfunctor_comp_kinterpfunctor)
- [Task 3 (T5.B.1): Strict round-trip equalities](#task-3-t5b1-strict-round-trip-equalities)
- [Task 4 (T5.B.2): Named natural isomorphisms](#task-4-t5b2-named-natural-isomorphisms)
- [Task 5 (T5.C): Equivalence packaging + IsEquivalence instances + umbrella](#task-5-t5c-equivalence-packaging--isequivalence-instances--umbrella)
- [Post-implementation](#post-implementation)

<!-- END doctoc -->

## File structure

T5 touches three Lean files plus the topic branch's per-task
commit log:

| File | Role | Action |
| --- | --- | --- |
| `GebLean/LawvereERKSim/ErToKFunctor.lean` | Existing T4 module; defines `erToKFunctor` and supporting lemmas | **Modify** — add one new `import`, two new theorems before `end GebLean` |
| `GebLean/LawvereERKSim/Equivalence.lean` | New module | **Create** — contains strict round-trip equalities, `eqToIso` natural isomorphisms, `erKSimEquiv` via `Equivalence.mk'`, two `IsEquivalence` instances |
| `GebLean/LawvereERKSim.lean` | Existing umbrella module | **Modify** — add one `import` and extend the module docstring's submodule list |

## Topic branch

All commits land on bookmark `feat/t5-equivalence` (already
created during the spec/plan phase). The implementer advances
the bookmark after each `jj commit` via `jj bookmark move
feat/t5-equivalence --to @-`. The umbrella docstring's
`ErToKFunctor` bullet remains intentionally unchanged across
the T5.A.1 / T5.A.2 commits; per spec §10 *Umbrella update*,
the umbrella edit rides on T5.C, so the SDD subagent must not
update the umbrella in T5.A.1 / T5.A.2 (doing so would break
per-task scope discipline).

## Common verification commands

Each task's "verify" step runs:

```bash
lake build                           # builds GebLean and tests
bash scripts/check-axioms.sh         # axiom envelope check
```

`lake build` must report no errors and no warnings (other than
the AXIOM_ALLOW-suppressed Classical.choice usages). The
axiom check must report envelope `[propext, Quot.sound]` after
AXIOM_ALLOW suppression.

If any `.md` file is touched (none expected in T5.A–T5.C
implementation tasks):

```bash
markdownlint-cli2 '**/*.md'          # must report 0 errors
doctoc '**/*.md'                     # regenerate TOCs
```

---

## Task 0 (T5.0): Baseline verification

**Files:**

- No on-disk artifact. T5.0 verifies the spec's stubs via
  `mcp__lean-lsp__lean_run_code`; nothing is written under the
  project tree. If the MCP is unavailable, HALT per Step 4.

This task does not produce a commit. It verifies that the
spec's three load-bearing assumptions about mathlib's API
elaborate under the current pin, so that the implementation
phase does not discover them after writing real code.

- [ ] **Step 1: Confirm baseline build is clean**

Run:

```bash
lake build
```

Expected: builds successfully with no errors. If errors
appear, halt — the working tree is not at a clean baseline.

- [ ] **Step 2: Confirm baseline axiom envelope is clean**

Run:

```bash
bash scripts/check-axioms.sh
```

Expected: reports only `[propext, Quot.sound]` (the standard
envelope, after AXIOM_ALLOW suppression).

- [ ] **Step 2.5: Confirm baseline test suite is clean**

Run:

```bash
lake test
```

Expected: succeeds with no failures. Surfaces any pre-existing
test-suite breakage at the T5.0 boundary rather than at Task 5
Step 7 (where it would have to halt mid-implementation).

- [ ] **Step 3: Assemble the §6.3 proof-shape stub**

Hold the following Lean snippet (do not yet write it to
disk; Step 4 passes it directly to the lean-lsp MCP):

```lean
import GebLean.LawvereERKSim.ErToKFunctor
import GebLean.LawvereKSimER
import GebLean.LawvereERInterp
import GebLean.LawvereKSimDCatInterp
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Functor.FullyFaithful

namespace GebLean

open CategoryTheory

-- §6.3 proof-shape stub:
-- Verifies that the Functor.hext + hcongr_hom + faithfulness
-- chain typechecks.
example
    (erToKFunctor_comp_kInterpFunctor :
      erToKFunctor ⋙ kInterpFunctor = erInterpFunctor) :
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

end GebLean
```

- [ ] **Step 4: Type-check the stub via the lean-lsp MCP**

Call the `mcp__lean-lsp__lean_run_code` tool with the entire
snippet content from Step 3 as the `code` parameter. The
lean-lsp MCP runs the snippet against the project's mathlib
pin and lakefile options, avoiding the `lake env lean`
pitfall (which CLAUDE.md bans because it misses
`lakefile.toml` options).

Expected: no errors reported by the MCP. The `example` block
elaborates, confirming the §6.3 proof shape typechecks.

If the lean-lsp MCP is unavailable in the SDD subagent's
environment: HALT and surface that as a tooling-pre-condition
issue. Do not attempt to substitute `lake env lean` (banned by
CLAUDE.md) or to commit a scratch source file inside the
project tree.

If type-check fails: HALT. Do not proceed to T5.A.1. File a
finding, revise the spec, dispatch a new adversarial-review
round.

- [ ] **Step 5: Assemble the §6.1 motive-elaboration stub**

Append the following snippet to the buffer from Step 3
immediately before the final `end GebLean` (i.e., remove the
trailing `end GebLean` from Step 3's buffer, append this
snippet, then re-add a single `end GebLean` at the very end —
yielding one `namespace GebLean … end GebLean` block wrapping
both stubs):

```lean
-- §6.1 motive-elaboration stub:
-- Verifies that the spelled-out lift function inside the
-- Quotient.inductionOn motive elaborates against the
-- post-`unfold erToKFunctor_map` goal. The proof body is
-- irrelevant (only motive elaboration matters); `sorry`
-- inside a non-committed example is acceptable.
-- Note: the anonymous constructor `{ hom := ..., depth_witness
-- := ... }` requires the explicit type ascription
-- `(... : KSimMor 2 n m)` because the motive position does not
-- propagate an expected type to the inner constructor block.
example {n m : ℕ} (e : ERMorNQuo n m) :
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
  sorry
```

- [ ] **Step 6: Type-check the fully assembled stub**

Re-invoke the `mcp__lean-lsp__lean_run_code` tool with the
combined buffer (the §6.3 stub from Step 3 and the §6.1
motive example appended in Step 5).

Expected: no errors (a `sorry` warning on the §6.1 example is
expected and acceptable — it is the proof-body placeholder,
not a type-check failure). Confirms that the §6.3 proof shape
elaborates (the `Functor.hext + hcongr_hom` chain) and the
§6.1 motive's spelled-out lift function with the
`(... : KSimMor 2 n m)` ascription elaborates against the
post-`unfold` goal.

`Equivalence.mk'` and the explicit `IsEquivalence` instances
are not separately stubbed at T5.0; they are verified
directly via `lake build` when T5.C lands.

If it fails (other than the `sorry` warning): HALT. Same
handling as Step 4.

- [ ] **Step 7: Confirm no working-copy changes**

Run:

```bash
jj status
```

Expected: "The working copy has no changes."

T5.0 produces no code commit by design.

---

## Task 1 (T5.A.1): `erToKFunctor_map_interp`

**Files:**

- Modify: `GebLean/LawvereERKSim/ErToKFunctor.lean` (add
  one import; add one theorem before `end GebLean`)

Spec reference: §4.1, §6.1, §7.

- [ ] **Step 1: Add the interp-functor imports**

Open `GebLean/LawvereERKSim/ErToKFunctor.lean`. The current
imports are:

```lean
import GebLean.LawvereERKSim.ErToK
import GebLean.LawvereERQuot
import GebLean.LawvereKSimQuot
```

Insert two new import lines at the end of the import block:

```lean
import GebLean.LawvereERKSim.ErToK
import GebLean.LawvereERQuot
import GebLean.LawvereKSimQuot
import GebLean.LawvereERInterp
import GebLean.LawvereKSimDCatInterp
```

The two new imports give access to `ERMorNQuo.interp` (from
`LawvereERInterp`) and `KMorNQuo.interp` (from
`LawvereKSimDCatInterp`), both used by the new theorem's
signature via `.hom.interp` dot-notation and `e.interp`
respectively. Neither import is transitively pulled in by the
existing import block.

- [ ] **Step 2: Verify the import-only change builds**

Run:

```bash
lake build
```

Expected: builds successfully. The new import does not break
anything.

- [ ] **Step 3: Add the theorem before `end GebLean`**

The file currently ends with:

```lean
def erToKFunctor : CategoryTheory.Functor
    LawvereERCat (LawvereKSimDCat 2) where
  obj n     := n
  map       := erToKFunctor_map
  map_id    := erToKFunctor_map_id
  map_comp  := erToKFunctor_map_comp

end GebLean
```

Insert the new theorem between the `def erToKFunctor` block
and the `end GebLean` line:

```lean
def erToKFunctor : CategoryTheory.Functor
    LawvereERCat (LawvereKSimDCat 2) where
  obj n     := n
  map       := erToKFunctor_map
  map_id    := erToKFunctor_map_id
  map_comp  := erToKFunctor_map_comp

-- AXIOM_ALLOW: Classical.choice (transitively via
-- `erToKN_interp` → `erToK_interp`; see
-- .claude/rules/lean-coding.md § Accepted exceptions).
/-- Morphism-level interpretation preservation: the
K^sim-quotient interpretation of `erToKFunctor_map e` agrees
with the ER-quotient interpretation of `e`.  Mirror:
`kToERFunctor_map_interp` at `LawvereKSimER.lean:488–520`,
with K and ER swapped; the proof asymmetry is that
`LawvereERCat`'s morphisms are a bare quotient (no depth
witness wrapping), so `Quotient.inductionOn` applies directly
to `e` rather than to a depth-witness component. -/
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

end GebLean
```

- [ ] **Step 4: Verify the theorem builds**

Run:

```bash
lake build
```

Expected: builds successfully with no errors. If `unfold` or
the motive elaboration fails, halt and consult the spec's
§6.1 (the spec's stub-verification step in T5.0 should have
caught this; if not, the spec needs amendment).

- [ ] **Step 5: Verify the axiom envelope is clean**

Run:

```bash
bash scripts/check-axioms.sh
```

Expected: `[propext, Quot.sound]` only. The AXIOM_ALLOW
comment must be recognised by the script and suppressed from
the failure output.

- [ ] **Step 6: Commit**

```bash
jj commit -m 'feat(ertok): add erToKFunctor_map_interp'
jj bookmark move feat/t5-equivalence --to @-
```

---

## Task 2 (T5.A.2): `erToKFunctor_comp_kInterpFunctor`

**Files:**

- Modify: `GebLean/LawvereERKSim/ErToKFunctor.lean` (add one
  theorem before `end GebLean`)

Spec reference: §4.1, §6.2, §7.

- [ ] **Step 1: Add the second theorem before `end GebLean`**

Insert after the just-added `erToKFunctor_map_interp` and
before `end GebLean`:

```lean
-- AXIOM_ALLOW: Classical.choice (transitively via
-- `erToKFunctor_map_interp`; see
-- .claude/rules/lean-coding.md § Accepted exceptions).
/-- Functor-level interpretation preservation: composing
`erToKFunctor` with `kInterpFunctor` equals `erInterpFunctor`
as functors `LawvereERCat ⥤ Type`.  Mirror:
`kToERFunctor_comp_erInterpFunctor` at
`LawvereKSimER.lean:538–547`, with K and ER swapped.  Both
functors are identity on objects (the obj equality is `rfl`),
so `CategoryTheory.Functor.ext`'s `eqToHom` transports
collapse trivially; the map equality discharges by
`erToKFunctor_map_interp`. -/
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

The theorem sits between the previous theorem (which ends
with `exact erToKN_interp rec ctx j`) and the `end GebLean`
line.

- [ ] **Step 1.5: Update the module docstring's
  `## Main statements` section**

Open the module docstring at the top of
`GebLean/LawvereERKSim/ErToKFunctor.lean`. The existing
`## Main statements` section lists `erToKN_interp`,
`erToKN_level`, `erToKN_compat_extEq`, `erToKFunctor_map_id`,
`erToKFunctor_map_comp` (the T4 surface). Append two new
bullets — one for the T5.A.1 theorem just landed, one for the
T5.A.2 theorem this task is adding:

```text
- `erToKFunctor_map_interp` : the K^sim-quotient
  interpretation of `erToKFunctor_map e` agrees with the
  ER-quotient interpretation of `e` (morphism-level interp
  preservation; mirror at `LawvereKSimER.lean:488`).
- `erToKFunctor_comp_kInterpFunctor` : the strict functor
  equality `erToKFunctor ⋙ kInterpFunctor = erInterpFunctor`
  (functor-level interp preservation; mirror at
  `LawvereKSimER.lean:538`).
```

This update is folded into T5.A.2 (rather than T5.A.1)
because T5.A.2 is the last task to touch this file in the T5
sequence; landing both bullets together keeps the module
docstring coherent with the full T5-A surface.

- [ ] **Step 2: Verify the theorem builds**

Run:

```bash
lake build
```

Expected: builds successfully.

- [ ] **Step 3: Verify the axiom envelope is clean**

Run:

```bash
bash scripts/check-axioms.sh
```

Expected: `[propext, Quot.sound]`.

- [ ] **Step 4: Commit**

```bash
jj commit -m 'feat(ertok): add erToKFunctor_comp_kInterp'
jj bookmark move feat/t5-equivalence --to @-
```

Verify the subject fits within the ≤ 72-char target before
running `jj commit`.

---

## Task 3 (T5.B.1): Strict round-trip equalities

**Files:**

- Create: `GebLean/LawvereERKSim/Equivalence.lean`

Spec reference: §4.2, §6.3, §6.4, §7. This task creates the
new module with the two strict round-trip equality theorems.
Subsequent tasks extend this same file with the `eqToIso`
natural isomorphisms (Task 4) and the `Equivalence` packaging
(Task 5).

- [ ] **Step 1: Create the new file with module docstring and imports**

Create `GebLean/LawvereERKSim/Equivalence.lean` with:

```lean
import GebLean.LawvereERKSim.ErToKFunctor
import GebLean.LawvereKSimER
import GebLean.LawvereERInterp
import GebLean.LawvereKSimDCatInterp
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Equivalence — categorical equivalence `LawvereERCat ≌ LawvereKSimDCat 2`

Packages the categorical equivalence `LawvereERCat ≌
LawvereKSimDCat 2` (Tourlakis 2018 Corollary 0.1.0.44 at
`n = 2`) by combining `erToKFunctor` (T4 work; reverse
direction) with the previously-landed `kToERFunctor` (kToER
work; forward direction). The two round-trip composites
`erToKFunctor ⋙ kToERFunctor` and `kToERFunctor ⋙
erToKFunctor` are shown equal as functors to the identity
functors via faithfulness of the interpretation functors
combined with the two functor-level interp-preservation
equalities. The `Equivalence` value is assembled via
`Equivalence.mk'` (the raw structure constructor) so that
its `unitIso` and `counitIso` slots store the user-supplied
`eqToIso`s verbatim.

## Main definitions

- `erToKKToErIso` : natural isomorphism
  `erToKFunctor ⋙ kToERFunctor ≅ 𝟭 LawvereERCat`.
- `kToErErToKIso` : natural isomorphism
  `kToERFunctor ⋙ erToKFunctor ≅ 𝟭 (LawvereKSimDCat 2)`.
- `erKSimEquiv` : the packaged equivalence
  `LawvereERCat ≌ LawvereKSimDCat 2`.

## Main statements

- `erToKFunctor_comp_kToERFunctor` : strict functor equality
  `erToKFunctor ⋙ kToERFunctor = 𝟭 LawvereERCat`.
- `kToERFunctor_comp_erToKFunctor` : strict functor equality
  `kToERFunctor ⋙ erToKFunctor = 𝟭 (LawvereKSimDCat 2)`.
- Two `Functor.IsEquivalence` instances on `erToKFunctor` and
  `kToERFunctor`, each a one-line projection of mathlib's
  global `Equivalence.isEquivalence_functor` /
  `Equivalence.isEquivalence_inverse` applied to
  `erKSimEquiv`.

## Implementation notes

The packaging uses `Equivalence.mk'` (the raw structure
constructor) rather than `Equivalence.mk` (the smart
constructor at `Mathlib/CategoryTheory/Equivalence.lean:351`)
because `mk` calls `adjointifyη η ε` on the user-supplied
unit, replacing it with an adjointified form. Using `mk'`
preserves `erKSimEquiv.unitIso = erToKKToErIso.symm` and
`erKSimEquiv.counitIso = kToErErToKIso` definitionally. The
triangle identity `functor_unitIso_comp` is discharged by an
explicit fifth argument `(by intro X; simp [erToKKToErIso,
kToErErToKIso])` — the `cat_disch` autoparam alone is
insufficient here because it cannot unfold the two `def`-bound
natural isomorphisms `erToKKToErIso` and `kToErErToKIso` (each
defined via `eqToIso`).

The explicit `IsEquivalence` instances (rather than relying
on typeclass search through the mathlib globals) are
required: typeclass search cannot bridge from a `def`-bound
`Equivalence` value to an `IsEquivalence` goal on a
named functor via unification.

## References

- Tourlakis 2018, *Topics in PR Complexity*, Corollary
  0.1.0.44.
- Spec:
  `docs/superpowers/specs/2026-05-25-step-t5-equivalence-design.md`.
- Mirror code (kToER side):
  `kToERFunctor_comp_erInterpFunctor` at
  `GebLean/LawvereKSimER.lean:538–547`.

## Tags

equivalence, functor, lawvere, ksim, ertok, ktoer
-/

namespace GebLean

open CategoryTheory

end GebLean
```

- [ ] **Step 2: Verify the empty-module skeleton builds**

Run:

```bash
lake build
```

Expected: builds successfully. The file is valid Lean even
though `namespace GebLean ... end GebLean` is empty.

- [ ] **Step 3: Add `erToKFunctor_comp_kToERFunctor` between
the namespace markers**

Insert before `end GebLean`:

```lean
-- AXIOM_ALLOW: Classical.choice (transitively via
-- `erToKFunctor_comp_kInterpFunctor` and
-- `kToERFunctor_comp_erInterpFunctor`; see
-- .claude/rules/lean-coding.md § Accepted exceptions).
/-- Strict functor equality for the ER → K → ER round-trip:
`erToKFunctor ⋙ kToERFunctor = 𝟭 LawvereERCat`. Proof uses
faithfulness of `erInterpFunctor` plus `Functor.hcongr_hom`
applied to the two functor-level interp-preservation
equalities. The proof routes through `Functor.hext` (the
heterogeneous-equality variant of `Functor.ext`) to avoid
`eqToHom` transports on the morphism side; since both functors
are identity on objects, the `HEq` reduces to plain `Eq` via
`heq_of_eq`. -/
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

- [ ] **Step 4: Verify the theorem builds**

Run:

```bash
lake build
```

Expected: builds successfully. If `change` fails (because
`Functor.comp_map` is not `rfl` under the current pin), halt
— the spec's §6.3 proof shape needs revision.

- [ ] **Step 5: Add `kToERFunctor_comp_erToKFunctor`
(symmetric to Step 3)**

Insert after the previous theorem and before `end GebLean`:

```lean
-- AXIOM_ALLOW: Classical.choice (transitively via
-- `erToKFunctor_comp_kInterpFunctor` and
-- `kToERFunctor_comp_erInterpFunctor`; see
-- .claude/rules/lean-coding.md § Accepted exceptions).
/-- Strict functor equality for the K → ER → K round-trip:
`kToERFunctor ⋙ erToKFunctor = 𝟭 (LawvereKSimDCat 2)`.
Symmetric to `erToKFunctor_comp_kToERFunctor`, using
faithfulness of `kInterpFunctor` instead of `erInterpFunctor`,
and `Functor.hcongr_hom` of the two interp-preservation
equalities in the opposite order. -/
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

- [ ] **Step 6: Verify both theorems build**

Run:

```bash
lake build
```

Expected: builds successfully.

- [ ] **Step 7: Verify the axiom envelope is clean**

Run:

```bash
bash scripts/check-axioms.sh
```

Expected: `[propext, Quot.sound]`.

- [ ] **Step 8: Commit**

```bash
jj commit -m 'feat(equivalence): add round-trip strict equalities'
jj bookmark move feat/t5-equivalence --to @-
```

---

## Task 4 (T5.B.2): Named natural isomorphisms

**Files:**

- Modify: `GebLean/LawvereERKSim/Equivalence.lean` (add two
  `def`s before `end GebLean`)

Spec reference: §4.2, §6.5, §7.

- [ ] **Step 1: Add `erToKKToErIso`**

Insert before `end GebLean`:

```lean
-- AXIOM_ALLOW: Classical.choice (transitively via
-- `erToKFunctor_comp_kToERFunctor`; see
-- .claude/rules/lean-coding.md § Accepted exceptions).
/-- Natural isomorphism witnessing the ER → K → ER round-trip
collapse: `erToKFunctor ⋙ kToERFunctor ≅ 𝟭 LawvereERCat`.
Defined as `eqToIso` of the strict functor equality
`erToKFunctor_comp_kToERFunctor`; supplies the `unitIso`
slot (post-`.symm`) of `erKSimEquiv`. -/
def erToKKToErIso :
    erToKFunctor ⋙ kToERFunctor ≅ 𝟭 LawvereERCat :=
  eqToIso erToKFunctor_comp_kToERFunctor
```

- [ ] **Step 2: Add `kToErErToKIso`**

Insert immediately after:

```lean
-- AXIOM_ALLOW: Classical.choice (transitively via
-- `kToERFunctor_comp_erToKFunctor`; see
-- .claude/rules/lean-coding.md § Accepted exceptions).
/-- Natural isomorphism witnessing the K → ER → K round-trip
collapse: `kToERFunctor ⋙ erToKFunctor ≅ 𝟭 (LawvereKSimDCat 2)`.
Defined as `eqToIso` of the strict functor equality
`kToERFunctor_comp_erToKFunctor`; supplies the `counitIso`
slot of `erKSimEquiv`. -/
def kToErErToKIso :
    kToERFunctor ⋙ erToKFunctor ≅ 𝟭 (LawvereKSimDCat 2) :=
  eqToIso kToERFunctor_comp_erToKFunctor
```

- [ ] **Step 3: Verify both `def`s build**

Run:

```bash
lake build
```

Expected: builds successfully.

- [ ] **Step 4: Verify the axiom envelope is clean**

Run:

```bash
bash scripts/check-axioms.sh
```

Expected: `[propext, Quot.sound]`.

- [ ] **Step 5: Commit**

```bash
jj commit -m 'feat(equivalence): add eqToIso natural isos'
jj bookmark move feat/t5-equivalence --to @-
```

---

## Task 5 (T5.C): Equivalence packaging + IsEquivalence instances + umbrella

**Files:**

- Modify: `GebLean/LawvereERKSim/Equivalence.lean` (add
  `erKSimEquiv` + two instances before `end GebLean`)
- Modify: `GebLean/LawvereERKSim.lean` (add one `import` and
  extend module docstring)

Spec reference: §4.3, §6.6, §6.7, §7.

- [ ] **Step 1: Add `erKSimEquiv` via `Equivalence.mk'`**

Insert in `Equivalence.lean` before `end GebLean`:

```lean
-- AXIOM_ALLOW: Classical.choice (transitively via
-- `erToKKToErIso` and `kToErErToKIso`; see
-- .claude/rules/lean-coding.md § Accepted exceptions).
/-- The packaged categorical equivalence
`LawvereERCat ≌ LawvereKSimDCat 2` (Tourlakis 2018 Corollary
0.1.0.44 at `n = 2`). Built via `Equivalence.mk'` (the raw
structure constructor) so that the stored `unitIso` and
`counitIso` are the user-supplied `eqToIso`s verbatim (the
smart constructor `Equivalence.mk` at
`Mathlib/CategoryTheory/Equivalence.lean:351` would replace
the unit by `adjointifyη η ε`). The `functor_unitIso_comp`
obligation is discharged by an explicit fifth argument
(the `cat_disch` autoparam alone is insufficient: it cannot
unfold `eqToIso.hom` / `eqToIso.inv` on the
`eqToIso _ |>.symm`-shaped unit). The `simp` set unfolds the
two natural-iso definitions and the two `Iso`-projection
lemmas, reducing the triangle to `𝟙 ≫ 𝟙 = 𝟙` via mathlib's
standard category simp set. -/
def erKSimEquiv : LawvereERCat ≌ LawvereKSimDCat 2 :=
  CategoryTheory.Equivalence.mk'
    erToKFunctor
    kToERFunctor
    erToKKToErIso.symm
    kToErErToKIso
    (by intro X; simp [erToKKToErIso, kToErErToKIso])
```

- [ ] **Step 2: Verify the equivalence builds**

Run:

```bash
lake build
```

Expected: builds successfully. The explicit fifth-argument
discharge (`by intro X; simp [erToKKToErIso, kToErErToKIso]`)
is the load-bearing recipe per spec §6.6; it has been
MCP-verified against axiomatised strict equalities and is the
minimal simp set (adding `eqToIso.hom` or `eqToIso.inv` would
trigger `unusedSimpArgs` warnings). If under a newer mathlib
pin the discharge fails for unexpected reasons, halt and
consult the spec.

- [ ] **Step 3: Add the two explicit `IsEquivalence` instances**

Insert immediately after `erKSimEquiv`:

```lean
-- AXIOM_ALLOW: Classical.choice (transitively via
-- `erKSimEquiv`; see .claude/rules/lean-coding.md
-- § Accepted exceptions).
/-- Explicit `IsEquivalence` instance for `erToKFunctor`.
Mathlib's global instance
`Equivalence.isEquivalence_functor` supplies
`IsEquivalence e.functor` for any `e : C ≌ D`; this instance
pre-applies it to `erKSimEquiv` so that typeclass search
on `erToKFunctor.IsEquivalence` succeeds (search cannot
bridge from a `def`-bound `Equivalence` value to a
named-functor `IsEquivalence` goal via unification). -/
instance : erToKFunctor.IsEquivalence :=
  erKSimEquiv.isEquivalence_functor

-- AXIOM_ALLOW: Classical.choice (transitively via
-- `erKSimEquiv`; see .claude/rules/lean-coding.md
-- § Accepted exceptions).
/-- Explicit `IsEquivalence` instance for `kToERFunctor`.
Symmetric to the `erToKFunctor` instance, projecting via
`Equivalence.isEquivalence_inverse` (which supplies
`IsEquivalence e.inverse`). -/
instance : kToERFunctor.IsEquivalence :=
  erKSimEquiv.isEquivalence_inverse
```

- [ ] **Step 4: Verify the instances build**

Run:

```bash
lake build
```

Expected: builds successfully. If a typeclass-search
ambiguity warning appears (because mathlib's global
`Equivalence.isEquivalence_functor` is also visible), the
explicit instance still wins by priority; the warning is
informational.

- [ ] **Step 5: Update the umbrella `GebLean/LawvereERKSim.lean`**

Open the umbrella file. The current import block ends with:

```lean
import GebLean.LawvereERKSim.RuntimeBound
import GebLean.LawvereERKSim.ErToK
import GebLean.LawvereERKSim.ErToKFunctor
```

Add one more import line:

```lean
import GebLean.LawvereERKSim.RuntimeBound
import GebLean.LawvereERKSim.ErToK
import GebLean.LawvereERKSim.ErToKFunctor
import GebLean.LawvereERKSim.Equivalence
```

Extend the module docstring's submodule list. The current
submodule list ends with `ErToKFunctor: ...`. Add a new bullet
for `Equivalence`:

```lean
- `ErToKFunctor`: multi-output ER-to-K^sim translator `erToKN`
  with per-slot `erToKN_interp` / `erToKN_level` and the
  ext-eq compatibility lemma `erToKN_compat_extEq`; the
  morphism component `erToKFunctor_map`, functor laws
  `erToKFunctor_map_id` and `erToKFunctor_map_comp`, the
  assembled functor
  `erToKFunctor : LawvereERCat ⥤ LawvereKSimDCat 2`, the
  morphism-level interp preservation
  `erToKFunctor_map_interp`, and the functor-level interp
  equality `erToKFunctor_comp_kInterpFunctor`.
- `Equivalence`: strict functor equalities for the
  round-trip composites
  `erToKFunctor ⋙ kToERFunctor = 𝟭 LawvereERCat` and dual;
  their `eqToIso` natural isomorphisms `erToKKToErIso` and
  `kToErErToKIso`; the packaged equivalence
  `erKSimEquiv : LawvereERCat ≌ LawvereKSimDCat 2` via
  `Equivalence.mk'`; explicit `IsEquivalence` instances on
  `erToKFunctor` and `kToERFunctor`.
```

(Replace the existing `ErToKFunctor` bullet body in
place — add the two new sentence fragments about
`erToKFunctor_map_interp` and `erToKFunctor_comp_kInterpFunctor`
— and add the new `Equivalence` bullet after it.)

- [ ] **Step 6: Verify the umbrella builds**

Run:

```bash
lake build
```

Expected: builds successfully. The umbrella's import order
matters; `Equivalence` must come last because it depends on
`ErToKFunctor`.

- [ ] **Step 7: Final verification**

Run:

```bash
lake build
bash scripts/check-axioms.sh
lake test
```

Expected:

- `lake build` succeeds with no errors.
- `bash scripts/check-axioms.sh` reports `[propext,
  Quot.sound]`.
- `lake test` succeeds (no new tests in T5; this safeguards
  against accidental breakage of existing tests).

- [ ] **Step 8: Commit**

```bash
jj commit -m 'feat(equivalence): package LawvereERCat ≌ LawvereKSimDCat 2'
jj bookmark move feat/t5-equivalence --to @-
```

---

## Post-implementation

After Task 5 commits, the T5 implementation is complete on
`feat/t5-equivalence`. Five commits total (T5.0 produces no
commit).

- [ ] **Final step: Dispatch holistic-review subagent**

Per the post-T4 handoff's Step G:

> After all tasks land, dispatch a fresh-context holistic
> final code reviewer over the full T5 diff.

The holistic reviewer reads the entire T5 diff
(`feat/t5-equivalence ↔ main@origin`) and reports any
cross-task defects or integration concerns. Apply fixes if
any are reported, then the spec author hands off to the user
for the PR-creation phase.

The reviewer dispatch is the responsibility of the
SDD-orchestrator and is described in
[`superpowers:subagent-driven-development`](../../../.claude/plugins/cache/claude-plugins-official/superpowers/5.1.0/skills/subagent-driven-development/README.md).
