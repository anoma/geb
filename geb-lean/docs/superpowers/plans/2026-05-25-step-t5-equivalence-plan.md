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
created and pointing at the spec convergence commit
`75ecc025`). The implementer advances the bookmark after
each `jj commit` via `jj bookmark move feat/t5-equivalence
--to @-`.

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

- No on-disk artifact when the lean-lsp MCP is used
  (recommended). Fallback path uses a temporary
  `GebLean/Scratch/T5Stubs.lean` deleted before the task
  completes; nothing is committed either way.

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
-- Verifies that the faithfulness + change/rw chain typechecks.
example
    (erToKFunctor_comp_kInterpFunctor :
      erToKFunctor ⋙ kInterpFunctor = erInterpFunctor) :
    erToKFunctor ⋙ kToERFunctor = 𝟭 LawvereERCat := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro n m e
  simp only [CategoryTheory.Functor.id_obj,
    CategoryTheory.Functor.comp_obj,
    eqToHom_refl, Category.comp_id, Category.id_comp,
    CategoryTheory.Functor.id_map,
    CategoryTheory.Functor.comp_map]
  apply erInterpFunctor.map_injective
  change (kToERFunctor ⋙ erInterpFunctor).map
            (erToKFunctor.map e)
       = erInterpFunctor.map e
  rw [kToERFunctor_comp_erInterpFunctor]
  change (erToKFunctor ⋙ kInterpFunctor).map e
       = erInterpFunctor.map e
  rw [erToKFunctor_comp_kInterpFunctor]

end GebLean
```

- [ ] **Step 4: Type-check the stub via the lean-lsp MCP**

Call the `mcp__lean-lsp__lean_run_code` tool with the entire
file content from Step 3 as the `code` parameter. The
lean-lsp MCP runs the snippet against the project's mathlib
pin and lakefile options, avoiding the `lake env lean`
pitfall (which CLAUDE.md bans because it misses
`lakefile.toml` options).

Expected: no errors reported by the MCP. The `example` block
elaborates, confirming the §6.3 proof shape typechecks.

Alternative if the MCP is unavailable: temporarily place the
stub at `GebLean/Scratch/T5Stubs.lean` (creating the
`Scratch/` directory if it does not exist), add it to a
local `lakefile.toml` `lean_lib` target, run `lake build`,
then delete the file and lakefile entry. Do not commit any
scratch artifact.

If type-check fails: HALT. Do not proceed to T5.A.1. File a
finding, revise the spec, dispatch a new adversarial-review
round.

- [ ] **Step 5: Assemble the §6.7 instance stub**

Append the following snippet to the buffer from Step 3 (the
combined buffer is passed to lean-lsp in Step 6):

```lean
namespace GebLean

-- §6.7 instance-availability stub:
-- Verifies that after defining the Equivalence via mk',
-- the explicit instance forms elaborate.
section InstanceStub
  variable
    (F : LawvereERCat ⥤ LawvereKSimDCat 2)
    (G : LawvereKSimDCat 2 ⥤ LawvereERCat)
    (η : 𝟭 LawvereERCat ≅ F ⋙ G)
    (ε : G ⋙ F ≅ 𝟭 (LawvereKSimDCat 2))

  example : LawvereERCat ≌ LawvereKSimDCat 2 :=
    CategoryTheory.Equivalence.mk' F G η ε

  example
      (myEquiv : LawvereERCat ≌ LawvereKSimDCat 2)
      (hF : myEquiv.functor = F)
      (hG : myEquiv.inverse = G) :
      F.IsEquivalence := by
    rw [← hF]
    exact myEquiv.isEquivalence_functor
end InstanceStub

end GebLean
```

- [ ] **Step 6: Type-check the augmented stub**

Re-invoke the `mcp__lean-lsp__lean_run_code` tool with the
*combined* content (the §6.3 stub from Step 3 plus the §6.7
section appended in Step 5).

Expected: no errors. Confirms that `Equivalence.mk'` is the
correct constructor name with the four-arg + autoparam
signature, and that the `isEquivalence_functor` projection
form elaborates.

If it fails: HALT. Same handling as Step 4.

- [ ] **Step 7: Clean up any scratch artifacts**

If the lean-lsp MCP was used (the recommended path), no
on-disk artifact remains; skip this step.

If the alternative `GebLean/Scratch/T5Stubs.lean` path was
used, remove the file and its `lakefile.toml` entry now:

```bash
rm GebLean/Scratch/T5Stubs.lean
rmdir GebLean/Scratch  # if empty
# manually revert the lakefile.toml lean_lib addition
```

The stub has served its purpose. No artifact is committed.

- [ ] **Step 8: Confirm no working-copy changes**

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

- [ ] **Step 1: Add the kInterpFunctor import**

Open `GebLean/LawvereERKSim/ErToKFunctor.lean`. The current
imports are:

```lean
import GebLean.LawvereERKSim.ErToK
import GebLean.LawvereERQuot
import GebLean.LawvereKSimQuot
```

Insert one new import line at the end of the import block:

```lean
import GebLean.LawvereERKSim.ErToK
import GebLean.LawvereERQuot
import GebLean.LawvereKSimQuot
import GebLean.LawvereKSimDCatInterp
```

The new import gives access to `KMorNQuo.interp` (which is
used in the new theorem's signature via `.hom.interp`
dot-notation).

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
            { hom := Quotient.mk (kMorNSetoid n m) (erToKN rec),
              depth_witness := Quotient.mk _
                { rep := erToKN rec,
                  rep_level := fun i => erToKN_level rec i,
                  rep_eq := rfl } })
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

(Subject `add erToKFunctor_comp_kInterp` is 33 chars; with
the `feat(ertok):` prefix plus separating space (13 chars),
total 46 chars, well under the ≤ 72-char target.)

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
triangle identity `functor_unitIso_comp` is discharged by the
`cat_disch` autoparam (both unit and counit component
applications reduce to `eqToHom rfl = 𝟙 _` since both
functors are identity on objects).

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
faithfulness of `erInterpFunctor` plus the two functor-level
interp-preservation equalities to collapse the round-trip
composite to the identity functor. Both functors are identity
on objects, so `CategoryTheory.Functor.ext`'s `eqToHom`
transports reduce to `𝟙 _` and disappear under
`simp only [Category.id_comp, Category.comp_id]`. -/
theorem erToKFunctor_comp_kToERFunctor :
    erToKFunctor ⋙ kToERFunctor = 𝟭 LawvereERCat := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro n m e
  simp only [CategoryTheory.Functor.id_obj,
    CategoryTheory.Functor.comp_obj,
    eqToHom_refl, Category.comp_id, Category.id_comp,
    CategoryTheory.Functor.id_map,
    CategoryTheory.Functor.comp_map]
  apply erInterpFunctor.map_injective
  change (kToERFunctor ⋙ erInterpFunctor).map
            (erToKFunctor.map e)
       = erInterpFunctor.map e
  rw [kToERFunctor_comp_erInterpFunctor]
  change (erToKFunctor ⋙ kInterpFunctor).map e
       = erInterpFunctor.map e
  rw [erToKFunctor_comp_kInterpFunctor]
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
faithfulness of `kInterpFunctor` instead of `erInterpFunctor`.
The two functor-level interp-preservation equalities are
applied in the reverse order from §6.3. -/
theorem kToERFunctor_comp_erToKFunctor :
    kToERFunctor ⋙ erToKFunctor = 𝟭 (LawvereKSimDCat 2) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro n m f
  simp only [CategoryTheory.Functor.id_obj,
    CategoryTheory.Functor.comp_obj,
    eqToHom_refl, Category.comp_id, Category.id_comp,
    CategoryTheory.Functor.id_map,
    CategoryTheory.Functor.comp_map]
  apply kInterpFunctor.map_injective
  change (erToKFunctor ⋙ kInterpFunctor).map
            (kToERFunctor.map f)
       = kInterpFunctor.map f
  rw [erToKFunctor_comp_kInterpFunctor]
  change (kToERFunctor ⋙ erInterpFunctor).map f
       = kInterpFunctor.map f
  rw [kToERFunctor_comp_erInterpFunctor]
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
autoparam is discharged by `cat_disch` because both unit and
counit component applications reduce to `𝟙 _` (both functors
are identity on objects, so `eqToIso _ |>.hom.app X =
eqToHom rfl = 𝟙 X`). -/
def erKSimEquiv : LawvereERCat ≌ LawvereKSimDCat 2 :=
  CategoryTheory.Equivalence.mk'
    erToKFunctor
    kToERFunctor
    erToKKToErIso.symm
    kToErErToKIso
```

- [ ] **Step 2: Verify the equivalence builds**

Run:

```bash
lake build
```

Expected: builds successfully. If `cat_disch` fails to close
the triangle identity, the spec's §6.6 commits to a manual
fallback `(by intro X; simp [eqToIso_symm, eqToIso_hom,
eqToHom_refl])` as an explicit fifth argument; apply it and
re-build.

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
