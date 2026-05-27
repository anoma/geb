# T5 equivalence plan — adversarial review round 3

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary](#summary)
- [Methodology](#methodology)
- [Findings](#findings)
  - [Round-2 status](#round-2-status)
  - [B3 — `cat_disch` does not discharge the triangle for the real `erKSimEquiv`](#b3--cat_disch-does-not-discharge-the-triangle-for-the-real-erksimequiv)
  - [B4 — Spec §6.6 fallback recipes both fail under the current pin](#b4--spec-66-fallback-recipes-both-fail-under-the-current-pin)
  - [B5 — Task 0 Step 5 instance-availability stub fails to elaborate](#b5--task-0-step-5-instance-availability-stub-fails-to-elaborate)
- [Convergence verdict](#convergence-verdict)

<!-- END doctoc -->

## Summary

Verdict: BLOCK — 3 blockers, 0 serious, 0 minor, 0 nits.

Round-2 blockers B1 (anonymous-constructor type ascription)
and B2 (`Functor.hext` proof shape) and round-2 minor M3'
(preamble cleanup) are all resolved and pass active
MCP re-verification on the current mathlib pin. Spec §6.1,
§6.3, §6.4 elaborate as written; plan Task 0 Steps 3 and 6,
Task 1 Step 3, Task 3 Steps 3 and 5 are faithful transcriptions
of those spec sections.

However, round-3 verification of plan Task 0 Step 5
(§6.7 instance-availability stub), plan Task 5 Step 1 / Step 2
(`erKSimEquiv` via `Equivalence.mk'`), and the spec §6.6
fallback recipes surfaced three new blockers. All three trace
to a single underlying fact:

- The `Equivalence.mk' ... ... ... ...` autoparam
  `functor_unitIso_comp` is discharged by `aesop_cat` (the
  mathlib alias `cat_disch` resolves to), and `aesop_cat`
  **cannot** discharge the triangle identity for `eqToIso`-shaped
  unit / counit isomorphisms — the very shape `erKSimEquiv`
  uses.

Symptoms:

- Plan Task 0 Step 5's first `example` (`Equivalence.mk' F G η ε`
  on opaque variables) fails to elaborate because the triangle
  cannot be discharged for opaque `F`, `G`, `η`, `ε`. This is the
  same class of failure as round-2's B1 and B2: the stub the plan
  prescribes does not type-check.
- Plan Task 5 Step 1's `erKSimEquiv` (using the same constructor
  on concrete `eqToIso`-shaped isos) fails to elaborate for the
  same reason: `aesop_cat` does not unfold `eqToIso _ |>.symm.hom
  .app X` to `eqToHom rfl` to reach `𝟙 _`.
- Spec §6.6's stated fallbacks
  `(by intro X; simp [eqToIso_symm, eqToIso_hom, eqToHom_refl])`
  and `(by intro X; dsimp; rfl)` both fail. Fallback A references
  identifiers (`eqToIso_symm`, `eqToIso_hom`) that do not exist
  under the current pin (the actual names are `eqToIso.hom` and
  `eqToIso.inv`, dot-prefixed). Fallback B leaves an unsolved
  `change` and `rfl` cannot close
  `erToKFunctor.map (eqToHom _) ≫ eqToHom _ = 𝟙 _` definitionally.

A working fifth-argument discharge under the current pin is:

```lean
(by intro X; simp [erToKKToErIso, kToErErToKIso,
                   eqToIso.hom, eqToIso.inv])
```

verified by MCP against axiomatised `erToKFunctor_comp_kToERFunctor`
and `kToERFunctor_comp_erToKFunctor`; `erKSimEquiv` elaborates and
both `IsEquivalence` instances follow. The spec must be amended to
adopt this discharge as the load-bearing recipe (not as a
fallback); the plan inherits.

The round-3 spec review (`2026-05-25-step-t5-equivalence-design
.review-3.md`) claimed `cat_disch` would close the triangle
based on a stand-in `MyObj` test with **identity-shaped**
`η`, `ε` (`Iso.refl _`). MCP re-verification confirms that case
works, but the actual `erKSimEquiv` uses `eqToIso (theorem-proof)
.symm` / `eqToIso (theorem-proof)`, which is a **strictly different
shape**: `Iso.refl _` reduces definitionally; `eqToIso h |>.symm
.hom.app X` reduces only under explicit `simp` direction. The
review's stand-in did not exercise the load-bearing shape.

## Methodology

1. Read the revised plan
   ([`2026-05-25-step-t5-equivalence-plan.md`](2026-05-25-step-t5-equivalence-plan.md))
   end-to-end.
2. Read the revised spec
   ([`2026-05-25-step-t5-equivalence-design.md`](../specs/2026-05-25-step-t5-equivalence-design.md))
   end-to-end, focusing on §§6.1, 6.3, 6.4, 6.6, 6.7.
3. Read prior reviews
   (`2026-05-25-step-t5-equivalence-design.review-1.md`,
   `.review-2.md`, `.review-3.md`;
   `2026-05-25-step-t5-equivalence-plan.review-1.md`,
   `.review-2.md`).
4. Re-fetched the four mathlib upstream guides via the in-repo
   digest at `.claude/rules/lean-coding.md` (the rules file's
   §§ Authoritative upstream guides reproduce the binding
   highlights; the live pages were re-fetched in round 2 and
   re-checked here against the revised plan's commit messages
   and naming).
5. Verified `CategoryTheory.Functor.hext` exists at
   `Mathlib/CategoryTheory/EqToHom.lean:256` with signature
   `(h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ X Y (f : X ⟶ Y), F.map f ≍ G.map f) : F = G`.
6. Verified `CategoryTheory.Functor.hcongr_hom` exists at
   `Mathlib/CategoryTheory/EqToHom.lean:304` with signature
   `{F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y) :
    F.map f ≍ G.map f`.
7. Verified `heq_of_eq` and `eq_of_heq` are standard Lean
   prelude (provided by `Init.Core`).
8. Verified `Faithful` instances exist:
   `kInterpFunctor.Faithful` at
   `GebLean/LawvereKSimDCatInterp.lean:84`,
   `erInterpFunctor.Faithful` at
   `GebLean/LawvereERInterp.lean:80`.
9. Verified `kToERFunctor_comp_erInterpFunctor` exists at
   `GebLean/LawvereKSimER.lean:538`.
10. Verified `CategoryTheory.Equivalence` structure at
    `Mathlib/CategoryTheory/Equivalence.lean:85` declares
    `where mk' ::`, so `Equivalence.mk'` is the raw structure
    constructor with the autoparam `functor_unitIso_comp` (line
    99).
11. Active MCP re-verification of round-2 blocker resolutions:

    - Plan Task 0 Step 3 / spec §6.3 (`Functor.hext` proof shape
      for `erToKFunctor_comp_kToERFunctor`) executed through
      `mcp__lean-lsp__lean_run_code` with the two functor-level
      interp-preservation equalities (the landed
      `kToERFunctor_comp_erInterpFunctor` and the hypothesised
      `erToKFunctor_comp_kInterpFunctor`) as inputs. Result:
      `success: true`, no diagnostics. B2 resolved for §6.3.
    - Spec §6.4 (symmetric) via MCP. Result: `success: true`, no
      diagnostics. B2 resolved for §6.4.
    - Plan Task 0 Step 6 / spec §6.1 motive stub with the
      type-ascription `(... : KSimMor 2 n m)` fix. Result:
      `success: true`, only the expected `sorry` warning. B1
      resolved.
    - Combined buffer (plan Task 0 Steps 3 + 5 + 6 + 7
      assembled per the plan's buffer-management instructions).
      Result: see B5 below — combined buffer fails at the §6.7
      instance-availability stub.

12. Active MCP re-verification of the §6.7 instance stub in
    isolation (Step 5 verbatim, with surrounding
    `namespace GebLean ... end GebLean`). Result: `success:
    false`. Error at
    `CategoryTheory.Equivalence.mk' F G η ε`: "could not
    synthesize default value for parameter
    'functor_unitIso_comp' using tactics" / "tactic 'aesop'
    failed". See B5.

13. Active MCP test of the real `erKSimEquiv` shape (Task 5
    Step 1 verbatim, with axiomatised
    `erToKFunctor_comp_kToERFunctor_ax` and
    `kToERFunctor_comp_erToKFunctor_ax` standing in for the
    landed strict equalities). Result: `success: false`.
    Same error: `aesop_cat` cannot discharge the triangle. See
    B3.

14. Active MCP test of spec §6.6's two stated fallback recipes:

    - `(by intro X; simp [eqToIso_symm, eqToIso_hom,
      eqToHom_refl])`: error "Unknown identifier
      `eqToIso_symm`", "Unknown identifier `eqToIso_hom`",
      and unsolved goal.
    - `(by intro X; dsimp; rfl)`: error "Tactic `rfl` failed",
      goal not definitionally equal.

    See B4.

15. Active MCP test of a corrected fallback derived from the
    actual mathlib API:

    ```lean
    (by intro X;
       simp [erToKKToErIso, kToErErToKIso,
             eqToIso.hom, eqToIso.inv])
    ```

    Result: `success: true`. The instances
    `erToKFunctor.IsEquivalence` and
    `kToERFunctor.IsEquivalence` also elaborate. This is the
    minimal working discharge under the current pin; see B4
    Recommendation.

16. Cross-checked the round-3 spec review's `cat_disch` claim
    (§Methodology: "Constructed a stand-in `MyObj` category with
    identity-on-objects `F`, `G`, identity-shaped `η`, `ε`,
    packaged as `def myEquiv : MyObj ≌ MyObj :=
    Equivalence.mk' F G η ε`"). Reproduced the stand-in via MCP
    with `Iso.refl _` for `η` and `ε`: `success: true`.
    Confirmed the round-3 spec review's positive result for the
    `Iso.refl`-shape case but isolated the gap: the stand-in did
    not exercise the `eqToIso`-shape case that `erKSimEquiv`
    actually uses.

17. Cross-checked the AXIOM_ALLOW comment convention against the
    spec's §7 table (`ErToKFunctor.lean` lines 55, 65, 73, 88,
    116, 139 cited as the precedent): comment placement
    (immediately above the declaration or inside its `/-- … -/`
    docstring) matches the convention.

18. Cross-checked banned-command compliance: no `lake env lean`,
    no `lake clean`, no bash process substitution, no raw
    mutating `git`. All verification uses `lake build`,
    `bash scripts/check-axioms.sh`, `lake test`, and
    `mcp__lean-lsp__lean_run_code`. Compliant.

19. Cross-checked commit-message conventions against
    `commit.html`: all-lowercase subject, imperative present
    tense, no trailing period, ≤ 72 chars. Subjects in the plan:

    - `feat(ertok): add erToKFunctor_map_interp` — 45 chars,
      conforming.
    - `feat(ertok): add erToKFunctor_comp_kInterp` — 44 chars,
      conforming.
    - `feat(equivalence): add round-trip strict equalities` —
      52 chars, conforming.
    - `feat(equivalence): add eqToIso natural isos` — 44 chars,
      conforming.
    - `feat(equivalence): package LawvereERCat ≌ LawvereKSimDCat 2` —
      59 chars (≌ counts as one char), conforming.

20. Cross-checked markdownlint-cleanliness of the plan and spec
    by structural inspection (heading hierarchy, fence languages,
    list indentation). No violations spotted.

## Findings

### Round-2 status

- **B1 — RESOLVED.** Spec §6.1 line 313 and plan Task 0 Step 6
  / Task 1 Step 3 all carry the `(... : KSimMor 2 n m)` type
  ascription on the anonymous constructor. MCP confirms the
  motive elaborates (only the expected `sorry` warning fires).
- **B2 — RESOLVED.** Spec §6.3 and §6.4, plan Task 0 Step 3,
  Task 3 Step 3, Task 3 Step 5 all use the `Functor.hext +
  hcongr_hom + Faithful.map_injective` proof shape. MCP confirms
  the shape elaborates cleanly for both directions, with the two
  functor-level interp-preservation equalities as inputs.
- **M3' — RESOLVED.** Plan Task 0 "Files:" preamble (lines
  110–112) now reads exactly the recommended replacement:

  > - No on-disk artifact. T5.0 verifies the spec's stubs via
  >   `mcp__lean-lsp__lean_run_code`; nothing is written under
  >   the project tree. If the MCP is unavailable, HALT per
  >   Step 4.

  No fallback scratch-path reference remains.

### B3 — `cat_disch` does not discharge the triangle for the real `erKSimEquiv`

**Locations.** Plan Task 5 Step 1 (the `erKSimEquiv` definition)
and Task 5 Step 2 ("Expected: builds successfully. If `cat_disch`
fails to close the triangle identity, the spec's §6.6 commits to
a manual fallback ..."). Spec §6.6 lines 504–511.

**Symptom.** MCP execution of the plan Task 5 Step 1 form
verbatim (with axiomatised `erToKFunctor_comp_kToERFunctor` and
`kToERFunctor_comp_erToKFunctor` standing in for the landed
strict equalities of T5.B.1):

```text
error: could not synthesize default value for parameter
  'functor_unitIso_comp' using tactics
error: tactic 'aesop' failed, failed to prove the goal after
  exhaustive search.
Remaining goals after safe rules:
  X : LawvereERCat
  ⊢ erToKFunctor.map (erToKKToErIso.inv.app X)
      ≫ kToErErToKIso.hom.app (erToKFunctor.obj X)
    = 𝟙 (erToKFunctor.obj X)
```

The `cat_disch` autoparam (which dispatches to `aesop_cat`)
cannot reduce the goal: `erToKKToErIso.inv.app X` is
`(eqToIso erToKFunctor_comp_kToERFunctor).inv.app X`, which is
`eqToHom (Functor.congr_obj _ X).symm`, which is `eqToHom rfl
= 𝟙 X` (because both functors are identity on objects), but
`aesop_cat`'s safe-rules set does not unfold `eqToIso.inv` or
`Functor.congr_obj`. The trace in spec §6.6 lines 513–526 is
mathematically correct ("`eqToIso _ |>.symm.hom.app X` is
`eqToHom h.symm` ... `eqToHom rfl = 𝟙 X`"), but the
**tactic** never reaches that normalisation because the unfold
lemmas are not in `aesop_cat`'s set.

**Why this is a blocker.** The plan's Task 5 Step 2 expects
`lake build` to succeed; per the same plan's HALT clause for
type-check failures, the implementer would halt at this point.
But the plan also says "If `cat_disch` fails to close the
triangle identity, the spec's §6.6 commits to a manual fallback
... apply it and re-build." That fallback is itself broken under
the current pin — see B4 — so the implementer cannot proceed
even by following the plan's fallback instruction.

**Fix.** The spec §6.6 must commit explicitly to a fifth
argument that discharges the triangle, **not** rely on
`cat_disch`. The working form (verified via MCP) is:

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

The plan inherits.

### B4 — Spec §6.6 fallback recipes both fail under the current pin

**Locations.** Spec §6.6 lines 528–532; plan Task 5 Step 2
fallback prose.

**Symptom A** — `(by intro X; simp [eqToIso_symm,
eqToIso_hom, eqToHom_refl])`:

```text
error: Unknown identifier `eqToIso_symm`
error: Unknown identifier `eqToIso_hom`
warning: This simp argument is unused: eqToHom_refl
error: unsolved goals ...
```

The names `eqToIso_symm` and `eqToIso_hom` do not exist under
the current pin. The actual mathlib lemmas at
`Mathlib/CategoryTheory/EqToHom.lean:197` and `:201` are
`eqToIso.hom` and `eqToIso.inv` (note the dot prefix and the
`inv`/`hom` distinction; there is no `eqToIso_symm` analogue
because `eqToIso _ |>.symm = eqToIso _.symm` is itself an `Iso`
fact reachable via the simp set).

**Symptom B** — `(by intro X; dsimp; rfl)`:

```text
error: Tactic `rfl` failed: The left-hand side
  erToKFunctor.map (erToKKToErIso.inv.app X)
    ≫ kToErErToKIso.hom.app (erToKFunctor.obj X)
is not definitionally equal to the right-hand side
  𝟙 (erToKFunctor.obj X)
```

`dsimp` does nothing because the expression involves
`eqToIso` applications that are not in the default `dsimp`
unfold set, and `rfl` cannot close the goal because the
`eqToHom`-laden composition is not definitionally `𝟙 _`
(it is propositionally so, via the chain in §6.6 lines
513–526, but propositional equality is not `rfl`).

**Why this is a blocker.** B3's fallback path points at these
recipes; both are broken. The plan as a whole describes no
recipe that actually works under the current pin.

**Fix.** Replace both fallback bullets in §6.6 with the
single working recipe verified above:

```lean
(by intro X;
    simp [erToKKToErIso, kToErErToKIso,
          eqToIso.hom, eqToIso.inv])
```

This unfolds the two `def`-bound `eqToIso` natural
isomorphisms and the two `Iso`-projection lemmas; the
resulting `eqToHom`-of-`rfl` reduces under simp to `𝟙 _`,
and the composition with `𝟙 _` reduces by mathlib's standard
category simp set. MCP-verified.

### B5 — Task 0 Step 5 instance-availability stub fails to elaborate

**Locations.** Plan Task 0 Step 5 lines 232–254 (the
§6.7 instance-availability stub).

**Symptom.** MCP execution of the verbatim Step 5 snippet
(within `namespace GebLean ... end GebLean`):

```text
error: could not synthesize default value for parameter
  'functor_unitIso_comp' using tactics
error: tactic 'aesop' failed, failed to prove the goal after
  exhaustive search.
Initial goal:
  F : LawvereERCat ⥤ LawvereKSimDCat 2
  G : LawvereKSimDCat 2 ⥤ LawvereERCat
  η : 𝟭 LawvereERCat ≅ F ⋙ G
  ε : G ⋙ F ≅ 𝟭 (LawvereKSimDCat 2)
  ⊢ ∀ (X : LawvereERCat),
    F.map (η.hom.app X) ≫ ε.hom.app (F.obj X) = 𝟙 (F.obj X)
```

The first `example` (`CategoryTheory.Equivalence.mk' F G η ε`)
asks `aesop_cat` to discharge the triangle identity for opaque
`F`, `G`, `η`, `ε`. The triangle is not provable for opaque
data; `aesop_cat` cannot make any reduction.

**Why this is a blocker.** Plan Task 0 Step 7 ("Type-check the
fully assembled stub") expects "no errors (a `sorry` warning on
the §6.1 example is expected and acceptable)". The MCP returns
two errors at the first `example` in Step 5. The plan's HALT
clause then fires — but the failure is in the plan's stub
construction itself, not in any spec-level claim that would
require a downstream amendment.

**Why the round-3 spec review missed this.** The spec review
constructed a stand-in `myEquiv : MyObj ≌ MyObj` with `η`, `ε`
of shape `Iso.refl _` (identity-shaped). MCP confirms that
case succeeds — `aesop_cat` reduces both sides to `𝟙 _`
directly. But the plan's Step 5 stub uses opaque variables,
and the actual `erKSimEquiv` uses `eqToIso _ .symm` /
`eqToIso _`; neither matches the `Iso.refl _` shape that the
spec review tested.

**Fix.** Replace the first `example` body in Step 5 with a
form that supplies an explicit fifth argument matching the
shape `erKSimEquiv` will actually use, or — simpler — drop
the opaque-variable test entirely and substitute the concrete
form against axiomatised strict equalities (paralleling B3's
fix). The minimal working replacement:

```lean
section InstanceStub
  variable
    (erToKFunctor_comp_kToERFunctor :
      erToKFunctor ⋙ kToERFunctor = 𝟭 LawvereERCat)
    (kToERFunctor_comp_erToKFunctor :
      kToERFunctor ⋙ erToKFunctor = 𝟭 (LawvereKSimDCat 2))

  example : LawvereERCat ≌ LawvereKSimDCat 2 :=
    CategoryTheory.Equivalence.mk'
      erToKFunctor
      kToERFunctor
      (eqToIso erToKFunctor_comp_kToERFunctor).symm
      (eqToIso kToERFunctor_comp_erToKFunctor)
      (by intro X;
          simp [eqToIso.hom, eqToIso.inv])

  example
      (myEquiv : LawvereERCat ≌ LawvereKSimDCat 2) :
      erToKFunctor.IsEquivalence
      ∨ kToERFunctor.IsEquivalence := by
    left; exact (myEquiv.isEquivalence_functor : _)
end InstanceStub
```

Or, since B3's fix already commits the spec's §6.6 to the
fifth-argument form, the cleaner choice is to delete the
§6.7 stub from Task 0 entirely and verify the real instance
declarations directly in Task 5 (the SDD loop already covers
this case under the per-task `lake build` step).

## Convergence verdict

BLOCK — 3 blockers (B3, B4, B5), 0 serious, 0 minor, 0 nits.

Round-2 blockers B1 and B2 and round-2 minor M3' are
resolved. Round-3 verification surfaced a tightly-coupled
cluster of three new blockers all rooted in the
`cat_disch` autoparam's inability to discharge the triangle
identity for `eqToIso`-shaped (and opaque-variable)
unit/counit isomorphisms. The spec §6.6 fallback recipes
are themselves broken. The plan-as-written prescribes
Lean code that does not type-check at Task 0 Step 5
(stub), Task 5 Step 1 (real `erKSimEquiv`), and offers no
working fallback at Task 5 Step 2.

Per CLAUDE.md and `docs/process.md` § Adversarial review,
BLOCK re-dispatches the spec for amendment and the plan for
re-write of Task 0 Step 5 (B5) and Task 5 Steps 1–2 (B3, B4).
A round-4 plan review will be needed after those amendments
land.

Re-dispatch order suggested:

1. Spec amendment round (`.review-4.md` on the spec) to
   replace §6.6's `cat_disch` claim and the two failed
   fallback recipes with the MCP-verified
   `simp [erToKKToErIso, kToErErToKIso, eqToIso.hom,
   eqToIso.inv]` discharge as a load-bearing explicit fifth
   argument; the spec amendment must be MCP-verified before
   committing.
2. Plan re-revision (carrying the spec fix into Task 5
   Step 1's `erKSimEquiv` body, removing Task 5 Step 2's
   stale fallback prose, and replacing Task 0 Step 5's
   opaque-variable stub with either the axiomatised-strict-
   equality form above or deleting the stub entirely).
3. Round-4 plan adversarial review.

No unaddressed round-1 or round-2 findings remain in either
the spec or the plan; the new blockers were not raised in
prior rounds because no prior reviewer ran the §6.6
`Equivalence.mk'` discharge against the `eqToIso`-shape
unit/counit (the round-3 spec review tested `Iso.refl`-shape
data, which `cat_disch` does handle).
