# T5 spec adversarial review — round 1

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary](#summary)
- [Methodology](#methodology)
- [Findings](#findings)
  - [B1 — `Equivalence.mk` does not preserve the user-supplied unit](#b1--equivalencemk-does-not-preserve-the-user-supplied-unit)
  - [S1 — Autoparam default is `by cat_disch`, not `by aesop_cat`](#s1--autoparam-default-is-by-cat_disch-not-by-aesop_cat)
  - [S2 — Round-trip strict-equality strengthening is unverified](#s2--round-trip-strict-equality-strengthening-is-unverified)
  - [S3 — Duplicate `IsEquivalence` instances on `erToKFunctor` and `kToERFunctor`](#s3--duplicate-isequivalence-instances-on-ertokfunctor-and-ktoerfunctor)
  - [S4 — §6.1 motive form does not match the mirror's `rcases`-based shape](#s4--61-motive-form-does-not-match-the-mirrors-rcases-based-shape)
  - [S5 — `(erToKFunctor_map e).hom.interp` type-shape mismatch](#s5--ertokfunctor_map-ehominterp-type-shape-mismatch)
  - [M1 — §6.6 narration about eqToHom rfl is stated of `.symm`](#m1--66-narration-about-eqtohom-rfl-is-stated-of-symm)
  - [M2 — Value-laden adjectives in spec prose](#m2--value-laden-adjectives-in-spec-prose)
  - [M3 — Spec calls T5-A both "warm-up" and "the first tasks"](#m3--spec-calls-t5-a-both-warm-up-and-the-first-tasks)
  - [M4 — Commit-message subjects: `(equivalence)` scope before file exists](#m4--commit-message-subjects-equivalence-scope-before-file-exists)
  - [M5 — `Equivalence` documented as "isomorphism of categories"](#m5--equivalence-documented-as-isomorphism-of-categories)
  - [M6 — Module-docstring "Implementation notes" / "Notation" sections](#m6--module-docstring-implementation-notes--notation-sections)
  - [M7 — Tourlakis citation: section vs Corollary](#m7--tourlakis-citation-section-vs-corollary)
  - [N1 — `lake test` in §10's verification list](#n1--lake-test-in-10s-verification-list)
  - [N2 — Inconsistent use of `LawvereKSimDCat 2` parenthesisation](#n2--inconsistent-use-of-lawvereksimdcat-2-parenthesisation)
  - [N3 — `unfold erToKFunctor_map` may not unfold the `Quotient.liftOn`](#n3--unfold-ertokfunctor_map-may-not-unfold-the-quotientlifton)
- [Convergence verdict](#convergence-verdict)

<!-- END doctoc -->

## Summary

One blocker, five serious findings, seven minor findings, three nits.
The blocker concerns `Equivalence.mk`'s semantics: mathlib's
`Equivalence.mk` does not store the user-supplied unit isomorphism
verbatim, it routes it through `adjointifyη η ε`, so the spec's
claim in §6.6 that "the triangle identity is expected to reduce
trivially" via `aesop_cat` rests on a structural misreading. The
serious findings cover the consequent uncertainty about the
"strict equality strengthening" central to §1's framing, a
redundant-instances concern, motive-shape divergence from the
mirror, and the outdated `aesop_cat` autoparam. The minor and nit
findings are markdown / prose / convention issues. Overall the
proof skeleton is structurally sound but several mathlib API
claims are stale or wrong, and the strengthening claim in §1
needs verification or scope adjustment before the spec can ship.

## Methodology

Read end-to-end:

- The spec at
  `docs/superpowers/specs/2026-05-25-step-t5-equivalence-design.md`.
- `CLAUDE.md`, `.claude/rules/lean-coding.md`,
  `.claude/rules/markdown-writing.md`.
- The post-T4 handoff at
  `docs/superpowers/plans/2026-05-25-post-t4-handoff.md`.
- Mirror code in `GebLean/LawvereKSimER.lean` lines 336–571, in
  particular `kToERN`, `kToERN_compat_extEq`,
  `kToERFunctor_map_interp` (line 488),
  `kToERFunctor_comp_erInterpFunctor` (line 538).
- `GebLean/LawvereKSimDCatInterp.lean` (kInterpFunctor at lines
  67–79; faithful instance at line 84).
- `GebLean/LawvereERInterp.lean` (erInterpFunctor at lines
  64–73; faithful instance at line 80).
- `GebLean/LawvereERKSim/ErToKFunctor.lean` (full file: the T4
  landed surface, with `erToKN_*` and `erToKFunctor_*` shapes).
- Mathlib `CategoryTheory/Equivalence.lean` lines 85–105 (the
  `Equivalence` structure declared with `mk' ::`, with
  autoparam default `by cat_disch`) and lines 348–352 (the
  smart constructor `Equivalence.mk`).
- Mathlib `CategoryTheory/Functor/Basic.lean` line 124
  (`Functor.comp_map = rfl`).
- Mathlib `CategoryTheory/Functor/FullyFaithful.lean` lines
  48–60 (`Faithful` class and `map_injective`).
- Mathlib `CategoryTheory/EqToHom.lean` lines 234–248
  (`Functor.ext` signature).
- `scripts/check-axioms.sh` (AXIOM_ALLOW scanning convention).

Re-fetched mathlib upstream guide highlights from the in-repo
digest in `.claude/rules/lean-coding.md`; cross-checked against
spec names, suggested commit messages, and doc placeholders.

## Findings

### B1 — `Equivalence.mk` does not preserve the user-supplied unit

**Location**: §6.6 and §6.7; also the framing in §1.

**Claim in spec**: §6.6 writes

```lean
def erKSimEquiv : LawvereERCat ≌ LawvereKSimDCat 2 :=
  CategoryTheory.Equivalence.mk
    erToKFunctor
    kToERFunctor
    erToKKToErIso.symm
    kToErErToKIso
```

and §6.6 narrates: "The triangle identity is expected to reduce
trivially: `η.hom.app X` and `ε.hom.app X` are both
`eqToHom rfl = 𝟙 X` ... `aesop_cat` is expected to close this; if
not, the manual discharge is `intro X; simp` or
`intro X; dsimp; rfl`."

**Problem**: Mathlib's `Equivalence.mk` at
`.lake/packages/mathlib/Mathlib/CategoryTheory/Equivalence.lean:351–352`
is

```lean
protected def mk (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G)
    (ε : G ⋙ F ≅ 𝟭 D) : C ≌ D :=
  ⟨F, G, adjointifyη η ε, ε, adjointify_η_ε η ε⟩
```

It takes exactly four arguments — no autoparam — and does not
store `η` as `unitIso`; it stores `adjointifyη η ε`, a corrected
unit assembled from `η` and `ε` so that the triangle identity
holds by construction (`adjointify_η_ε η ε`).

This invalidates two of the spec's claims:

1. §6.6's narration about "η.hom.app X is `eqToHom rfl = 𝟙 X`" is
   describing the **input** `erToKKToErIso.symm`, not the
   `unitIso` slot of the resulting `Equivalence`. The triangle
   identity is **provided automatically** by `Equivalence.mk` via
   `adjointify_η_ε`, so the "expected to reduce trivially" /
   "fallback to aesop_cat" discussion is moot — there is no
   autoparam to close.
2. Consequently the spec's framing as a strict isomorphism of
   categories (§1) is at risk: the `unitIso` of
   `erKSimEquiv` is **not** `eqToIso erToKFunctor_comp_kToERFunctor`
   — it is the adjointified version. The strict
   equality theorems in §4.2 remain valid as stated, but they
   are **not** what `erKSimEquiv.unitIso` reduces to. Downstream
   code that uses `erKSimEquiv.unitIso` will see the
   adjointified form, not the raw `eqToIso` form.

The spec should either:

- Use the raw structure constructor `Equivalence.mk'` with
  the four explicit fields (and the autoparam discharged
  manually), preserving `unitIso = erToKKToErIso.symm` as written;
  OR
- Acknowledge that `erKSimEquiv.unitIso` is the adjointified
  form, and (a) provide a separate `eqToIso`-form lemma if
  downstream callers need it, (b) drop the §1 framing of
  "strict isomorphism of categories" or restate it as a
  property of the round-trip composites (which holds) rather
  than a property of the `Equivalence` packaging.

The raw `mk'` constructor (declared via `where mk' ::` at line
85 of mathlib's `Equivalence.lean`) takes:

```lean
(functor : C ⥤ D) (inverse : D ⥤ C)
(unitIso : 𝟭 C ≅ functor ⋙ inverse)
(counitIso : inverse ⋙ functor ≅ 𝟭 D)
(functor_unitIso_comp :
  ∀ X, functor.map (unitIso.hom.app X) ≫
       counitIso.hom.app (functor.obj X) =
       𝟙 (functor.obj X) := by cat_disch)
```

Note `mk'` is the **structure-level** auto-generated constructor;
the file declares the structure as `where mk' ::`, suppressing
the default name `mk` for the structure constructor and reserving
`mk` for the smart constructor at line 351 that
adjointifies. Using `mk'` directly with the four-arg shape +
autoparam preserves user-supplied unit and counit verbatim, and
the §6.6 narration about the triangle reducing trivially via
`cat_disch` (see S1) applies to **that** form.

**Recommendation**: Replace `Equivalence.mk` with anonymous-
constructor syntax `⟨..., ..., ..., ..., by ...⟩` matching the
raw `mk'` field order, or with explicit `Equivalence.mk' F G η ε
(by ...)`; **verify** during implementation that the typeclass
search for `IsEquivalence` instances (S3) still works with this
form (it should: `Equivalence.isEquivalence_functor` consumes any
`Equivalence`, regardless of which constructor produced it).
Update §1's strict-equality framing to match whichever path is
chosen.

### S1 — Autoparam default is `by cat_disch`, not `by aesop_cat`

**Location**: §6.6.

**Claim in spec**: "plus an autoparam `functor_unitIso_comp : ∀
X, F.map (η.hom.app X) ≫ ε.hom.app (F.obj X) = 𝟙 (F.obj X) := by
aesop_cat`."

**Problem**: The actual autoparam in
`.lake/packages/mathlib/Mathlib/CategoryTheory/Equivalence.lean:99–101`
is `by cat_disch`, not `by aesop_cat`. Mathlib has shifted to a
dedicated `cat_disch` tactic for category-theory autoparams (also
visible in `NatTrans.lean:56`, `EqToHom.lean:238`, and many other
mathlib category-theory files). This is the current pin's API.

**Recommendation**: Change `aesop_cat` to `cat_disch` in §6.6
and elsewhere if relevant. If B1's recommendation is followed
(use `mk'` directly), the `by cat_disch` default is still what
the structure offers; the spec should mention this for accuracy
even though the implementation might still need a manual
discharge.

### S2 — Round-trip strict-equality strengthening is unverified

**Location**: §1, §4.2, §6.3.

**Claim in spec**: "T5 proves the two round-trip composites
`erToKFunctor ⋙ kToERFunctor = 𝟙 LawvereERCat` and
`kToERFunctor ⋙ erToKFunctor = 𝟙 (LawvereKSimDCat 2)` as strict
equalities of functors (an isomorphism of categories, not merely
a categorical equivalence)."

**Problem**: The proof shape in §6.3 reduces to:

```lean
apply erInterpFunctor.map_injective
change (kToERFunctor ⋙ erInterpFunctor).map (erToKFunctor.map e)
     = erInterpFunctor.map e
rw [kToERFunctor_comp_erInterpFunctor]
change (erToKFunctor ⋙ kInterpFunctor).map e
     = erInterpFunctor.map e
rw [erToKFunctor_comp_kInterpFunctor]
```

After the first `rw`, the LHS becomes `kInterpFunctor.map
(erToKFunctor.map e)`. The second `change` rewrites this via
definitional `Functor.comp_map` to `(erToKFunctor ⋙
kInterpFunctor).map e`. The second `rw` then turns the LHS into
`erInterpFunctor.map e`, which is the RHS.

This argument is sound **provided** that `kToERFunctor.map
(erToKFunctor.map e)` and `(kToERFunctor ⋙ erInterpFunctor).map
(erToKFunctor.map e)` line up by `change`-unification — but
`kToERFunctor.map (erToKFunctor.map e)` involves applying
`kToERFunctor.map` to a term of type `KSimMor 2 n m`, and the
goal after `apply ... map_injective` is
`erInterpFunctor.map (kToERFunctor.map (erToKFunctor.map e)) =
erInterpFunctor.map e`. The `change` to `(kToERFunctor ⋙
erInterpFunctor).map (erToKFunctor.map e)` reduces by
`Functor.comp_map = rfl` to `erInterpFunctor.map
(kToERFunctor.map (erToKFunctor.map e))`, which is the LHS. So
this `change` should succeed.

However, the `simp only [..., Category.comp_id, Category.id_comp,
Functor.id_map, Functor.comp_map]` set at the start of the proof
introduces `Functor.comp_map` as a `simp` lemma, which rewrites
the LHS to `kToERFunctor.map (erToKFunctor.map e)`. That happens
**before** the `apply ... map_injective`. After `simp` rewrites,
the subsequent `change (kToERFunctor ⋙ erInterpFunctor).map
(erToKFunctor.map e) = ...` is the **reverse** of the rewrite —
asking Lean to fold `kToERFunctor.map (erToKFunctor.map e)` back
to `(kToERFunctor ⋙ erInterpFunctor).map (erToKFunctor.map e)`.
Since `Functor.comp_map = rfl`, both directions are
definitionally equal, so `change` should succeed.

The proof is plausible but rests on several `rfl`-by-defeq steps
that should be verified during implementation rather than
assumed. The spec asserts the strengthening as a fact without
having actually elaborated the proof; this is an unverified
claim at spec time.

**Recommendation**: Replace "T5 proves … as strict equalities of
functors" in §1 with "T5 proves … as strict equalities of
functors **subject to the proof shape in §6.3/§6.4 going
through**; if those proofs require `eqToHom` transports for
reasons not apparent from the spec, the implementation falls
back to natural-isomorphism-level statements only." Or: commit
to writing a one-page `lake build`-only sanity check inside T5.0
that compiles a stub of §6.3's proof shape to verify it
type-checks before the spec is locked.

### S3 — Duplicate `IsEquivalence` instances on `erToKFunctor` and `kToERFunctor`

**Location**: §6.7.

**Claim in spec**:

```lean
instance : erToKFunctor.IsEquivalence :=
  erKSimEquiv.isEquivalence_functor
instance : kToERFunctor.IsEquivalence :=
  erKSimEquiv.symm.isEquivalence_functor
```

**Problem**: Mathlib already provides
`Equivalence.isEquivalence_functor` and
`Equivalence.isEquivalence_inverse` as global `instance`s at
`Equivalence.lean:630` and `:632`. These automatically supply
`IsEquivalence (e.functor)` and `IsEquivalence (e.inverse)` for
any `e : C ≌ D` via typeclass search. Since `erKSimEquiv.functor`
is **definitionally** `erToKFunctor` (because
`Equivalence.mk F G η ε` puts `F` in the `functor` field), Lean's
typeclass search will already find `IsEquivalence erToKFunctor`
without the explicit instance — provided typeclass elaboration is
willing to unfold `erKSimEquiv.functor` to `erToKFunctor`.

If typeclass search **does** unfold this (likely, since `Equivalence`
projections are `@[simps]`-derived), the spec's explicit
instances are **redundant** and risk producing an "instance
already declared" warning or causing diamond-search issues. If
typeclass search **does not** unfold this, the explicit instances
are useful — but the spec should commit to which path it expects,
and justify the redundancy if it intends to keep the explicit
instances anyway.

Also: `erKSimEquiv.symm.isEquivalence_functor` produces an
`IsEquivalence (erKSimEquiv.symm.functor)`. But
`erKSimEquiv.symm.functor` is `erKSimEquiv.inverse = kToERFunctor`
definitionally. The explicit instance is therefore equivalent to
the global `Equivalence.isEquivalence_inverse` applied to
`erKSimEquiv`, which is shorter.

**Recommendation**: Either drop the explicit instances (rely on
the global mathlib instances) or keep them with explicit
justification in §6.7 that the project prefers to surface
typeclass-search anchors at the named functor level. If kept,
state the second one as
`erKSimEquiv.isEquivalence_inverse` rather than going through
`.symm`.

### S4 — §6.1 motive form does not match the mirror's `rcases`-based shape

**Location**: §6.1 versus the mirror at
`LawvereKSimER.lean:488–520`.

**Claim in spec**: §6.1 says "Mirror: `kToERFunctor_map_interp`
at `LawvereKSimER.lean:488–520`. The motive-shape detail (the
`Quotient.liftOn` placeholders) is identical to the mirror's
form, with K/ER swapped."

**Problem**: The mirror at line 488 starts:

```lean
theorem kToERFunctor_map_interp ... := by
  unfold kToERFunctor_map
  rcases f with ⟨fh, fdw⟩
  refine Quotient.inductionOn (motive := fun fdw : ... => ...) fdw ?_
```

It destructures `f : KSimMor 2 n m` into `⟨fh, fdw⟩` because
`KSimMor` is a structure with `hom` and `depth_witness` fields,
and the `Quotient.inductionOn` is on the **depth_witness**, not
on the top-level argument.

§6.1's proof has:

```lean
unfold erToKFunctor_map
refine Quotient.inductionOn
    (motive := fun (e : ERMorNQuo n m) => ...) e ?_
```

The target argument is `e : ERMorNQuo n m` — a plain quotient.
This is correct in shape **because** `erToKFunctor_map` lifts
from `ERMorNQuo` (not from a structure). But the spec's claim
that the motive shape is "identical … with K/ER swapped" is
incorrect: the mirror's motive is on the depth witness because of
the depth-witness wrapper, whereas the spec's motive is directly
on the ER quotient. The two proofs are structurally similar but
not "identical with K/ER swapped" — there's an asymmetry from
the fact that `LawvereERCat`'s morphisms are a bare quotient
whereas `LawvereKSimDCat 2`'s morphisms are a sigma over a
depth witness.

**Recommendation**: Reword §6.1's mirror-claim to "mirrors the
structure of `kToERFunctor_map_interp`; the motive operates
directly on the ER quotient (rather than the K side's depth
witness, since `LawvereERCat`'s morphisms are a bare quotient)."

### S5 — `(erToKFunctor_map e).hom.interp` type-shape mismatch

**Location**: §4.1 (type signature of `erToKFunctor_map_interp`)
and §6.1.

**Claim in spec**: The signature in §4.1 reads
`∀ {n m : ℕ} (e : ERMorNQuo n m), (erToKFunctor_map e).hom.interp
= e.interp`.

**Problem**: `erToKFunctor_map e : KSimMor 2 n m`, so
`(erToKFunctor_map e).hom : KMorNQuo n m`, so
`(erToKFunctor_map e).hom.interp : (Fin n → ℕ) → (Fin m → ℕ)`.
But `e.interp` on `e : ERMorNQuo n m` is `ERMorNQuo.interp e`,
which is also `(Fin n → ℕ) → (Fin m → ℕ)`. So the type-shape is
fine — but the `.hom.interp` notation needs `KMorNQuo.interp` to
be resolvable via dot notation on `KMorNQuo`, which it is by the
definition at `LawvereKSimDCatInterp.lean:25` (`def
KMorNQuo.interp`). Confirmed.

However, the spec's *mirror* form `(kToERFunctor_map f).interp =
f.hom.interp` at `LawvereKSimER.lean:489–490` is differently
shaped: the LHS is `(kToERFunctor_map f).interp` (where the
result is `ERMorNQuo n m`, no `.hom` needed) and the RHS is
`f.hom.interp` (where `f : KSimMor 2 n m`, so `.hom` extracts).
The spec's T5-A.1 swaps the `.hom` from RHS to LHS, which is
correct for the K-result direction — but it means §6.1's
`change (erToKN rec j).interp ctx = (rec j).interp ctx` is
operating on `KMor1` (since `erToKN rec : KMorN n m`), whereas
the mirror's analogous `change` works on `ERMor1`. The spec
doesn't explicitly note this — a reader might assume the `change`
is matching the mirror line for line.

Furthermore, the spec's signature uses `.hom.interp` with **two
dot accesses**. Lean's `KMorNQuo.interp` from
`LawvereKSimDCatInterp.lean:25` is a function `KMorNQuo n m →
(Fin n → ℕ) → (Fin m → ℕ)`; the dot notation requires the
namespace prefix to match. `(erToKFunctor_map e).hom :
KMorNQuo n m`, so `.interp` resolves to `KMorNQuo.interp` by dot
notation. This should work.

**Recommendation**: Reword §6.1 to note that the proof shape
differs from the mirror in this respect: the K side `.interp`
applies to the `KMorN` constructed by `erToKN`, not to an
`ERMor1`-shaped term. Confirm by hand that the `change` step
elaborates against the post-`Quotient.inductionOn` goal.

### M1 — §6.6 narration about eqToHom rfl is stated of `.symm`

**Location**: §6.6.

**Claim in spec**: "`η.hom.app X` and `ε.hom.app X` are both
`eqToHom rfl = 𝟙 X` (both obj equalities ... are `rfl`)."

**Problem**: `η` is `erToKKToErIso.symm`, which is the symm of an
`eqToIso`. By mathlib's `eqToIso_symm` / `Iso.symm`-on-`eqToIso`
behavior, `(eqToIso h).symm = eqToIso h.symm`. So `η.hom.app X =
(eqToIso erToKFunctor_comp_kToERFunctor.symm).hom.app X =
eqToHom (Functor.congr_obj _ X)`. The obj equality is
`(𝟙 LawvereERCat).obj X = (erToKFunctor ⋙ kToERFunctor).obj X`,
which **is** `rfl` since both sides equal `X` — but the
narration glosses over the application-of-`.app` step that
extracts a per-component morphism from a natural iso of functors.
The collapse to `𝟙 X` requires that `Functor.congr_obj
erToKFunctor_comp_kToERFunctor.symm X = rfl`, which holds since
the obj-part of the iso has `eqToHom rfl = 𝟙` collapse.

This is minor — the proof should still go through — but the
narration as written is imprecise about which `eqToHom rfl`
applies to what term. Subsumed by B1's recommendation to switch
to `mk'` (where the triangle is discharged directly), this
becomes moot.

**Recommendation**: If B1 is resolved by switching to raw `mk'`,
either spell out the `eqToIso` / `.symm` / `.hom.app` reduction
chain in §6.6, or replace the narration with "the autoparam
default `by cat_disch` is expected to close the triangle; if
not, manual discharge `intro X; simp [eqToIso, ...]` is the
fallback."

### M2 — Value-laden adjectives in spec prose

**Location**: §1 ("the headline result"); §1 ("free"); §6.6
("expected to reduce trivially"); §11.7 ("reasonably creep").

**Claim in spec**: Various adjectives flagged by
`.claude/rules/markdown-writing.md` § Prose style and `CLAUDE.md`
§ Style guidelines.

**Problem**: The rules list "key / important / crucial / elegant /
beautiful / neat / clever / powerful / interesting" — the spec
uses **headline** ("the headline result the ER ↔ K^sim_2
workstream has been building toward"), **free** ("makes the
strict-equality strengthening free"), **trivially** ("expected to
reduce trivially"). These are stylistic markers more than
informational. Per the project's prose discipline they should be
replaced or removed.

**Recommendation**: Replace "headline" with "Tourlakis 2018
§0.1.0.44 at n = 2" (already in the same sentence; the
"headline" qualifier adds nothing). Replace "free" with
"available without additional proof effort beyond what
faithfulness supplies" (or similar). Replace "trivially" with
"by `rfl`" or "definitionally" where appropriate. Scan the rest
of the spec for similar markers.

### M3 — Spec calls T5-A both "warm-up" and "the first tasks"

**Location**: Spec §1 (uses "warm-up" not at all; the post-T4
handoff calls T5-A "warm-up"); spec §5 (calls T5-A.1 and T5-A.2
the first commits).

**Problem**: The post-T4 handoff at `post-t4-handoff.md`
introduces "T5-A — Two small named-composite tasks (warm-up)" —
but the spec text drops the "warm-up" framing entirely. This
isn't a contradiction inside the spec but the project's framing
moves between documents. The bigger concern: §5 says T5-A.1
"≈ 18 LOC" and T5-A.2 "≈ 15 LOC" while the handoff's T5-A
section calls them "≈ 15 Lean lines" and "≈ 10 Lean lines"
respectively. The spec's higher estimates should be reconciled
with the handoff's lower ones, or at least acknowledged.

**Recommendation**: Note in §5 that the spec's LOC estimates
include docstring + AXIOM_ALLOW + signature + proof body (a
larger envelope than the handoff's "Lean lines" figure); pin
which envelope is canonical.

### M4 — Commit-message subjects: `(equivalence)` scope before file exists

**Location**: §10 (commit-message conventions).

**Claim in spec**: Suggested subjects:

- T5.A.1: `feat(equivalence): add erToKFunctor_map_interp`
- T5.A.2: `feat(equivalence): add erToKFunctor_comp_kInterpFunctor`
- T5.B.1: `feat(equivalence): add round-trip strict equalities`
- T5.B.2: `feat(equivalence): add eqToIso natural isomorphisms`
- T5.C: `feat(equivalence): package LawvereERCat ≌ LawvereKSimDCat 2`

**Problem**: All five subjects use scope `(equivalence)`. But
T5.A.1 and T5.A.2 land in `ErToKFunctor.lean`, not in
`Equivalence.lean` (which doesn't exist until T5.B.1). The scope
conventionally tracks the file/module being modified. Either:

- T5.A.1 and T5.A.2 should use scope `(ertok)` (matching prior
  T4 commits in `ErToKFunctor.lean`); or
- The scope `(equivalence)` is taken to mean "the equivalence
  workstream" not "the `Equivalence.lean` file", which is fine
  but should be stated explicitly.

Also: T5.A.2's subject `add erToKFunctor_comp_kInterpFunctor`
is 63 chars + the `feat(equivalence):` prefix (19 chars including
trailing space) = 82 chars total,
**exceeding the ≤ 72-char target** in `.claude/rules/lean-coding.md`
§ Commit messages. T5.C's `package LawvereERCat ≌ LawvereKSimDCat
2` is 49 chars + 19-char prefix = 68 chars — under but close.

**Recommendation**: Reduce T5.A.2's subject (e.g., `add
erToKFunctor_comp_kInterp`) or use a different scope. Pin the
scope semantics in §10.

### M5 — `Equivalence` documented as "isomorphism of categories"

**Location**: §1.

**Claim in spec**: "T5 proves the two round-trip composites … as
strict equalities of functors (an isomorphism of categories, not
merely a categorical equivalence)."

**Problem**: This is technically right (strict round-trip equality
yields an isomorphism of categories, which is strictly stronger
than an equivalence). But the parenthetical "not merely a
categorical equivalence" — given B1's finding that
`Equivalence.mk` adjointifies — overpromises what the **packaging**
delivers. The strict equalities are theorems, but the
`Equivalence` packaging is not an "isomorphism of categories"
unless we also expose the underlying strict equalities to
downstream callers (which T5 does, as separate theorems).

**Recommendation**: Reword to "T5 proves the strict round-trip
equalities (theorem-level) and packages them as a
`CategoryTheory.Equivalence` (the standard mathlib structure)."
Avoid the "isomorphism of categories" claim if B1's resolution
puts adjointification between the user-supplied isos and the
stored `unitIso`.

### M6 — Module-docstring "Implementation notes" / "Notation" sections

**Location**: §3 (module-docstring template for
`Equivalence.lean`).

**Claim in spec**: §3 shows the placeholder

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

**Problem**: Per `.claude/rules/lean-coding.md` § Documentation,
the required sections are: `# Title`, brief summary, `## Main
definitions`, `## Main statements`, `## Notation` (**if any**),
`## Implementation notes` (**if any**), `## References` (**if
any**), and `## Tags`. The spec's template omits "Notation" and
"Implementation notes" — fine if they're not needed, but the
spec should state which "if any" sections will be present. Given
that T5-A surfaces a `aesop_cat` / `cat_disch` discharge
decision (now updated per S1), an "Implementation notes" section
might be informational.

**Recommendation**: Either pin that `Equivalence.lean`'s module
docstring will have no "Notation" / "Implementation notes"
sections, or include them with placeholder content (e.g.,
"Implementation notes: triangle-identity discharge uses
`cat_disch` per the mathlib autoparam default" if §6.6 keeps the
autoparam form).

### M7 — Tourlakis citation: section vs Corollary

**Location**: §1, §2, §12 use "§0.1.0.44"; the handoff at
post-T4-handoff.md and the existing `kToERFunctor` docstring
both use "Corollary 0.1.0.44" (visible in `LawvereKSimER.lean:
180–182`).

**Problem**: Citation style inconsistency. Either is fine; pick
one.

**Recommendation**: Adopt one form (the handoff's "Corollary
0.1.0.44" reads slightly clearer; mathlib doc-style citations
typically include the artifact type) and use it consistently
across spec, plan, and docstrings.

### N1 — `lake test` in §10's verification list

**Location**: §10 (verification before each commit, item 5).

**Claim in spec**: "5. `lake test` succeeds (only formality at
this layer; no new tests in T5 per §8)."

**Problem**: §8 commits to "No `#guard` or runtime tests at this
layer." If no new tests are added, `lake test` runs the **same
test suite** as before T5 — it's not a meaningful "verification"
of T5 content. The check is a defensive practice against
accidentally breaking the existing test suite, which is fine, but
the spec should say so rather than imply T5 adds tests that
`lake test` validates.

**Recommendation**: Reword: "5. `lake test` succeeds (carries
the pre-T5 test suite unchanged; safeguards against accidental
breakage of existing tests, not new T5 content)."

### N2 — Inconsistent use of `LawvereKSimDCat 2` parenthesisation

**Location**: §4.2, §4.3, §6.3, §6.4, §6.6.

**Claim in spec**: Sometimes `𝟙 (LawvereKSimDCat 2)`, sometimes
`(LawvereKSimDCat 2)` without `𝟙`, sometimes `LawvereKSimDCat 2`
bare.

**Problem**: Style inconsistency. `LawvereKSimDCat 2` is an
application of a function to a `ℕ` argument; in mathlib style
the parenthesisation is mandatory whenever the term is the
argument of another operator (`𝟙 _` and `≌`).

**Recommendation**: Audit and standardise. Likely the canonical
form is `𝟙 (LawvereKSimDCat 2)` and `LawvereERCat ≌
LawvereKSimDCat 2` (no parens around the RHS of `≌` because
`≌` has lower precedence than application).

### N3 — `unfold erToKFunctor_map` may not unfold the `Quotient.liftOn`

**Location**: §6.1.

**Claim in spec**: §6.1 starts the proof with `unfold
erToKFunctor_map`.

**Problem**: `erToKFunctor_map` is defined as `Quotient.liftOn e
(fun rec => ...) (fun e₁ e₂ h => ...)`. `unfold` reveals the
definition body but the goal then contains a literal
`Quotient.liftOn` expression. The subsequent `refine
Quotient.inductionOn (motive := fun e => KMorNQuo.interp
(Quotient.liftOn ... e _ _).hom = ...) e ?_` then has to elaborate
that motive — Lean's elaborator must match `Quotient.liftOn (s :=
erMorNSetoid n m) e _ _` against the unfolded body. The mirror at
`LawvereKSimER.lean:491–502` shows this is feasible (it does
exactly this), but the underscore placeholders `_ _` in the motive
need Lean to fill in the lift function and the well-definedness
proof; this can fail if the elaborator can't infer them from the
expected motive type.

**Recommendation**: Confirm by lean-lsp / `lake build` of a
stub during T5.0 baseline (or T5.A.1 first iteration) that the
motive-with-underscores form elaborates. If not, fall back to
spelling out the lift function and well-definedness proof
explicitly in the motive, as the mirror does on
`LawvereKSimER.lean:497–501`.

## Convergence verdict

BLOCK — 1 blocker, 5 serious. Address and re-dispatch round 2.
