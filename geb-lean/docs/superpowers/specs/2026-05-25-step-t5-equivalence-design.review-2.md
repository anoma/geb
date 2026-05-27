# T5 spec adversarial review — round 2

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary](#summary)
- [Methodology](#methodology)
- [Findings](#findings)
  - [Round-1 status](#round-1-status)
  - [S6 — §6.7 typeclass-search default contradicts mathlib behaviour](#s6--67-typeclass-search-default-contradicts-mathlib-behaviour)
  - [S7 — §11 punch list (11.6, 11.8) is stale relative to §6.6](#s7--11-punch-list-116-118-is-stale-relative-to-66)
  - [M8 — §6.6 trace conflates identity morphism with object](#m8--66-trace-conflates-identity-morphism-with-object)
  - [M9 — §1's "stub form" of §6.3 is described but not specified](#m9--1s-stub-form-of-63-is-described-but-not-specified)
  - [N4 — §6.1 motive: two-underscore form is unverified at spec time](#n4--61-motive-two-underscore-form-is-unverified-at-spec-time)
  - [N5 — §6.6 narration claims `eqToIso_symm` rewrite but spec spells it](#n5--66-narration-claims-eqtoiso_symm-rewrite-but-spec-spells-it)
- [Convergence verdict](#convergence-verdict)

<!-- END doctoc -->

## Summary

Zero blockers, two serious findings, two minor findings, two
nits. The two serious findings are both new (introduced or
surfaced by the round-1 fixes); they do not block the spec on
mathematical grounds but they pin claims that are demonstrably
wrong on the current mathlib pin and that the implementation
would discover early. S6 (typeclass-search default) is confirmed
wrong by a `lean_run_code` experiment; S7 (stale punch list) is
a synchronisation defect in §11. The rest is minor or cosmetic.
Round 1's blocker B1 and all five serious findings (S1–S5) are
resolved. The spec is *close to* converged but not yet at zero
serious.

## Methodology

Read end-to-end:

- The revised spec at
  `docs/superpowers/specs/2026-05-25-step-t5-equivalence-design.md`.
- Round-1 findings at
  `docs/superpowers/specs/2026-05-25-step-t5-equivalence-design.review-1.md`.
- `CLAUDE.md`, `.claude/rules/lean-coding.md`,
  `.claude/rules/markdown-writing.md`,
  `docs/process.md` § Adversarial review.
- The post-T4 handoff at
  `docs/superpowers/plans/2026-05-25-post-t4-handoff.md`.
- Mirror code in `GebLean/LawvereKSimER.lean` lines 480–571.
- `GebLean/LawvereERKSim/ErToKFunctor.lean` (full file).
- `GebLean/LawvereKSimDCatInterp.lean` lines 60–95.
- `GebLean/LawvereERInterp.lean` lines 55–95.
- Mathlib `CategoryTheory/Equivalence.lean` lines 80–105
  (the `mk' ::` structure), lines 188–205
  (`Equivalence_mk'_unit` and companions), lines 348–352
  (the smart `mk`), and lines 622–645 (`Functor.IsEquivalence`
  class plus the global `isEquivalence_functor` /
  `isEquivalence_inverse` instances).
- Mathlib `CategoryTheory/Functor/FullyFaithful.lean`
  lines 48–60 (`Faithful` and `Functor.map_injective`).
- Mathlib `CategoryTheory/Functor/Basic.lean` (verified
  `(F ⋙ G).map f = G.map (F.map f)` is `rfl` by an inline
  `example`).

Re-fetched the four mathlib upstream guides via the in-repo
digest at `.claude/rules/lean-coding.md` §§ Authoritative
upstream guides. Cross-checked against the revised spec's
declaration names, suggested commit messages, and docstring
placeholders.

Active verification via `lean_run_code`:

- Confirmed that `@Equivalence.mk'` resolves and has the
  expected signature with `autoParam` discharging to
  `Equivalence.functor_unitIso_comp._autoParam`.
- Confirmed that the field projections
  `(Equivalence.mk' F G η ε h).unitIso = η`,
  `(Equivalence.mk' F G η ε h).counitIso = ε`, and
  `(Equivalence.mk' F G η ε h).functor = F` all hold by `rfl`.
- Constructed a stand-in `MyObj`-category test in which both
  forward and inverse functors are identity on objects (the
  same shape as `erToKFunctor` / `kToERFunctor`) and confirmed
  that `cat_disch` closes the triangle automatically in
  `Equivalence.mk'` in this concrete setting.
- Confirmed that in the same stand-in test,
  `example : F.IsEquivalence := inferInstance` *fails* even
  with `def myEquiv : MyObj ≌ MyObj := ...` in scope: the
  global `Equivalence.isEquivalence_functor` instance does
  not bridge from the `def` to a typeclass-search hit. See S6.

## Findings

### Round-1 status

- **B1 — Resolved.** §6.6 now uses `Equivalence.mk'` (the raw
  structure constructor) explicitly and the spec narrates that
  `unitIso` and `counitIso` are stored verbatim. The `mk'` name
  and the field-projection-by-`rfl` claim are both confirmed by
  direct `lean_run_code` test. §1's framing has been rewritten
  to remove the "isomorphism of categories" overpromise.
- **S1 — Resolved.** The autoparam is now identified as
  `by cat_disch`, including in §6.6 and §11.8 prose. The
  underlying autoparam name `Equivalence.functor_unitIso_comp._autoParam`
  is correct under the current pin.
- **S2 — Resolved.** §1 now describes the strict-equality claim
  as "theorem-level, conditional on the proof shapes in §6.3/§6.4
  going through under the current mathlib pin" and commits to a
  T5.0 stub type-check. See M9 for a residual minor about how
  the stub is specified.
- **S3 — Not adequately addressed; replaced by S6 (new).**
  Round 1 noted that explicit `IsEquivalence` instances were
  redundant. The spec's fix went further and *removed* the
  explicit instances, claiming that typeclass search would find
  them. That stronger claim is now demonstrably wrong under the
  current pin (`lean_run_code` test). See S6.
- **S4 — Resolved.** §6.1 has been reworded with three explicit
  asymmetries between T5-A.1 and the mirror; the motive-on-bare-
  quotient distinction is called out.
- **S5 — Resolved.** §6.1 now explicitly identifies the
  `KMor1`-level / `ERMor1`-level asymmetry in the inner `change`
  step relative to the mirror.
- **M1 — Resolved in part (see M8).** §6.6 now spells out the
  `eqToIso_symm` / `eqToIso_hom` reduction chain. A residual
  type-confusion remains: see M8.
- **M2 — Resolved.** "Headline" and "trivially" are gone;
  "free" replaced with "without additional proof effort beyond
  what faithfulness supplies"; "reasonably creep" gone.
- **M3 — Resolved.** "Warm-up" is gone from the spec; LOC
  reconciliation pinned in §5's trailing paragraph.
- **M4 — Resolved.** Commit-message scope split is now
  `(ertok)` for T5.A and `(equivalence)` for T5.B/T5.C; T5.A.2's
  subject `add erToKFunctor_comp_kInterp` is 25 chars, under
  the 72-char target.
- **M5 — Resolved.** "Isomorphism of categories" framing is
  removed.
- **M6 — Resolved.** §3 explicitly pins the `Equivalence.lean`
  module-docstring sections including `## Implementation notes`
  (committing to `Equivalence.mk'` + `cat_disch`) and explicitly
  omits `## Notation`.
- **M7 — Resolved.** Tourlakis is consistently cited as
  "Corollary 0.1.0.44" throughout.
- **N1 — Resolved.** §10 item 5 now reads "the pre-T5 test
  suite runs unchanged; … safeguards against accidental breakage
  of existing tests, not against new T5 content".
- **N2 — Resolved.** `LawvereKSimDCat 2` parenthesisation is
  consistent.
- **N3 — Partially addressed; see N4 below.** §6.1 acknowledges
  the underscore-elaboration risk and commits to an explicit
  spell-out fallback. The residual nit is that this is left
  unverified at spec time.

### S6 — §6.7 typeclass-search default contradicts mathlib behaviour

**Location**: §6.7 (entire section); §4.3 final paragraph; §1
("Mathlib's global instances on `Equivalence` supply
`Functor.IsEquivalence` for both functors through typeclass
search (no explicit named instances; see §6.7)").

**Claim in spec**: §6.7 commits that

> Since `erKSimEquiv.functor` and `erKSimEquiv.inverse` reduce
> definitionally to `erToKFunctor` and `kToERFunctor` respectively
> (by the `Equivalence.mk'` field-storage in §6.6), Lean's
> typeclass search finds `IsEquivalence erToKFunctor` and
> `IsEquivalence kToERFunctor` automatically from the existence of
> `erKSimEquiv`.

§6.7 closes: "the spec's default is no explicit instances".

**Problem**: Confirmed by `lean_run_code` test. Even with a
`def myEquiv : MyObj ≌ MyObj := Equivalence.mk' F G ...` in
scope, `example : F.IsEquivalence := inferInstance` *fails*:

```text
failed to synthesize instance of type class F.IsEquivalence
```

The reason is structural, not a `rfl`-unfolding accident.
The mathlib global instance is

```lean
instance Equivalence.isEquivalence_functor (F : C ≌ D) :
    IsEquivalence F.functor
```

Typeclass search looking for `IsEquivalence ?F` would have to
discover that `?F = e.functor` for some `e : C ≌ D` and that
`e = erKSimEquiv` specifically. Definitional-equality of
`erKSimEquiv.functor` with `erToKFunctor` does *not* give the
typeclass-search engine a way to invert that equality and
recover the relevant `e`. There is no `simp` / `unif` hint, no
`@[instance]` on the `def myEquiv` (the spec declares
`erKSimEquiv` as a `def`, not an `instance`), and no metavariable
the search can unify on.

The spec acknowledges a "fallback to two explicit one-liner
instances `instance : erToKFunctor.IsEquivalence :=
inferInstanceAs _` or similar" but pins the default to no
explicit instances. This default is wrong.

There is a second issue with the proposed fallback as written:
`inferInstanceAs _` would require synthesising the underscore;
since the underscore is the target typeclass and there's no other
way to get it, the elaborator would loop. The likely-correct
fallback is `erKSimEquiv.isEquivalence_functor` (and
`erKSimEquiv.isEquivalence_inverse`) — direct dot-notation
projections of the global instance pre-applied to `erKSimEquiv`,
which `lean_run_code` confirms works. The spec should:

1. Make explicit instance declarations the *default*, not the
   fallback;
2. Use the projection form
   `erKSimEquiv.isEquivalence_functor` (and `.isEquivalence_inverse`)
   as the RHS of each `instance :`;
3. Update §4.3, §6.7, §1, and §11.6 to reflect the corrected
   default.

**Recommendation**: Rewrite §6.7 to:

- State the global instances exist and supply
  `IsEquivalence e.functor` / `IsEquivalence e.inverse` *for the
  specific equivalence value `e`*, not for arbitrary functors
  via unification.
- Commit to two explicit instances on `erToKFunctor` and
  `kToERFunctor`, each as a one-line projection of the global
  instance applied to `erKSimEquiv`.
- Drop "the spec's default is no explicit instances."

This raises the T5-C LOC slightly (≈ 2 lines for the two extra
instances + AXIOM_ALLOW comments); §5's LOC estimate for T5.C
can absorb this within the ±50% bound.

### S7 — §11 punch list (11.6, 11.8) is stale relative to §6.6

**Location**: §11.6 and §11.8.

**Claim in spec**: §11.6 still reads "`Equivalence.mk` takes the
four-argument shape used in §6.6 plus the autoparam
`functor_unitIso_comp` defaulted to `by aesop_cat`". §11.8 still
reads "`aesop_cat` will close the `functor_unitIso_comp`
autoparam in `Equivalence.mk`".

**Problem**: Both are stale. §6.6 was rewritten in the round-1
fix to use `Equivalence.mk'` and `by cat_disch`. The punch list
in §11 is the adversarial-reviewer obligation list; if it
references the *old* API names, future-round reviewers may
either chase the wrong claim or report it as already-resolved.

The contradiction between §6.6 (`mk'`, `cat_disch`) and §11.6
/ §11.8 (`mk`, `aesop_cat`) is internal to the spec and is a
direct hangover from the round-1 fix being applied only to
prose body, not to the punch list.

**Recommendation**: Rewrite §11.6 and §11.8 to reference
`Equivalence.mk'`, the five-argument shape (four data + one
autoparam), and `cat_disch`. While editing, also align
§11.6's adversarial-obligation prose with the now-revised
§6.6 (no `aesop_cat` mention).

### M8 — §6.6 trace conflates identity morphism with object

**Location**: §6.6, lines 451–460.

**Claim in spec**: The spec writes

> `erToKKToErIso.symm.hom.app X` is
> `(eqToIso erToKFunctor_comp_kToERFunctor).symm.hom.app X`,
> which by `eqToIso_symm` and `eqToIso_hom` is
> `eqToHom (h.symm)` for `h : 𝟙 X = (erToKFunctor ⋙
> kToERFunctor).obj X` derived from
> `erToKFunctor_comp_kToERFunctor.symm`.

**Problem**: `eqToHom` takes an *object* equality, not a
*morphism* equality. The `h` here cannot be `𝟙 X = ...obj X`
(LHS is a morphism `X ⟶ X`, RHS is an object `LawvereERCat`).
The correct form is

```text
h : (𝟭 LawvereERCat).obj X = (erToKFunctor ⋙ kToERFunctor).obj X
```

which definitionally reduces to `X = X` and is `rfl`. The spec's
narration uses `𝟙 X` (a morphism) where it should write the
object `X` (or `(𝟭 LawvereERCat).obj X`). The conclusion of the
trace (`eqToHom rfl = 𝟙 X`) is correct; the intermediate type
ascription is not.

This is minor — the proof goes through and `cat_disch` closes
it (verified in the stand-in `MyObj` test). The defect is in the
spec's prose only, but a careful adversarial reader would flag
it as type-incorrect on first reading.

**Recommendation**: Rewrite the `h` line as

> `eqToHom h.symm` for `h : (𝟭 LawvereERCat).obj X =
> (erToKFunctor ⋙ kToERFunctor).obj X` derived from
> `erToKFunctor_comp_kToERFunctor.symm`.

### M9 — §1's "stub form" of §6.3 is described but not specified

**Location**: §1 ("T5.0 (baseline verification) includes a
type-check of a stub form of §6.3's proof shape …"); §5 (the
T5.0 row).

**Claim in spec**: T5.0 includes a stub of §6.3's proof shape
and §6.7's typeclass-search assumption.

**Problem**: The stub is left underspecified: not where it
lives (a comment in `Equivalence.lean`? a scratch file under
`/tmp`?), not whether it survives into the committed code or
gets removed before T5.B.1, not what it contains exactly. The
process commitment is reasonable in shape but vague. Given that
§6.7's typeclass-search assumption is *wrong* (S6), the T5.0
stub for that assumption would have caught the defect early —
which is the point — but the spec should pin what "caught" means
operationally (does T5.0 then patch §6.7 mid-execution, or does
the implementation phase loop back to spec revision?).

**Recommendation**: §1 or §5 should state explicitly: (a) the
stub lives in a scratch file outside the committed Lean source
or as a temporary `example :` block to be removed before T5.B.1
commits; (b) if T5.0 finds the stub does not type-check, the
implementation phase pauses and the spec is revised before any
T5.A/B/C commit lands. The current spec leaves the implementer
to guess.

### N4 — §6.1 motive: two-underscore form is unverified at spec time

**Location**: §6.1, lines 313–317.

**Claim in spec**: "The motive's `Quotient.liftOn (s := erMorNSetoid
n m) e _ _` form leaves two underscores (the lift function and
the well-definedness proof). T5.0 baseline includes a stub
type-check that this elaborates against the post-`unfold` goal;
if Lean's elaborator cannot infer the underscores from the
motive's expected type, the implementation spells them out
explicitly, as the mirror does at `LawvereKSimER.lean:497–501`."

**Observation**: `Quotient.liftOn` takes three arguments (the
quotient value, the lift function, the well-definedness proof),
so two underscores after `e` is positionally correct. The
mirror at `LawvereKSimER.lean:496–501` spells out the lift
function and the proof, *not* leaving them as underscores. The
spec's preference for underscores is a deviation from the mirror,
and the spec's own hedge ("if Lean's elaborator cannot infer …
the implementation spells them out explicitly") acknowledges
this is unverified.

This is a process nit, not a correctness defect. The spec
should either commit to the spell-out form (matching the
mirror, no elaboration risk) or to the underscore form (with a
T5.0 type-check that explicitly verifies it). The current
phrasing is "try the shorter form; fall back if it fails",
which is fine but adds an iteration risk to T5.A.1.

**Recommendation**: For lower implementation risk, commit
upfront to the spell-out form matching the mirror. The cost is
a few extra lines in T5.A.1 (the lift function and the
well-definedness proof body), already estimated at ≈ 18 LOC
and within the budget. Optional; the current spec is acceptable
if the implementation is willing to iterate on T5.A.1.

### N5 — §6.6 narration claims `eqToIso_symm` rewrite but spec spells it

**Location**: §6.6 (line 453).

**Claim in spec**: "which by `eqToIso_symm` and `eqToIso_hom`
is `eqToHom (h.symm)`".

**Observation**: This invokes named mathlib lemmas
(`eqToIso_symm`, `eqToIso_hom`) for which the spec does not
provide citations. The lemmas exist in mathlib at
`CategoryTheory/EqToHom.lean` (the namespace `CategoryTheory`)
but the spec's prose treats them as known without a citation
hook. For an adversarial reviewer doing a name-by-name pass on
the spec, this is a missing-citation nit.

**Recommendation**: Add a parenthetical citation, e.g.,
`(CategoryTheory/EqToHom.lean)`, after the first invocation, or
move the lemma names into the §12 References list. Low priority.

## Convergence verdict

PARTIAL — 0 blockers, 2 serious findings, 2 minor findings, 2
nits. The serious findings (S6 and S7) are both single-section,
locally-correctable, and not mathematical. S6 is a content
defect (the typeclass-search default is wrong) and requires a
spec rewrite of §6.7 (≈ 15 lines) plus reference updates in §1
and §4.3. S7 is a synchronisation defect: the §11 punch list
needs to be re-synced with §6.6's API choices (≈ 4 lines).

Round-1's B1 and S1–S5 are all resolved. The round-2 findings
are new (S6, S7) or are surface defects revealed by tightening
the round-1 fixes (M8). The spec is *one short round* from
convergence: apply the S6 and S7 fixes and re-dispatch round 3
to confirm zero serious.
