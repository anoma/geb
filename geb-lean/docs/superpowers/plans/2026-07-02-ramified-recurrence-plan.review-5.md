# Ramified recurrence plan review, round 5

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Fix verification (round-4 findings)](#fix-verification-round-4-findings)
- [Nit findings](#nit-findings)
  - [R5-N1: Tech Stack asset inventory omits the free-monad assets](#r5-n1-tech-stack-asset-inventory-omits-the-free-monad-assets)
  - [R5-N2: Task 1.1 Step 2 echoes the pre-fix `recurse` realization](#r5-n2-task-11-step-2-echoes-the-pre-fix-recurse-realization)
- [Verification coverage](#verification-coverage)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Verdict: CONVERGED (0 blocker, 0 major, 0 minor, 2 nit).

Document under review:
`docs/superpowers/plans/2026-07-02-ramified-recurrence-plan.md` at
commit `025e5a0a` ("docs(plans): address ramified-recurrence plan
review round 4"). Reviewed against the fix diff
(`07a92a7732a7..025e5a0a47dc`), the round-4 review, the user-approved
spec
(`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`),
the free-monad module of `GebLean/PolyAlg.lean` at the current pin,
`GebLean/PolyUMorph.lean`, `GebLean/Era.lean`, `CLAUDE.md`,
`.claude/rules/lean-coding.md`, `.claude/rules/markdown-writing.md`,
and the mathlib naming and style guides (re-fetched this round).

Both nit findings are residuals of round-4 fix sites, cannot
mislead an executor (every binding site is correct), and do not
gate convergence.

## Fix verification (round-4 findings)

| Finding | Status | Evidence |
| --- | --- | --- |
| R4-M1 | Resolved (residual: R5-N1) | Task 1.3's interface block and Step 2 instantiate the existing free-monad module ("consumed, not rebuilt"); the `polyBetweenCoprod`/`constPolyEndo` reconstruction and the "proven once via initiality" claim are gone; the `Term.lean` file-structure row and decision 8 name the assets. All quoted lines verified at the pin (see coverage). The Tech Stack asset inventory, also named in the R4-M1 fix directive, was not extended (R5-N1). |
| R4-M2 | Resolved | The `RIdent` docstring places the defining-term data in the shapes ("for `defn`, the defining term as a skeleton over the base signature with holes for identifier occurrences; for `mrec`/`frec`, the sorts and clause skeletons") and makes the directions' children the referenced identifiers, with the explicit exclusion "a `Tm` value cannot occupy a direction". |
| R4-m1 | Resolved | The Task 1.3 header reads "the spec s4.2 contract, realized on the `PolyEndo` stack per decision 8"; "representation-independent" no longer occurs in the plan. |
| R4-m2 | Resolved (residual echo: R5-N2) | The `FreeAlg.recurse` docstring names the paramorphism and both realizations: `polyFixFold` (`GebLean/PolyAlg.lean:359`, verified) at the product carrier `FreeAlg A × (P → C)`, or the dependent eliminator `PolyFix.ind` (`:206`, verified — its step receives the children). |
| R4-N1 | Resolved | Decision 8 reads "the migration replaces the underlying polynomial-functor stack under the same construction"; "stack swap" does not occur. |
| R4-N2 | Resolved | The architecture paragraph reads "term-layer substitution and its laws obtained from the repository's existing free-monad structure"; decision 8 additionally carries the binder-calculi qualification (route L contexts index the syntax; substitution by the corresponding indexed folds), consistent with decision 7 and the route L1 text. |
| R4-N3 | Resolved | The decision-8 heading reads "(spec s7, s1.1; user decision 2026-07-02)" and attributes each quote: "syntax as W-types where practicable" verified verbatim at spec line 81 (s1.1); "If a default must be chosen without spikes: B" verified verbatim at spec lines 1145-1146 (s7). |

## Nit findings

### R5-N1: Tech Stack asset inventory omits the free-monad assets

Location: Tech Stack paragraph (plan lines 87-95).

Evidence: R4-M1's required fix named the Tech Stack asset list among
the sites to update. The fix diff does not touch it: the
polynomial-stack parenthetical still enumerates
`PolyFunctorBetweenCat`/`PolyEndo`, `PolyFix` with initiality, and
coproducts, but not `PolyFreeM`/`polyFreeMBind`/the monad laws that
decision 8 and Task 1.3 now name as the consumed substitution layer.
Nothing in the paragraph is false — the coproduct citation
(`GebLean/PolyUMorph.lean:422`, verified) retains a plausible
consumer in Task 2.2's summand-structured identifier functor (spec
s7 lists `polyBetweenCoprod` summands under approach B), and
initiality (`:533`) is cited by Task 1.1 — so this is an inventory
gap only; every binding site carries full file:line citations.

Suggested fix: extend the parenthetical, e.g. "; the free monad
(`PolyFreeM`, `polyFreeMBind`, monad laws),
`GebLean/PolyAlg.lean:3344,:3980,:3993-:4021`".

### R5-N2: Task 1.1 Step 2 echoes the pre-fix `recurse` realization

Location: Task 1.1, Step 2: "implement ... `FreeAlg.recurse` via
`polyFixFold`".

Evidence: the R4-m2 fix corrected the `FreeAlg.recurse` docstring
(paramorphism; `polyFixFold` at the product carrier, or
`PolyFix.ind`), but Step 2 retains the unqualified "via
`polyFixFold`" phrasing. An executor writes the corrected docstring
first, so the plain-carrier failure mode R4-m2 described is averted;
the step merely pins one of the docstring's two permitted
realizations without the product-carrier qualifier.

Suggested fix: "via `polyFixFold` at the product carrier (or
`PolyFix.ind`), per the docstring above".

## Verification coverage

Checked this round and found correct (not repeated as findings):

- The fix diff (`07a92a7732a7..025e5a0a47dc`) was read hunk-by-hunk
  against the current plan; all seven round-4 findings map to hunks;
  no unrelated content changed.
- Free-monad claims verified against `GebLean/PolyAlg.lean` at the
  pin: `PolyFreeM` (`:3344`, an `abbrev` equal to
  `PolyFix (polyTranslate A P) x`); `polyTranslate` (`:3293`);
  `polyFreeMPure` (`:3950`, argument
  `{ v : A.left // A.hom v = x }`); `polyFreeMBind` (`:3980`, exact
  signature `(t : PolyFreeM A P x) (f : ∀ y, { a : A.left //
  A.hom a = y } → PolyFreeM B P y) : PolyFreeM B P x`);
  `polyFreeM_pure_bind` (`:3993`), `polyFreeM_bind_pure` (`:4001`),
  `polyFreeM_bind_assoc` (`:4021`) — decision 8's range
  `:3993-:4021` covers exactly these three; `polyFreeMonad`
  (`:9615`, `(polyFreeForgetAdjunction P).toMonad` — "the adjunction
  monad" is accurate).
- Shape consistency of the Task 1.3 sketch with those signatures:
  `PolyFreeM` takes `A : Over X` then `P : PolyEndo X`, matching the
  plan's `PolyFreeM (varOver Γ) sig.polyEndo`; `varOver Γ : Over S`
  with `left = Fin Γ.length`, `hom = Γ.get` makes
  `Tm sig Γ : S → Type` well-formed at `X = S`; `Tm.var` is
  `polyFreeMPure` at the fiber element `⟨i, rfl⟩`; `Tm.subst`'s
  tuple `∀ i, Tm sig Δ (Γ.get i)` converts to `polyFreeMBind`'s
  leaf map by fiber transport (`polyFreeMPure_transport`, `:3968`,
  exists for the `subst_id` instance), with `B = varOver Δ`; the
  `subst_id`/`subst_subst` attributions to
  `polyFreeM_bind_pure`/`polyFreeM_bind_assoc` are the correct law
  shapes. No argument-order or misstatement defect.
- `polyFreeMBind` is defined by native `match` and structural
  recursion, and the laws at `:4001`/`:4021` are proved by
  induction, not initiality; the plan no longer makes any claim
  about how the laws are derived, and the no-native-inductives
  constraint scopes to "this development", so consuming `PolyFix`
  (`:176`, a native inductive in repository code) is consistent
  with decision 8 as written.
- Stale-name sweep: `constPolyEndo`, `varFam`, `polyBetweenCoprod`,
  "stack swap", "representation-independent" have zero occurrences
  in the plan (the Tech Stack "coproducts" citation is by file:line
  only, R5-N1); Tasks 1.4/1.5, Phase 2, and the self-review
  checklist reference only surviving names (`Tm.subst_subst`,
  `subst_id`, `QuotRel`, `varOver` via Task 1.3).
- The clone-law precedent citation resolves: `Era.Tm.subst_id`
  (`GebLean/Era.lean:88`) and `Era.Tm.subst_subst` (`:96`).
- The `RIdent` paragraph's revised factoring is expressible as a
  `PolyEndo (List RType × RType)` (shapes carry skeleton data;
  direction fibers are `Over` objects mapped to the referenced
  identifiers' `(arity, result)` indices), matching R4-M2's
  required fix; the direction/child phrasing ("the directions, the
  children in the fixed point") is the loose usage already present
  and accepted in round 4's own fix text.
- Spec quotes verified verbatim at source lines (s1.1 line 81; s7
  lines 1145-1146); the decision-8 attribution matches.
- `markdownlint-cli2 --config .markdownlint-cli2.jsonc --no-globs`
  on the plan: 0 errors; `doctoc --dryrun --update-only` on the
  plan: up to date.
- Mathlib naming and style guides re-fetched: the fix's one new
  identifier, `varOver`, is a data-valued def in lowerCamelCase;
  the removed identifiers introduce no dangling references; no new
  theorem names or commit messages were added by the fix.
- Fresh-eyes pass over the full document at the severity discipline
  of rounds 1-4: no findings beyond the two nits above; items
  cleared by earlier rounds' coverage lists were not relitigated
  and no round-4 edit invalidated them.
