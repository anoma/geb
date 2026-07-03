# Ramified recurrence plan review, round 4

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Major findings](#major-findings)
  - [R4-M1: Task 1.3 re-derives the repository's existing free-monad assets](#r4-m1-task-13-re-derives-the-repositorys-existing-free-monad-assets)
  - [R4-M2: `RIdent`'s sketch assigns defining terms to polynomial directions](#r4-m2-ridents-sketch-assigns-defining-terms-to-polynomial-directions)
- [Minor findings](#minor-findings)
  - [R4-m1: Task 1.3's interface header retains the pre-rework framing](#r4-m1-task-13s-interface-header-retains-the-pre-rework-framing)
  - [R4-m2: `FreeAlg.recurse`'s stated realization cannot see the subterms](#r4-m2-freealgrecurses-stated-realization-cannot-see-the-subterms)
- [Nit findings](#nit-findings)
  - [R4-N1: "stack swap" metaphor in decision 8](#r4-n1-stack-swap-metaphor-in-decision-8)
  - [R4-N2: the free-monad-substitution claim is unqualified against route L1](#r4-n2-the-free-monad-substitution-claim-is-unqualified-against-route-l1)
  - [R4-N3: decision 8 quotes spec s1.1 under a heading citing s7 only](#r4-n3-decision-8-quotes-spec-s11-under-a-heading-citing-s7-only)
- [Verification coverage](#verification-coverage)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Verdict: NOT CONVERGED (0 blocker, 2 major, 2 minor, 3 nit).

Document under review:
`docs/superpowers/plans/2026-07-02-ramified-recurrence-plan.md` at
commit `07a92a77` ("docs(plans): adopt the PolyEndo representation
throughout; drop the spike gate"). Reviewed against the rework diff
(`f550b60bad3a..07a92a7732a7`), the two binding user decisions of
2026-07-02 (representation; citation style), the user-approved spec
(`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`),
the in-repository polynomial stack (`GebLean/Polynomial.lean`,
`GebLean/PolyAlg.lean`, `GebLean/PolyUMorph.lean`,
`GebLean/PolyAlgUMorph.lean`, `GebLean/PLang/TreeCalcPoly.lean`,
`GebLean/PLang/IndexedEAT.lean`), rounds 1-3, `CLAUDE.md`,
`.claude/rules/lean-coding.md`, `.claude/rules/markdown-writing.md`,
and the mathlib naming and style guides (re-fetched this round).

The user decisions themselves are not under review; the findings
concern the rework's realization of them against the repository.

## Major findings

### R4-M1: Task 1.3 re-derives the repository's existing free-monad assets

Location: Task 1.3 interface block and Step 2; Tech Stack; file
structure (`Term.lean` row).

Evidence: the Task 1.3 block directs, as new Phase 1 work:

- "Terms are the free monad of sig.polyEndo at the context's variable
  family, realized as the PolyFix of the coproduct
  (polyBetweenCoprod, GebLean/PolyUMorph.lean:422) of the signature
  summand and the variables summand";
- "`Tm.subst` : ... the free-monad bind along the variable-family
  map, defined by polyFixFold (GebLean/PolyAlg.lean:359)";
- "the free-monad laws, proven once via initiality
  (polyFixAlg_isInitial :533, polyFixFoldHom_unique :517)";
- Step 2: "`subst` as bind by `polyFixFold`, and the clone laws once,
  generically, from initiality".

The repository already provides exactly this structure, unclaimed by
the plan:

- `polyTranslate (A : Over X) (P : PolyEndo X) : PolyEndo X` — the
  "leaves + nodes" functor the sketch rebuilds from
  `polyBetweenCoprod` and `constPolyEndo` (`GebLean/PolyAlg.lean:3293`);
- `PolyFreeM (A : Over X) (P : PolyEndo X) (x : X) : Type u :=
  PolyFix (polyTranslate A P) x` (`:3344`), with carrier `:3350`;
- `polyFreeMPure` (`:3950`) — the `Tm.var` injection;
- `polyFreeMBind` (`:3980`) — the bind whose leaf-map argument
  `(f : ∀ y, { a // A.hom a = y } → PolyFreeM B P y)` is precisely
  the sorted substitution tuple;
- the three monad laws: `polyFreeM_pure_bind` (`:3993`),
  `polyFreeM_bind_pure` (`:4001`) — the `subst_id` shape — and
  `polyFreeM_bind_assoc` (`:4021`) — the `subst_subst` shape;
- `polyFreeMonad` (`:9615`).

`CLAUDE.md` (Reuse existing abstractions): "Before defining a new
mathematical concept, check whether it already exists in mathlib,
CSLib, or elsewhere in this repository. Instantiate the existing
abstraction rather than defining a parallel concept." The rework's
realization sketch instructs the executor to re-derive bind and its
laws from the initial-algebra API — parallel to assets three thousand
lines below the very declarations it cites — and its law-derivation
claim ("proven once via initiality") differs from how the repository
actually proves them (structural induction at `:4001`, `:4021`).

Required fix: rewrite the Task 1.3 realization to instantiate the
existing free-monad module: `Tm sig Γ s` as
`PolyFreeM <varFam Γ as Over S> sig.polyEndo s` (the `S`-indexed
family becomes an `Over S` object via `familySliceForward` or a
direct `Over.mk`), `Tm.var` from `polyFreeMPure`, `Tm.subst` from
`polyFreeMBind`, and `subst_id`/`subst_subst` as instances of
`polyFreeM_bind_pure`/`polyFreeM_bind_assoc`, with file:line
citations. Drop `constPolyEndo` and the
`polyBetweenCoprod`/initiality derivation from the sketch (or record
concretely why the existing assets do not fit). Update the Tech Stack
asset list, the `Term.lean` file-structure row, and Step 2
accordingly. The architecture and decision-8 claims ("substitution
and its laws come from free-monad structure") are unaffected — the
fix realizes them by reuse instead of reconstruction.

### R4-M2: `RIdent`'s sketch assigns defining terms to polynomial directions

Location: Task 2.2 interface block, `RIdent` docstring.

Evidence: "Realized (decision 8) as the `PolyFix` of an indexed
signature endofunctor over the index type `List RType × RType`,
whose shapes are the three schema formers below and whose directions
are the referenced sub-identifiers and defining terms."

For `P : PolyEndo (List RType × RType)`, the child at a direction of
a `PolyFix` node is an element of the fixed point at the direction's
index — `PolyFix P ((polyBetweenFamily _ _ P x i).hom e)`
(`GebLean/PolyAlg.lean:176-180`) — that is, another identifier. A
defining term is a `Tm` value, which is not an element of any fiber
of this fixed point, so "defining terms" cannot be directions. With
the shapes fixed as the bare three formers and the term data pushed
to the directions, the `defn` former is unrealizable as written: an
executor following the sentence literally hits an immediate type
error and must redesign the identifier functor without plan guidance
(Task 2.2 carries full detail here; no sub-plan corrects it).

Required fix: place the defining-term data in the shapes. For
example: the `defn` shape at index `(Γ, τ)` is a term skeleton over
the base signature extended with identifier-shaped hole operations
(one operation per `(arity, result)` pair; `SortedSig.Op : Type`
admits the infinite family), and the directions are the hole
occurrences, each mapped to its `(arity, result)` index; `mrec`'s and
`frec`'s directions are the step-function references, one per
constructor of `A` (arbitrary direction types are supported:
`polyBetweenFamily` is any `Over` object, so an infinite `A.B` is
unproblematic). Any equivalent factoring is acceptable provided the
functor remains a `PolyEndo` over `List RType × RType` (or the sketch
records a revised index type) and the terms live in shape data, not
directions.

## Minor findings

### R4-m1: Task 1.3's interface header retains the pre-rework framing

Location: Task 1.3, "**Interfaces (produces; from spec s4.2,
representation-independent):**" (plan line 613).

Evidence: "representation-independent" was the pre-decision-8 label
for the contract both candidate realizations were to satisfy (spec
s4.2: "both the native-inductive and the `PolyFix` realizations must
provide it"). The reworked block beneath the header is now
representation-committed: `SortedSig.polyEndo`, `constPolyEndo`, the
`PolyFix`-of-coproduct definition of `Tm`, and
`polyFixFold`/initiality references. The parenthetical is false of
more than half the block's content and is a stale artifact of the
deleted A-versus-B framing.

Required fix: reword the header, e.g. "(produces; contract from spec
s4.2, realized per decision 8)".

### R4-m2: `FreeAlg.recurse`'s stated realization cannot see the subterms

Location: Task 1.1 interface block, `FreeAlg.recurse` docstring.

Evidence: "Realized by the catamorphism `polyFixFold`
(GebLean/PolyAlg.lean:359) with the paper's parameter/subterm
threading." The step function `g` receives the subterms
(`Fin (A.ar b) → FreeAlg A`) as well as the recursive results — a
paramorphism, not a plain catamorphism. A fold at the obvious carrier
(`P → C`) provides only the recursive results; the subterm argument
requires either a fold at a product carrier
(`FreeAlg A × (P → C)` — the standard paramorphism-as-catamorphism
factoring) or direct use of `PolyFix.ind`
(`GebLean/PolyAlg.lean:206`), whose step does receive the children.
The sketch names neither, so an executor following it at the obvious
carrier fails and must rediscover the factoring. (Compare round 1's
R1-m7, the same defect class: an ambiguous realization in a
full-detail task.)

Required fix: name the realization in the note — "by `polyFixFold` at
a product carrier (paramorphism)" or "by `PolyFix.ind`".

## Nit findings

### R4-N1: "stack swap" metaphor in decision 8

Location: decision 8: "the migration is a stack swap under the same
construction."

Evidence: `CLAUDE.md` (Avoid colloquialisms and metaphors). The spec
states the same content in technical terms: "migration from B via a
`polyEndoEquiv`-style bridge" (spec s7).

Required fix: reword, e.g. "the migration replaces the polynomial
stack under the same construction" or adopt the spec's phrasing.

### R4-N2: the free-monad-substitution claim is unqualified against route L1

Location: Architecture ("with substitution and its laws obtained from
free-monad structure") and decision 8 ("substitution and its laws
come from free-monad structure (bind) rather than per-system
proofs"), against Phase 6 route L1.

Evidence: decision 7's own rationale states that free-monad
substitution "requires variables to occupy the monad's unit
positions, which is exactly the contexts-as-parameters form". L1's
applicative calculi index by context ("index = context and type;
binders shift the context index"), so their substitution operators
are not that bind; the L1 text correctly leaves them to the sub-plan
("the sub-plan fixes the indexed functors") but the development-wide
claims do not carry the qualification.

Required fix: scope the claim to the schematic term layer (Task 1.3)
— e.g. "with the term layer's substitution and its laws obtained
from free-monad structure" — or add the L1 qualification at one of
the two sites.

### R4-N3: decision 8 quotes spec s1.1 under a heading citing s7 only

Location: decision 8: "strengthened from 'syntax as W-types where
practicable' to unconditional", under the heading "(spec s7; user
decision 2026-07-02)".

Evidence: the quoted phrase is spec s1.1's ("data structures are
defined through the repository's dependent polynomial functors, with
syntax as W-types where practicable", spec line 81); s7 contains the
other quote ("If a default must be chosen without spikes: B",
verified verbatim) but not this one.

Required fix: add the s1.1 pointer next to the quoted phrase.

## Verification coverage

Checked this round and found correct (not repeated as findings):

- The rework diff (`f550b60bad3a..07a92a7732a7`, 672 lines) was read
  hunk-by-hunk against the current plan; all other findings above
  arise from rework-touched text.
- Stale-artifact sweep (attack A): grep for `spike`, `SpikeA`,
  `SpikeB`, `G5`, `G1-G4` as a gate-closure range, `G1/G2/G4`,
  `throwaway`, `timebox`, `abandon`, `exempt`, `per the G3
  realization`, `seven plan-fixed`, `Transcription.` finds no stale
  occurrence: the only remaining `spike` tokens are decision 8's and
  the checklist's intended "no-spike default", the only `G1-G4` is
  the now-correct gate-record range, and the pre-commit-triad spike
  exemption is gone from Global constraints. R4-m1 is the one stale
  framing artifact found.
- Gate renumbering is total: every landing-choice site reads G3
  (decision 2, phase map row 6, Phase 6 preamble, Task 6.0 Step 1,
  route T3, route L5 twice, decision-note section "G3: landing
  choice", commit message `docs(ramified): record G3 landing
  choice`); every Otto site reads G4 (task heading, note section
  "G4: Otto 1995", commit message, file-structure row, References
  entry, self-review checklist). "Eight plan-fixed decisions" matches
  the list. The doctoc TOC was regenerated and is current
  (`doctoc --dryrun --update-only` clean); `markdownlint-cli2` passes
  on the plan (0 errors).
- Repository line references quoted by the rework verified:
  `PolyEndo` (`GebLean/PolyAlg.lean:55`), `PolyFix` (`:176`),
  `PolyFix.ind` (`:206`, motive in `Sort _`, so the Task 2.1
  `DecidableEq` construction is available), `polyFixFold` (`:359`),
  `polyFixFoldHom_unique` (`:517`), `polyFixAlg_isInitial` (`:533`),
  `PolyFunctorBetweenCat` (`GebLean/Polynomial.lean:956`),
  `polyBetweenCoprod` (`GebLean/PolyUMorph.lean:422`).
- Shape checks of the sketches against the real signatures:
  `AlgSig.polyEndo : PolyEndo PUnit` matches the prior art
  (`polyValue : PolyEndo PUnit`, `GebLean/PLang/TreeCalcPoly.lean:40`,
  with `PolyFix polyValue PUnit.unit` at `:51`); `PolyFix P : X →
  Type u` makes `FreeAlg = PolyFix A.polyEndo _` and `Tm sig Γ : S →
  Type` well-formed; `polyBetweenCoprod (I) (F : I → ...)` accepts
  the `![...]` two-element vector at `I = Fin 2`; all indices live in
  `Type 0`, so no universe mismatch. Directions may be arbitrary
  types (`polyBetweenFamily` returns any `Over X`), so `mrec`'s
  `A.B`-indexed step family is expressible (the `defn` defect is
  R4-M2, not an expressibility limit).
- Kernel-computability of `polyFixFold` values on small inputs has
  in-repo precedent (`Value.fold` lemmas proven by `rfl`,
  `GebLean/PLang/TreeCalcPoly.lean:135-236`), so the Task 1.1/2.x
  `#guard`/`rfl` test steps stand with the pitfalls-section caveats
  already in place.
- Decision coherence (attack C): decision 6 matches Task 1.4's
  `Presentation` (plain data); decision 7 matches Task 1.3 (`Γ` a
  parameter; `varFam`; bind along a variable-family map); decision 8
  matches every task body's realization notes (Tasks 1.1, 1.3, 2.1,
  2.2, route L1) and the Global constraints bullet; the self-review
  checklist's mapping (open question 4 to decision 7, 5 to
  decision 6, 6 to G4, s7 to decision 8) matches spec section 10.
- Spec fidelity (attack D): the s7 default quote is verbatim; the
  strengthening is recorded as a user decision, dated, with the
  spec's own no-spike clause cited; the s7 table's B-cost ("Proof
  ergonomics ... costs (custom recursors)") is acknowledged and
  accepted in decision 8, not denied; approach C's
  convergence-target status is retained. Phase ordering is coherent
  across the how-to bullet, the phase map, Task 5.0/6.0, and the
  Phase 6 preamble (G1-G3 before Phase 1; G4 non-blocking; Phase 6
  after G1/G2/G3, Phases 2-3, and Phase 5 sub-plan convergence).
  Task 7.3 Step 2 covers the spec supersession pointers for the
  representation decision.
- Citation-style sweep across all interface blocks: no bare
  trailing "Transcription." labels remain; the reworked docstrings
  phrase sources naturally (Tasks 1.1, 2.1, 2.2, 2.3, 5.1 checked
  individually); novel-packaging markings are retained where spec
  s2.5 classifies novel (Phase 1 preamble, Tasks 1.2, 1.3, 1.4).
- Naming and style guides re-fetched: the rework's new identifiers
  (`AlgSig.polyEndo`, `SortedSig.polyEndo`, `constPolyEndo`,
  `varFam`, `rTypePolyEndo`) are data-valued defs in lowerCamelCase;
  no new theorem names were introduced; the renamed commit messages
  (`docs(ramified): record G3 landing choice`, `docs(ramified):
  record G4 Otto acquisition attempt`) keep the repository's
  established type/scope form, imperative lowercase subjects under
  72 characters.
