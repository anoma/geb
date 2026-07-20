# Handoff: ramified-on-vendored-polynomial-functors, Phase B

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [How to use this document](#how-to-use-this-document)
- [Workstream overview](#workstream-overview)
- [Binding constraints and conventions (all phases)](#binding-constraints-and-conventions-all-phases)
- [Phase A — delivered (on `main`)](#phase-a--delivered-on-main)
  - [Phase A learnings and idioms (reuse in B)](#phase-a-learnings-and-idioms-reuse-in-b)
- [Phase B — the free-monad bridge and `Tm'`](#phase-b--the-free-monad-bridge-and-tm)
  - [The legacy target (what B reimplements)](#the-legacy-target-what-b-reimplements)
  - [The vendored approach (fixed by spec s4.2 / s11)](#the-vendored-approach-fixed-by-spec-s42--s11)
  - [Design questions for the B.0 sub-plan to resolve](#design-questions-for-the-b0-sub-plan-to-resolve)
- [Process to follow for Phase B](#process-to-follow-for-phase-b)
- [Pointers](#pointers)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## How to use this document

A fresh session picking up this workstream should read this end to end,
then read the spec and plan (linked below). Phase A is merged to `main`;
this document carries the workstream context, the Phase A deliverables
and learnings, and the Phase B starting point.

## Workstream overview

Goal: provide a second implementation of the `Ramified` recursive layer
(`FreeAlg`, `RType`, `Tm`) on the vendored geb-mathlib polynomial-functor
stack (`Geb.Mathlib.Data.PFunctor.Slice.W`), connected to the existing
`GebLean.PolyAlg`-based implementation by transport-grade equivalences,
and — as the terminal step — to rebuild the first-order presentation
layer on the primed types so the existing inter-definability with
elementary-recursive arithmetic (`ERMor`) transfers by an equivalence of
categories, reusing (not redoing) the ER definability/soundness proofs.

Authoritative documents (on `main`):

- Spec: `docs/superpowers/specs/2026-07-19-ramified-polynomial-design.md`
  (revision 4; converged through 3 adversarial-review rounds).
- Plan: `docs/superpowers/plans/2026-07-19-ramified-polynomial-plan.md`
  (revision 3; master plan, Phase A detailed, Phases B/C boundary-fixed
  with mandatory sub-plans).
- Reviews: `…-plan.review-1.md`, `.review-2.md`, `.review-3.md`.

Phase structure:

- Phase A (DONE, merged as PR #265): the W-type bridge and the `FreeAlg'`
  / `RType'` instantiation.
- Phase B (NEXT, this handoff): the free-monad bridge and `Tm'`.
- Phase C: inter-definability on the primed type system (rebuild the
  primed `Presentation'` / `SynCatFO'`, relate `RMRecCat' ≌ RMRecCat`,
  transfer the endpoints). User-decided to be the full presentation
  rebuild, not a free transport (spec section 6, review-2 P2).

## Binding constraints and conventions (all phases)

- No `noncomputable` anywhere; `Classical.choice` in proofs only. The
  axiom gate (`lake build GebLeanAxiomChecks`) accepts only `propext` /
  `Quot.sound` / `Classical.choice`; `sorryAx` and any other axiom fail.
- Recursor-only elimination of the recursive tree datatypes: on the
  vendored side `SlicePFunctor.W.elim` / `.RecProp` / `.induction`; on
  the legacy side (only where a bridge must consume it) `PolyFix.ind`.
  Forbidden over the tree types: the `induction` / `cases` / recursive
  `rcases` tactics, structural `match`-with-self-calls, `termination_by`,
  well-founded recursion, and `WType.rec` / a native `.rec` in
  computational content. `Nat.rec` / induction on `Nat` / `Bool` / `Fin`
  is fine (not tree types); a non-recursive `match` on a finite shape is
  fine.
- No novelty claims in `.lean` comments/docstrings — cite only the
  literature transcribed (novelty annotations live in spec/plan only).
- File headers: match the existing `GebLean` convention — plain
  `import ...`, no `module` keyword, no copyright/author header, then a
  mandatory `/-! -/` module docstring (`# Title`, summary,
  `## Main definitions`, `## Main statements`, `## References`,
  `## Tags`); `/-- -/` on every `def`/`theorem`. (`lean-coding.md`
  prescribes the `module` keyword, but only ~5/375 non-vendored files
  use it; matching neighbours is correct and was accepted at review.)
- Tests: mirror each source module under `GebLeanTests/`, register it in
  the aggregators (`GebLeanTests.lean`, `GebLeanTests/Ramified.lean`).
  Route numeric/semantic assertions through proven `@[simp]` lemmas —
  NOT kernel reduction of composite `W`-trees (project memory: Gödel /
  ER interpreters are not `#guard`-safe).
- Build only with `lake build <Module>` / `lake test`; never
  `lake env lean` or `lake clean`. Pre-commit for any `.lean` commit:
  `bash scripts/pre-commit.sh`; full gate before push:
  `bash scripts/pre-push.sh`.
- VCS: `jj` (colocated), not raw mutating `git` (a hook blocks it).
  Commit with `jj commit -m` (mathlib message convention: `<type>(<scope>):
  <imperative lowercase subject>`, no trailing period, ≤72 chars). NO
  `jj git push` without user line-by-line review.

## Phase A — delivered (on `main`)

The generic bridge and the single-sorted instantiation. New modules:

- `GebLean/PolyBridge/Slice.lean` —
  `toSlice {X} (P : PolyEndo X) : SlicePFunctor X X` (shapes
  `Σ x, polyBetweenIndex X X P x`; `q = fst`; positions
  `(polyBetweenFamily …).left`; `r =` the family hom), with `@[simp]`
  `toSlice_A/_B/_q/_r`.
- `GebLean/PolyBridge/WEquiv.lean` — THE GENERIC BRIDGE, general in `X`:
  `toSliceFib`/`toSliceW`/`wIndex_toSliceW`, `ofSliceW`, round-trips
  `ofSliceW_toSliceW`/`toSliceW_ofSliceW`, the fiberwise
  `polyFixSliceEquiv {X} (P : PolyEndo X) (x : X) : PolyFix P x ≃
  { w : (toSlice P).W // wIndex w = x }`, and constructor naturality
  `polyFixSliceEquiv_mk`. Helpers `transport_snd`, `toSliceW_transport`,
  `ofSliceW_fst`. (`elim_polyFixSliceEquiv` was intentionally omitted —
  no consumer.)
- `GebLean/Ramified/Polynomial/FreeAlg.lean` — `FreeAlg' A :=
  { w : (toSlice A.polyEndo).W // wIndex w = PUnit.unit }`; `FreeAlg'.mk`;
  the tupling paramorphism `FreeAlg'.tupleFold` / `FreeAlg'.recurse`
  (same signature as legacy `FreeAlg.recurse`) with the reconstruction
  identity `FreeAlg'.tupleFold_snd` and the reduction rule
  `FreeAlg'.recurse_mk` (a proved theorem, NOT `rfl`);
  `freeAlgSliceEquiv (A) : FreeAlg' A ≃ FreeAlg A` (= `polyFixSliceEquiv
  A.polyEndo PUnit.unit |>.symm`); `natToFreeAlg'` / `freeAlgToNat'`
  (native, combinator-style) and `natFreeAlgEquiv' : FreeAlg' natAlgSig
  ≃ ℕ`.
- `GebLean/Ramified/Polynomial/RType.lean` — `RType' := FreeAlg' rTypeSig`,
  `RType'.o/arrow/omega`, `rTypeSliceEquiv : RType' ≃ RType`, the ten
  operations reimplemented by kind (shape/IsObj one-level; `interp` via
  `W.elim` at `Type`; `IsTower`/`IsSimple` via `W.RecProp`;
  `objTarget`/`domains` paramorphic via `FreeAlg'.recurse`;
  `omegaShift`/`ord` catamorphic; `tower` via `Nat.rec`), each with a
  compatibility lemma (`rTypeSliceEquiv_shape/_omegaShift/_objTarget/
  _domains/_interp/_ord/_tower/_isObj/_isTower/_isSimple`). A reusable
  `FreeAlg'.induction` wrapper lives here.

Equivalence chain (all directions verified): `toSlice` →
`polyFixSliceEquiv` → `freeAlgSliceEquiv` (`.symm`) → `rTypeSliceEquiv`
→ `natFreeAlgEquiv'`.

### Phase A learnings and idioms (reuse in B)

- The A.0 spike (validate the hardest constructions sorry-free BEFORE
  writing the real files) was decisive. Do the same in B: spike the
  augmented-signature free-monad construction on a concrete signature
  before committing file structure.
- `polyFixSliceEquiv` is GENERAL in `X` — it applies directly to a
  multi-sorted `PolyEndo S`. Only `FreeAlg'`/`RType'` specialised to
  `X = PUnit` (using `Subsingleton.elim` to discharge every `Compatible`
  side goal). `Tm'` is MULTI-SORTED (`X = S`, the sort type), so it must
  use the general fiber machinery — the `Subsingleton.elim` shortcut is
  NOT available; expect the genuine compatibility proofs.
- `PolyFix.ind`'s iota reduces DEFINITIONALLY on `mk`, so `W.elim_mk`
  (itself `rfl`) fires without an explicit `rw`.
- Cast idiom for the backward map: retype the raw equality first —
  `show (node.1.2 e).1 = (polyBetweenFamily …).hom e from congrFun
  node.2 e) ▸ …` — a bare `▸` fails to locate the sides. `hg` for the
  `W.elim` over-map is `funext fun _ => rfl` when `cod` is trivial.
- Use `change` (not `show`) to beta-reduce recursor motives (avoids the
  `linter.style.show` linter).
- A paramorphism from the catamorphic `W.elim`: fold into `C × μ` and
  project `.1`; the `.2` reconstructs the subtree; its reduction rule
  needs a reconstruction-identity lemma proved by `W.induction`
  (NOT definitional).
- `@[simp]` only on constructor-compatibility lemmas (push the equiv
  through constructors); operation/naturality compat lemmas must NOT be
  `@[simp]` (they collide with the `_mk` reductions under `simpNF`).
- Two plan-text imprecisions found and fixed in-code (fold into the plan
  before B if editing): `freeAlgSliceEquiv` needs `.symm`
  (`polyFixSliceEquiv` is `FreeAlg A ≃ FreeAlg' A`); and for
  `RType'`-valued ops the well-typed compat form is the naturality
  `rTypeSliceEquiv (op' t) = op (rTypeSliceEquiv t)` (with `.map` for
  `domains`), not `op' t = op (rTypeSliceEquiv t)`.
- Optional Phase-A minors left for a future pass (non-blocking): the
  unused `wIndex_toSliceW`; `FreeAlg'.induction`'s placement in
  `RType.lean` rather than `FreeAlg.lean`.

## Phase B — the free-monad bridge and `Tm'`

Branch (plan phase-map): `feat/ramified-poly-freemonad`. First task is
B.0: write and converge the Phase B sub-plan
(`docs/superpowers/plans/2026-07-19-ramified-poly-freemonad-subplan.md`)
via brainstorming + writing-plans + adversarial review + user review,
THEN execute via subagent-driven development.

### The legacy target (what B reimplements)

`GebLean/Ramified/Term.lean`:

- `Tm (sig : SortedSig S) (Γ : Ctx S) : S → Type := PolyFreeM (varOver Γ)
  sig.polyEndo` — terms are the free monad of the multi-sorted signature
  endofunctor at the context's variable family.
- `Tm.var` (free-monad unit / `polyFreeMPure`), `Tm.op` (a `PolyFix`
  node), `Tm.subst` (free-monad bind / `polyFreeMBind`), `Tm.reind`,
  `Tm.weaken`.
- Clone laws `Tm.subst_id`, `Tm.subst_subst`, `Tm.var_subst`,
  `Tm.subst_reind` (the free monad's right-unit, associativity,
  left-unit).

Underlying legacy primitive: `PolyFreeM V P` in `GebLean/PolyAlg.lean` —
the free monad, realized as `PolyFix` of the signature endofunctor
augmented with variable leaves (`Sum.inl` leaves / `Sum.inr` nodes; see
`polyFixToPolyFreeM`/`polyFreeMToPolyFix`, `PolyFreeMLeafPos`,
`PolyFreeMLeafFiber`, `polyFreeMPure`, `polyFreeMBind`, and the monad
laws `polyFreeM_bind_pure` / `polyFreeM_bind_assoc`).

### The vendored approach (fixed by spec s4.2 / s11)

- Build the AUGMENTED signature endofunctor: `sig.polyEndo : PolyEndo S`
  extended by variable leaves from `varOver Γ` (leaves have no
  children). Its slice W-type (via the SAME `toSlice` /
  `polyFixSliceEquiv` machinery from Phase A, now at `X = S`) is the free
  monad `polyFreeMSlice`.
- `polyFreeMSliceEquiv` — the carrier equivalence, reusing
  `polyFixSliceEquiv` on the augmented `PolyEndo`.
- `Tm'`, `Tm'.var`, `Tm'.op`, `Tm'.subst`; substitution compatibility
  `Tm'.subst ↔ Tm.subst` across the equivalence; the clone laws for `Tm'`
  transported or reproved via the recursor.
- Start from the PLAIN augmented `SlicePFunctor.W` (single-context free
  monad). The `PresheafPFunctor` presheaf-monad presentation is DEFERRED
  (spec s11) — do not reach for it unless full presheaf-monad
  substitution is wanted.

### Design questions for the B.0 sub-plan to resolve

1. How to present the augmented signature (nodes `sig.polyEndo` + leaves
   `varOver Γ`) as a single `PolyEndo S`, so `toSlice`/`polyFixSliceEquiv`
   apply. Mirror how legacy `PolyFreeM` augments `P` (the `Sum` leaf/node
   split) — build a `polyFreeMSlice` generic in `(V, P)`, analogous to
   Phase A's generic `freeAlgSliceEquiv`.
2. Whether to bridge at the generic free-monad level (a reusable
   `polyFreeMSliceEquiv {V P}`) and instantiate for `Tm'`, mirroring the
   generic-then-instantiate structure of Phase A.
3. How `Tm'.subst` maps to the vendored monad multiplication / bind, and
   whether the clone laws transport across `polyFreeMSliceEquiv` or are
   reproved via `W.induction` (multi-sorted — no `Subsingleton` shortcut).
4. The variable-family/context handling (`varOver Γ = Over.mk Γ.get`) on
   the slice side.

Phase C (later) consumes the `Tm'` equivalence and `Tm'.subst`
compatibility to rebuild `SynCat'`/`SynCatFO'` (whether `SynCat'` uses
legacy `Tm` over the primed signature or the vendored `Tm'` is itself a
C.0 decision).

## Process to follow for Phase B

1. `superpowers:brainstorming` the free-monad design (start from the
   source: the legacy `Tm`/`PolyFreeM` construction and the vendored
   slice W-type), resolving the design questions above; produce the
   Phase B sub-plan design.
2. `superpowers:writing-plans` → the B.0 sub-plan with bite-sized tasks.
3. Adversarial review of the sub-plan (fresh-context reviewers verifying
   every named declaration against source; re-fetch the mathlib upstream
   guides) BEFORE the user-review handoff; converge to zero-defect.
4. User line-by-line review of the sub-plan.
5. `superpowers:subagent-driven-development` — spike first, then a fresh
   implementer + task review per task, then a whole-branch review. Cheap
   models for transcription (post-spike), capable models for the hard
   proofs and the final review.

## Pointers

- Spec / plan / reviews: see "Workstream overview" above.
- Phase A ledger (SDD progress, with per-task commits and the discovered
  plan corrections):
  `.superpowers/sdd/progress-ramified-polynomial.md` (parent `geb/`
  dir; git-ignored scratch — recover from `git log` if lost).
- Area docs updated in Phase A: `docs/areas/polynomial-functors.md`
  (`GebLean/PolyBridge/`), `docs/areas/ramified-recurrence.md`
  (`GebLean/Ramified/Polynomial/`).
- Phase A modules: `GebLean/PolyBridge/{Slice,WEquiv}.lean`,
  `GebLean/Ramified/Polynomial/{FreeAlg,RType}.lean` and their tests.
- Vendored stack: `vendor/geb-mathlib/Geb/Mathlib/Data/PFunctor/Slice/
  {Basic,W}.lean` (and `Presheaf/`, `IndRec/` for the deferred layers).
- Legacy free monad: `GebLean/PolyAlg.lean` (`PolyFreeM`,
  `polyFreeMPure`, `polyFreeMBind`); legacy terms:
  `GebLean/Ramified/Term.lean`.
