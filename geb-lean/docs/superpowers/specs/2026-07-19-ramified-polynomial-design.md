# Ramified recurrence on the vendored polynomial-functor stack

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [1. Scope and policy](#1-scope-and-policy)
  - [1.1 Purpose](#11-purpose)
  - [1.2 Decisions fixed during brainstorming and user review](#12-decisions-fixed-during-brainstorming-and-user-review)
  - [1.3 Transcription-versus-novel policy](#13-transcription-versus-novel-policy)
- [2. Background: the two polynomial-functor stacks](#2-background-the-two-polynomial-functor-stacks)
  - [2.1 The legacy stack (`GebLean.PolyAlg`)](#21-the-legacy-stack-gebleanpolyalg)
  - [2.2 The vendored stack (`Geb.Mathlib.Data.PFunctor`)](#22-the-vendored-stack-gebmathlibdatapfunctor)
  - [2.3 How `Ramified` sits on the legacy stack](#23-how-ramified-sits-on-the-legacy-stack)
- [3. Constraints (non-negotiable)](#3-constraints-non-negotiable)
- [4. The generic bridge](#4-the-generic-bridge)
  - [4.1 W-type bridge (Phase A)](#41-w-type-bridge-phase-a)
  - [4.2 Free-monad bridge (Phase B)](#42-free-monad-bridge-phase-b)
- [5. The `Ramified` instantiation (`GebLean/Ramified/Polynomial/`)](#5-the-ramified-instantiation-gebleanramifiedpolynomial)
- [6. Inter-definability on the primed type system (Phase C)](#6-inter-definability-on-the-primed-type-system-phase-c)
- [7. Approaches considered](#7-approaches-considered)
- [8. Deliverables and phasing](#8-deliverables-and-phasing)
- [9. Testing](#9-testing)
- [10. Deferred and future work](#10-deferred-and-future-work)
- [11. Resolved during user review](#11-resolved-during-user-review)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Status: brainstorming-phase design, revision 4. Revision 2 folded in
the user-review resolutions of section 11; revision 3 folded in
adversarial review 1 (the operation-kind routing, the fiber-motive
forward fold, and the paramorphism-via-tupling of section 4-5) and the
Phase C reframe of section 6; revision 4 folds in adversarial review 2
(the reconstruction identity behind `recurse_mk`, and the correction
that a primed `SynCatFO'` is a presentation rebuild related by an
equivalence of categories, not a free transport — section 6).

## 1. Scope and policy

### 1.1 Purpose

The `Ramified` area formalizes Leivant III's higher-type ramified
recurrence and its inter-definability with elementary-recursive
arithmetic (`ERMor`). Its recursive data and syntax rest entirely on
the repository's legacy polynomial-functor stack `GebLean.PolyAlg`
(`PolyEndo`, `PolyFix`, `PolyFreeM`). The vendored geb-mathlib stack
`Geb.Mathlib.Data.PFunctor` now provides polynomial functors built on
mathlib's `PFunctor`, with dependent recursive datatypes and their
recursion and induction expressed through recursor combinators rather
than a Lean `inductive` with a native recursor.

This workstream produces a second implementation of the `Ramified`
recursive layer on the vendored stack and an equivalence between the
two implementations, so that the existing inter-definability with
`ERMor` transfers to the new implementation by composition. The
existing implementation is not migrated; it stands unchanged beside
the new one.

### 1.2 Decisions fixed during brainstorming and user review

- Coverage is the whole recursive layer: the free-algebra data type
  and the recursive syntax that rests on it (`RType`, `Tm`), reached
  by reimplementing the underlying primitives rather than each type
  in isolation.
- The terminal step (Phase C) additionally rebuilds the first-order
  presentation layer (`Presentation'` / `SynCatFO'`) on the primed
  types and relates it to the legacy one by an equivalence of
  categories, transferring the ER inter-definability without redoing
  the definability or soundness proofs. This enlarges the workstream
  beyond a bare data-structure equivalence (user decision, review 2).
- The equivalence is pitched at the generic primitive level: a bridge
  between the legacy primitives (`PolyFix`, `PolyFreeM`) and their
  vendored counterparts, proved once; every `Ramified` recursive type
  is an instantiation.
- The equivalence is transport-grade: a fiberwise `Equiv` on carriers,
  constructor naturality, and recursor agreement, sufficient to carry
  every existing `Ramified` result across by transport. The
  free-monad bridge additionally makes substitution commute. A
  categorical algebra-isomorphism statement is out of scope.
- The new implementation and the equivalence live in fresh
  narrow-and-deep directories, each with its index file: the generic
  bridge under `GebLean/PolyBridge/` (index `GebLean/PolyBridge.lean`),
  the `Ramified` instantiation under `GebLean/Ramified/Polynomial/`
  (index `GebLean/Ramified/Polynomial.lean`).
- The free-monad bridge starts from the plain augmented
  `SlicePFunctor.W` (a single-context free monad); the
  `PresheafPFunctor` presheaf-monad presentation is reserved for later
  should full presheaf-monad substitution be wanted.

### 1.3 Transcription-versus-novel policy

Each definition and statement is marked below as transcription (of a
published result) or novel (packaging assembled by this development).
These annotations are confined to this spec and the plan. Lean source
comments and docstrings cite only the literature they transcribe and
make no novelty claim, per the project documentation rule.

The mathematical content of the bridge is transcription: two W-type
presentations of the same polynomial endofunctor have equivalent
carriers by the initial-algebra property (Abbott, Altenkirch, Ghani,
"Containers: constructing strictly positive types", TCS 2005;
Gambino, Kock, "Polynomial functors and polynomial monads", 2013).
The packaging — the specific translation between the Grothendieck
presentation of `PolyEndo` and the `(shapes, positions, q, r)`
presentation of `SlicePFunctor`, and the transport-grade equivalence
assembled from each side's eliminator — is novel.

## 2. Background: the two polynomial-functor stacks

### 2.1 The legacy stack (`GebLean.PolyAlg`)

- `PolyEndo X` presents a polynomial endofunctor on `Over X` in
  Grothendieck form: at each `x : X` a coproduct of covariant
  representables, with index type `polyBetweenIndex X X P x` and, per
  index, a fiber family `polyBetweenFamily X X P x i : Over X`.
- `PolyFix P : X → Type` is a Lean `inductive`: an indexed family of
  well-founded trees whose node at `x` carries an index and a
  child assigned to each fiber element. Its eliminator `PolyFix.ind`
  is the auto-generated recursor; `PolyFix.mk` its constructor.
- `PolyFreeM V P` is the free monad of `P` at a variable family `V`,
  with unit `polyFreeMPure` and bind `polyFreeMBind`.

`PolyFix` being a native `inductive` is the material point: the
legacy "polynomial-functor" layer is, underneath, the bespoke
recursive type the vendored stack is intended to replace.

### 2.2 The vendored stack (`Geb.Mathlib.Data.PFunctor`)

- `SlicePFunctor dom cod` (in `PFunctor/Slice/Basic.lean`) is a
  dependent polynomial functor `Type/dom → Type/cod`: a mathlib
  `PFunctor` with a shape-output map `q` and a direction-input map
  `r`.
- `SlicePFunctor.W` (in `PFunctor/Slice/W.lean`) is its W-type,
  realized as a subtype of the mathlib `PFunctor` W-type `WType`,
  indexed by the structure map `wIndex : F.W → I`. It provides `mk`,
  `dest`, `elim` (with `elim_mk` and the over-`I` law `comp_elim`),
  the `Prop`-valued paramorphism `RecProp` (with `recProp_mk`), and
  `Prop` induction `induction`. Values are folded by the non-dependent
  `WType.elim`; `WType.rec` is used only in erased `Prop` proofs, so
  nothing becomes `noncomputable` and the core is
  `Classical.choice`-free.
- `PresheafPFunctor` (in `PFunctor/Presheaf/`) adds the contravariant
  action carrying substitution as a presheaf monad; `IndRec` (in
  `PFunctor/IndRec/`) supplies dependent recursors for
  inductive-recursive codes and `contCode` for a plain container.

### 2.3 How `Ramified` sits on the legacy stack

- `FreeAlg A = PolyFix A.polyEndo PUnit.unit`, with `FreeAlg.mk` and
  the recurrence `FreeAlg.recurse` (a paramorphism through
  `PolyFix.ind`). `natFreeAlgEquiv : FreeAlg natAlgSig ≃ ℕ` is the
  single bridge to the numeric carrier feeding `ERMor`.
- `RType = FreeAlg rTypeSig`; its operations (`shape`, `omegaShift`,
  `objTarget`, `domains`, `interp`, `ord`, `tower`, and the predicates
  `IsObj`, `IsTower`, `IsSimple`) are recurrences over `FreeAlg`.
- `Tm sig Γ = PolyFreeM (varOver Γ) sig.polyEndo`; substitution
  `Tm.subst` is the free-monad bind, and the clone laws are its monad
  laws.

Every `Ramified` module transitively uses `FreeAlg`. Two distinct free
algebras appear: the numeric carrier `FreeAlg natAlgSig` (the algebra of
naturals), which occurs inside the denotation machinery and not in the
endpoint statements; and `RType = FreeAlg rTypeSig` (the type system),
which the endpoints (`ramified_definability`,
`ramified_definability_kSim`) use pervasively via `ObjCtx` and
`SynCatFO`, alongside `Tm`. Reimplementing `RType` and `Tm` is therefore
the substantive content, and the primed-stack restatement of the
endpoints (section 6) rests on it.

## 3. Constraints (non-negotiable)

- Constructive discipline: no `noncomputable`; `Classical.choice` in
  proofs only; the `GebLeanAxiomChecks` axiom gate must pass
  (`propext`, `Quot.sound`, `Classical.choice` accepted; `sorryAx`
  and any other axiom rejected).
- Recursor-only elimination. All elimination of the recursive
  datatypes is expressed by applying recursor or eliminator
  combinators: on the vendored side `SlicePFunctor.W.elim`,
  `SlicePFunctor.W.RecProp`, the `IndRec` recursors, and the
  free-monad bind; on the legacy side, only where the bridge must
  consume `PolyFix`, its recursor `PolyFix.ind`. Forbidden over these
  types: the `induction` / `cases` / recursive `rcases` tactics,
  structurally-recursive definitions (a `match` with recursive
  self-calls), `termination_by` and well-founded recursion, and
  applications of `WType.rec` or a native `.rec` in computational
  (non-erased) content. A non-recursive single-level `match`, and the
  trivial recursors `Eq.rec`, `Subtype`/`Sigma` projection, are
  permitted: they are not recursion over the recursive structure. The
  constraint governs the recursive tree datatypes (`PolyFix`,
  `SlicePFunctor.W`, `FreeAlg'`, `RType'`, `Tm'`); recursion over other
  inductives (for example `Nat` via `Nat.rec`) is permitted.
  `Type`-valued eliminations use `W.elim` at the needed `Type` universe,
  recursive `Prop` ones `W.RecProp`, and paramorphic ones the tupling
  encoding into `C × FreeAlg' A`.
- Documentation: novelty annotations confined to spec and plan;
  source comments cite only transcribed literature. Module and
  declaration docstrings mandatory; mathlib naming and style; lines
  at most 100 characters; forward-only style.
- Testing: every source module mirrored by a `GebLeanTests/` module;
  compositional tests.

## 4. The generic bridge

### 4.1 W-type bridge (Phase A)

- `toSlice : PolyEndo X → SlicePFunctor X X` — translate the
  Grothendieck presentation into the `(shapes, positions, q, r)`
  presentation. Transcription of the standard correspondence; the
  explicit translation is novel packaging.
- `polyFixSliceEquiv : PolyFix P x ≃ { w : (toSlice P).W // wIndex w = x }`
  — the fiberwise carrier equivalence. The vendored side carries its
  index as the map `wIndex`, so the fiber over `x` is the counterpart
  of the legacy family member at `x`.
- Constructor naturality: `polyFixSliceEquiv (PolyFix.mk …)` equals
  the `SlicePFunctor.W.mk` node with children mapped through the
  equivalence.
- Recursor agreement: eliminating with `PolyFix.ind` agrees, across
  the equivalence, with `SlicePFunctor.W.elim`; established via
  `elim_mk`.

Construction (fold-both-ways): the forward map folds `PolyFix` by
`PolyFix.ind` at the fiber motive `{ w // wIndex w = x }` — carrying the
index proof each `SlicePFunctor.W.mk` node needs from its children —
into `W.mk` nodes; the backward map folds by `SlicePFunctor.W.elim` into
`PolyFix.mk` nodes, transporting each child along the node's
compatibility; the two round-trips are closed by `PolyFix.ind` and by
`W.induction`. No `induction` tactic and no structural recursion appear.

### 4.2 Free-monad bridge (Phase B)

- The free monad as the W-type of the augmented signature (the
  signature endofunctor extended by variable leaves). `polyFreeMSlice`
  instantiates the vendored W-type at that augmented `SlicePFunctor`;
  `polyFreeMSliceEquiv` is the carrier equivalence, reusing Phase A on
  the augmented pfunctor.
- Substitution commutes: `polyFreeMBind` corresponds, across the
  equivalence, to the vendored monad multiplication; unit corresponds
  to unit.

## 5. The `Ramified` instantiation (`GebLean/Ramified/Polynomial/`)

- `FreeAlg'`, `RType'`, `Tm'` are defined by instantiating the
  vendored primitives at `A.polyEndo`, `rTypeSig`, and `sig.polyEndo`.
- Their operations are programmed natively in combinator style on the
  vendored recursors, routed by kind: catamorphic data operations via
  `SlicePFunctor.W.elim`; paramorphic ones (whose step reads the raw
  subterm, such as `RType.objTarget` / `domains`) via a tupling encoding
  into `C × FreeAlg' A`; `Type`-valued ones (`RType.interp`) via
  `W.elim` at a `Type` universe; recursive `Prop` predicates
  (`RType.IsTower` / `IsSimple`) via `W.RecProp`; `Tm'` substitution via
  the free-monad bind. `FreeAlg'.recurse` is the paramorphism built by
  tupling. This is the object of the exercise: recursion is factored
  entirely into polynomial-functor operations.
- Compatibility lemmas link each new definition to its legacy
  counterpart across the bridge. Corollaries include
  `FreeAlg' natAlgSig ≃ ℕ`, `RType' ≃ RType`, and
  `Tm' sig Γ ≃ Tm sig Γ`, with the operations agreeing under these
  equivalences.

## 6. Inter-definability on the primed type system (Phase C)

The existing endpoints `ramified_definability` /
`ramified_definability_kSim` quantify over `ObjCtx` (contexts of
`RType`) and `SynCatFO` morphisms (over `Tm`), concluding
`collapseDenotation g = arityCongr … f.interp`. They do not mention the
numeric carrier `FreeAlg natAlgSig` (which lives inside the denotation),
but they rest pervasively on `RType` and `Tm`. Phase C therefore carries
the endpoints onto the primed types. `SynCat` / `RMRecCat` are
parametrized by a whole `Presentation` and hardwired to legacy `Tm`, so
a type equivalence does not transport into a category directly: a primed
`SynCatFO'` is built from a primed `Presentation'` (a primed
`higherOrder'` and standard model over `RType'`), after which the
Phase A/B equivalences establish `RMRecCat' ≌ RMRecCat` and the
endpoints (`ramified_definability'` / `ramified_definability_kSim'`)
transfer across that equivalence of categories. The ER-side definability
and soundness proofs are reused unchanged; transferring the endpoint
equation additionally requires a lemma that `collapseDenotation'` agrees
with `collapseDenotation` across the equivalence. The result is
inter-definability between the vendored-stack `Ramified` type
system and `ERMor`, obtained without redoing those proofs. The rebuild
is the chosen path (user review); the rebuild scope — in particular
whether `SynCat'` uses legacy `Tm` over the primed signature or the
vendored `Tm'` — is settled in the Phase C sub-plan.

## 7. Approaches considered

- Fold-both-ways (chosen): explicit mediating maps via each side's
  eliminator, round-trips by recursor. Direct, computational, matches
  the recursor-only and constructive constraints.
- Shared-`WType` normal form: rejected — `PolyFix` is a native
  `inductive`, not a `WType`, so there is no common `WType` to reduce
  both sides to cheaply.
- Initial-algebra universal property: rejected as its own route —
  `Slice/W` establishes only the existence half of initiality, so
  uniqueness would be re-proved via `RecProp`, collapsing into the
  fold-both-ways round-trips with added categorical wrapping.

## 8. Deliverables and phasing

One concern per branch:

- Phase A: `toSlice`, the W-type bridge, and the `FreeAlg'` / `RType'`
  instantiation with compatibility lemmas.
- Phase B: the free-monad bridge and the `Tm'` instantiation with
  substitution compatibility.
- Phase C: the ER-composition restatements.

Each phase is spec-adversarial-reviewed and merged independently.

## 9. Testing

Compositional, mirrored tests: `freeAlgToNat' (natToFreeAlg' n) = n`;
`polyFixSliceEquiv` round-trips on sample trees; `FreeAlg'.recurse`
reduction rules; `RType'` operation values matching `RType` across the
bridge; `Tm'.subst` clone laws.

## 10. Deferred and future work

- The cofree / M-type (coinductive) side of the bridge.
- A categorical algebra-isomorphism strengthening of the equivalence.
- Migration (rather than paralleling) of the existing `Ramified`
  implementation onto the vendored stack, retiring `PolyFix`.

## 11. Resolved during user review

1. Slice-W versus Presheaf-W for `Tm'`: start from the plain augmented
   `SlicePFunctor.W`. The `PresheafPFunctor` presheaf-monad
   presentation is deferred (section 10) and revisited only if full
   presheaf-monad substitution is wanted.
2. Placement of the generic bridge: a fresh narrow-and-deep directory
   `GebLean/PolyBridge/` with index `GebLean/PolyBridge.lean`, rather
   than another file in the populated flat polynomial-functors area.

## References

- M. Abbott, T. Altenkirch, N. Ghani, "Containers: constructing
  strictly positive types", Theoretical Computer Science 342 (2005)
  3-27. DOI `10.1016/j.tcs.2005.06.002`.
- N. Gambino, J. Kock, "Polynomial functors and polynomial monads",
  Mathematical Proceedings of the Cambridge Philosophical Society 154
  (2013) 153-192. DOI `10.1017/S0305004112000394`.
- D. Leivant, "Ramified recurrence and computational complexity III:
  Higher type recurrence and elementary complexity", Annals of Pure
  and Applied Logic 96 (1999) 209-229. DOI
  `10.1016/S0168-0072(98)00040-2`.
