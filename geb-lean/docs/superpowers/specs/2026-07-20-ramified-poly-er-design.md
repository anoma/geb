# Phase C design: inter-definability on the primed type system

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [1. Scope and provenance](#1-scope-and-provenance)
- [2. Decisions](#2-decisions)
- [3. Module layout](#3-module-layout)
- [4. Term-layer completion (`Polynomial/Interp.lean`)](#4-term-layer-completion-polynomialinterplean)
- [5. Primed syntactic category and step 1](#5-primed-syntactic-category-and-step-1)
- [6. Signature-translation layer (step 2)](#6-signature-translation-layer-step-2)
- [7. Identifier rebuild](#7-identifier-rebuild)
- [8. Primed presentation and the composite equivalence](#8-primed-presentation-and-the-composite-equivalence)
- [9. First-order sub-theory replacement](#9-first-order-sub-theory-replacement)
- [10. Collapse packaging and endpoints](#10-collapse-packaging-and-endpoints)
- [11. Constraints](#11-constraints)
- [12. `TODO.md` porting record](#12-todomd-porting-record)
- [13. Testing](#13-testing)
- [14. Process](#14-process)
- [References](#references)

<!-- END doctoc generated TOC -->

## 1. Scope and provenance

This document is the Phase C sub-plan design for the
ramified-on-vendored-polynomial-functors workstream. It refines the
master spec
([2026-07-19-ramified-polynomial-design.md](2026-07-19-ramified-polynomial-design.md),
section 6) and the master plan
([../plans/2026-07-19-ramified-polynomial-plan.md](../plans/2026-07-19-ramified-polynomial-plan.md),
Phase C), resolving the five design questions recorded in the Phase C
handoff
([../notes/2026-07-20-ramified-polynomial-phaseC-handoff.md](../notes/2026-07-20-ramified-polynomial-phaseC-handoff.md)).
It feeds the C.0 sub-plan
(`docs/superpowers/plans/2026-07-19-ramified-poly-er-subplan.md`).

Deliverable boundary (master plan, enlarged at user decision — section
2, decisions 1 and 6): `ObjCtx'` / `SynCatFO'` / `collapseDenotation'`
on `RType'` and `Tm'`, built from a primed presentation `higherOrder'`
with a native standard model; `RMRecCat' ≌ RMRecCat`;
`ramified_definability'` and `ramified_definability_kSim'` transferred
across the equivalence with the ER-side proofs reused unchanged; a full
rebuild of the identifier layer (`RIdent'`) on the vendored stack with
a bridge equivalence; a replacement (not a mirror) of the first-order
sub-theory module on the primed stack; and a `TODO.md` record of the
geb-mathlib-eligible modules.

## 2. Decisions

Resolutions of the handoff's design questions and the additional
scope decisions, decided during brainstorming:

1. **Identifier layer: full rebuild (user decision).** `RIdent'` is
   re-founded on the vendored stack — `identEndo'` over the index type
   `List RType' × RType'`, `RIdent'` as a fiber of the vendored
   `W`-type, `DefnShape'` bodies as `Tm'` terms, and a native
   `RIdent'.interp` over the carriers `RType'.interp (FreeAlg' A)` —
   related to the legacy `RIdent` by a bridge equivalence
   `identSliceEquiv` with interp compatibility. The
   reuse-legacy-identifiers alternative (legacy trees as operation
   data at primed indices) was declined by the user in favour of a
   primed signature from which no legacy recursive type is reachable.
2. **Term layer: `Tm'` (handoff question 1).** The syntactic category
   is built over the vendored `Tm'`. Forced by decision 1: `DefnShape'`
   bodies are primed terms, so the whole term layer is primed.
3. **Quotient layer: native (handoff question 2).** Phase C adds a
   native evaluation `Tm'.eval` (decision 1 requires it for `defn'`
   bodies), a primed `QuotRel'` structure, and the native
   interpretative relation `interpQuotRel'`. The
   pull-back-across-`tmSliceEquiv` alternative was declined: with
   `Tm'.eval` required anyway, the native relation costs one
   agreement lemma (`tmSliceEquiv_eval`) and keeps the primed layer
   self-contained.
4. **Equivalence shape: two-step composite (handoff question 3, user
   decision).** `RMRecCat' ≌ RMRecCat` is the composite of a
   term-layer step and a signature-layer step through the middle
   category `SynCat (higherOrder' A) (interpQuotRel (higherOrder' A))`
   (legacy `Tm` over the primed presentation, available because
   `SynCat` is generic over `Presentation`). Step 1 is generic in the
   presentation; step 2 is a generic
   presentation-equivalence-to-category-equivalence construction over
   legacy `Tm`. The direct-functor-pair alternative was declined:
   each half is separately provable and reusable, and the underlying
   term translation factors through the same middle point either way.
5. **Agreement lemma (handoff question 4).** Stated as
   `collapseDenotation (synCatFOSliceEquiv.functor.map g') =
   arityCongr h₁ h₂ (collapseDenotation' g')` with `h₁`, `h₂` the
   `List.length_map` arity identifications; hosted on the primed side
   (`GebLean/Ramified/Polynomial/Collapse.lean`).
6. **First-order module: replacement (user decision).** The legacy
   `GebLean/Ramified/FirstOrder.lean` has no consumers beyond the
   `GebLean/Ramified.lean` index import and its own test mirror
   (measured during brainstorming), so it is deleted together with
   `GebLeanTests/Ramified/FirstOrder.lean` and rebuilt on the primed
   stack as `GebLean/Ramified/Polynomial/FirstOrder.lean`. No
   legacy-to-primed first-order bridge is written. The
   mirror-plus-equivalence alternative was declined: its cost is
   permanent while the replacement's cost is proportional to
   consumers, which are zero. The replacement serves the deferred
   transcription of the first-order polynomial-time results (Leivant,
   "Ramified recurrence and computational complexity I", in Feasible
   Mathematics II, 1995, DOI `10.1007/978-1-4612-2566-9_11`) on the
   geb-mathlib stack.
7. **Presentation reuse (handoff question 5).** `Presentation`,
   `SortedSig`, `SortedModel`, `SortedSig.sum`, `constructorSig`,
   `interpSetoid` / `interpQuotRel`, `SynCat` (for the middle
   category), `finAppL` / `finAppR` / `get_finAppL` / `get_finAppR` /
   `get_append_lt` / `get_append_ge`, and `arityCongr` are generic
   over the sort type or purely numeric and are reused as-is.
   `higherOrder' A` is a new instance of the existing `Presentation`
   structure at `S := RType'`, not a new structure.

## 3. Module layout

New modules, each mirrored by a `GebLeanTests/` module and registered
in the aggregators:

| Module | Content |
| --- | --- |
| `GebLean/SliceW/Reindex.lean` | `SlicePFunctor.reindex`, `W`-equivalence, fiber form |
| `GebLean/Ramified/SigEquiv.lean` | `SortedSigEquiv`, `tmMap` / `tmEquiv`, naturality, round trips |
| `GebLean/Ramified/PresentationEquiv.lean` | model agreement, generic step-2 category equivalence |
| `GebLean/Ramified/Polynomial/Interp.lean` | `Tm'.eval`, `QuotRel'`, `interpQuotRel'`, `tmSliceEquiv_eval` |
| `GebLean/Ramified/Polynomial/SynCat.lean` | `HomTuple'`, `Hom'`, `SynCat'`, category and product instances |
| `GebLean/Ramified/Polynomial/SynCatEquiv.lean` | step-1 generic equivalence `synCatSliceEquiv` |
| `GebLean/Ramified/Polynomial/Ident.lean` | `appSig'`, currying, `defnSig'`, shapes, `identEndo'`, `RIdent'`, `interp` |
| `GebLean/Ramified/Polynomial/IdentEquiv.lean` | `identCtxEquiv`, the `Iso`, `identSliceEquiv`, interp agreement |
| `GebLean/Ramified/Polynomial/HigherOrder.lean` | `appChain'`, identifier summands, `higherOrderModel'`, `higherOrder'`, `RMRecCat'` |
| `GebLean/Ramified/Polynomial/HigherOrderEquiv.lean` | summand equivalences, `rmRecCatSliceEquiv` |
| `GebLean/Ramified/Polynomial/FirstOrder.lean` | first-order sub-theory (replacement; section 9) |
| `GebLean/Ramified/Polynomial/Collapse.lean` | `SynCatFO'`, `ObjCtx'`, `collapseDenotation'`, restriction, agreement |
| `GebLean/Ramified/Polynomial/Characterization.lean` | `collapseFunctor'`, endpoints |

Additive changes to existing modules: `FreeM.elim` with computation
rules in `GebLean/SliceW/FreeM.lean`; `freeAlgSliceEquiv_recurse` and
`RType'.interp_isObj` (both absent from Phase A) in
`GebLean/Ramified/Polynomial/RType.lean`, where `FreeAlg'.induction`
is in scope; `natFreeAlgEquiv'_slice` (holding by `rfl`, since
Phase A defines `natFreeAlgEquiv'` as the composite) in
`GebLean/Ramified/Polynomial/FreeAlg.lean`; `RType.interpCongr` (the
congruence of the legacy denotation along a base-carrier equivalence)
in the legacy `GebLean/Ramified/RType.lean`, with the carrier bridge
`carrierSliceEquiv` and `carrierSliceEquiv_isObj` in
`GebLean/Ramified/Polynomial/RType.lean`; `Tm'.reind_symm` /
`Tm'.reind_symm'` in `GebLean/Ramified/Polynomial/Term.lean`.
Deletions: `GebLean/Ramified/FirstOrder.lean`,
`GebLeanTests/Ramified/FirstOrder.lean`, and their aggregator entries.
Documentation: `docs/areas/polynomial-functors.md`,
`docs/areas/ramified-recurrence.md`, and the `TODO.md` porting record
(section 12).

## 4. Term-layer completion (`Polynomial/Interp.lean`)

The pieces Phase B left unported, mirroring
`GebLean/Ramified/Interp.lean`:

- `FreeM.elim` (in `GebLean/SliceW/FreeM.lean`): the fold of the free
  monad into a family `C : I → Type` given a leaf function on `v` and
  an algebra on `F`-nodes, realized by one `SlicePFunctor.W.elim` over
  `translate v F`, with computation rules `elim_pure` and `elim_node`.
  Novel packaging (the free monad's universal property restricted to
  its existence half, as in `Slice/W.lean`).
- `Tm'.eval {sig Γ} (M : SortedModel sig) (ρ : M.Env Γ) {s} (t : Tm'
  sig Γ s) : M.carrier s`: instantiation of `FreeM.elim`; a variable
  leaf reads `ρ` transported along its fiber equality, an operation
  node applies `M.interpOp` transported along its result-sort
  equality. Mirrors the legacy `Tm.eval` (novel packaging of Leivant
  III section 2.7 semantics; the `SortedModel` vocabulary is reused
  unchanged).
- `Tm'.eval_transport`, `Tm'.eval_subst` (by the `bind` computation
  rules and `W.induction`), mirroring the legacy statements.
- `QuotRel'`: the `QuotRel` structure with `Tm` replaced by `Tm'`
  (`rel` family plus `subst_congr` over `Tm'.subst`), with
  `QuotRel'.rel_reind`. Novel packaging.
- `interpQuotRel' (P : Presentation) : QuotRel' P.sig`: extensional
  equality of `Tm'.eval` at `standardModel P` under every environment;
  substitution congruence by `Tm'.eval_subst`. Novel packaging.
- `tmSliceEquiv_eval`: for every `P`, `M`, `ρ`,
  `(tmSliceEquiv Γ s t).eval M ρ = t.eval M ρ` — the two evaluations
  agree on the nose (sorts, contexts, and model are shared; only the
  term carrier differs). Proved by `W.induction` on the primed side
  with `tmSliceEquiv_var` / `tmSliceEquiv_op` and the computation
  rules of both evals.

## 5. Primed syntactic category and step 1

`Polynomial/SynCat.lean` mirrors `GebLean/Ramified/SynCat.lean` over
`Tm'`: `HomTuple'`, `HomTuple'.id` / `.comp`, `homSetoid'`, `Hom'`
with identity, composition, and the category laws from the `Tm'`
clone laws; `joinTuple'` / `fstTuple'` / `sndTuple'` and the chosen
finite products by context concatenation (`SynCat'.instCategory`,
`SynCat'.instCartesianMonoidalCategory`), reusing the sort-generic
position lemmas of the legacy module. `Hom'.eval` and its `eval_mk` /
`eval_comp` mirror the legacy statements. All novel packaging along
the legacy module's precedent line (its references apply unchanged).

`Polynomial/SynCatEquiv.lean` provides step 1, generic in
`P : Presentation`:

- `synCatSliceEquiv P : SynCat' P (interpQuotRel' P) ≌
  SynCat P (interpQuotRel P)`. Identity on objects (both carriers are
  `Ctx P.S`). The hom bridge is componentwise `tmSliceEquiv`,
  descending to the quotients by `tmSliceEquiv_eval` (native primed
  interpretative equality holds iff legacy interpretative equality of
  the translated tuple holds — environments and model are shared).
  Identity and composition laws by `tmSliceEquiv_var` and
  `tmSliceEquiv_subst`. The hom maps are descended bijections and the
  object map is the identity, so unit and counit are identities up to
  `eqToIso`. Novel packaging.

## 6. Signature-translation layer (step 2)

`SigEquiv.lean` (generic, legacy `Tm` on both sides; transcription of
the standard signature-morphism and reduct machinery of multi-sorted
universal algebra — Sannella and Tarlecki, "Foundations of Algebraic
Specification and Formal Software Development", 2012, DOI
`10.1007/978-3-642-17336-3`, Chapter 1; the Lean packaging is novel):

- `SortedSigEquiv sig sig̅` (top-level in the namespace, not
  `SortedSig.Equiv`, avoiding the shadowing of mathlib's `Equiv`
  inside the namespace): `sortEquiv : S ≃ S̅`,
  `opEquiv : sig.Op ≃ sig̅.Op`,
  `arity_comm : sig̅.arity (opEquiv o) = (sig.arity o).map sortEquiv`,
  `result_comm : sig̅.result (opEquiv o) = sortEquiv (sig.result o)`.
- `SortedSigEquiv.tmMap`, packaged as `tmEquiv : Tm sig Γ s ≃
  Tm sig̅ (Γ.map sortEquiv) (sortEquiv
  s)`: both directions by `PolyFix.ind`, with reindexing transports
  along `get_map` (a new shared helper reading `get` through
  `List.map` — core and mathlib carry only `List.getElem_map`) at
  variables and along `arity_comm` /
  `result_comm` at operation nodes; round trips by `PolyFix.ind`.
  Naturality lemmas at `var` and `op`, and commutation with `subst`
  and `reind`.

`PresentationEquiv.lean` (generic; same provenance):

- `PresentationEquiv P P̅`: a `SortedSigEquiv` of the signatures
  together with model agreement for the standard models — a carrier
  equivalence `carrierEquiv : (standardModel P).carrier s ≃
  (standardModel P̅).carrier (sortEquiv s)` and `interpOp` agreement
  through `carrierEquiv` and `arity_comm` / `result_comm`. An
  equivalence, not an equality: at the Phase C instantiation the base
  carriers `FreeAlg' A` and `FreeAlg A` are related only by
  `freeAlgSliceEquiv`, so no carrier equality exists.
- `PresentationEquiv.tmMap_eval`: evaluation commutes with the term
  translation
  through `carrierEquiv` (by `PolyFix.ind`; the pattern of
  `foTm_eval`).
- `PresentationEquiv.synCatEquiv : SynCat P (interpQuotRel P) ≌
  SynCat P̅ (interpQuotRel P̅)`: object map `List.map sortEquiv`; hom
  map componentwise `tmMap` with reindexing along
  `get_map`; well-definedness and the functor laws by
  `Quotient.sound` from `tmMap_eval` (the `foInclusion` proof
  pattern); the inverse functor from the symmetric data; unit and
  counit by `eqToIso` on the propositional object round trips
  (`List.map_map` and the sort equivalence's round trips), their hom
  conditions again by interpretative equality.

## 7. Identifier rebuild

`SliceW/Reindex.lean` (generic, legacy-free; transcription of base
change of polynomial functors — Gambino and Kock 2013, DOI
`10.1017/S0305004112000394`, section 1 — restricted to base change
along an equivalence; the Lean packaging is novel):

- `SlicePFunctor.reindex (e : I ≃ J) (F : SlicePFunctor I I) :
  SlicePFunctor J J`: shapes and positions unchanged, `q` and `r`
  conjugated by `e`.
- `reindex.wEquiv : F.W ≃ (reindex e F).W` and its fiber form
  `{ w : F.W // wIndex w = e.symm j } ≃`
  `{ w' : (reindex e F).W // wIndex w' = j }`: the
  underlying `PFunctor.W` trees are identical; admissibility is
  conjugated by a `Prop`-valued induction (`RecProp` /
  `W.induction`), and `wIndex` commutes with `e`.

`Polynomial/Ident.lean` mirrors `GebLean/Ramified/HigherOrder.lean`'s
identifier layer on the primed stack (transcription of Leivant III
section 2.3 — explicit definitions, ramified monotonic recurrence
eq. (4), flat recurrence eq. (5) — through the vendored W-type; the
packaging is novel along the legacy module's precedent):

- The module split cuts the legacy `HigherOrder.lean` below the
  identifier layer, so no import cycle arises: `Ident.lean` holds the
  shared summands and everything up to `RIdent'.interp` — `appSig'`,
  `stdConstructorInterp'`, `stdAppInterp'`, `RType'.curried` with
  `curried_nil` / `curried_cons`, and `curryInterp'` — while
  `Polynomial/HigherOrder.lean` (section 8) takes `appChain'` onward
  and imports `Ident.lean`. `defnSig' A n holeIdx'` is
  `constructorSig A RType'.IsObj` summed with `appSig'`,
  `holeSig' n holeIdx'`, and `holeConstSig' n holeIdx'` (hole indices
  over `List RType' × RType'`, curried results via `RType'.curried`,
  the `foldr` of `RType'.arrow`).
- `DefnShape' A Γ' τ'` (`numHoles`, `holeIdx'`, `body : Tm' (defnSig'
  A numHoles holeIdx') Γ' τ'`), `MrecShape'` / `FrecShape'` (context
  equations via `RType'.omega` / `RType'.o`), `IdentShape'`,
  `IdentDir'`, `identTarget'`, `identEndo' A : PolyEndo (List RType' ×
  RType')` (non-recursive signature data, as `toSlice sig.polyEndo`
  already consumes for `Tm'`).
- `RIdent' A Γ' τ'`: the fiber of `(toSlice (identEndo' A)).W` at
  `(Γ', τ')` (the `FreeAlg'` fiber-subtype idiom), with formers
  `defn'` / `mrec'` / `frec'` via `W.mk` and `@[simp]`
  constructor-compatibility lemmas.
- `defnModel'`, `childEnv'` / `envHead'` / `envLast'` (primed
  mirrors), `RIdent'.interpStep`, and `RIdent'.interp` as a
  catamorphism via `W.elim` at the index-dependent motive; the
  `defn'` case folds the body by `Tm'.eval` against `defnModel'`, the
  `mrec'` / `frec'` cases recurse via `FreeAlg'.recurse`. Fully
  native: no cast against the legacy world occurs in the model.

`Polynomial/IdentEquiv.lean` (novel packaging):

- `identCtxEquiv : List RType' × RType' ≃ List RType × RType`: the
  product of `Equiv.listEquivOfEquiv rTypeSliceEquiv` (forward map
  `List.map rTypeSliceEquiv`) and `rTypeSliceEquiv`.
- A same-index `SlicePFunctor.Iso (toSlice (identEndo' A))
  (reindex identCtxEquiv.symm (toSlice (identEndo A)))`. Its
  `shapeEquiv` maps `IdentShape'` to `IdentShape` at translated
  indices summand-wise: `DefnShape'` bodies through the composite of
  `tmSliceEquiv` and `tmEquiv` at the `defnSig'`-to-`defnSig`
  signature equivalence; `MrecShape'` / `FrecShape'` by congruence on
  the context equations (`rTypeSliceEquiv_omega`, `rTypeSliceEquiv_o`,
  `List.map_append`).
- `identSliceEquiv : RIdent' A Γ' τ' ≃ RIdent A (Γ'.map
  rTypeSliceEquiv) (rTypeSliceEquiv τ')`: the reindex fiber
  equivalence composed with `Iso.wEquivFiber` and Phase A's
  `polyFixSliceEquiv.symm` (the `polyFreeMSliceEquiv` assembly
  pattern). Former-naturality lemmas `identSliceEquiv_defn` /
  `_mrec` / `_frec` via `wMap_mk`.
- `identSliceEquiv_interp` (the phase's summit): the legacy `interp`
  of the translated identifier agrees with the native
  `RIdent'.interp` under the named carrier bridge
  `carrierSliceEquiv A t' : RType'.interp (FreeAlg' A) t' ≃
  RType.interp (FreeAlg A) (rTypeSliceEquiv t')` — the `Equiv.cast`
  of `rTypeSliceEquiv_interp` at `FreeAlg' A` composed with
  `RType.interpCongr (freeAlgSliceEquiv A)`, the congruence of the
  legacy denotation along a base-carrier equivalence. By
  `W.induction` over the identifier tree: the `defn'` case
  by `tmSliceEquiv_eval` composed with `tmMap_eval` at
  `defnModel'` / `defnModel` with hole interpretations matched by the
  induction hypothesis; the `mrec'` / `frec'` cases by
  `freeAlgSliceEquiv_recurse` (new agreement lemma for Phase A's
  paramorphism, by `FreeAlg'.induction` and `recurse_mk` on both
  sides) with `childEnv'`-matching lemmas.

## 8. Primed presentation and the composite equivalence

`Polynomial/HigherOrder.lean` mirrors the remainder of
`GebLean/Ramified/HigherOrder.lean` (same transcription sources):
`appChain'` with `appChain_curryInterp'`, `identSig'` /
`identConstSig'` (operations `Σ Γ' τ', RIdent' A Γ' τ'`),
`higherOrderModel' A` (carrier `RType'.interp (FreeAlg' A)`,
identifier operations read by `RIdent'.interp` and `curryInterp'` —
fully native), `higherOrder' A : Presentation` (`S := RType'`,
`IsObj := RType'.IsObj`, `alg := A`, `std := higherOrderModel' A`),
`RMRecCat' A := SynCat' (higherOrder' A) (interpQuotRel' (higherOrder'
A))`, and `identHom'` with `identHom_eval'`.

`Polynomial/HigherOrderEquiv.lean` instantiates step 2 and composes:

- The `SortedSigEquiv` between `(higherOrder' A).sig` and
  `(higherOrder A).sig`, summand-wise: the constructor summand by
  subtype congruence along `rTypeSliceEquiv_isObj` (arities by
  `List.map` of `List.replicate`); `appSig'` by product congruence
  (arities by `rTypeSliceEquiv_arrow`); `identSig'` /
  `identConstSig'` by sigma congruence along `Equiv.listEquivOfEquiv
  rTypeSliceEquiv` and `rTypeSliceEquiv`, with `identSliceEquiv` at
  the identifier component and `rTypeSliceEquiv_curried` (new, by
  `List.foldr` induction) at the constant summand's results.
- Model agreement: carriers by `carrierSliceEquiv` (section 7); the
  constructor cases by `freeAlgSliceEquiv_mk` with
  `carrierSliceEquiv_isObj` at the object-sort readings, the
  application cases through `RType.interpCongr`'s arrow equation, the
  identifier cases by `identSliceEquiv_interp`, the constant cases by
  a `curryInterp'` agreement induction on the context.
- `rmRecCatSliceEquiv A : RMRecCat' A ≌ RMRecCat A`:
  `Equivalence.trans` of `synCatSliceEquiv (higherOrder' A)` and the
  instantiated `PresentationEquiv.synCatEquiv`.

## 9. First-order sub-theory replacement

`Polynomial/FirstOrder.lean` replaces the deleted legacy module,
transcribing the same source (Leivant III section 2.4(3), p. 216; the
first-order examples section 2.4(2); the DLMZ tier-vector prose
convention, DOI `10.4204/EPTCS.23.4`) on the primed stack. The legacy
module's names are freed by the deletion, so the replacement keeps
them unprimed except where the declaration is a member of a primed
type's namespace:

- `Tm'.TowerSorts` and `RIdent'.FirstOrder`: recursive `Prop`
  predicates via `W.RecProp` (the Phase A `IsTower` pattern), with
  `@[simp]` unfolding lemmas at variables / operations and at the
  formers; `RIdent.shapeFO`'s primed counterpart `RIdent'.ShapeFO` on
  `IdentShape'`.
- `foIdentSig`, `foIdentConstSig`, `firstOrderSig`,
  `firstOrderModel`, `firstOrderPresentation` over the primed
  summands and `{ f : RIdent' A Γ' τ' // f.FirstOrder }`.
- `foOp`, `foTm` (elimination by `FreeM.elim`), `foOp_eval`,
  `foTm_eval` (consuming `Tm'.eval`), `foHomMap`, and `foInclusion :
  SynCat' (firstOrderPresentation A) (interpQuotRel' …) ⥤ RMRecCat'
  A`, mirroring the legacy proofs with the primed vocabulary.

## 10. Collapse packaging and endpoints

`Polynomial/Collapse.lean` mirrors the packaging (not the soundness
content) of `GebLean/Ramified/Soundness/Collapse.lean`:

- `isObjCtx'`, `SynCatFO' := isObjCtx'.FullSubcategory`,
  `SynCatFO'.toObjCtx'`, `objLen'`, `ObjCtx' n := Fin n → { s :
  RType' // s.IsObj }`, `ObjCtx'.toCtx` with its length and
  `get`-lemmas, `oObj'`, `oCtx'`, `ObjCtx'.toSynCatFO'`,
  `objToNat'` / `objFromNat'` (via `natFreeAlgEquiv'` and
  `RType'.interp_isObj`), `ramifiedEnv'`, `ramifiedDenotation'`,
  `collapseHom'`, `collapseDenotation'`, and the identity and
  composition laws, mirroring the legacy statements. `arityCongr` is
  reused unchanged (purely numeric).
- `synCatFOSliceEquiv : SynCatFO' ≌ SynCatFO`: the restriction of
  `rmRecCatSliceEquiv natAlgSig` to the full subcategories, using the
  object-property correspondence from `rTypeSliceEquiv_isObj`
  (via mathlib's `ObjectProperty.lift`; the executor searches for a
  ready-made equivalence-restriction lemma first and assembles
  manually otherwise, recording the outcome — the sub-plan carries
  the decision procedure).
- The agreement lemma (decision 5):
  `collapseDenotation (synCatFOSliceEquiv.functor.map g') =
  arityCongr h₁ h₂ (collapseDenotation' g')`, proved by unfolding
  both denotations to evaluations and applying the model agreement,
  `tmSliceEquiv_eval` / `tmMap_eval`, and the `objToNat'`
  correspondence (`carrierSliceEquiv_isObj` composed with the
  `natFreeAlgEquiv'` agreement).

`Polynomial/Characterization.lean` mirrors
`GebLean/Ramified/Characterization.lean`:

- `ObjCtx'.toSynCatFO'` lifting lemmas, `synCatFOHom'`, and the
  `oCtx'`-to-`oCtx` object correspondence (via `rTypeSliceEquiv_o`).
- `collapseFunctor' := synCatFOSliceEquiv.functor ⋙ collapseFunctor`
  with its `Faithful` instance (composite of an equivalence functor
  and the faithful `collapseFunctor`); `collapseKFunctor' :=
  collapseFunctor' ⋙ erToKFunctor`, faithful likewise.
- `ramified_definability' {n m : LawvereERCat} (f : n ⟶ m)`:
  `∃ (Γ' : ObjCtx' n) (g' : Γ'.toSynCatFO' ⟶ (oCtx' m).toSynCatFO'),
  collapseDenotation' g' = arityCongr … f.interp` — mirror-exact with
  primes (Leivant III Theorem 14 (1) ⇒ (2), section 6.1). Proved from
  the legacy `ramified_definability` witnesses pulled back through
  `synCatFOSliceEquiv.inverse` with `eqToHom` conjugation, closed by
  the agreement lemma and an `arityCongr` composition identity.
- `ramified_definability_kSim'` likewise from
  `ramified_definability_kSim` (with Tourlakis 2018 Corollary
  0.1.0.44 at `n = 2` supplying the equivalence, as in the legacy
  statement).

The ER-side content — `erMorN_ramified_definable`, the
`collapseFunctor` faithfulness proof, `f.interp`, and everything
under `Soundness/` and `Definability/` — is reused unchanged.

## 11. Constraints

The master spec section 3 constraints apply unchanged: no
`noncomputable`; `Classical.choice` in proofs only; the axiom gate
passes; recursor-only elimination over the recursive tree types
(`W.elim`, `W.RecProp`, `W.induction`, `FreeM.elim`, the free-monad
bind on the vendored side; `PolyFix.ind` on the legacy side only
where a bridge consumes it — here `SortedSigEquiv.tmMap` and its lemmas, `RType.interpCongr`,
and the legacy halves of the agreement proofs); `GebLean/SliceW/*`
stays legacy-free; module docstrings, mathlib naming and style, lines
at most 100 characters; `@[simp]` only on constructor-compatibility
and field-characterization lemmas.

## 12. `TODO.md` porting record

A bullet in `TODO.md`'s "To be done in geb-mathlib" section,
**slicew-promotion** (delivered: committed on this branch by the
`doc(todo)` commit preceding the sub-plan), records the
geb-mathlib-eligible modules — the
ones depending only on the vendored `Geb.Mathlib` tree, mathlib, or
CSLib and written to geb-mathlib standards: `GebLean/SliceW.lean`,
`GebLean/SliceW/{Translate,Iso,FreeM,Reindex}.lean` and their
`GebLeanTests/SliceW/` mirrors (with `Reindex` and the `FreeM.elim`
extension added by this phase) — together with the promotion-time
residue recorded by Phase B (mark the four `Iso` transport helpers
`private`; re-check the `uY`-first universe declaration order in
`Translate.lean`), and the follow-through step: after porting,
refresh the vendored tree and replace the `GebLean/SliceW`
originals with the vendored copies.

## 13. Testing

Compositional, lemma-routed tests (numeric and semantic assertions
through proven lemmas, never kernel reduction of composite
`W`-trees), one mirror module per source module: `reindex` round
trips on a sample tree; `Tm'.eval` on Phase B's two-sorted
mixed-arity smoke signature; `tmEquiv` round trips and eval
agreement on a small signature equivalence; `identSliceEquiv`
former-naturality and interp agreement on a small identifier over
`natAlgSig`; the first-order predicates on tower and non-tower
samples; an endpoint smoke test instantiating
`ramified_definability'` at a concrete `ERMor` (mirroring the legacy
`Characterization` tests).

## 14. Process

1. Spike first (the A.0 / B.1 pattern): validate sorry-free, before
   any real file, (a) `reindex` with its `W`-equivalence, (b)
   `Tm'.eval` with its computation rules, (c) the `Iso.shapeEquiv`
   for `identEndo'` (the `DefnShape'` leg through the composite term
   equivalence), and (d) the `defn'` case of
   `identSliceEquiv_interp` on a minimal instance.
2. C.0 sub-plan at
   `docs/superpowers/plans/2026-07-19-ramified-poly-er-subplan.md`
   (the master plan's fixed name), bite-sized tasks, spike-first.
3. Adversarial review of this design and the sub-plan (fresh-context
   reviewers verifying every named declaration against source;
   re-fetch the mathlib upstream guides), converged to zero-defect,
   before the user-review handoff.
4. User line-by-line review.
5. Subagent-driven development on branch `feat/ramified-poly-er`:
   spike task first, fresh implementer and task review per task,
   whole-branch review at the end.

## References

- N. Gambino, J. Kock, "Polynomial functors and polynomial monads",
  Mathematical Proceedings of the Cambridge Philosophical Society 154
  (2013) 153-192. DOI `10.1017/S0305004112000394`.
- D. Leivant, "Ramified recurrence and computational complexity III:
  Higher type recurrence and elementary complexity", Annals of Pure
  and Applied Logic 96 (1999) 209-229. DOI
  `10.1016/S0168-0072(98)00040-2`.
- D. Leivant, "Ramified recurrence and computational complexity I:
  Word recurrence and poly-time", in P. Clote, J. B. Remmel (eds.),
  Feasible Mathematics II, Birkhäuser, 1995. DOI
  `10.1007/978-1-4612-2566-9_11`.
- D. Sannella, A. Tarlecki, "Foundations of Algebraic Specification
  and Formal Software Development", Springer, 2012. DOI
  `10.1007/978-3-642-17336-3`.
- N. Danner, D. Leivant, J.-Y. Marion, et al. (DLMZ), tier-vector
  notation. DOI `10.4204/EPTCS.23.4`.
