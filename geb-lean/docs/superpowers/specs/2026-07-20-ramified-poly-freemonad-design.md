# Phase B design: the native slice free monad and `Tm'`

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [1. Scope and provenance](#1-scope-and-provenance)
- [2. Decisions](#2-decisions)
- [3. Module layout](#3-module-layout)
- [4. Native layer (`GebLean/SliceW/`)](#4-native-layer-gebleanslicew)
  - [4.1 `SlicePFunctor.translate`](#41-slicepfunctortranslate)
  - [4.2 `FreeM`: carrier and operations](#42-freem-carrier-and-operations)
  - [4.3 Laws](#43-laws)
  - [4.4 `SlicePFunctor` isomorphisms (`Iso.lean`)](#44-slicepfunctor-isomorphisms-isolean)
- [5. Bridge (`GebLean/PolyBridge/FreeMEquiv.lean`)](#5-bridge-gebleanpolybridgefreemequivlean)
- [6. Term layer (`GebLean/Ramified/Polynomial/Term.lean`)](#6-term-layer-gebleanramifiedpolynomialtermlean)
- [7. Constraints](#7-constraints)
- [8. Testing](#8-testing)
- [9. Process](#9-process)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## 1. Scope and provenance

This document is the Phase B sub-plan design for the
ramified-on-vendored-polynomial-functors workstream. It refines the
master spec
([2026-07-19-ramified-polynomial-design.md](2026-07-19-ramified-polynomial-design.md),
sections 4.2, 5, 11) and the master plan
([../plans/2026-07-19-ramified-polynomial-plan.md](../plans/2026-07-19-ramified-polynomial-plan.md),
Phase B), resolving the four design questions recorded in the Phase B
handoff
([../notes/2026-07-20-ramified-polynomial-phaseB-handoff.md](../notes/2026-07-20-ramified-polynomial-phaseB-handoff.md)).
It feeds the B.0 sub-plan
(`docs/superpowers/plans/2026-07-19-ramified-poly-freemonad-subplan.md`).

Deliverable boundary (fixed by the master plan): `polyFreeMSlice` (here
realized as `SlicePFunctor.FreeM`), `polyFreeMSliceEquiv`, `Tm'` with
`var` / `op` / `subst`, substitution compatibility across the
equivalence, and the clone laws for `Tm'`.

## 2. Decisions

Resolutions of the handoff's design questions, decided during
brainstorming:

1. **Augmented signature: native slice-level presentation.** The
   augmentation is a new operation on the vendored side,
   `SlicePFunctor.translate`, taking a leaf family presented as a bare
   structure map `v : Y → I` (the presentation `Geb.Mathlib.Data.PFunctor.Slice.W`
   uses for every slice object) and a `SlicePFunctor I I`, and forming
   the endofunctor with leaf shapes `Y` (empty positions) and node
   shapes inherited. The legacy-side alternative (reusing
   `polyTranslate` under `toSlice`) was declined: the native operation
   depends on nothing legacy, which serves the deferred migration goal
   (master spec section 10) and upstream promotion.
2. **Generic level: yes.** The free-monad layer is generic in
   `(v, F)`; the term layer instantiates it. Mirrors Phase A's
   generic-then-instantiate structure.
3. **Substitution and laws: native.** `FreeM.bind` is a single
   `SlicePFunctor.W.elim`; the monad laws are proved natively by
   `SlicePFunctor.W.induction`, keeping the layer self-contained and
   upstream-promotable. The clone laws for `Tm'` are thin instances of
   the native laws; the bridge carries only compatibility statements.
   The alternative (conjugating the legacy laws through the
   equivalence) was declined because it would tie the native layer's
   laws to `GebLean/PolyAlg.lean`.
4. **Variable family: nothing new.** `varOver Γ = Over.mk Γ.get`
   instantiates the bare-map presentation as `Γ.get : Fin Γ.length → S`.
   The leaf fiber at sort `y` is `{ i : Fin Γ.length // Γ.get i = y }`,
   the same subtype the legacy `Tm.var` inhabits at `⟨i, rfl⟩`.

Placement (decided during brainstorming): the native machinery lives in
a new narrow-and-deep directory `GebLean/SliceW/`, written to
geb-mathlib standards with no legacy imports, so a later phase can
promote it to geb-mathlib through the established backport flow.
Developing it upstream-first was declined as a cross-repo scope
expansion; extending `GebLean/PolyBridge/` was declined because the
machinery is not bridging.

Bridge route (decided during brainstorming): the comparison to the
legacy free monad crosses two gaps. Phase A covers legacy-to-slice:
`PolyFreeM V P` is definitionally `PolyFix (polyTranslate V P)`, so
`polyFixSliceEquiv (polyTranslate V P) x` reaches the fiber of
`(toSlice (polyTranslate V P)).W`. The remaining gap —
`toSlice (polyTranslate V P)` versus the native
`translate V.hom (toSlice P)`, isomorphic but not equal — is crossed by
a generic single-step lemma: an isomorphism of `SlicePFunctor`s induces
an equivalence of their W-types respecting `wIndex`. The bespoke
fold-both-ways alternative was declined as single-use.

## 3. Module layout

| Module | Content | Imports |
| --- | --- | --- |
| `GebLean/SliceW/Iso.lean` | `SlicePFunctor` isomorphisms; induced W-type equivalence | vendored stack only |
| `GebLean/SliceW/Translate.lean` | `SlicePFunctor.translate` | vendored stack only |
| `GebLean/SliceW/FreeM.lean` | `FreeM` carrier, `pure` / `node` / `bind`, monad laws, transport lemmas | vendored stack only |
| `GebLean/SliceW.lean` | directory index | the above |
| `GebLean/PolyBridge/FreeMEquiv.lean` | concrete isomorphism, `polyFreeMSliceEquiv`, compatibility lemmas | both stacks |
| `GebLean/Ramified/Polynomial/Term.lean` | `Tm'` layer | `SliceW`, `FreeMEquiv`, `Ramified/Term` |

Tests mirror each module under `GebLeanTests/` and are registered in
the aggregators (`GebLeanTests.lean`, `GebLeanTests/Ramified.lean`).

## 4. Native layer (`GebLean/SliceW/`)

### 4.1 `SlicePFunctor.translate`

`translate (v : Y → I) (F : SlicePFunctor I I) : SlicePFunctor I I`:

- shapes `A := Y ⊕ F.A`;
- positions `B := Sum.rec (fun _ => PEmpty) F.B`;
- shape-output `q := Sum.elim v F.q`;
- direction-input `r` inherited on node positions (leaf positions are
  empty, so their clause is `PEmpty.elim`).

Transcription: the "translation" endofunctor `Y + F(−)` whose initial
algebra carries the free monad [GambinoKock2013]; the legacy
counterpart is `polyTranslate` (`GebLean/PolyAlg.lean`). Characterizing
`@[simp]` lemmas for each field, following the `toSlice_A/_B/_q/_r`
precedent (`GebLean/PolyBridge/Slice.lean`).

### 4.2 `FreeM`: carrier and operations

- `FreeM (v : Y → I) (F : SlicePFunctor I I) (i : I) :=`
  `{ w : (translate v F).W // wIndex w = i }` — the fibered carrier
  (universe level as the vendored `W` dictates),
  following the Phase A subtype idiom (`FreeAlg'`). Transcription: the
  free monad on a polynomial functor as the W-type of the translation
  [GambinoKock2013].
- `FreeM.pure : { a : Y // v a = i } → FreeM v F i` — `W.mk` at an
  `inl` shape; the empty child family is `PEmpty.elim`.
- `FreeM.node` — the operation-node constructor: `W.mk` at an `inr`
  shape, taking the shape's compatible family of `FreeM` children.
  The piece `Tm'.op` instantiates.
- `FreeM.bind`, for leaf families `v : Y → I` and `v' : Y' → I` (the
  target leaf family has its own leaf type, as the legacy
  `polyFreeMBind` changes the leaf family from `A` to `B`):
  `FreeM v F i → (∀ j, { a : Y // v a = j } → FreeM v' F j) → FreeM v' F i`
  — a single `SlicePFunctor.W.elim` into the slice algebra
  `((translate v' F).W, wIndex)`: a leaf shape dispatches to the
  substitution function (its fiber property supplies the over-index
  side condition); a node shape re-applies `W.mk`. The fiber property
  of the result comes from `SlicePFunctor.W.comp_elim`. No structural
  recursion; recursor-only elimination throughout.

Compatibility side goals are genuine (the index type `I` is arbitrary;
no `Subsingleton.elim` shortcut). Novel packaging: the free-monad
structure maps realized on the vendored eliminator.

### 4.3 Laws

Proved natively by `SlicePFunctor.W.induction`, with no legacy imports:

- `FreeM.pure_bind` — expected definitional or near-definitional, from
  `W.elim_mk` at a leaf shape;
- `FreeM.bind_node` — the computation rule at an operation node, from
  `W.elim_mk`; consumed by the bridge's bind-naturality proof;
- `FreeM.bind_pure` — right unit (stated at `Y' = Y`, `v' = v`);
- `FreeM.bind_assoc` — associativity;
- `FreeM.pure_transport`, `FreeM.bind_transport` — commutation of
  `pure` and `bind` with reindexing along a fiber equality, the native
  analogues of `polyFreeMPure_transport` / `polyFreeMBind_transport`
  (`GebLean/PolyAlg.lean`), consumed by the clone-law instances.

Transcription: the free-monad laws [GambinoKock2013]; statement forms
follow the legacy `polyFreeM_pure_bind` / `polyFreeM_bind_pure` /
`polyFreeM_bind_assoc`.

### 4.4 `SlicePFunctor` isomorphisms (`Iso.lean`)

A structure packaging: an equivalence of shape types commuting with
`q`, and per-shape equivalences of position types commuting with `r`.
The induced map on W-types is a `SlicePFunctor.W.elim` in each
direction; the round trips are closed by `SlicePFunctor.W.induction`;
the equivalence respects `wIndex`. Novel packaging of the standard fact
that isomorphic containers have equivalent initial algebras
[AbbottAltenkirchGhani2005].

## 5. Bridge (`GebLean/PolyBridge/FreeMEquiv.lean`)

- The concrete isomorphism
  `toSlice (polyTranslate V P) ≅ translate V.hom (toSlice P)`: on
  shapes, distribute `Σ x, ({ a // V.hom a = x } ⊕ i)` to
  `V.left ⊕ Σ x, i`, contracting `Σ x, { a // V.hom a = x } ≃ V.left`;
  positions match leaf-to-leaf (`PEmpty` to `PEmpty`) and node-to-node
  (identical carriers); `q` and `r` commute definitionally on node
  shapes and on positions, while on leaf shapes `q`-commutation is
  `V.hom a = x`, discharged by the leaf shape's stored fiber witness.
- `polyFreeMSliceEquiv (V : Over X) (P : PolyEndo X) (x : X) :`
  `PolyFreeM V P x ≃ FreeM V.hom (toSlice P) x` — the composite of
  `polyFixSliceEquiv (polyTranslate V P) x` (Phase A, applied verbatim
  since `PolyFreeM V P` is definitionally `PolyFix (polyTranslate V P)`)
  with the fiber restriction of the induced W-equivalence.
- Compatibility lemmas, in the naturality form validated in Phase A
  (`equiv (op' t) = op (equiv t)`):
  - `pure`-naturality: `polyFreeMSliceEquiv` carries `polyFreeMPure`
    to `FreeM.pure`;
  - `node`-naturality: it carries a `PolyFix.mk` node at `Sum.inr` to
    `FreeM.node`;
  - `bind`-naturality: it carries `polyFreeMBind` to `FreeM.bind`,
    proved by `PolyFix.ind` on the legacy side.

Novel packaging throughout.

## 6. Term layer (`GebLean/Ramified/Polynomial/Term.lean`)

- `Tm' (sig : SortedSig S) (Γ : Ctx S) : S → Type :=`
  `FreeM Γ.get (toSlice sig.polyEndo)`.
- `Tm'.var`, `Tm'.op`, `Tm'.subst`, `Tm'.weaken` — thin instances of
  `FreeM.pure` / `FreeM.node` / `FreeM.bind`, mirroring the legacy
  signatures (`GebLean/Ramified/Term.lean`) exactly, including the
  substitution tuple's transport `a.2 ▸ σ a.1`, so that Phase C can
  exchange the layers. `Tm'.reind` is the bare transport `h ▸ t`, as
  in the legacy layer.
- Clone laws `Tm'.subst_id`, `Tm'.subst_subst`, `Tm'.var_subst`,
  `Tm'.subst_reind` — instances of the native laws and transport
  lemmas of section 4.3; the bridge is not involved.
- `tmSliceEquiv : Tm' sig Γ s ≃ Tm sig Γ s` —
  `(polyFreeMSliceEquiv (varOver Γ) sig.polyEndo s).symm`, noting
  `(varOver Γ).hom = Γ.get`. The `.symm` re-orients the bridge so the
  primed carrier reads as the source, as in Phase A's
  `freeAlgSliceEquiv` (the orientation imprecision the handoff records
  from Phase A).
- Compatibility lemmas `tmSliceEquiv_var` / `tmSliceEquiv_op` /
  `tmSliceEquiv_subst` — instances of the bridge naturality lemmas.

Novel packaging: the free-algebra term conventions of Leivant III
section 2.1 [Leivant1999] presented through the vendored stack.

## 7. Constraints

All Phase A constraints continue to bind: no `noncomputable`
(`Classical.choice` in proofs only; the axiom gate accepts only
`propext` / `Quot.sound` / `Classical.choice`); recursor-only
elimination of the recursive tree types (`W.elim` / `W.induction` /
`W.RecProp` on the vendored side, `PolyFix.ind` only in the bridge);
`@[simp]` on constructor-compatibility lemmas only (operation
naturality lemmas are not `@[simp]`, per the Phase A `simpNF`
finding); universe polymorphism as far as it compiles; file headers
and docstrings per the existing `GebLean` convention; no novelty
claims in `.lean` comments (citations only).

## 8. Testing

- Mirrored test modules for `SliceW/Iso`, `SliceW/Translate`,
  `SliceW/FreeM`, `PolyBridge/FreeMEquiv`, and
  `Ramified/Polynomial/Term`, registered in the aggregators.
- Semantic assertions route through proven `@[simp]` lemmas
  (constructor naturality, reduction rules), never kernel reduction of
  composite W-trees.
- A concrete multi-sorted smoke signature exercises `Tm'.var` /
  `Tm'.op` / `Tm'.subst` and the clone laws at more than one sort, so
  the genuinely multi-sorted side conditions are covered.

## 9. Process

Per the Phase A learnings: execution starts with a spike validating
the two hardest constructions sorry-free before real files are laid
out — the induced W-equivalence of `Iso.lean` and `FreeM.bind` via
`W.elim` — on a concrete signature. Then subagent-driven development
with a fresh implementer and reviewer per task and a whole-branch
review.

## References

- N. Gambino, J. Kock, "Polynomial functors and polynomial monads",
  Mathematical Proceedings of the Cambridge Philosophical Society 154
  (2013) 153-192. DOI `10.1017/S0305004112000394`.
- M. Abbott, T. Altenkirch, N. Ghani, "Containers: constructing
  strictly positive types", Theoretical Computer Science 342 (2005)
  3-27. DOI `10.1016/j.tcs.2005.06.002`.
- D. Leivant, "Ramified recurrence and computational complexity III:
  Higher type recurrence and elementary complexity", Annals of Pure
  and Applied Logic 96 (1999) 209-229.
  DOI `10.1016/S0168-0072(98)00040-2`.
