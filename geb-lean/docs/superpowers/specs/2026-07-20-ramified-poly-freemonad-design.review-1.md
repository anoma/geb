# Adversarial review 1: Phase B free-monad sub-plan design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Majors](#majors)
- [Minors](#minors)
- [Nits](#nits)
- [Verified without defect](#verified-without-defect)
- [Disposition](#disposition)
- [Overall](#overall)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Round 1, 2026-07-20. One fresh-context reviewer (declaration
verification, definitional-fact checking, construction realizability,
consistency, style) against source at branch
`feat/ramified-poly-freemonad`. Every claim below was re-verified
against source before entry.

## Majors

None.

## Minors

- M1 (section 6, `tmSliceEquiv` direction). The document declares
  `tmSliceEquiv : Tm' sig Γ s ≃ Tm sig Γ s` as `polyFreeMSliceEquiv`
  at `(varOver Γ, sig.polyEndo)`, but section 5's
  `polyFreeMSliceEquiv V P x : PolyFreeM V P x ≃ FreeM V.hom (toSlice P) x`
  instantiates to `Tm sig Γ s ≃ Tm' sig Γ s` — the opposite
  orientation; `.symm` is required. The Phase A precedent is
  `freeAlgSliceEquiv` (`GebLean/Ramified/Polynomial/FreeAlg.lean`),
  and the handoff records the same imprecision from Phase A. Fix:
  state the `.symm`.
- M2 (section 5, commutation claim). "`q` and `r` commute by
  computation" holds definitionally on node shapes and on positions,
  but on leaf shapes `q`-commutation is `V.hom a = x`, discharged by
  the leaf shape's stored fiber witness
  (`GebLean/PolyAlg.lean`, `polyTranslateIndex`), not by reduction.
  Fix: state the leaf-shape case separately.
- M3 (section 4.2, `FreeM.bind` leaf family). The signature introduces
  `v'` without a binder; a literal reading places `v'` over the same
  leaf type `Y`, which cannot instantiate `Tm'.subst` between distinct
  contexts (`Fin Γ.length` versus `Fin Δ.length`; the legacy
  `polyFreeMBind` likewise changes the leaf family). Fix: declare
  `v' : Y' → I` over its own leaf type, with `bind_pure` stated at
  `Y' = Y`, `v' = v`.

## Nits

- N1 (section 6, `Tm'.reind` classification). `Tm.reind` is the bare
  transport `h ▸ t` (`GebLean/Ramified/Term.lean`), not an instance of
  `FreeM.pure` / `FreeM.node` / `FreeM.bind`. Fix: list it separately
  as the transport it is.

## Verified without defect

- All named declarations exist with the stated meanings and
  signatures, across `GebLean/PolyAlg.lean`,
  `GebLean/Ramified/Term.lean`, `GebLean/PolyBridge/{Slice,WEquiv}.lean`,
  `GebLean/Ramified/Polynomial/FreeAlg.lean`, and the vendored
  `Geb/Mathlib/Data/PFunctor/Slice/{Basic,W}.lean` (including
  `W.elim`'s `(g, hg)` signature and `W.comp_elim` / `W.elim_mk` /
  `W.induction` / `W.RecProp`).
- `PolyFreeM` is an `abbrev` for `PolyFix (polyTranslate · ·)`, so the
  definitional claim holds; `(varOver Γ).hom = Γ.get` is definitional
  on this toolchain; leaf positions of `toSlice (polyTranslate V P)`
  are `PEmpty`; the section 5 shape distribution and the contraction
  `Σ x, { a // V.hom a = x } ≃ V.left` are correct with no universe
  obstruction.
- `FreeM.bind` as a single `W.elim` into `((translate v' F).W, wIndex)`
  is type-correct in outline (non-recursive `Sum` split; `Compatible`
  transfers at `inr`; `hg` provable by `funext` with the leaf fiber
  property; result fiber from `comp_elim`); the section 4.4 induced
  W-equivalence is constructible from `W.elim` both ways plus
  `W.induction` round trips, respecting `wIndex` via `comp_elim`.
- Consistent with the master plan's fixed Phase B deliverables, the
  handoff's constraints, and master spec sections 4.2 / 5 / 10 / 11;
  the Gambino–Kock 2013 citation covers the free monad as the initial
  algebra of the translation; markdown style rules hold.

## Disposition

All four findings applied to the design document in the same commit as
this review.

## Overall

0 blockers, 0 majors, 3 minors, 1 nit. Converged pending application
of M1–M3, N1.
