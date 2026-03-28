# Workstream: Lawvere BT Interpretation Functor

## Status

Active — soundness complete; next: functor
construction and faithfulness

## Goal

Construct a faithful functor from `LawvereBTQuotCat`
(the Lawvere theory of parameterized binary tree objects)
into `Type u` for arbitrary universe `u`.

## Files

- `GebLean/LawvereBT.lean` — `interpU`, `interpUStep`,
  computation lemmas, helper lemmas, `interpU_fold`,
  `interpU_subst` (all complete, no sorry)
- `GebLean/LawvereBTInterp.lean` — `BT.fold_leaf`,
  `BT.fold_node`, `fold_eta_*`, `fold_uniq_interp_gen`,
  `interpU_sound` (all complete, no sorry)
- `GebLean/LawvereBTQuot.lean` — category instance,
  PBTO instance (unchanged)

## What exists (all compiling)

### Definitions

- `interpUStep` — named step function for `interpU`
  (factored out to enable `change ... (step :=
  interpUStep) ...` in proofs)
- `BTMor1.interpU` — universe-polymorphic
  interpretation via `BTMor1.ind` with `interpUStep`
- `BTMorN.interpU` — extension to n-to-m morphisms
- `BT.fold_leaf`, `BT.fold_node` — BT fold computation
  rules (both `rfl`)

### Computation lemmas (all `rfl`)

- `interpU_proj`, `interpU_leaf`, `interpU_branch`

### Helper/transport lemmas

- `ind_btMorInject` — `BTMor1.ind step (btMorInject j
  eval) = step j pos children ih` (proved by `unfold
  BTMor1.ind btMorInject polyFixStrFamily; rfl`)
- `polyFixCoprodStr_inj_child` — relates
  `polyFixChildAt` on coproduct injection to
  `(congrFun (Over.w mor) e) ▸ (mor.left e).2`
  (existing, in `PolyAlgUMorph.lean`)
- `btMorInd_cast_ctx` — `(BTMor1.ind step (h ▸ t))
  ctx = (BTMor1.ind step t) (fun v => ctx (h ▸ v))`
  (proved by `subst h; rfl`)
- `polyFixInd_cast` — same as above for `PolyFix.ind`
- `polyFixInd_child_ctx` — congruence for
  `PolyFix.ind` on child and context
- `interpU_cast` — `(h ▸ t).interpU ctx = t.interpU
  (fun v => ctx (h ▸ v))`
- `Fin.val_cast` — `(h ▸ v).val = v.val`
- `subst_sigma_snd` — `(hfst ▸ s.2) = t` when
  `s = ⟨a, t⟩`
- `dite_subst_pos/neg_pos/neg_neg` — resolve
  `hfst ▸ (dite ...).2` for each dite branch
- `ind_subst_sigma` — combined `BTMor1.ind` +
  sigma transport + context resolution

### `interpU_fold` proof structure

```lean
  unfold BTMor1.interpU BTMor1.fold
  rw [ind_btMorInject]
  simp only [interpUStep]
  apply congr_fun; congr 3
  · funext i; sorry    -- base child
  · funext l r j'; sorry  -- step child
  · sorry              -- tree child
```

The outer structure compiles. Each sorry needs to
show that a `polyFixChildAt`-wrapped child with a
transported context equals the original child with
the original context.

## Completed: `interpU_fold`

The proof was completed by factoring out:

- `foldEval` — abbreviation for the eval tuple
- `foldChildSigma_{base,step,tree}` — sigma-level
  equalities for each child range, resolving the
  `dite` at the sigma level (where rewriting works)
- `ind_interpUStep_sigma` — combines sigma
  resolution (`subst hsig`) with transport
  elimination (`cases hfst`) and context
  adjustment (`finCast`) in one step
- `interpU_snd_resolve` — resolves `s.snd.interpU`
  when `s` is a known sigma

The dependent-sigma obstacle (`.snd` on a `dite`
inside a `▸` transport) was bypassed by working
at the sigma level first, then using `subst`/`cases`
instead of `rw`/`simp`.

## Previous obstacles (resolved)

```lean
(BTMor1.ind interpUStep
  (polyFixChildAt ⟨3, pos⟩ mor ⟨dir, _⟩))
  (fun v => ctx (finCast _ v))
= (BTMor1.ind interpUStep original_child) ctx
```

After `simp only [polyFixCoprodStr_inj_child]`,
this becomes:

```lean
(BTMor1.ind interpUStep
  (hfst ▸ (pbefMor eval).left ⟨dir, _⟩).2))
  (fun v => ctx (finCast _ v))
= (BTMor1.ind interpUStep original_child) ctx
```

After `unfold pbefMor ptoefMor ccrEvalMor` +
`simp only [Over.homMk_left, btMorComponents,
btMorFoldPoly, polyBetweenFamily, polyToOverFamily,
ccrObjMk, ccrFamily, pbefIndex, ptoefIndex]`,
the child becomes `(hfst ▸ (dite ...).2)` and the
fiber map becomes `(Over.mk (fun d => if ↑d < m
then n else ...)).hom ⟨dir, _⟩`.

The blocker: the fiber map uses `ite` (not `dite`),
and the sigma first component expected by
`subst_sigma_snd`/`dite_subst_pos` is the
UNREDUCED `(Over.mk ...).hom ⟨dir, _⟩` form, not
`n`/`m+m`/`n`. The `dif_pos`/`if_pos` proofs
don't unify with this unreduced form.

## Path forward

Two approaches:

### Approach A: Reduce the fiber map first

Add `if_pos`/`if_neg` to the `simp only` that
reduces the fiber map, so that `(Over.mk ...).hom
⟨dir, _⟩` reduces to `n`/`m+m`/`n` BEFORE
`subst_sigma_snd` runs. The issue is that
`if_pos` with the direction-specific proof
(`i.isLt`, `omega`, etc.) didn't fire via
`simp only` — possibly because the `ite` is
inside `Over.mk.hom` which `simp` doesn't enter.

Fix: use `conv` or `dsimp` to force `Over.mk.hom`
reduction, then `if_pos` fires.

### Approach B: Combined polyFixChildAt lemma

Prove three lemmas directly in `LawvereBT.lean`:

```lean
fold_polyFixChildAt_base (i : Fin m) :
    polyFixChildAt ⟨3, pos⟩ mor ⟨↑i, _⟩ =
    (fiber_proof ▸ f ⟨↑i, i.isLt⟩)
```

These lemmas unfold `polyFixChildAt` +
`polyFixCoprodStr_inj_child` + `pbefMor` +
fiber map + `dif_pos`/`dif_neg` all in ONE step,
hiding the intermediate complexity. Then
`interpU_fold` just `rw`s with these three lemmas.

## Dependencies

- `LawvereBTInterp.lean` imports `LawvereBTQuot.lean`
- `interpU` and helpers are in `LawvereBT.lean`
  (access to private `btMorInject`)
- `BT.fold_leaf`/`BT.fold_node` are in
  `LawvereBTInterp.lean`
- `finAppend` in `LawvereBT.lean` was made
  universe-polymorphic (`{α : Type _}`)

## After `interpU_fold`

1. Soundness (`btMorRel` implies equal `interpU`)
   — by induction on `btMorRel`, using
   `interpU_fold` for the fold cases
2. Functor construction (`LawvereBTQuotCat ⥤ Type u`)
   — lift `interpU` through quotient, prove functor
   laws
3. Faithfulness — completeness of the standard
   model `BT` for the equational theory
4. (Later) Primitive recursion correspondence,
   non-fullness
