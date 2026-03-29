# Workstream: Lawvere BT Interpretation Functor

## Status

Active — functor constructed; `interpU_complete`
(completeness) remaining for faithfulness

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
  `interpU_sound`, `interpFunctor`,
  `Faithful` instance (depends on `interpU_complete`,
  1 underscore)
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

## Progress

1. [done] Soundness (`interpU_sound`): by induction
   on `btMorRel`, 9 cases, using `interpU_fold`
   for fold cases and `interpU_subst` for
   substitution-related cases
2. [done] `interpU_subst`: naturality of interpU
   under substitution, proved by `BTMor1.ind`
3. [done] Functor (`interpFunctor`): lifts
   `BTMorN.interpU` through quotient via
   `interpU_sound`; `map_id` by `interpU_proj`,
   `map_comp` by `interpU_subst`
4. [done] BT structural lemmas:
   - `BT.leaf_ne_node`: via `PolyFix.index`
     extraction (`Sum.inl` vs `Sum.inr`)
   - `BT.node_inj`: via `bt_node_eq_mk` reducing
     `BT.node` to `PolyFix.mk` with explicit
     match-based children, then `PolyFix.mk.inj`
   - `BT.cases`: match on PolyFix then Sum index
   - `quoteBT_interpU`: induction on PolyFreeM
     structure, using `BT.fold_leaf/node` and
     `BTMor1.interpU_leaf/branch`
5. [in progress] Faithfulness: `Faithful` instance
   defined, depends on `interpU_complete` (1
   underscore). This is completeness of BT for
   the equational theory.
6. (Later) Primitive recursion correspondence,
   non-fullness

## Remaining: `interpU_complete`

Statement: `∀ ctx, t1.interpU ctx = t2.interpU ctx
→ btMorRel n t1 t2`

This is the converse of soundness -- completeness
of the standard model `BT` for the equational
theory `btMorRel`.

### Current state

One underscore remains: `interpU_complete` (line
~802 of LawvereBTInterp.lean). The helper lemmas
`interpU_always_leaf` and `interpU_always_node` are
defined as corollaries of `interpU_complete`. The
`Faithful` instance is fully defined modulo
`interpU_complete`.

### Proof structure analysis

The non-fold cases (proj, leaf, branch) of
`interpU_complete` are straightforward using
`BT.leaf_ne_node`, `BT.node_inj`, and `BT.cases`
for context discrimination.

The fold case is the principal obstacle. Given
`fold m f g tree j` with the same `interpU` as
some `t2`, we need `btMorRel n (fold m f g tree j)
t2`.

### Approaches analyzed for the fold case

1. **foldUniq with constant-leaf phi**: Fails
   because the leaf premise requires `btMorRel n
   (f j') BTMor1.leaf` for ALL `j'`, but the fold
   at position `j` being leaf does not imply that
   all base children are leaf.

2. **foldUniq with "natural" phi** (phi j' = fold
   with generic tree variable): Always yields a
   reflexivity, since the substitution recovers the
   original fold.

3. **congFold**: Requires `btMorRel` on the tree
   arguments, which is what we are proving.

4. **n=0 normalization** (`norm0`): Prove that
   every closed `BTMor1 0` term is btMorRel to
   `quoteBT` of its interpretation. The fold case
   of norm0 requires recursion on `(g j).subst
   (sigma_fold)`, which is NOT a sub-term of the
   original fold. Termination requires showing that
   the depth of the fold's tree argument's
   interpretation decreases. This is true (fold on
   `BT.node l r` reduces to sub-folds on `l` and
   `r`), but requires a joint induction: structural
   (`BTMor1.ind`) for the term + well-founded
   (`BT.depth` of tree interpretation) for the fold
   expansion.

5. **Reduction from general n to n=0**: If norm0 is
   proved, general completeness follows from showing
   that closed-substitution equivalence implies open
   equivalence. This "lifting" step itself requires
   non-trivial equational reasoning (and cannot be
   done by `congFold` alone since it would be
   circular).

### Session 2026-03-28 analysis

Exhaustive exploration of proof strategies yielded
the following conclusions:

**Fold axioms alone are insufficient.** The axioms
`foldEta`, `foldUniq`, `foldLeaf`, `foldBranch`,
and `congFold` cannot prove completeness for
syntactically different terms without structural
decomposition of both terms. Every attempt to use
`foldEta` + `congFold` to relate `t1` and `t2`
requires `btMorRel n t1 t2` as a hypothesis to
`congFold`, creating circularity. Every attempt to
use `foldUniq` requires constructing a `phi` that
captures the semantic relationship between `t1` and
`t2`, which requires structural knowledge of at
least one of them.

**Single induction is insufficient.** Inducting on
`t1` alone leaves the base cases (proj, leaf)
without an induction hypothesis, and proving
`btMorRel n (proj i) t2` or `btMorRel n leaf t2`
for arbitrary `t2` requires analyzing `t2`.

**Double induction is required.** The proof must
analyze both `t1` and `t2` structurally. This gives
16 case combinations (4 constructors x 4
constructors). Of these, 6 are contradictions
(cross-constructor), 2 are trivial (same
constructor, no children), 1 uses outer IH
(branch-branch), and 7 involve fold and require
fold axioms + IH.

**Implementation approach**: Define
`interpU_complete` by nested `BTMor1.ind` (or
nested `PolyFix` pattern match with
`termination_by`). The outer induction on `t1` gives
IH for children of `t1`. The inner induction on
`t2` gives IH for children of `t2`. Together, these
handle all 16 cases.

**Technical obstacle**: The nested BTMor1.ind
approach requires the inner motive to be
fiber-generic (since fold children are at fiber
`m+m`, not `n`). This necessitates a `finCast`-style
transport (as in `interpU_subst`). The low-level
PolyFix representation makes the 16-case analysis
very verbose.

### Helper lemmas added (compiling)

- `distinguishCtx`, `distinguishCtx_self`,
  `distinguishCtx_ne`: context that maps one index
  to a node and all others to leaf
- `BT.node_ne_leaf`: symmetric version of
  `BT.leaf_ne_node`
- `fin_eq_of_ctx_eq`: if projections agree on all
  contexts, the indices are equal
- `proj_ne_const_leaf`, `proj_ne_const_node`:
  projection cannot be constant
- `node_interp_ne_leaf`, `leaf_ne_node_interp`:
  node/leaf contradiction helpers

### Recommended approach (updated)

Approach A (Double BTMor1.ind):

Prove by `BTMor1.ind` on `t1`, then `BTMor1.ind`
on `t2` within each case. Use the helper lemmas for
contradiction cases and `BT.node_inj` for the
branch-branch case. For fold cases, use `foldLeaf`,
`foldBranch`, `foldEta`, and `foldUniq` combined
with both IHs.

Approach B (norm0 + lift):

As described previously. This approach separates the
ground case (n=0) from the open case, potentially
simplifying the argument at the cost of needing a
lifting lemma.

### Infrastructure needed

- For approach A: fiber-generic inner motive with
  `finCast` transport, analogous to `interpU_subst`
- For approach B: `BT.depth`, well-founded
  interleaving, lifting lemma
- Both approaches need ~500-1000 lines of Lean code
  for the full proof
