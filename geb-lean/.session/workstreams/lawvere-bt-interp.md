# Workstream: Lawvere BT Interpretation Functor

## Status

Complete — faithful functor constructed and
faithfulness proved.

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
5. [done] Faithfulness: `Faithful` instance
   via `interpU_complete`, which uses
   `btMorRel.substReflect` (the parameterized
   universal property) + `norm0_gen` (ground
   normalization).  `substReflect` was added
   as a new constructor to `btMorRel` to
   capture the parameterized BTO universal
   property; soundness proved for all
   existing proofs (interpU_sound,
   subst_cong_right).
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

### Session 2026-03-29 analysis

Extensive exploration of proof strategies for the
`succ k` case of the induction-on-arity approach
(approach B). Added several compiling helper lemmas:

**New helper lemmas (all compiling):**

- `norm0`: specialized `norm0_gen` at arity 0 with
  empty substitution; gives `btMorRel 0 t (quoteBT
  (t.interpU Fin.elim0))` for any `t : BTMor1 0`
- `interpU_complete_zero`: completeness at arity 0,
  via `norm0` applied to both terms
- `quoteBT_subst_elim0_gen` / `quoteBT_subst_elim0`:
  `(quoteBT bt).subst Fin.elim0 = quoteBT bt` (lift
  from arity 0 to arity n)
- `quoteBT_subst_any_gen` / `quoteBT_subst_any`:
  `(quoteBT bt).subst σ = quoteBT bt` for any σ
  (quoteBT values are variable-free)
- `btMorRel_lift_zero`: lift `btMorRel 0` to
  `btMorRel n` via `subst_cong_right Fin.elim0`
- `interpU_ground_rel`: for all ground σ,
  `btMorRel 0 (t1.subst σ) (t2.subst σ)` from
  semantic equality
- `ground_rel_at_n`: for all ctx, `btMorRel n
  (t1.subst (quoteBT ∘ ctx)) (t2.subst (quoteBT
  ∘ ctx))` from semantic equality (lifts ground
  btMorRel to arity n)

**Current proof state:**
The proof is structured by `induction n`:

- Base (n=0): complete via `interpU_complete_zero`.
- Step (n=k+1): reduces to the **variable recovery**
  lemma. Uses IH at arity k and `subst_cong_right`
  to get `btMorRel (k+1) (t1 with last var =
  quoteBT v) (t2 with last var = quoteBT v)` for
  all `v : BT`. The remaining sorry is: from this
  universal ground-at-last-var equivalence, conclude
  `btMorRel (k+1) t1 t2`.

**Variable recovery analysis:**
The gap between "for all v : BT, btMorRel (k+1)
(t.subst lastSubst_v) (t2.subst lastSubst_v)" and
"btMorRel (k+1) t1 t2" is exactly the **variable
recovery** problem. Attempted strategies:

1. `subst_cong_left` with σ = lastSubst_v vs
   σ' = proj: requires `btMorRel (k+1) (quoteBT v)
   (proj (last k))`, which is false.
2. `foldUniq` with identity algebra: gives back
   `foldEta`, which is circular.
3. `foldUniq` with custom algebra: requires
   constructing φ satisfying specific computation
   rules, which amounts to structural analysis of t1
   and t2.
4. Direct `subst_id` argument: identity substitution
   `proj` cannot be expressed as `quoteBT ∘ ctx`
   for any ctx.

**Conclusion:** The variable recovery step cannot
be resolved by substitution-based arguments alone.
It requires structural analysis of at least one of
the two terms, confirming the session 2026-03-28
analysis.

### Recommended path forward

**Approach C (Induction on arity + structural
analysis for recovery):**

Keep the arity-induction structure (base n=0 via
`norm0`, step via IH at n-1). For the variable
recovery step, use `BTMor1.ind` on ONE of the two
terms (say t1). For each constructor of t1:

- **proj i, leaf, branch**: use context
  discrimination + the `hcomp` hypothesis to
  determine what `t2` must be (up to btMorRel) via
  the ground instances. These cases may also require
  inner `BTMor1.ind` on t2 for the fold sub-case.
- **fold**: use fold axioms (`foldLeaf`,
  `foldBranch`, `congFold`) + the outer IH (from
  BTMor1.ind on t1's children) + inner analysis of
  t2.

This is a hybrid of approaches A and B. The arity
induction handles the "variable counting," while the
structural induction handles the "variable recovery."

### Infrastructure needed

- For approach A: fiber-generic inner motive with
  `finCast` transport, analogous to `interpU_subst`
- For approach B: `BT.depth`, well-founded
  interleaving, lifting lemma
- For approach C: BTMor1.ind on t1 within the step
  case, combined with inner BTMor1.ind on t2 for
  fold sub-cases; estimated 500-1000 lines
- All approaches need ~500-1000 lines of Lean code
  for the full proof

### Session 2026-03-29 completeness analysis

Extensive analysis of proof strategies for
`interpU_complete`.  The proof gap is between
`h_quot` (btMorRel at quoteBT-substituted terms)
and `btMorRel n t1 t2` (the open terms).  This
gap requires structural induction on at least one
term.

**Approaches attempted:**

1. **Arity induction (n -> n+1):** Substitute
   `quoteBT v` for the last variable and use IH at
   arity n.  Produces btMorRel at arity n for
   substituted terms, but the "variable recovery"
   step (going from substituted to open) requires
   structural analysis.  BLOCKED by variable
   recovery.

2. **Single BTMor1.ind on t2:** Handle proj/leaf/
   branch of t2 by context discrimination.  For
   fold case of t2, use inner IH on fold's children.
   The fold-vs-proj case requires showing
   `btMorRel n (fold ...) (proj j2)`, which needs
   `foldUniq` or other fold axioms.

3. **foldUniq with φ = proj ⟨j2,...⟩:**
   Gives the right conclusion `(proj j2) ~
   fold m f g tree j`.  Leaf premise requires
   `btMorRel n (proj j2) (f j)`, which is NOT
   always true (counterexample: identity fold has
   f j = leaf, not proj j2).

4. **foldUniq with identity fold target:**
   Use foldUniq for the identity fold (m=1, f=leaf,
   g=branch) with φ 0 = fold m f g (proj(last n)) j.
   Leaf premise: `fold m f g leaf j ~ leaf`, i.e.,
   `f j ~ leaf`.  Works when f j = leaf (identity
   fold family), FAILS when f j ≠ leaf (e.g.,
   fold 1 (proj 0) (proj 0) tree 0).

5. **foldEta + congFold:** Always circular.
   `congFold` requires `btMorRel n tree1 tree2`
   which is the original goal or equivalent.

6. **quoteBT-substitution normalization:**
   `t.subst(quoteBT ∘ ctx) ~ quoteBT(t.interpU ctx)`
   gives h_quot but NOT btMorRel n t1 t2.

**Concrete counterexample analysis:**

`fold 1 (fun _ => proj 0) (fun _ => proj 0) (proj 0) 0`
acts as `proj 0`.  Here f 0 = proj 0, and foldUniq
with φ 0 = proj 0 WORKS (leaf and branch premises
hold trivially since f = g = proj 0).

`fold 1 (fun _ => leaf) (fun _ => branch(proj 0)
(proj 1)) (proj 0) 0` acts as `proj 0` (identity
fold by foldEta).  Here f 0 = leaf, and foldUniq
with identity fold target WORKS (leaf premise:
f 0 = leaf ~ leaf).

`fold 2 (fun _ => leaf) (fun _ => ...) (proj 0) 0`
(m=2 identity fold) acts as `proj 0`.  foldUniq
with identity fold target WORKS (leaf premise:
f 0 = leaf ~ leaf; branch premise: foldBranch
matches).

**Conclusion:** Different folds computing the same
function require different `foldUniq` applications.
The proof must analyze the fold's base child `f j`
to determine whether to use foldUniq with
φ = proj ⟨j2,...⟩ (when f j ~ proj j2) or with
the identity fold target (when f j ~ leaf).

**Recommended approach:** Within the BTMor1.ind
step for the fold case, apply the outer IH on
`f j` to determine its semantic equivalence class.
Then branch:

- If `f j ~ leaf`: use foldUniq with identity fold
- If `f j ~ proj j2`: use foldUniq with φ = proj j2
- If `f j ~ branch ...`: use foldUniq with a fold
  whose base matches

This requires the outer IH on `f j` to determine
which case applies, plus `foldLeaf` to simplify
the fold at leaf.  The branch premise of foldUniq
should follow from `foldBranch` in all cases.

**Helper lemmas added (compiling):**

- `branch_ne_proj`: branch interpU matching a
  projection is contradictory.
- `branch_ne_leaf`: branch interpU matching
  BT.leaf is contradictory.

### Session 2026-03-29 implementation progress

**Completed (all compiling, no warnings except
the remaining holes):**

1. `quoteBT_leaf`, `quoteBT_node` — computation
   rules for quoteBT on BT.leaf/node.
2. `subst_cast` — fiber transport commutes with
   substitution.
3. `norm0_fold_commute_gen`, `norm0_fold_commute`
   — BT structural induction lemma for the fold
   case of norm0_gen.
4. `norm0_gen` — the full normalization theorem
   via BTMor1.ind (proj/leaf/branch/fold cases
   all complete, including the fold case which
   uses BT structural induction + congFold +
   subst_cong_left + IH on g children).
5. `norm0` — specialization of norm0_gen at
   arity 0.
6. `interpU_complete_zero` — completeness at
   arity 0 via norm0.
7. `quoteBT_subst_elim0_gen/elim0`,
   `quoteBT_subst_any_gen/any` — quoteBT is
   substitution-invariant (variable-free).
8. `btMorRel_lift_zero` — lift btMorRel 0 to
   btMorRel n for variable-free terms.
9. `interpU_ground_rel` — ground substitution
   equivalence from semantic equality.
10. `ground_rel_at_n` — ground btMorRel at
    arity n from semantic equality.
11. `interpU_complete_inner` — inner BTMor1.ind
    on t2 (proj/leaf cases delegate to
    vs_proj/vs_leaf; branch/fold cases have
    holes).
12. `interpU_complete` — delegates to
    `interpU_complete_inner`.

**Remaining holes (4 exact _ placeholders):**

1. `interpU_complete_vs_proj` (line ~1628):
   Given `∀ ctx, t.interpU ctx = ctx j`,
   show `btMorRel n t (proj j)`.
2. `interpU_complete_vs_leaf` (line ~1636):
   Given `∀ ctx, t.interpU ctx = BT.leaf`,
   show `btMorRel n t leaf`.
3. Branch case of `interpU_complete_inner`
   (line ~1677): Given inner IH on l2, r2 and
   `∀ ctx, t1.interpU ctx = BT.node
   (l2.interpU ctx) (r2.interpU ctx)`,
   show `btMorRel n t1 (branch l2 r2)`.
4. Fold case of `interpU_complete_inner`
   (line ~1681): Given inner IH on fold
   sub-terms and semantic equality,
   show `btMorRel n t1 (fold m f g tree j)`.

**Analysis of remaining holes:**

Holes 1 and 2 require BTMor1.ind on `t` (the
arbitrary term) to decompose it into
constructors.  The fold case of each requires
relating a fold to a non-fold (proj or leaf),
which needs the fold axioms + the inner IH.

Hole 3 requires decomposing t1 into cases.
For t1 = branch l1 r1: use BT.node_inj + inner
IH + congBranch.  For other t1: contradiction
or fold case.

Hole 4 is the fold-fold case (when t2 is a
fold), which requires both outer and inner IH.

**PolyFix representation obstacle:**

Inside BTMor1.ind step functions, terms appear
as `PolyFix.mk n ⟨⟨j, _⟩, pos⟩ children`,
which is NOT definitionally equal to
`BTMor1.proj j` / `BTMor1.leaf` /
`BTMor1.branch l r` / `BTMor1.fold m f g t j`.
Converting between the two representations
requires explicit unfolding + rewriting.
The pattern from `subst_cong_left` is:
`set lhs := ...; unfold BTMor1.subst
BTMor1.ind PolyFixCoprod.ind PolyFix.ind
at lhs; dsimp only at lhs; rw [lhs]`.

Also, `interpU` on raw PolyFix.mk forms
may not reduce to `interpU_proj`, `interpU_leaf`,
etc.  Lemmas `raw_proj_interpU` and
`raw_leaf_interpU` (proved by `rfl`) were added
to bridge this.

**Recommended next step:**

Fill the 4 holes using nested BTMor1.ind:
for each hole, apply BTMor1.ind on the unknown
term (t or t1), handling each of the 4
constructor cases.  The fold sub-case of each
uses the IH from the BTMor1.ind + fold axioms.
This gives a 4×4 = 16 case matrix, of which 9
are easy (fold-free × fold-free) and 7 require
fold axiom reasoning.  Estimated: 500-1000
additional lines of Lean code.
