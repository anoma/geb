# Lawvere BT Quotient Category Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended)
> or superpowers:executing-plans to implement this plan
> task-by-task.  Steps use checkbox (`- [ ]`) syntax
> for tracking.

**Goal:** Quotient the syntactic morphisms of
`LawvereBTCat` by fold computation equations to
obtain the true Lawvere theory of binary trees, with
`HasChosenFiniteProducts` and `HasPBTO`.

**Architecture:** Define a 7-component polynomial
`btMorEqPoly : PolyEndo N` whose initial algebra
gives proof trees witnessing equalities between
parallel `BTMor1` terms.  The 7 components are:
`refl`, `symm`, `trans`, `congBranch`, `congFold`,
`foldLeaf`, `foldBranch`.  Extract endpoint functions
`eqLhs, eqRhs : BTMorEq n -> BTMor1 n` via the
polynomial induction principle.  Define the relation
`btMorRel` as the existence of a proof tree with
matching endpoints, quotient via Lean's `Quot`, lift
substitution to the quotient, and derive the
`Category`, `HasChosenFiniteProducts`, and `HasPBTO`
instances.

**Tech Stack:** Lean 4, mathlib CategoryTheory,
GebLean polynomial infrastructure (`PolyAlg`,
`PolyAlgUMorph`), `Quot` (Lean built-in)

---

## Background

`LawvereBT.lean` defines:

- `BTMor1 n = PolyFix btMorPoly n` (syntactic terms)
- `BTMorN n m = Fin m -> BTMor1 n` (tuples)
- `BTMor1.subst` (simultaneous substitution)
- `BTMor1.subst_id`, `BTMor1.subst_comp`,
  `BTMor1.subst_proj` (substitution laws)
- `fold_subst_eq` (substitution distributes over
  fold; currently `private`, must be made public)
- `LawvereBTCat` with `Category` instance (the free
  theory, before quotienting)
- `HasChosenFiniteProducts LawvereBTCat`

The fold computation rules (`fold(f,g,leaf) = f` and
`fold(f,g,branch(t1,t2)) = g[fold results]`) hold
semantically but not syntactically.  The quotient
category makes these into equalities.

## Prerequisites

- Tasks 1-3 of the prior plan
  (`2026-03-19-lawvere-bt-universal-properties.md`)
  are complete.
- `HasChosenFiniteProducts LawvereBTCat` is
  implemented.
- `HasPBTO` on the unquotiented `LawvereBTCat` is
  NOT a prerequisite; `HasPBTO` will be defined
  directly on the quotient category.

## File structure

- **Modify:** `GebLean/LawvereBT.lean` -- make
  `fold_subst_eq` and related helpers public; add
  `BTMor1.subst_leaf`, `BTMor1.subst_branch`; define
  `btFoldFullMor` (syntactic fold morphism)
- **Create:** `GebLean/LawvereBTEq.lean` --
  equation polynomial, proof trees, named
  constructors, endpoint extraction, relation,
  setoid, congruence lemmas
- **Create:** `GebLean/LawvereBTQuot.lean` --
  quotient morphisms, substitution lift, quotient
  category, `HasChosenFiniteProducts`, `HasPBTO`
- **Modify:** `GebLean.lean` -- add imports
- **Create:** `test/TestLawvereBTQuot.lean` --
  tests for quotient category

---

### Task 5: Syntactic prerequisites in LawvereBT.lean

**Files:**

- Modify: `GebLean/LawvereBT.lean`

**Goal:** Make `fold_subst_eq` and related helpers
public.  Add substitution interaction lemmas for
`leaf` and `branch`.  Define `btFoldFullMor` (the
syntactic fold morphism `BTMorN (n+1) m`).

- [x] **Step 1: Make fold_subst_eq public**
  Remove `private` from `fold_subst_eq`.  Also
  remove `private` from `subst_child_eval`,
  `fiberCast_child_eval`, and any other helpers
  referenced by `fold_subst_eq` that need to be
  visible from `LawvereBTEq.lean`.  Build.

- [x] **Step 2: Prove BTMor1.subst_leaf**
  `theorem BTMor1.subst_leaf {n m : N}
    (s : Fin n -> BTMor1 m) :
    BTMor1.leaf.subst s = BTMor1.leaf`
  Should be `rfl` (the leaf case of `subst`
  returns `BTMor1.leaf` unconditionally).  Build.

- [x] **Step 3: Prove BTMor1.subst_branch**
  `theorem BTMor1.subst_branch {n m : N}
    (l r : BTMor1 n) (s : Fin n -> BTMor1 m) :
    (BTMor1.branch l r).subst s =
    BTMor1.branch (l.subst s) (r.subst s)`
  Should be `rfl` or close to it.  Build.

- [x] **Step 4: Define btFoldFullMor**
  The syntactic fold morphism for the universal
  property.  Given `f : BTMorN n m` (base) and
  `g : BTMorN (m+m) m` (step), produce
  `BTMorN (n+1) m`:

  ```lean
  def btFoldFullMor {n m : N}
      (f : BTMorN n m)
      (g : BTMorN (m+m) m) :
      BTMorN (n+1) m :=
    fun j => BTMor1.fold m
      (fun i => (f i).shift 1)
      g
      (BTMor1.proj (n, by omega))
      j
  ```

  Build.

- [x] **Step 5: Build and verify no warnings**
  `lake build && lake test`.

---

### Task 6: Equation polynomial components

**Files:**

- Create: `GebLean/LawvereBTEq.lean`

**Goal:** Define the 7 component polynomials of
`btMorEqPoly`, each as a `PolyEndo N`.  Positions
carry `BTMor1` terms as data; directions encode
sub-proof children.

Each component follows the same pattern as the
`btMorPoly` components in `LawvereBT.lean`: a
function `N -> CoprodCovarRepCat` specifying
positions and their families at each fiber.

#### Component definitions

**refl** (component 0): at fiber `n`, positions are
`BTMor1 n`, no directions.

**symm** (component 1): at fiber `n`, positions are
`BTMor1 n x BTMor1 n` (the conclusion pair: the
proof witnesses `lhs ~ rhs` where the child proves
`rhs ~ lhs`), one direction at fiber `n`.

**trans** (component 2): at fiber `n`, positions are
`BTMor1 n x BTMor1 n x BTMor1 n` (`t1, t2, t3`);
child 0 proves `t1 ~ t2`, child 1 proves `t2 ~ t3`,
conclusion is `t1 ~ t3`.  Two directions (`Bool`) at
fiber `n`.

**congBranch** (component 3): at fiber `n`, positions
are `BTMor1 n x BTMor1 n x BTMor1 n x BTMor1 n`
(`l1, l2, r1, r2`); child 0 proves `l1 ~ l2`, child
1 proves `r1 ~ r2`, conclusion is
`branch(l1,r1) ~ branch(l2,r2)`.  Two directions
(`Bool`) at fiber `n`.

**congFold** (component 4): at fiber `n`, positions
are `(m : N) x Fin m x (Fin m -> BTMor1 n) x
(Fin m -> BTMor1 n) x (Fin m -> BTMor1 (m+m)) x
(Fin m -> BTMor1 (m+m)) x BTMor1 n x BTMor1 n`
(i.e., `m, j, f, f', g, g', tree, tree'`).
Directions: `Fin (m + m + 1)`, fiber map: first `m`
to `n` (base congruence: `f i ~ f' i`), next `m`
to `m + m` (step congruence: `g i ~ g' i`), last
to `n` (tree congruence: `tree ~ tree'`).
Conclusion: `fold(m,f,g,tree,j) ~
fold(m,f',g',tree',j)`.  Same direction structure
as `btMorFoldPoly`.

**foldLeaf** (component 5): at fiber `n`, positions
are `(m : N) x Fin m x (Fin m -> BTMor1 n) x
(Fin m -> BTMor1 (m+m))` (i.e., `m, j, f, g`),
no directions.  Axiom: `fold(m,f,g,leaf,j) ~ f j`.

**foldBranch** (component 6): at fiber `n`, positions
are `(m : N) x Fin m x (Fin m -> BTMor1 n) x
(Fin m -> BTMor1 (m+m)) x BTMor1 n x BTMor1 n`
(i.e., `m, j, f, g, t1, t2`), no directions.
Axiom: `fold(m,f,g,branch(t1,t2),j) ~
(g j).subst (fun i =>
  if i.val < m
  then fold(m,f,g,t1,Fin.mk i.val ...)
  else fold(m,f,g,t2,Fin.mk (i.val-m) ...))`.

- [x] **Step 1: File header and imports**
  Create `GebLean/LawvereBTEq.lean` with imports
  of `GebLean.LawvereBT` and
  `GebLean.PolyAlgUMorph`.  Open `GebLean` and
  `CategoryTheory` namespaces.  Build.

- [x] **Step 2: Define btMorEqReflPoly**
  `polyBetweenConst (polyFixCarrier btMorPoly)`.
  Build.

- [x] **Step 3: Define btMorEqSymmPoly**
  At fiber `n`, position `BTMor1 n x BTMor1 n`,
  one `PUnit` direction at fiber `n`.  Build.

- [x] **Step 4: Define btMorEqTransPoly**
  At fiber `n`, position
  `BTMor1 n x BTMor1 n x BTMor1 n`,
  `Bool` directions at fiber `n`.  Build.

- [x] **Step 5: Define btMorEqCongBranchPoly**
  At fiber `n`, position `(BTMor1 n)^4`,
  `Bool` directions at fiber `n`.  Build.

- [x] **Step 6: Define btMorEqCongFoldPoly**
  At fiber `n`, position carries full fold data
  for two related fold terms.  `Fin (m+m+1)`
  directions with fiber map matching
  `btMorFoldPoly`.  Build.

- [x] **Step 7: Define btMorEqFoldLeafPoly**
  `polyBetweenConst` with position type encoding
  `(m, j, f, g)` over `N`.  Build.

- [x] **Step 8: Define btMorEqFoldBranchPoly**
  Same position type as foldLeaf but with two
  additional `BTMor1 n` fields (`t1, t2`).
  Build.

- [x] **Step 9: Define btMorEqComponents and
  btMorEqPoly**
  `btMorEqComponents : Fin 7 -> PolyEndo N`
  `btMorEqPoly := polyBetweenCoprod (Fin 7)
    btMorEqComponents`
  Build.

---

### Task 7: Proof tree type and named constructors

**Files:**

- Modify: `GebLean/LawvereBTEq.lean`

**Goal:** Define `BTMorEq n := PolyFix btMorEqPoly n`
and named constructors (intro rules) via
`btMorEqInject`, following the pattern of
`btMorInject` / `BTMor1.proj` / etc. in
`LawvereBT.lean`.

- [x] **Step 1: Define BTMorEq and btMorEqInject**
  `abbrev BTMorEq (n : N) : Type :=
    PolyFix btMorEqPoly n`
  `private def btMorEqInject (j : Fin 7) ...`
  (same pattern as `btMorInject`).  Build.

- [x] **Step 2: Define BTMorEq.refl**
  Takes `t : BTMor1 n`, produces `BTMorEq n`.
  Build.

- [x] **Step 3: Define BTMorEq.symm**
  Takes `t1 t2 : BTMor1 n` (the conclusion pair:
  witnesses `t1 ~ t2`) and `child : BTMorEq n`
  (witnesses `t2 ~ t1`), produces `BTMorEq n`.
  Convention: position `(t1, t2)` means the child
  proves `t2 ~ t1` and the conclusion is
  `t1 ~ t2`.  Build.

- [x] **Step 4: Define BTMorEq.trans**
  Takes `t1 t2 t3 : BTMor1 n`; child 0 proves
  `t1 ~ t2`, child 1 proves `t2 ~ t3`;
  conclusion is `t1 ~ t3`.  Build.

- [x] **Step 5: Define BTMorEq.congBranch**
  Takes `l1 l2 r1 r2 : BTMor1 n`; child 0 proves
  `l1 ~ l2`, child 1 proves `r1 ~ r2`.  Build.

- [x] **Step 6: Define BTMorEq.congFold**
  Takes full fold position data plus
  `(m + m + 1)` children.  Build.

- [x] **Step 7: Define BTMorEq.foldLeaf**
  Takes `(m, j, f, g)`, produces `BTMorEq n`.
  Build.

- [x] **Step 8: Define BTMorEq.foldBranch**
  Takes `(m, j, f, g, t1, t2)`, produces
  `BTMorEq n`.  Build.

---

### Task 8: Induction principle and endpoint extraction

**Files:**

- Modify: `GebLean/LawvereBTEq.lean`

**Goal:** Define `BTMorEq.ind` (via
`PolyFixCoprod.ind`) and endpoint extraction
functions `eqLhs, eqRhs : BTMorEq n -> BTMor1 n`.

- [x] **Step 1: Define BTMorEq.ind**
  Wrapper around `PolyFixCoprod.ind` with 7
  step functions, same pattern as `BTMor1.ind`.
  Build.

- [x] **Step 2: Define eqLhs via BTMorEq.ind**
  Motive: `fun {n} _ => BTMor1 n`.
  Cases:
  - refl(t): `t`
  - symm(t1, t2, child): `t1`
  - trans(t1, t2, t3, c1, c2): `t1`
  - congBranch(l1, l2, r1, r2, c1, c2):
    `branch(l1, r1)`
  - congFold(m, j, f, f', g, g', tree, tree',
    ...): `fold(m, f, g, tree, j)`
  - foldLeaf(m, j, f, g):
    `fold(m, f, g, leaf, j)`
  - foldBranch(m, j, f, g, t1, t2):
    `fold(m, f, g, branch(t1, t2), j)`
  Build.

- [x] **Step 3: Define eqRhs via BTMorEq.ind**
  Cases:
  - refl(t): `t`
  - symm(t1, t2, child): `t2`
  - trans(t1, t2, t3, c1, c2): `t3`
  - congBranch(l1, l2, r1, r2, c1, c2):
    `branch(l2, r2)`
  - congFold(...): `fold(m, f', g', tree', j)`
  - foldLeaf(m, j, f, g): `f j`
  - foldBranch(m, j, f, g, t1, t2):
    `(g j).subst (fun i =>
      if h : i.val < m
      then fold(m, f, g, t1, Fin.mk i.val h)
      else fold(m, f, g, t2,
        Fin.mk (i.val - m) (by omega)))`
  Build.

- [x] **Step 4: Prove endpoint computation lemmas**
  For each of the 7 components, prove:
  `eqLhs_refl`, `eqRhs_refl`,
  `eqLhs_symm`, `eqRhs_symm`, etc.
  These should be `rfl` or close to it.
  Build after each pair.

---

### Task 9: Relation and Setoid

**Files:**

- Modify: `GebLean/LawvereBTEq.lean`

**Goal:** Define `btMorRel` as the existence of a
proof tree with matching endpoints.  Prove it is
an equivalence relation.  Define the `Setoid`.

- [x] **Step 1: Define btMorRel**

  ```lean
  def btMorRel (n : N) (t1 t2 : BTMor1 n) :
      Prop :=
    exists (p : BTMorEq n),
      eqLhs p = t1 /\ eqRhs p = t2
  ```

  Build.

- [x] **Step 2: Prove btMorRel is reflexive**
  Use `BTMorEq.refl` + `eqLhs_refl` +
  `eqRhs_refl`.  Build.

- [x] **Step 3: Prove btMorRel is symmetric**
  Use `BTMorEq.symm` + `eqLhs_symm` +
  `eqRhs_symm`.  Build.

- [x] **Step 4: Prove btMorRel is transitive**
  Use `BTMorEq.trans` + endpoint lemmas.
  Build.

- [x] **Step 5: Define btMor1Setoid**

  ```lean
  instance btMor1Setoid (n : N) :
      Setoid (BTMor1 n) :=
    { r := btMorRel n
      iseqv := ... }
  ```

  Build.

---

### Task 10: Congruence lemmas

**Files:**

- Modify: `GebLean/LawvereBTEq.lean`

**Goal:** Prove that `btMorRel` is a congruence
for all constructors and for substitution.

- [x] **Step 1: Prove btMorRel_congBranch**
  `btMorRel n l1 l2 -> btMorRel n r1 r2 ->
    btMorRel n (branch l1 r1) (branch l2 r2)`
  Use `BTMorEq.congBranch` + endpoint lemmas.
  Build.

- [x] **Step 2: Prove btMorRel_congFold**
  Full congruence for fold.  Build.

- [x] **Step 3: Prove btMorRel_foldLeaf**
  `btMorRel n (fold m f g leaf j) (f j)`
  Use `BTMorEq.foldLeaf` + endpoint lemmas.
  Build.

- [x] **Step 4: Prove btMorRel_foldBranch**

  ```lean
  btMorRel n
    (fold m f g (branch t1 t2) j)
    ((g j).subst (fun i =>
      if h : i.val < m
      then fold(m,f,g,t1,Fin.mk i.val h)
      else fold(m,f,g,t2,
        Fin.mk (i.val-m) (by omega))))
  ```

  Use `BTMorEq.foldBranch` + endpoint lemmas.
  Build.

- [x] **Step 5a: Define subst_cong_right helpers**
  Factor out 7 helper lemmas, one per equation
  component (refl, symm, trans, congBranch,
  congFold, foldLeaf, foldBranch).  Define each
  with an underscore body.  Build (expect 7
  errors).

- [x] **Step 5b: Fill subst_cong_right_refl**
  `t.subst s ~ t.subst s` by `btMorRel.refl`.
  Build.

- [x] **Step 5c: Fill subst_cong_right_symm**
  By IH + `btMorRel.symm`.  Build.

- [x] **Step 5d: Fill subst_cong_right_trans**
  By IH + `btMorRel.trans`.  Build.

- [x] **Step 5e: Fill subst_cong_right_congBranch**
  Subst distributes over branch; by IH +
  `btMorRel_congBranch`.  Build.

- [x] **Step 5f: Fill subst_cong_right_congFold**
  Use `fold_subst_eq` to rewrite both sides as
  folds, then `btMorRel_congFold` + IH.  Build.

- [x] **Step 5g: Fill subst_cong_right_foldLeaf**
  Use `fold_subst_eq` + `BTMor1.subst_leaf` to
  show `fold(f[s], g, leaf, j) ~ (f j).subst s`,
  then `btMorRel_foldLeaf`.  Build.

- [x] **Step 5h: Fill subst_cong_right_foldBranch**
  Use `fold_subst_eq` + `BTMor1.subst_branch` +
  `subst_comp` + `btMorRel_foldBranch`.  Build.

- [x] **Step 5i: Prove subst_cong_right**
  Assemble: induction on proof tree, dispatch
  each case to its helper.  Build.

- [x] **Step 6a: Define subst_cong_left helpers**
  Factor out 4 helper lemmas (proj, leaf, branch,
  fold).  Define with underscore bodies.  Build.

- [x] **Step 6b: Fill subst_cong_left_proj**
  `(proj i).subst s = s i`, `(proj i).subst s' =
  s' i`.  Hypothesis gives `s i ~ s' i`.  Build.

- [x] **Step 6c: Fill subst_cong_left_leaf**
  Both sides are `leaf`; `refl`.  Build.

- [x] **Step 6d: Fill subst_cong_left_branch**
  IH + `btMorRel_congBranch`.  Build.

- [x] **Step 6e: Fill subst_cong_left_fold**
  `fold_subst_eq` on both sides; step children
  shared (refl); IH for base and tree +
  `btMorRel_congFold`.  Build.

- [x] **Step 6f: Prove subst_cong_left**
  Assemble: induction on `t`, dispatch each
  case.  Build.

- [x] **Step 7: Prove subst_cong**
  `btMorRel n t1 t2 ->
    (forall i, btMorRel m (s i) (s' i)) ->
    btMorRel m (t1.subst s) (t2.subst s')`
  By `btMorRel.trans` of `subst_cong_right` and
  `subst_cong_left`.  Build.

---

### Task 11: Quotient morphisms and category

**Files:**

- Create: `GebLean/LawvereBTQuot.lean`

**Goal:** Define quotient morphism types, lift
substitution and composition, prove category laws.

**Substitution lifting strategy:** Define
`mapSubst : BTMor1 m -> (Fin m -> BTMor1Q n) ->
BTMor1Q n` by structural induction on the `BTMor1 m`
term via `BTMor1.ind`.  At each `proj i` leaf,
return `s i : BTMor1Q n`.  At each `leaf`, return
`Quot.mk leaf`.  At each `branch(l, r)`, combine
recursive results.  At each `fold`, combine.

Then define composition:
`compQ (f : BTMorNQ n m) (g : BTMorNQ m k) j :=
  mapSubst (Quot.lift ...) f`

where `Quot.lift` on `g j : BTMor1Q m` extracts a
representative, applies `mapSubst`, and the
respect proof uses `subst_cong_right`.

More precisely:

1. `mapSubstRaw (t : BTMor1 m)
     (s : Fin m -> BTMor1 n) : BTMor1 n :=
     t.subst s`
2. `mapSubstQ (t : BTMor1 m)
     (s : Fin m -> BTMor1Q n) : BTMor1Q n`
   by `BTMor1.ind` on `t`:
   - proj i: `s i`
   - leaf: `Quot.mk _ BTMor1.leaf`
   - branch(l, r): combine via `Quot.lift2`
   - fold: combine via `Quot.liftN`

3. Prove `mapSubstQ t s = Quot.mk (t.subst rep)`
   when each `s i = Quot.mk (rep i)`.

4. Define `compQSingle (f : BTMorNQ n m)
     (gj : BTMor1Q m) : BTMor1Q n :=
     Quot.lift (fun gj_raw =>
       mapSubstQ gj_raw f) (respect) gj`
   where respect uses `subst_cong_right`.

This avoids `Quotient.out` and is fully
constructive.

- [x] **Step 1: File header and imports**
  Create `GebLean/LawvereBTQuot.lean` with import
  of `GebLean.LawvereBTEq`.  Build.

- [x] **Step 2: Define BTMor1Q and BTMorNQ**
  Use `Quot (btMorRel n)` (not `Quotient`).
  Build.

- [x] **Step 3: Define mapSubstQ**
  By `BTMor1.ind` on the term, with the strategy
  above.  Build after each constructor case.

- [x] **Step 4: Prove mapSubstQ_mk**
  When all `s i = Quot.mk (rep i)`,
  `mapSubstQ t s = Quot.mk (t.subst rep)`.
  By induction on `t`.  Build.

- [x] **Step 5: Define compQSingle**
  `Quot.lift (fun gj => mapSubstQ gj f)
    (respect) gj`
  Respect proof uses `subst_cong_right` +
  `mapSubstQ_mk`.  Build.

- [x] **Step 6: Define BTMorNQ.comp**
  `fun j => compQSingle f (g j)`.  Build.

- [x] **Step 7: Define BTMorNQ.id**
  `fun i => Quot.mk _ (BTMor1.proj i)`.  Build.

- [x] **Step 8: Prove id_comp on quotient**
  By `Quot.ind` on each component of `f`,
  reduce to `BTMorN.id_comp` on representatives.
  Build.

- [x] **Step 9: Prove comp_id on quotient**
  By `Quot.ind`, reduce to `BTMorN.comp_id`.
  Build.

- [x] **Step 10: Prove comp_assoc on quotient**
  By `Quot.ind`, reduce to `BTMorN.comp_assoc`.
  Build.

- [x] **Step 11: Define LawvereBTQuotCat**
  `@[reducible] def LawvereBTQuotCat := N`
  Build.

- [x] **Step 12: CategoryStruct and Category**
  `Hom := BTMorNQ`, `id := BTMorNQ.id`,
  `comp := BTMorNQ.comp`.  Build.

---

### Task 12: HasChosenFiniteProducts on quotient

**Files:**

- Modify: `GebLean/LawvereBTQuot.lean`

**Goal:** Terminal object and binary products on
the quotient category.

- [x] **Step 1: Define terminal and its uniqueness**
  `BTMorNQ.terminal`, `BTMorNQ.terminal_uniq`.
  Build.

- [x] **Step 2: Define projections and pairing**
  `BTMorNQ.fst`, `BTMorNQ.snd`, `BTMorNQ.pair`
  as `Quot.mk` of the syntactic versions.  Build.

- [x] **Step 3: Prove pair_fst and pair_snd**
  By `Quot.ind`, reduce to syntactic proofs.
  Build.

- [x] **Step 4: Prove pair_uniq**
  By `Quot.ind`, reduce to syntactic proof.
  Build.

- [x] **Step 5: ChosenTerminal,
  ChosenBinaryProduct, HasChosenFiniteProducts**
  Assemble instances.  Build.

---

### Task 13: HasPBTO on quotient

**Files:**

- Modify: `GebLean/LawvereBTQuot.lean`

**Goal:** The parameterized binary tree object on
`LawvereBTQuotCat`.  `T = 1`, leaf and branch as
quoted constructors, `elim` via the syntactic fold
`btFoldFullMor` lifted to the quotient.

- [x] **Step 1: Define btLeafQ and btBranchQ**
  `Quot.mk` of `btLeaf` and `btBranch`.  Build.

- [x] **Step 2: Define elimQ**
  Lift `btFoldFullMor` to the quotient using
  `Quot.lift` and congruence lemmas.  Build.

- [x] **Step 3a: Prove elim_l helper**
  At the syntactic level: for each `j`,
  `(btFoldFullMor f g j).subst (insertLeaf n)`
  is related to `f j` via `btMorRel`.
  Use `fold_subst_eq` + `BTMor1.subst_leaf` +
  `subst_id` + `btMorRel_foldLeaf`.  Build.

- [x] **Step 3b: Prove elim_l**
  `cfpInsertSnd btLeafQ A >>> elimQ f g = f`
  Assemble from the helper via `Quot.sound`.
  Build.

- [x] **Step 4a: Prove elim_beta helper**
  At the syntactic level: for each `j`,
  `(btFoldFullMor f g j).subst (insertBranch n)`
  is related to the branch computation RHS via
  `btMorRel`.  Use `fold_subst_eq` +
  `BTMor1.subst_branch` + `btMorRel_foldBranch`.
  Build.

- [x] **Step 4b: Prove elim_beta**
  Assemble from helper.  Build.

- [x] **Step 5a: Prove elim_uniq induction base**
  If `phi` satisfies the computation rules, then
  for trees of the form `leaf`, `phi(a, leaf)`
  agrees with `elimQ(a, leaf)`.  Both equal
  `f(a)` by the leaf computation rule.  Build.

- [x] **Step 5b: Prove elim_uniq induction step**
  If `phi` agrees with `elimQ` on `t1` and `t2`,
  then it agrees on `branch(t1, t2)`.  Both
  equal `g(phi(a,t1), phi(a,t2))` by the branch
  computation rule and IH.  Build.

- [x] **Step 5c: Prove elim_uniq**
  Assemble: by induction on the tree variable
  (structural induction on BT via `BT.fold` or
  `PolyFix.ind`), using base + step.  Build.

- [x] **Step 6: HasPBTO instance**
  Assemble `T := 1`, `l := btLeafQ`,
  `beta := btBranchQ`, `elim := elimQ`,
  plus the three proofs.  Build.

---

### Task 14: Tests and integration

**Files:**

- Create: `test/TestLawvereBTQuot.lean`
- Modify: `GebLean.lean`

- [x] **Step 1: Add imports to GebLean.lean**
  `import GebLean.LawvereBTEq`
  `import GebLean.LawvereBTQuot`
  Build.

- [x] **Step 2: Write quotient tests**
  Test that `BTMor1Q` operations are well-typed.
  Test `LawvereBTQuotCat` has `Category`.
  Test `HasPBTO LawvereBTQuotCat` exists.
  Build and test.

- [x] **Step 3: Full build and test**
  `lake build && lake test`.  Verify no warnings.

---

## Helper lemma inventory

### In LawvereBT.lean (additions, Task 5)

- `fold_subst_eq` (make public)
- `subst_child_eval` (make public)
- `fiberCast_child_eval` (make public)
- `BTMor1.subst_leaf`
- `BTMor1.subst_branch`
- `btFoldFullMor`

### In LawvereBTEq.lean

**Endpoint computation** (one per component):

- `eqLhs_refl`, `eqRhs_refl`
- `eqLhs_symm`, `eqRhs_symm`
- `eqLhs_trans`, `eqRhs_trans`
- `eqLhs_congBranch`, `eqRhs_congBranch`
- `eqLhs_congFold`, `eqRhs_congFold`
- `eqLhs_foldLeaf`, `eqRhs_foldLeaf`
- `eqLhs_foldBranch`, `eqRhs_foldBranch`

**Relation introduction:**

- `btMorRel.refl`, `btMorRel.symm`,
  `btMorRel.trans`
- `btMorRel_congBranch`, `btMorRel_congFold`
- `btMorRel_foldLeaf`, `btMorRel_foldBranch`

**subst_cong_right case helpers:**

- `subst_cong_right_refl`
- `subst_cong_right_symm`
- `subst_cong_right_trans`
- `subst_cong_right_congBranch`
- `subst_cong_right_congFold`
- `subst_cong_right_foldLeaf`
- `subst_cong_right_foldBranch`

**subst_cong_left case helpers:**

- `subst_cong_left_proj`
- `subst_cong_left_leaf`
- `subst_cong_left_branch`
- `subst_cong_left_fold`

**Combined:**

- `subst_cong`

### In LawvereBTQuot.lean

- `mapSubstQ`
- `mapSubstQ_mk`
- `compQSingle`
- `BTMorNQ.comp`, `BTMorNQ.id`
- `BTMorNQ.id_comp`, `BTMorNQ.comp_id`,
  `BTMorNQ.comp_assoc`
- `BTMorNQ.pair_fst`, `BTMorNQ.pair_snd`,
  `BTMorNQ.pair_uniq`
- `elimQ`, `elimQ_l_helper`, `elimQ_beta_helper`
- `elimQ_uniq_base`, `elimQ_uniq_step`
