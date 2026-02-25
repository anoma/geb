# PshRel Subobject Refactoring Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans
> to implement this plan task-by-task.

**Goal:** Replace `PshRel P Q` from `Skeleton (PshProdOver P Q)` to
`Subfunctor (pshProdPresheaf P Q)`, enabling functoriality of
`profRelInterp`.

**Architecture:** Redefine `PshRel` as a `Subfunctor` of the product
presheaf, rewrite all 22 Skeleton-dependent definitions/theorems in
`PshRelDouble.lean` to use `Subfunctor.ext` and propositional
reasoning, then propagate changes to `YonedaRelDouble.lean` and
`PshTypeExpr.lean`.  The `PshProdOver` level is retained as internal
proof infrastructure.

**Tech Stack:** Lean 4, mathlib (`Subfunctor` from
`Mathlib.CategoryTheory.Subfunctor.Basic`, `Subfunctor.range` from
`Mathlib.CategoryTheory.Subfunctor.Image`).

---

## Task 1: Add Subfunctor imports and redefine PshRel core

**Files:**

- Modify: `GebLean/PshRelDouble.lean:1-8` (imports)
- Modify: `GebLean/PshRelDouble.lean:204-212` (PshRel, pshRelId)
- Modify: `GebLean/PshRelDouble.lean:339-408` (pshRelComp through
  pshRelGraph_comp)

**Step 1:** Add import for `Subfunctor`:

```lean
import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.CategoryTheory.Subfunctor.Image
```

**Step 2:** Redefine `PshRel` (replacing lines 204-206):

```lean
abbrev PshRel (P Q : Cop => Type w) :=
  Subfunctor (pshProdPresheaf P Q)
```

**Step 3:** Redefine `pshRelId` (replacing lines 210-212):

```lean
def pshRelId (P : Cop => Type w) : PshRel P P where
  obj c := { pp | pp.1 = pp.2 }
  map f _ h := congrArg (P.map f) h
```

**Step 4:** Add `pshProdOverToRel` projection:

```lean
def pshProdOverToRel
    {P Q : Cop => Type w}
    (R : PshProdOver P Q) : PshRel P Q where
  obj c := { pq | exists w : R.left.obj c,
    (R.hom >> pshProdFst P Q).app c w = pq.1 /\
    (R.hom >> pshProdSnd P Q).app c w = pq.2 }
  map f _ := ...
```

**Step 5:** Redefine `pshRelComp` (replacing lines 343-352):

```lean
def pshRelComp {P Q W : Cop => Type w} :
    PshRel P Q -> PshRel Q W -> PshRel P W :=
  fun R S => {
    obj := fun c => { pw | exists q,
      (pw.1, q) in R.obj c /\ (q, pw.2) in S.obj c }
    map := fun f _ <q, hr, hs> =>
      <Q.map f q, R.map f hr, S.map f hs> }
```

**Step 6:** Prove `pshRelComp_id_left`, `pshRelComp_id_right`,
`pshRelComp_assoc` using `Subfunctor.ext` and `Set.ext`:

These replace lines 354-386.  Each proof is propositional:

- `id_left`: `exists q, (p = q) /\ R q w` iff `R p w`
- `id_right`: `exists q, R p q /\ (q = w)` iff `R p w`
- `assoc`: `exists q, (exists q', R p q' /\ S q' q) /\ T q w`
  iff `exists q, R p q /\ (exists q', S q q' /\ T q' w)`

**Step 7:** Redefine `pshRelGraph` (replacing lines 390-393):

```lean
def pshRelGraph {P Q : Cop => Type w}
    (alpha : P -> Q) : PshRel P Q where
  obj c := { pq | alpha.app c pq.1 = pq.2 }
  map f _ h := by
    simp only [Set.mem_setOf_eq,
      pshProdPresheaf] at h |-
    rw [<- h, FunctorToTypes.naturality]
```

**Step 8:** Prove `pshRelGraph_eq_id`, `pshRelGraph_comp`
(replacing lines 395-408) using `Subfunctor.ext` + `Set.ext`.

**Step 9:** Build and fix errors.

**Step 10:** Commit: "Redefine PshRel as Subfunctor of product
presheaf"

---

## Task 2: Rewrite PshRelCategory and PshRelDagger sections

**Files:**

- Modify: `GebLean/PshRelDouble.lean:412-594`

**Step 1:** The `PshRelCat` structure (lines 420-422) and
`Category` instance (lines 424-431) should compile unchanged
once the operations from Task 1 are in place.  Build and verify.

**Step 2:** Redefine `pshRelDagger` (replacing lines 549-555):

```lean
def pshRelDagger {P Q : Cop => Type w} :
    PshRel P Q -> PshRel Q P :=
  fun R => {
    obj := fun c => { qp | (qp.2, qp.1) in R.obj c }
    map := fun f _ h => R.map f h }
```

**Step 3:** Prove `pshRelDagger_dagger`, `pshRelDagger_id`,
`pshRelDagger_comp` using `Subfunctor.ext` + `Set.ext`.

- `dagger_dagger`: swapping twice is identity
- `dagger_id`: the diagonal is its own swap
- `dagger_comp`: `exists q, S(q,w) /\ R(p,q)` iff
  `exists q, R_dag(q,p) /\ S_dag(w,q)` -- swap + reorder

**Step 4:** The `DaggerCategory` instance (lines 587-592) should
compile unchanged.  Build and verify.

**Step 5:** Commit: "Rewrite PshRelDagger for Subfunctor-based
PshRel"

---

## Task 3: Rewrite PshRelatedMorphisms section

**Files:**

- Modify: `GebLean/PshRelDouble.lean:596-754`

**Step 1:** The `PshProdOver`-level definitions (`pshProdMap`,
`PshProdOverRelated`, `pshProdOverRelated_iso`,
`pshProdOverRelated_graph_iff`) remain unchanged.

**Step 2:** Redefine `pshRelRelated` (replacing lines 700-709):

```lean
def pshRelRelated
    {P P' Q Q' : Cop => Type w}
    (alpha : P -> Q) (beta : P' -> Q')
    (R : PshRel P P') (S : PshRel Q Q') : Prop :=
  forall (c : Cop) (p : P.obj c) (p' : P'.obj c),
    (p, p') in R.obj c ->
    (alpha.app c p, beta.app c p') in S.obj c
```

**Step 3:** Build and fix errors.

**Step 4:** Commit: "Redefine pshRelRelated for Subfunctor-based
PshRel"

---

## Task 4: Rewrite PshRelDoubleCategory section

**Files:**

- Modify: `GebLean/PshRelDouble.lean:756-997`

**Step 1:** The `pshRelSQS` type family and `PshProdOver`-level
simp lemmas remain.

**Step 2:** Rewrite `pshRelRelatedHComp` (lines 797-818):
prove directly from the `pshRelRelated` membership condition
(no `Quotient.inductionOn`).

**Step 3:** Rewrite `pshRelRelatedSqHorId` (lines 823-830):
prove directly (identity relation means `p = p'`, so
`alpha.app c p = alpha.app c p'`).

**Step 4:** Rewrite `pshRelRelatedVComp` (lines 853-904):
prove directly by composing the existential witnesses.

**Step 5:** The `DoubleCategoryOps`, `DoubleCategoryLaws`, and
`DoubleCategoryData` instances should compile.  Build and verify.

**Step 6:** Commit: "Rewrite PshRelDoubleCategory for
Subfunctor-based PshRel"

---

## Task 5: Rewrite PshBarrExtension section

**Files:**

- Modify: `GebLean/PshRelDouble.lean:999-1162`

**Step 1:** The `PshProdOver`-level definitions (`pshBarrLift`,
`pshBarrLift_fst`, `pshBarrLift_snd`, `pshBarrLift_iso`,
`pshBarrLift_related`) remain unchanged.

**Step 2:** Redefine `pshBarrLiftSkel` (replacing lines 1069-1079).
The Barr extension of a `Subfunctor R` of `P x Q` through
`G : PSh(C) => PSh(C)` is the image of `pshBarrLift G` applied
to the underlying presheaf `R.toFunctor` with its inclusion `R.i`.
Use `Subfunctor.range` or define directly:

```lean
def pshBarrLiftSkel
    {P Q : Cop => Type w}
    (G : (Cop => Type w) => (Cop => Type w))
    (R : PshRel P Q) :
    PshRel (G.obj P) (G.obj Q) where
  obj c := { gpgq |
    exists w : G.obj R.toFunctor |>.obj c,
      G.map R.i.fst ... = gpgq.1 /\
      G.map R.i.snd ... = gpgq.2 }
  map := ...
```

The exact formulation depends on how `R.toFunctor` relates to
`P` and `Q`.  The internal presheaf of a `Subfunctor` of
`P x Q` has elements `{ pq // pq in R.obj c }` at stage `c`,
with projections `pq.val.1 : P.obj c` and `pq.val.2 : Q.obj c`.
The Barr extension applies `G` to this subtype presheaf and
projects.

**Step 3:** Prove `pshBarrLiftSkel_graph` using `Subfunctor.ext`
and `Set.ext`.

**Step 4:** Rewrite `pshBarrLiftSkel_related` (replacing lines
1148-1160): prove directly from the `pshRelRelated` membership
condition.

**Step 5:** Build and fix errors.

**Step 6:** Commit: "Rewrite PshBarrExtension for Subfunctor-based
PshRel"

---

## Task 6: Rewrite PshInternalHom section (arrow relation)

**Files:**

- Modify: `GebLean/PshRelDouble.lean:1164-1476`

**Step 1:** The `PshProdOver`-level definitions (`pshIhomProfMap`,
`pshArrowRelPred`, `pshArrowRelPresheaf`, `pshArrowRel`,
`pshArrowRel_iso`, `pshArrowRel_related`) remain unchanged.

**Step 2:** Redefine `pshArrowRelSkel` (replacing lines 1385-1396).
For `R : PshRel A1 A2` and `S : PshRel B1 B2`, the arrow
relation is the subfunctor of `(A1.functorHom B1) x
(A2.functorHom B2)` whose elements are pairs `(g1, g2)` such
that for all stages `d`, morphisms `h : c -> d`, and pairs
`(a1, a2)` with `(a1, a2) in R.obj d`, we have
`(g1 h a1, g2 h a2) in S.obj d`.

**Step 3:** Prove `pshArrowRelSkel_related` (replacing lines
1451-1474) directly from the `pshRelRelated` membership condition.

**Step 4:** Build and fix errors.

**Step 5:** Commit: "Rewrite PshInternalHom for Subfunctor-based
PshRel"

---

## Task 7: Rewrite TypeRelations section

**Files:**

- Modify: `GebLean/PshRelDouble.lean:1711-1892`

**Step 1:** Most definitions here are abbreviations that delegate
to the `pshRel*` operations.  They should compile unchanged.
Build and verify.

**Step 2:** Any definitions that break (especially
`typeRelGraph_eq_id`, `typeRelGraph_comp`) should be fixed
using the new `Subfunctor.ext` proof style.

**Step 3:** Build and verify all of `PshRelDouble.lean` compiles
with no warnings.

**Step 4:** Commit: "Complete PshRelDouble.lean refactoring"

---

## Task 8: Propagate to YonedaRelDouble.lean

**Files:**

- Modify: `GebLean/YonedaRelDouble.lean`

**Step 1:** `YonedaRel` (line 305) changes from
`Skeleton (YonedaProdOver X Y)` to
`Subfunctor (yonedaProdPresheaf X Y)`.  This is an `abbrev`,
so it should propagate from the changed `PshRel`.

**Step 2:** Remove `yonedaProdOverComp_iso` (lines 314-320) --
this was only needed for `Skeleton.lift2` well-definedness.

**Step 3:** Fix `yonedaRelGraph_eq_relId` (lines 403-407) --
rewrite the `simp` proof targeting `Subfunctor`-based definitions.

**Step 4:** Fix any `change` + `simp` patterns in
`relRelatedHComp`, `relRelatedSqHorId` (lines 622-652) that
expose `pshRelRelated` internals.

**Step 5:** Fix `yonedaRelDoubleLaws` square-law cases
(lines 714-762) if `simp` targets change.

**Step 6:** Build and verify.

**Step 7:** Commit: "Propagate Subfunctor-based PshRel to
YonedaRelDouble"

---

## Task 9: Propagate to PshTypeExpr.lean

**Files:**

- Modify: `GebLean/PshTypeExpr.lean`

**Step 1:** Definitions using `PshRel` in their type
(`relInterp`, `fullRelInterp`, etc.) should compile unchanged
since `PshRel` is still a type alias.  Build and check.

**Step 2:** Fix `pshRelSectionsRelated` (lines 294-302) -- it
currently uses `.lift` on the `Skeleton` quotient.  Redefine
using the `Subfunctor` membership:

```lean
def pshRelSectionsRelated
    (R : PshRel F G) (s0 : F.sections) (s1 : G.sections)
    : Prop :=
  forall (c : Cop), (s0.val c, s1.val c) in R.obj c
```

**Step 3:** Fix `yonedaULiftRel` (lines 486-489) -- currently
uses `toSkeleton`.  Redefine as a `Subfunctor` directly:

```lean
def yonedaULiftRel (R : A -> B -> Prop) :
    PshRel (yonedaULift A) (yonedaULift B) :=
  pshProdOverToRel (yonedaULiftRelOver R)
```

**Step 4:** Fix `pshRelSectionsRelated_toSkeleton` (lines
547-555) -- restate in terms of `pshProdOverToRel`.

**Step 5:** Fix `fullRelInterp_pshRep_eq` (lines 759-785) --
this proof deeply depends on `Skeleton.lift` / `Skeleton.lift2`
internals.  Restate as:
`T.toPshTypeExpr.fullRelInterp (yonedaULiftRel R) =
  pshProdOverToRel (T.fullRelInterpPshRep R)`
and prove by induction, unfolding `pshBarrLiftSkel` and
`pshArrowRelSkel` through their new `Subfunctor` definitions.

**Step 6:** Fix `yonedaULiftRel_graphRel` (lines 1661-1690) --
currently uses `toSkeleton_eq_iff`.  Rewrite using
`Subfunctor.ext` + `Set.ext`.

**Step 7:** Verify `ParametricFamily.toPshParametricAtRep`
compiles (it chains together several PshRel lemmas).

**Step 8:** Build and verify all of `PshTypeExpr.lean` compiles.

**Step 9:** Commit: "Propagate Subfunctor-based PshRel to
PshTypeExpr"

---

## Task 10: Verify ParanaturalTopos.lean and full build

**Files:**

- Modify: `GebLean/ParanaturalTopos.lean` (if needed)

**Step 1:** `ParanaturalTopos.lean` has light `PshRel` usage.
Build and check for errors.

**Step 2:** Fix any breakage (likely in the
`propRelToYonedaProdOver` / `arrowRel_iff_yonedaProdOverRelated`
bridge theorems).

**Step 3:** Run `lake build` and `lake test`.  Fix all errors
and warnings.

**Step 4:** Commit: "Complete PshRel subobject refactoring"

---

## Task 11: Remove dead Skeleton code from PshRelDouble.lean

**Files:**

- Modify: `GebLean/PshRelDouble.lean`

**Step 1:** Remove definitions that are no longer needed:

- `pshProdOverComp_iso` (was needed for `Skeleton.lift2`)
- `pshProdOverDagger_iso` (was needed for `Skeleton.lift`)
- `pshProdOverDagger_comp` (was needed for `pshRelDagger_comp`
  via `Skeleton`)
- `pshProdOverDagger_id` (was needed for `pshRelDagger_id`
  via `Skeleton`)

Check whether any of the `PshProdOver`-level isomorphisms are
still referenced.  Keep `pshProdOverComp_id_left`,
`pshProdOverComp_id_right`, `pshProdOverComp_assoc`,
`pshProdOverGraph_comp` if they are used by downstream proofs
(e.g., in the Barr extension or bridge theorems).

**Step 2:** Remove `import GebLean.Utilities.Skeleton` if no
longer needed by this file (check whether `Skeleton` is still
used anywhere in the file).

**Step 3:** Build and verify.

**Step 4:** Commit: "Remove dead Skeleton code from
PshRelDouble"

---

## Task 12: Update session workstream documentation

**Files:**

- Modify: `.session/workstreams/yoneda-rel-parametricity.md`
- Modify: `.session/workstreams/parametric-generalization.md`
- Modify: `.session/workstreams/yoneda-rel-category.md`

**Step 1:** Update workstream files to reflect the completed
refactoring: `PshRel` is now `Subfunctor`-based, the
`profRelInterp` functoriality obstacle is resolved, and the
path to `TypeExpr.profRelInterp` as a functor on
`TypePropRelCat` (now just `TypeRelCat`) is open.

**Step 2:** Note in `parametric-generalization.md` that the
next step is defining `TypeExpr.profRelInterp` as the
morphism-map of an endoprofunctor on `TypeRelCat`.
