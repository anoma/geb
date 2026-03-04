import GebLean.PolyAlg

/-!
# Distributive Law for Polynomial Endofunctors

This module constructs the canonical distributive law
`lambda : T . D --> D . T` where `T = polyFreeMonad X P` and
`D = polyCofreeComonad X P`, for a polynomial endofunctor `P`
on `Over X`.

The construction proceeds via the universal property of the
cofree comonad (the anamorphism / terminal coalgebra map):

1. Given a P-coalgebra `(C, k)`, define a P-coalgebra on `T(C)`.
2. Define a `polyScale(T(A), P)`-coalgebra on `T(D(A))`.
3. Apply the anamorphism `polyCofixUnfold` to obtain
   `lambda_A : T(D(A)) --> D(T(A))`.
4. Verify the distributive law axioms.
-/

namespace GebLean

open CategoryTheory

universe u

variable {X : Type u}

/-! ## Step 1: P-coalgebra on the Free Monad

Given a P-coalgebra `(C, k : C → P(C))`, we construct a
P-coalgebra on `T(C) = polyFreeMCarrier C P`.

- At a leaf `c : C`: apply `k(c)` to get a P-operation and
  wrap each child in a leaf via `polyFreeMPure`.
- At an internal node `(p, children)`: return `(p, children)`
  as the P-structure directly.
-/

/--
The P-coalgebra structure on `T(C)` at a fiber element,
given a P-coalgebra `k` on `C`.
-/
def polyFreeMCoalgStrAt
    (C : Over X) (P : PolyEndo X)
    (k : C ⟶ (polyEndoFunctor X P).obj C)
    {x : X}
    (t : PolyFreeM C P x) :
    polyBetweenEvalFamily X X P
      (polyFreeMCarrier C P) x :=
  match t with
  | PolyFix.mk _ (Sum.inl c) _ =>
    let kc := k.left c.val
    have hfib : kc.1 = x := by
      have h := congrFun (Over.w k) c.val
      simp only at h
      rw [c.property] at h
      exact h
    let elem : polyBetweenEvalFamily X X P C kc.1 :=
      kc.2
    let childMor := elem.2
    hfib ▸ ⟨elem.1, Over.homMk
      (fun e =>
        ⟨(polyBetweenFamily X X P kc.1 elem.1).hom e,
         polyFreeMPure C P
           ⟨childMor.left e,
            congrFun (Over.w childMor) e⟩⟩)
      rfl⟩
  | PolyFix.mk _ (Sum.inr p) children =>
    ⟨p, Over.homMk
      (fun e =>
        ⟨(polyBetweenFamily X X P x p).hom e,
         children e⟩)
      rfl⟩

/--
The underlying function of the P-coalgebra structure map
on `polyFreeMCarrier C P`.
-/
def polyFreeMCoalgStrLeft
    (C : Over X) (P : PolyEndo X)
    (k : C ⟶ (polyEndoFunctor X P).obj C) :
    (polyFreeMCarrier C P).left →
    ((polyEndoFunctor X P).obj
      (polyFreeMCarrier C P)).left :=
  fun ⟨x, t⟩ => ⟨x, polyFreeMCoalgStrAt C P k t⟩

/--
The P-coalgebra structure map on `polyFreeMCarrier C P`
commutes with projections to X.
-/
lemma polyFreeMCoalgStr_comm
    (C : Over X) (P : PolyEndo X)
    (k : C ⟶ (polyEndoFunctor X P).obj C) :
    polyFreeMCoalgStrLeft C P k ≫
    ((polyEndoFunctor X P).obj
      (polyFreeMCarrier C P)).hom =
    (polyFreeMCarrier C P).hom := rfl

/--
The P-coalgebra structure map on `T(C)`, given a
P-coalgebra `k` on `C`.
-/
def polyFreeMCoalgStr
    (C : Over X) (P : PolyEndo X)
    (k : C ⟶ (polyEndoFunctor X P).obj C) :
    polyFreeMCarrier C P ⟶
    (polyEndoFunctor X P).obj
      (polyFreeMCarrier C P) :=
  Over.homMk
    (polyFreeMCoalgStrLeft C P k)
    (polyFreeMCoalgStr_comm C P k)

/--
The P-coalgebra on `T(C)` induced by a P-coalgebra on `C`.
-/
def polyFreeMCoalg
    (C : Over X) (P : PolyEndo X)
    (k : C ⟶ (polyEndoFunctor X P).obj C) :
    PolyCoalg P where
  V := polyFreeMCarrier C P
  str := polyFreeMCoalgStr C P k

/-! ## Step 2: polyScale Coalgebra on T(D(A))

Given `A : Over X` and `P : PolyEndo X`, define a
`polyScale(T(A), P)`-coalgebra on `T(D(A))` by combining:

- The T(A)-projection: apply `polyFreeMapAt` with
  `polyCofreeCounit A P` to map each leaf's cofree
  element to its root annotation.
- The P-coalgebra: from `polyFreeMCoalgStrAt` using
  the cofree comonad's structure map `polyCofreeStr A P`.
-/

/--
The `polyScale(T(A), P)`-coalgebra structure on `T(D(A))`
at a fiber element.  The result pairs a T(A)-element
(obtained by applying the counit at each leaf) with the
P-coalgebra structure inherited from D(A).
-/
def polyDistLawScaleCoalgStrAt
    (A : Over X) (P : PolyEndo X) {x : X}
    (t : PolyFreeM (polyCofreeCarrier A P) P x) :
    polyBetweenEvalFamily X X
      (polyScale (polyFreeMCarrier A P) P)
      (polyFreeMCarrier
        (polyCofreeCarrier A P) P) x :=
  let pCoalg :=
    polyFreeMCoalgStrAt
      (polyCofreeCarrier A P) P
      (polyCofreeStr A P) t
  let ta : PolyFreeM A P x :=
    polyFreeMapAt
      (polyCofreeCarrier A P) A P
      (polyCofreeCounit A P) x t
  ⟨(⟨⟨x, ta⟩, rfl⟩, pCoalg.1), pCoalg.2⟩

/--
The underlying function of the
`polyScale(T(A), P)`-coalgebra structure map on
`T(D(A))`.
-/
def polyDistLawScaleCoalgStrLeft
    (A : Over X) (P : PolyEndo X) :
    (polyFreeMCarrier
      (polyCofreeCarrier A P) P).left →
    ((polyEndoFunctor X
      (polyScale (polyFreeMCarrier A P) P)).obj
      (polyFreeMCarrier
        (polyCofreeCarrier A P) P)).left :=
  fun ⟨x, t⟩ =>
    ⟨x, polyDistLawScaleCoalgStrAt A P t⟩

/--
The `polyScale(T(A), P)`-coalgebra structure map on
`T(D(A))` commutes with projections to X.
-/
lemma polyDistLawScaleCoalgStr_comm
    (A : Over X) (P : PolyEndo X) :
    polyDistLawScaleCoalgStrLeft A P ≫
    ((polyEndoFunctor X
      (polyScale (polyFreeMCarrier A P) P)).obj
      (polyFreeMCarrier
        (polyCofreeCarrier A P) P)).hom =
    (polyFreeMCarrier
      (polyCofreeCarrier A P) P).hom := rfl

/--
The `polyScale(T(A), P)`-coalgebra structure map on
`T(D(A))`.
-/
def polyDistLawScaleCoalgStr
    (A : Over X) (P : PolyEndo X) :
    polyFreeMCarrier (polyCofreeCarrier A P) P ⟶
    (polyEndoFunctor X
      (polyScale (polyFreeMCarrier A P) P)).obj
      (polyFreeMCarrier
        (polyCofreeCarrier A P) P) :=
  Over.homMk
    (polyDistLawScaleCoalgStrLeft A P)
    (polyDistLawScaleCoalgStr_comm A P)

/--
The `polyScale(T(A), P)`-coalgebra on `T(D(A))`.
-/
def polyDistLawScaleCoalg
    (A : Over X) (P : PolyEndo X) :
    PolyCoalg
      (polyScale (polyFreeMCarrier A P) P) where
  V := polyFreeMCarrier
    (polyCofreeCarrier A P) P
  str := polyDistLawScaleCoalgStr A P

/-! ## Step 3: Distributive Law Morphism via Anamorphism

The distributive law morphism
`lambda_A : T(D(A)) --> D(T(A))` is the anamorphism from
the `polyScale(T(A), P)`-coalgebra on `T(D(A))` to the
terminal `polyScale(T(A), P)`-coalgebra, which is
`polyCofreeCarrier (polyFreeMCarrier A P) P = D(T(A))`.
-/

/--
The distributive law morphism `T(D(A)) --> D(T(A))`
at a specific object `A : Over X`.  This is the
anamorphism from the polyScale coalgebra on T(D(A))
to the terminal polyScale coalgebra (the cofree
comonad carrier D(T(A))).
-/
def polyDistLawMor
    (A : Over X) (P : PolyEndo X) :
    polyFreeMCarrier (polyCofreeCarrier A P) P ⟶
    polyCofreeCarrier (polyFreeMCarrier A P) P :=
  polyCofixUnfold
    (polyScale (polyFreeMCarrier A P) P)
    (polyDistLawScaleCoalg A P)

/-! ## Step 5: Counit Coherence

Counit coherence states:
`lambda_A ≫ epsilon_{T(A)} = T(epsilon_A)`

At the concrete level, the counit of the cofree comonad
extracts the root annotation.  The root annotation of
the anamorphism result is the T(A)-component of the
polyScale coalgebra structure, which equals `T(epsilon_A)`.
-/

/--
The head of the anamorphism `polyDistLawMor` at an
element `t` has first component (the T(A)-annotation)
equal to `polyFreeMapAt ... (polyCofreeCounit A P) x t`.
-/
lemma polyDistLawMor_head_fst
    (A : Over X) (P : PolyEndo X) {x : X}
    (t : PolyFreeM (polyCofreeCarrier A P) P x) :
    let m := polyCofixUnfoldAt
      (polyScale (polyFreeMCarrier A P) P)
      (polyDistLawScaleCoalg A P)
      x ⟨⟨x, t⟩, rfl⟩
    (polyCofreeExtract
      (polyFreeMCarrier A P) P m).val =
    ⟨x, polyFreeMapAt
      (polyCofreeCarrier A P) A P
      (polyCofreeCounit A P) x t⟩ := by
  simp only [polyCofreeExtract, PolyCofix.head,
    polyCofixUnfoldAt, polyCofixUnfoldApprox]
  simp only [polyDistLawScaleCoalg,
    polyDistLawScaleCoalgStr, Over.homMk_left,
    polyDistLawScaleCoalgStrLeft]
  simp only [PolyCofixApprox.getIndex,
    polyDistLawScaleCoalgStrAt]

/--
Counit coherence:
`lambda_A ≫ epsilon_{T(A)} = T(epsilon_A)`.
-/
lemma polyDistLaw_counit
    (A : Over X) (P : PolyEndo X) :
    polyDistLawMor A P ≫
    polyCofreeCounit (polyFreeMCarrier A P) P =
    polyFreeMap
      (polyCofreeCarrier A P) A P
      (polyCofreeCounit A P) := by
  apply Over.OverMorphism.ext
  funext ⟨x, t⟩
  simp only [Over.comp_left, types_comp_apply,
    polyDistLawMor, polyCofixUnfold,
    Over.homMk_left, polyCofixUnfoldLeft,
    polyCofreeCounit, polyCofreeCounitLeft,
    polyFreeMap, polyFreeMapLeft]
  exact polyDistLawMor_head_fst A P t

/--
`polyFreeMPure` is proof-irrelevant: the result depends
only on the underlying value, not on the fiber proof.
When the fiber proofs target different fibers `x` and `y`
with `A.hom a = x` and `A.hom a = y`, the results are
related by `HEq`.
-/
lemma polyFreeMPure_proof_irrel
    (A : Over X) (P : PolyEndo X)
    (a : A.left) {x y : X}
    (h1 : A.hom a = x)
    (h2 : A.hom a = y) :
    HEq (polyFreeMPure A P ⟨a, h1⟩)
        (polyFreeMPure A P ⟨a, h2⟩) := by
  cases h1
  cases h2
  rfl

/-! ## Step 6: Unit Coherence

Unit coherence states:
`T.eta.app (D.obj A) ≫ dist.app A = D.map (T.eta.app A)`

LHS: embed a cofree element as a leaf in `T(D(A))`,
then apply the distributive law.
RHS: map each annotation in the cofree element by
the free monad unit (wrapping in a leaf).

Both produce the same cofree element with leaf-wrapped
annotations at every depth.
-/

/--
Approximation-level lemma for unit coherence: the
anamorphism applied to a leaf wrapping a cofree element
`m` agrees at every depth with the cofree map that wraps
each annotation in a leaf.
-/
lemma polyDistLaw_unit_approx
    (A : Over X) (P : PolyEndo X) {x : X}
    (m : PolyCofreeM A P x) (n : Nat) :
    polyCofixUnfoldApprox
      (polyScale (polyFreeMCarrier A P) P)
      (polyDistLawScaleCoalg A P) n x
      ⟨⟨x, polyFreeMPure
        (polyCofreeCarrier A P) P
        ⟨⟨x, m⟩, rfl⟩⟩, rfl⟩ =
    polyCofreeMapApprox A
      (polyFreeMCarrier A P) P
      (polyFreeUnit A P) (m.approx n) := by
  induction n generalizing x m with
  | zero =>
    simp only [polyCofixUnfoldApprox]
    cases m.approx 0
    rfl
  | succ n ih =>
    have hidx_eq :
      (m.approx (n + 1)).getIndex = m.head :=
      m.index_eq_head n
    generalize ha :
      m.approx (n + 1) = a at hidx_eq
    match a, hidx_eq with
    | .intro _ idx childFun, hidx_eq =>
      subst hidx_eq
      -- Simplify both sides
      simp only [polyCofixUnfoldApprox,
        polyDistLawScaleCoalg,
        polyDistLawScaleCoalgStr,
        Over.homMk_left,
        polyDistLawScaleCoalgStrLeft,
        polyDistLawScaleCoalgStrAt,
        polyFreeMCoalgStrAt,
        polyCofreeStr, polyCofreeStrLeft,
        polyCofreeStrFamily,
        polyFreeMapAt, polyFreeMBind,
        polyFreeMPure,
        polyCofreeCounit,
        polyCofreeCounitLeft]
      congr 1
      · -- Scale index equality
        congr 1
        apply Subtype.ext
        simp only [polyFreeUnit,
          Over.homMk_left, polyFreeUnitLeft]
        apply Sigma.ext
        · exact m.head.1.property.symm
        · apply polyFreeMPure_proof_irrel
      · -- Children equality
        funext e
        simp only [polyCofreeChildrenMor,
          Over.homMk_left]
        have hchild :
          (m.children e).approx n =
            childFun e := by
          simp only [PolyCofix.children,
            PolyCofix.childApproxAt]
          cases n with
          | zero =>
            simp only [
              PolyCofix.childApproxAt_zero]
            exact
              (PolyCofixApprox.approx_zero_eq_continue
                (childFun e)).symm
          | succ k =>
            simp only [
              PolyCofix.childApproxAt_succ]
            have heq1 :
              (m.approx (k + 2)).getIndex =
                m.head :=
              m.index_eq_head (k + 1)
            conv_lhs =>
              rw [PolyCofix.childApproxAt_succ_aux_proof_irrel
                m.head (m.approx (k + 2))
                (m.index_eq_head (k + 1))
                heq1 e]
            generalize haa :
              m.approx (k + 2) = aa at heq1
            rw [ha] at haa
            subst haa
            conv_lhs =>
              rw [PolyCofix.childApproxAt_succ_aux_proof_irrel
                m.head
                (.intro x m.head childFun)
                heq1 rfl e]
            exact
              PolyCofix.childApproxAt_succ_aux_intro
                m.head childFun e
        rw [← hchild]
        exact ih (m.children e)

/--
Unit coherence:
`T.eta.app (D.obj A) ≫ dist.app A =
  D.map (T.eta.app A)`.
-/
lemma polyDistLaw_unit
    (A : Over X) (P : PolyEndo X) :
    polyFreeUnit (polyCofreeCarrier A P) P ≫
    polyDistLawMor A P =
    polyCofreeMap A
      (polyFreeMCarrier A P) P
      (polyFreeUnit A P) := by
  apply Over.OverMorphism.ext
  funext ⟨x, m⟩
  simp only [Over.comp_left, types_comp_apply,
    polyFreeUnit, Over.homMk_left,
    polyFreeUnitLeft,
    polyDistLawMor, polyCofixUnfold,
    polyCofixUnfoldLeft,
    polyCofreeMap, polyCofreeMapLeft]
  apply Sigma.ext
  · rfl
  · simp only [heq_eq_eq, polyCofreeMapAt]
    apply PolyCofix.ext
    intro n
    exact polyDistLaw_unit_approx A P m n

/-! ## Step 4: Naturality of the Distributive Law

Naturality states: for all `f : A ⟶ B`,
```
T(D(f)) ≫ lambda_B = lambda_A ≫ D(T(f))
```
where `T(D(f)) = polyFreeMap ... (polyCofreeMap A B P f)` and
`D(T(f)) = polyCofreeMap ... (polyFreeMap A B P f)`.

The proof proceeds by `PolyCofix.ext` + induction on the
approximation depth.
-/

/--
Annotation naturality: the T-annotation component of the
distributive law scale coalgebra commutes with `f`.

Concretely, applying `T(D(f))` to a tree and then extracting
the T(B)-annotation equals extracting the T(A)-annotation
and then applying `T(f)`.
-/
lemma polyDistLaw_annot_natural
    (A B : Over X) (P : PolyEndo X) (f : A ⟶ B)
    {x : X}
    (t : PolyFreeM (polyCofreeCarrier A P) P x) :
    polyFreeMapAt
      (polyCofreeCarrier B P) B P
      (polyCofreeCounit B P) x
      (polyFreeMapAt
        (polyCofreeCarrier A P)
        (polyCofreeCarrier B P) P
        (polyCofreeMap A B P f) x t) =
    polyFreeMapAt A B P f x
      (polyFreeMapAt
        (polyCofreeCarrier A P) A P
        (polyCofreeCounit A P) x t) := by
  rw [← polyFreeMapAt_comp]
  rw [← polyFreeMapAt_comp]
  congr 1
  exact polyCofreeCounit_naturality A B P f

/--
`polyCofixUnfoldApprox` results are HEq when the base
points are equal and the inputs are HEq.
-/
lemma polyCofixUnfoldApprox_input_heq
    (Q : PolyEndo X) (α : PolyCoalg Q) {n : Nat}
    {x1 x2 : X} (hx : x1 = x2)
    {v1 : { a // α.V.hom a = x1 }}
    {v2 : { a // α.V.hom a = x2 }}
    (hv : HEq v1 v2) :
    HEq (polyCofixUnfoldApprox Q α n x1 v1)
        (polyCofixUnfoldApprox Q α n x2 v2) := by
  subst hx
  exact heq_of_eq (congrArg _ (eq_of_heq hv))

/--
For `polyScale` approximations, two `.intro` values are equal
when their P-indices match, annotations match, and children
match (with the same domain since the P-indices agree).
-/
lemma polyCofixApprox_intro_polyScale_congr
    (T : Over X) (P : PolyEndo X) {n : Nat} {x : X}
    {a1 : { v : T.left // T.hom v = x }}
    {a2 : { v : T.left // T.hom v = x }}
    {p1 p2 : polyBetweenIndex X X P x}
    (hp : p1 = p2)
    (ha : a1 = a2)
    {ch1 :
      ∀ (e : (polyBetweenFamily X X P x p1).left),
      PolyCofixApprox (polyScale T P) n
        ((polyBetweenFamily X X P x p1).hom e)}
    {ch2 :
      ∀ (e : (polyBetweenFamily X X P x p2).left),
      PolyCofixApprox (polyScale T P) n
        ((polyBetweenFamily X X P x p2).hom e)}
    (hch : HEq ch1 ch2) :
    @PolyCofixApprox.intro X (polyScale T P) n x
      ⟨a1, p1⟩ ch1 =
    @PolyCofixApprox.intro X (polyScale T P) n x
      ⟨a2, p2⟩ ch2 := by
  subst hp
  subst ha
  exact congrArg _ (eq_of_heq hch)

/--
Leaf case of approximation-level naturality.

When the tree is a leaf `Sum.inl c` (embedding a cofree
comonad element), the anamorphism on the mapped leaf equals
the cofree map of the anamorphism on the original leaf.
-/
lemma polyDistLaw_naturality_approx_leaf
    (A B : Over X) (P : PolyEndo X) (f : A ⟶ B)
    {x : X}
    (c : { a // (polyCofreeCarrier A P).hom a = x })
    (n : Nat)
    (ih : ∀ {x : X}
      (t : PolyFreeM (polyCofreeCarrier A P) P x),
      polyCofixUnfoldApprox
        (polyScale (polyFreeMCarrier B P) P)
        (polyDistLawScaleCoalg B P) n x
        ⟨⟨x, polyFreeMapAt
          (polyCofreeCarrier A P)
          (polyCofreeCarrier B P) P
          (polyCofreeMap A B P f) x t⟩, rfl⟩ =
      polyCofreeMapApprox
        (polyFreeMCarrier A P)
        (polyFreeMCarrier B P) P
        (polyFreeMap A B P f)
        (polyCofixUnfoldApprox
          (polyScale (polyFreeMCarrier A P) P)
          (polyDistLawScaleCoalg A P) n x
          ⟨⟨x, t⟩, rfl⟩)) :
    polyCofixUnfoldApprox
      (polyScale (polyFreeMCarrier B P) P)
      (polyDistLawScaleCoalg B P) (n + 1) x
      ⟨⟨x, polyFreeMapAt
        (polyCofreeCarrier A P)
        (polyCofreeCarrier B P) P
        (polyCofreeMap A B P f) x
        (PolyFix.mk x (Sum.inl c) nofun)⟩, rfl⟩ =
    polyCofreeMapApprox
      (polyFreeMCarrier A P)
      (polyFreeMCarrier B P) P
      (polyFreeMap A B P f)
      (polyCofixUnfoldApprox
        (polyScale (polyFreeMCarrier A P) P)
        (polyDistLawScaleCoalg A P) (n + 1) x
        ⟨⟨x,
          PolyFix.mk x (Sum.inl c) nofun⟩, rfl⟩) := by
  obtain ⟨⟨xm, m⟩, rfl⟩ := c
  simp only [polyCofixUnfoldApprox,
    polyDistLawScaleCoalg,
    polyDistLawScaleCoalgStr,
    Over.homMk_left,
    polyDistLawScaleCoalgStrLeft,
    polyDistLawScaleCoalgStrAt,
    polyFreeMapAt, polyFreeMBind,
    polyFreeMCoalgStrAt,
    polyFreeMPure,
    polyCofreeMapApprox]
  refine polyCofixApprox_intro_polyScale_congr
    (polyFreeMCarrier B P) P
    (polyCofreeMapAt_head_snd A B P f m) ?_ ?_
  · -- Annotation equality: leaf of counit_B(cofreeMap_f m)
    -- = freeMap_f (leaf of counit_A m)
    simp only [polyFreeMap, Over.homMk_left,
      polyFreeMapLeft, polyFreeMapAt,
      polyFreeMBind, polyFreeMPure]
    congr 1
    congr 1
    congr 1
    congr 1
    ext
    exact congrFun
      (congrArg CommaMorphism.left
        (polyCofreeCounit_naturality A B P f))
      ⟨xm, m⟩
  · -- Children HEq
    apply Function.hfunext
    · exact congrArg
        (fun p =>
          (polyBetweenFamily X X P
            ((polyCofreeCarrier A P).hom ⟨xm, m⟩)
            p).left)
        (polyCofreeMapAt_head_snd A B P f m)
    · intro a a' ha
      have hfib := overType_hom_heq
        (congrArg (polyBetweenFamily X X P
          ((polyCofreeCarrier A P).hom ⟨xm, m⟩))
          (polyCofreeMapAt_head_snd A B P f m))
        a a' ha
      have ih_eq := ih
        (PolyFix.mk _
          (Sum.inl
            ⟨((polyCofreeStr A P).left
                ⟨xm, m⟩).snd.snd.left a',
              rfl⟩)
          nofun)
      refine HEq.trans ?_ (HEq.trans
        (heq_of_eq ih_eq) ?_)
      · apply polyCofixUnfoldApprox_input_heq
          _ _ hfib
        dsimp only [polyFreeMapAt, polyFreeMBind,
          polyFreeMPure]
        refine subtype_heq_of_val_eq ?_ ?_
        · ext y
          dsimp only [polyDistLawScaleCoalg,
            polyDistLawScaleCoalgStr,
            polyFreeMCarrier, polyFixCarrier,
            polyCofreeCarrier, polyCofixCarrier,
            familySliceForward,
            familySliceForwardObj,
            polyScale, polyScaleAt,
            polyScaleFamily,
            ccrObjMk,
            polyBetweenFamily, polyToOverFamily,
            ccrFamily,
            polyCofreeStr, polyCofreeStrLeft,
            polyCofreeStrFamily,
            polyCofreeChildrenMor]
          simp only [Over.mk_hom, Over.homMk_left]
          exact Iff.of_eq (congrArg _ hfib)
        · refine Sigma.ext ?_ ?_
          · dsimp only [polyCofreeStr,
              polyCofreeStrLeft,
              polyCofreeStrFamily,
              polyCofreeMap, polyCofreeMapLeft,
              polyCofreeChildrenMor,
              polyCofreeCarrier, polyCofixCarrier,
              familySliceForward,
              familySliceForwardObj]
            simp only [Over.homMk_left,
              Over.mk_hom]
            exact hfib
          · dsimp only [polyCofreeStr,
              polyCofreeMap,
              polyCofreeCarrier, polyCofixCarrier,
              familySliceForward,
              familySliceForwardObj]
            simp only [Over.homMk_left,
              Over.mk_hom]
            dsimp only [polyCofreeStrLeft,
              polyCofreeMapLeft,
              polyCofreeStrFamily,
              polyCofreeChildrenMor]
            simp only [Over.homMk_left]
            congr 1
            congr 1
            · exact congrArg Subtype
                (funext fun v =>
                  congrArg (Eq v.fst) hfib)
            · exact congrArg
                (polyBetweenIndex X X P) hfib
            · exact subtype_heq_of_val_eq
                (funext fun v =>
                  congrArg (Eq v.fst) hfib)
                (Sigma.ext hfib
                  (polyCofreeMapAt_children_heq
                    A B P f m a' a
                    ha.symm).symm)
      · exact heq_of_eq (by
          congr 1; congr 1
          refine Subtype.ext (Sigma.ext rfl ?_)
          refine heq_of_eq ?_
          dsimp only [polyCofreeCarrier,
            polyCofixCarrier,
            familySliceForward,
            familySliceForwardObj,
            polyCofreeStr, polyCofreeStrLeft,
            polyCofreeStrFamily,
            polyCofreeChildrenMor,
            polyBetweenFamily, polyToOverFamily,
            ccrFamily]
          simp only [Over.mk_hom,
            Over.homMk_left]
          congr 1
          funext e; exact PEmpty.elim e)

/--
Approximation-level naturality: the anamorphism applied to
a mapped tree agrees at every depth with the mapped anamorphism
of the original tree.
-/
lemma polyDistLaw_naturality_approx
    (A B : Over X) (P : PolyEndo X) (f : A ⟶ B)
    {x : X}
    (t : PolyFreeM (polyCofreeCarrier A P) P x)
    (n : Nat) :
    polyCofixUnfoldApprox
      (polyScale (polyFreeMCarrier B P) P)
      (polyDistLawScaleCoalg B P) n x
      ⟨⟨x, polyFreeMapAt
        (polyCofreeCarrier A P)
        (polyCofreeCarrier B P) P
        (polyCofreeMap A B P f) x t⟩, rfl⟩ =
    polyCofreeMapApprox
      (polyFreeMCarrier A P)
      (polyFreeMCarrier B P) P
      (polyFreeMap A B P f)
      (polyCofixUnfoldApprox
        (polyScale (polyFreeMCarrier A P) P)
        (polyDistLawScaleCoalg A P) n x
        ⟨⟨x, t⟩, rfl⟩) := by
  induction n generalizing x t with
  | zero =>
    simp only [polyCofixUnfoldApprox,
      polyCofreeMapApprox]
  | succ n ih =>
    match t with
    | PolyFix.mk _ (Sum.inr p) children =>
      simp only [polyCofixUnfoldApprox,
        polyDistLawScaleCoalg,
        polyDistLawScaleCoalgStr,
        Over.homMk_left,
        polyDistLawScaleCoalgStrLeft,
        polyDistLawScaleCoalgStrAt,
        polyFreeMapAt, polyFreeMBind,
        polyFreeMCoalgStrAt,
        polyCofreeMapApprox]
      congr 1
      · congr 1
        apply Subtype.ext
        simp only [polyFreeMap, Over.homMk_left,
          polyFreeMapLeft]
        exact congrArg (Sigma.mk x)
          (polyDistLaw_annot_natural A B P f
            (PolyFix.mk x (Sum.inr p) children))
      · funext e
        exact ih (children e)
    | PolyFix.mk _ (Sum.inl c) _ =>
      exact polyDistLaw_naturality_approx_leaf
        A B P f c n ih

/-! ## Annotation Reindexing for Anamorphisms

Given a `polyScale(A, P)`-coalgebra `alpha` on V and a
morphism `f : A ⟶ B`, the composition of the anamorphism
from `alpha` with `polyCofreeMap f` equals the anamorphism
from a reindexed `polyScale(B, P)`-coalgebra where the
annotation component is composed with `f`.
-/

/--
Reindex the annotation in a `polyScale(A, P)` evaluation
from A to B via `f : A ⟶ B`.  The underlying function maps
`(x, ((a, ha), p), ch)` to `(x, ((f.left a, hb), p), ch)`
where `hb` uses `f`'s fiber-preservation.
-/
def polyScaleReindexLeft
    (A B : Over X) (P : PolyEndo X) (f : A ⟶ B)
    (V : Over X) :
    ((polyEndoFunctor X (polyScale A P)).obj V).left →
    ((polyEndoFunctor X (polyScale B P)).obj V).left :=
  fun ⟨x, (⟨a, ha⟩, p), ch⟩ =>
    ⟨x,
     (⟨f.left a, by
        rw [← ha]; exact congrFun (Over.w f) a⟩,
      p),
     ch⟩

/--
The reindexing preserves the fiber projection.
-/
lemma polyScaleReindex_comm
    (A B : Over X) (P : PolyEndo X) (f : A ⟶ B)
    (V : Over X) :
    polyScaleReindexLeft A B P f V ≫
    ((polyEndoFunctor X (polyScale B P)).obj V).hom =
    ((polyEndoFunctor X (polyScale A P)).obj V).hom :=
  rfl

/--
Reindex a `polyScale(A, P)`-coalgebra to a
`polyScale(B, P)`-coalgebra by composing the annotation
component with `f : A ⟶ B`.
-/
def polyScaleReindexCoalg
    (A B : Over X) (P : PolyEndo X) (f : A ⟶ B)
    (α : PolyCoalg (polyScale A P)) :
    PolyCoalg (polyScale B P) where
  V := α.V
  str := α.str ≫ Over.homMk
    (polyScaleReindexLeft A B P f α.V)
    (polyScaleReindex_comm A B P f α.V)

/--
Reduction lemma for `polyCofreeMapApprox` on an `.intro`
constructor with an abstract (non-destructured) position.
-/
@[simp]
lemma polyCofreeMapApprox_intro
    (A B : Over X) (P : PolyEndo X) (f : A ⟶ B)
    {n : Nat} {y : X}
    (i : polyBetweenIndex X X (polyScale A P) y)
    (children :
      ∀ (e : (polyBetweenFamily X X
        (polyScale A P) y i).left),
        PolyCofixApprox (polyScale A P) n
          ((polyBetweenFamily X X
            (polyScale A P) y i).hom e)) :
    polyCofreeMapApprox A B P f
      (PolyCofixApprox.intro y i children) =
    @PolyCofixApprox.intro X (polyScale B P) n y
      (⟨⟨f.left i.1.val,
          polyCofreeMap_fiber_eq A B f i.1⟩,
        i.2⟩)
      (fun e =>
        polyCofreeMapApprox A B P f (children e)) := by
  cases i with
  | mk a b => rfl

/--
Approximation-level lemma: mapping annotations by `f`
after unfolding from a `polyScale(A, P)`-coalgebra equals
unfolding from the reindexed `polyScale(B, P)`-coalgebra.
-/
lemma polyScaleReindex_approx
    (A B : Over X) (P : PolyEndo X) (f : A ⟶ B)
    (α : PolyCoalg (polyScale A P))
    (n : Nat) {x : X}
    (s : { v : α.V.left // α.V.hom v = x }) :
    polyCofreeMapApprox A B P f
      (polyCofixUnfoldApprox
        (polyScale A P) α n x s) =
    polyCofixUnfoldApprox
      (polyScale B P)
      (polyScaleReindexCoalg A B P f α) n x s := by
  induction n generalizing x s with
  | zero =>
    simp only [polyCofixUnfoldApprox,
      polyCofreeMapApprox]
  | succ n ih =>
    simp only [polyCofixUnfoldApprox]
    rw [polyCofreeMapApprox_cast]
    congr 1
    rw [polyCofreeMapApprox_intro]
    congr 1
    funext e
    exact ih _

/--
Mapping annotations by `f` after unfolding from a
`polyScale(A, P)`-coalgebra equals unfolding from
the reindexed `polyScale(B, P)`-coalgebra.
-/
lemma polyScaleReindex
    (A B : Over X) (P : PolyEndo X) (f : A ⟶ B)
    (α : PolyCoalg (polyScale A P)) :
    polyCofixUnfold (polyScale A P) α ≫
    polyCofreeMap A B P f =
    polyCofixUnfold (polyScale B P)
      (polyScaleReindexCoalg A B P f α) := by
  apply Over.OverMorphism.ext
  funext a
  simp only [Over.comp_left, types_comp_apply,
    polyCofixUnfold, polyCofixUnfoldLeft,
    Over.homMk_left,
    polyCofreeMap, polyCofreeMapLeft]
  apply Sigma.ext
  · rfl
  · simp only [heq_eq_eq, polyCofreeMapAt]
    apply PolyCofix.ext
    intro n
    exact polyScaleReindex_approx
      A B P f α n _

/--
Naturality of the distributive law:
`T(D(f)) ≫ lambda_B = lambda_A ≫ D(T(f))`.
-/
lemma polyDistLaw_naturality
    (A B : Over X) (P : PolyEndo X) (f : A ⟶ B) :
    polyFreeMap
      (polyCofreeCarrier A P)
      (polyCofreeCarrier B P) P
      (polyCofreeMap A B P f) ≫
    polyDistLawMor B P =
    polyDistLawMor A P ≫
    polyCofreeMap
      (polyFreeMCarrier A P)
      (polyFreeMCarrier B P) P
      (polyFreeMap A B P f) := by
  apply Over.OverMorphism.ext
  funext ⟨x, t⟩
  simp only [Over.comp_left, types_comp_apply,
    polyFreeMap, Over.homMk_left,
    polyFreeMapLeft,
    polyDistLawMor, polyCofixUnfold,
    polyCofixUnfoldLeft,
    polyCofreeMap, polyCofreeMapLeft]
  apply Sigma.ext
  · rfl
  · simp only [heq_eq_eq, polyCofreeMapAt]
    apply PolyCofix.ext
    intro n
    exact polyDistLaw_naturality_approx
      A B P f t n

/-! ## Step 7: Comultiplication Coherence

Comultiplication coherence states:
```
T.map(D.δ_A) ≫ dist_{DA} ≫ D.map(dist_A)
  = dist_A ≫ D.δ_{TA}
```
Both sides are morphisms `T(D(A)) → D(D(T(A)))`.

The LHS first duplicates cofree annotations (applying
the comultiplication to each leaf), then distributes over
the doubled cofree structure, then re-annotates using
the original distributive law.

The RHS first distributes then duplicates.

The proof uses the comonad counit law
`D.δ_A ≫ D.ε_{DA} = id` (the left triangle identity)
to simplify the root annotation of the LHS, reducing
to an approximation-level induction.
-/

/--
The counit law applied inside `polyFreeMapAt`: mapping
by the comultiplication then the counit is the identity.
-/
lemma polyDistLaw_comul_annot_eq
    (A : Over X) (P : PolyEndo X) {x : X}
    (t : PolyFreeM (polyCofreeCarrier A P) P x) :
    polyFreeMapAt
      (polyCofreeCarrier (polyCofreeCarrier A P) P)
      (polyCofreeCarrier A P) P
      (polyCofreeCounit (polyCofreeCarrier A P) P)
      x
      (polyFreeMapAt
        (polyCofreeCarrier A P)
        (polyCofreeCarrier
          (polyCofreeCarrier A P) P) P
        (polyCoalgUnit P (polyCofreeCoalg A P))
        x t) = t := by
  rw [← polyFreeMapAt_comp]
  have h : polyCoalgUnit P (polyCofreeCoalg A P) ≫
      polyCofreeCounit (polyCofreeCarrier A P) P =
      𝟙 (polyCofreeCarrier A P) :=
    polyCofree_left_triangle P (polyCofreeCoalg A P)
  rw [h, polyFreeMapAt_id]

/-! ### Abbreviations for the comultiplication coherence proof

The comultiplication coherence equation involves deeply
nested types.  The following abbreviations reduce the
verbosity of the lemma signatures.
-/

/--
The `polyScale(D(T(A)), P)`-coalgebra used on the LHS
of comultiplication coherence: the `polyDistLawScaleCoalg`
at `D(A)` reindexed by `dist_A`.
-/
abbrev polyDistLaw_comul_lhsCoalg
    (A : Over X) (P : PolyEndo X) :
    PolyCoalg (polyScale
      (polyCofreeCarrier
        (polyFreeMCarrier A P) P) P) :=
  polyScaleReindexCoalg
    (polyFreeMCarrier
      (polyCofreeCarrier A P) P)
    (polyCofreeCarrier
      (polyFreeMCarrier A P) P) P
    (polyDistLawMor A P)
    (polyDistLawScaleCoalg
      (polyCofreeCarrier A P) P)

/--
The `P`-coalgebra on `D(T(A))` used on the RHS of
comultiplication coherence.
-/
abbrev polyDistLaw_comul_rhsCoalg
    (A : Over X) (P : PolyEndo X) :
    PolyCoalg P :=
  polyCofreeCoalg (polyFreeMCarrier A P) P

/--
The LHS input: `T.map(δ_A)(t)`, i.e., `polyFreeMapAt`
by the comultiplication applied to `t`.  The result
lives in `T(D(D(A)))`.
-/
abbrev polyDistLaw_comul_lhsInput
    (A : Over X) (P : PolyEndo X) {x : X}
    (t : PolyFreeM (polyCofreeCarrier A P) P x) :
    { a : (polyFreeMCarrier
        (polyCofreeCarrier
          (polyCofreeCarrier A P) P) P).left //
      (polyFreeMCarrier
        (polyCofreeCarrier
          (polyCofreeCarrier A P) P) P).hom
        a = x } :=
  ⟨⟨x, polyFreeMapAt
    (polyCofreeCarrier A P)
    (polyCofreeCarrier
      (polyCofreeCarrier A P) P) P
    (polyCoalgUnit P (polyCofreeCoalg A P))
    x t⟩, rfl⟩

/--
The RHS input: `dist_A(t)`, i.e., the anamorphism
applied to `t`.
-/
abbrev polyDistLaw_comul_rhsInput
    (A : Over X) (P : PolyEndo X) {x : X}
    (t : PolyFreeM (polyCofreeCarrier A P) P x) :
    { a : (polyCofreeCarrier
        (polyFreeMCarrier A P) P).left //
      (polyCofreeCarrier
        (polyFreeMCarrier A P) P).hom a = x } :=
  ⟨⟨x, polyCofixUnfoldAt
    (polyScale (polyFreeMCarrier A P) P)
    (polyDistLawScaleCoalg A P) x
    ⟨⟨x, t⟩, rfl⟩⟩, rfl⟩

/-! ### Comultiplication coherence: RHS child equality

The RHS of the comultiplication coherence at a node
`PolyFix.mk x (Sum.inr p) ch` involves extracting the
children of the M-type `dist_A(node(p,ch))`.  The
following lemma shows that the e-th child of this M-type
(as used by `polyCoalgUnitApprox`) equals
`polyDistLaw_comul_rhsInput A P (ch e)`.
-/

/--
The `hx` transport in `polyCofixUnfoldApprox` for
`polyDistLawScaleCoalg A P` is always a proof of `x = x`,
hence propositionally `rfl`.
-/
private lemma polyDistLaw_hx_rfl
    (A : Over X) (P : PolyEndo X) {x : X}
    (t : PolyFreeM (polyCofreeCarrier A P) P x) :
    (congrFun
      (Over.w (polyDistLawScaleCoalg A P).str)
      (⟨x, t⟩ :
        (polyFreeMCarrier
          (polyCofreeCarrier A P) P).left)) =
    (rfl : x = x) :=
  Subsingleton.elim _ _

/--
At a node `PolyFix.mk x (Sum.inr p) ch`, the head of
`polyCofixUnfoldAt (polyScale TA P) α x ⟨⟨x, node⟩, rfl⟩`
has P-component `p`.
-/
lemma polyDistLaw_comul_head_snd_node
    (A : Over X) (P : PolyEndo X) {x : X}
    (p : polyBetweenIndex X X P x)
    (ch : ∀ (e : (polyBetweenFamily X X
        (polyTranslate
          (polyCofreeCarrier A P) P)
        x (Sum.inr p)).left),
      PolyFix
        (polyTranslate (polyCofreeCarrier A P) P)
        ((polyBetweenFamily X X
          (polyTranslate
            (polyCofreeCarrier A P) P)
          x (Sum.inr p)).hom e)) :
    (polyCofixUnfoldAt
      (polyScale (polyFreeMCarrier A P) P)
      (polyDistLawScaleCoalg A P) x
      ⟨⟨x, PolyFix.mk x (Sum.inr p) ch⟩,
        rfl⟩).head.2 = p := by
  simp only [PolyCofix.head,
    polyCofixUnfoldAt, polyCofixUnfoldApprox,
    PolyCofixApprox.getIndex,
    polyDistLawScaleCoalg,
    polyDistLawScaleCoalgStr,
    polyDistLawScaleCoalgStrLeft,
    polyDistLawScaleCoalgStrAt,
    Over.homMk_left,
    polyFreeMCoalgStrAt]

/--
The family equality for the distributive law anamorphism
at a node: the `polyBetweenFamily` for the head of the
M-type equals the `polyBetweenFamily` for `p`.
-/
lemma polyDistLaw_comul_family_eq_node
    (A : Over X) (P : PolyEndo X) {x : X}
    (p : polyBetweenIndex X X P x)
    (ch : ∀ (e : (polyBetweenFamily X X
        (polyTranslate
          (polyCofreeCarrier A P) P)
        x (Sum.inr p)).left),
      PolyFix
        (polyTranslate (polyCofreeCarrier A P) P)
        ((polyBetweenFamily X X
          (polyTranslate
            (polyCofreeCarrier A P) P)
          x (Sum.inr p)).hom e)) :
    let m := polyCofixUnfoldAt
      (polyScale (polyFreeMCarrier A P) P)
      (polyDistLawScaleCoalg A P) x
      ⟨⟨x, PolyFix.mk x (Sum.inr p) ch⟩, rfl⟩
    polyBetweenFamily X X
      (polyScale (polyFreeMCarrier A P) P)
      x m.head =
    polyBetweenFamily X X P x p := by
  intro m
  change polyBetweenFamily X X P x m.head.2 =
    polyBetweenFamily X X P x p
  rw [polyDistLaw_comul_head_snd_node A P p ch]

/-! ### Comultiplication coherence: node case -/

/--
Node case of the approximation-level comultiplication
coherence.
-/
lemma polyDistLaw_comul_approx_node
    (A : Over X) (P : PolyEndo X) {x : X}
    (p : polyBetweenIndex X X P x)
    (ch : ∀ (e : (polyBetweenFamily X X
        (polyTranslate
          (polyCofreeCarrier A P) P)
        x (Sum.inr p)).left),
      PolyFix
        (polyTranslate (polyCofreeCarrier A P) P)
        ((polyBetweenFamily X X
          (polyTranslate
            (polyCofreeCarrier A P) P)
          x (Sum.inr p)).hom e))
    (n : Nat)
    (ih : ∀ {x : X}
      (t : PolyFreeM
        (polyCofreeCarrier A P) P x),
      polyCofixUnfoldApprox
        (polyScale (polyCofreeCarrier
          (polyFreeMCarrier A P) P) P)
        (polyDistLaw_comul_lhsCoalg A P)
        n x
        (polyDistLaw_comul_lhsInput A P t) =
      polyCoalgUnitApprox P
        (polyDistLaw_comul_rhsCoalg A P)
        n x
        (polyDistLaw_comul_rhsInput A P t)) :
    polyCofixUnfoldApprox
      (polyScale (polyCofreeCarrier
        (polyFreeMCarrier A P) P) P)
      (polyDistLaw_comul_lhsCoalg A P)
      (n + 1) x
      (polyDistLaw_comul_lhsInput A P
        (PolyFix.mk x (Sum.inr p) ch)) =
    polyCoalgUnitApprox P
      (polyDistLaw_comul_rhsCoalg A P)
      (n + 1) x
      (polyDistLaw_comul_rhsInput A P
        (PolyFix.mk x (Sum.inr p) ch)) := by
  conv_lhs => rw [← polyScaleReindex_approx]
  simp only [polyCofixUnfoldApprox,
    polyCoalgUnitApprox,
    polyDistLawScaleCoalg,
    polyDistLawScaleCoalgStr,
    polyDistLawScaleCoalgStrLeft,
    polyDistLawScaleCoalgStrAt,
    Over.homMk_left]
  rw [polyDistLaw_comul_annot_eq]
  simp only [polyCofreeMapApprox_intro]
  simp only [polyFreeMapAt, polyFreeMBind,
    polyFreeMCoalgStrAt,
    polyCofreeCoalg, polyCofreeStr,
    polyCofreeStrLeft,
    Over.homMk_left]
  congr 1
  funext e
  erw [polyScaleReindex_approx]
  erw [ih (ch e)]
  congr 1
  -- M-type children equality: needs
  -- polyCofixUnfoldAt_children_heq
  _

/-! ### Comultiplication coherence: leaf case -/

/--
Leaf case of the approximation-level comultiplication
coherence.
-/
lemma polyDistLaw_comul_approx_leaf
    (A : Over X) (P : PolyEndo X) {x : X}
    (c : { a // (polyCofreeCarrier A P).hom a = x })
    (ch : ∀ (e : (polyBetweenFamily X X
        (polyTranslate
          (polyCofreeCarrier A P) P)
        x (Sum.inl c)).left),
      PolyFix
        (polyTranslate (polyCofreeCarrier A P) P)
        ((polyBetweenFamily X X
          (polyTranslate
            (polyCofreeCarrier A P) P)
          x (Sum.inl c)).hom e))
    (n : Nat)
    (ih : ∀ {x : X}
      (t : PolyFreeM
        (polyCofreeCarrier A P) P x),
      polyCofixUnfoldApprox
        (polyScale (polyCofreeCarrier
          (polyFreeMCarrier A P) P) P)
        (polyDistLaw_comul_lhsCoalg A P)
        n x
        (polyDistLaw_comul_lhsInput A P t) =
      polyCoalgUnitApprox P
        (polyDistLaw_comul_rhsCoalg A P)
        n x
        (polyDistLaw_comul_rhsInput A P t)) :
    polyCofixUnfoldApprox
      (polyScale (polyCofreeCarrier
        (polyFreeMCarrier A P) P) P)
      (polyDistLaw_comul_lhsCoalg A P)
      (n + 1) x
      (polyDistLaw_comul_lhsInput A P
        (PolyFix.mk x (Sum.inl c) ch)) =
    polyCoalgUnitApprox P
      (polyDistLaw_comul_rhsCoalg A P)
      (n + 1) x
      (polyDistLaw_comul_rhsInput A P
        (PolyFix.mk x (Sum.inl c) ch)) := by
  _

/-! ### Main comultiplication coherence lemma -/

/--
Approximation-level comultiplication coherence:
at every depth, the LHS (T.map(δ_A) followed by the
reindexed anamorphism) equals the RHS (dist_A followed
by δ_{TA}).
-/
lemma polyDistLaw_comul_approx
    (A : Over X) (P : PolyEndo X) {x : X}
    (t : PolyFreeM (polyCofreeCarrier A P) P x)
    (n : Nat) :
    polyCofixUnfoldApprox
      (polyScale
        (polyCofreeCarrier
          (polyFreeMCarrier A P) P) P)
      (polyDistLaw_comul_lhsCoalg A P)
      n x
      (polyDistLaw_comul_lhsInput A P t) =
    polyCoalgUnitApprox P
      (polyDistLaw_comul_rhsCoalg A P) n x
      (polyDistLaw_comul_rhsInput A P t) := by
  induction n generalizing x t with
  | zero =>
    simp only [polyCofixUnfoldApprox,
      polyCoalgUnitApprox]
  | succ n ih =>
    match t with
    | PolyFix.mk _ (Sum.inr p) ch =>
      exact polyDistLaw_comul_approx_node
        A P p ch n ih
    | PolyFix.mk _ (Sum.inl c) ch =>
      exact polyDistLaw_comul_approx_leaf
        A P c ch n ih

end GebLean
