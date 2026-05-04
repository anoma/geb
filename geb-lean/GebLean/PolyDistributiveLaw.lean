import GebLean.PolyAlg
import GebLean.Utilities.DistributiveLaw

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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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
  apply Subtype.ext
  simp only [polyCofreeStrFamily,
    polyCofreeChildrenMor, Over.homMk_left]
  have hch := polyCofixUnfoldAt_children_heq
    (polyScale (polyFreeMCarrier A P) P)
    (polyDistLawScaleCoalg A P)
    ⟨x, PolyFix.mk x (Sum.inr p) ch⟩
    e e HEq.rfl
  have hfst := polyCofixUnfold_coalg_comm_child_fst_eq
    (polyScale (polyFreeMCarrier A P) P)
    (polyDistLawScaleCoalg A P)
    ⟨x, PolyFix.mk x (Sum.inr p) ch⟩
    e e HEq.rfl
  exact Sigma.ext hfst hch

/--
When two sigma pairs wrap the same type-level data
related by fiber equality and M-type heterogeneous
equality, the sigma pairs (of free monad pure terms
wrapping cofree elements) are equal.
-/
lemma polyFreeMPure_cofree_sigma_eq
    (C : Over X) (P : PolyEndo X)
    {x₁ x₂ : X} (hx : x₁ = x₂)
    {c₁ : PolyCofreeM C P x₁}
    {c₂ : PolyCofreeM C P x₂}
    (hc : HEq c₁ c₂) :
    (⟨x₁, PolyFix.mk x₁
      (Sum.inl (⟨⟨x₁, c₁⟩, rfl⟩ :
        { a : (Σ x, PolyCofreeM C P x) //
          a.1 = x₁ }))
      (fun e => PEmpty.elim e)⟩ :
      (Σ x, PolyFreeM
        (polyCofreeCarrier C P) P x)) =
    ⟨x₂, PolyFix.mk x₂
      (Sum.inl (⟨⟨x₂, c₂⟩, rfl⟩ :
        { a : (Σ x, PolyCofreeM C P x) //
          a.1 = x₂ }))
      (fun e => PEmpty.elim e)⟩ := by
  subst hx
  have := eq_of_heq hc
  subst this
  rfl

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
  obtain ⟨⟨y, m_val⟩, hc⟩ := c
  have hc' : y = x := hc
  subst hc'
  conv_lhs => rw [← polyScaleReindex_approx]
  simp only [polyCofixUnfoldApprox,
    polyCoalgUnitApprox,
    polyDistLawScaleCoalg,
    polyDistLawScaleCoalgStr,
    polyDistLawScaleCoalgStrLeft,
    polyDistLawScaleCoalgStrAt,
    Over.homMk_left]
  rw [polyDistLaw_comul_annot_eq]
  simp only [polyCofreeMapApprox_intro,
    polyCoalgUnit]
  simp only [polyFreeMapAt, polyFreeMBind,
    polyFreeMCoalgStrAt, polyFreeMPure,
    polyCofreeCoalg, polyCofreeStr,
    polyCofreeStrLeft,
    Over.homMk_left]
  congr 1
  funext e
  erw [polyScaleReindex_approx]
  -- Use ih for the e-th cofree child
  -- wrapped in a free monad leaf.
  let child_e :=
    (polyCofreeChildrenMor A P m_val).left e
  have hchild_e_fib :
      (polyCofreeCarrier A P).hom child_e =
      (polyBetweenFamily X X P y
        m_val.head.2).hom e :=
    congrFun
      (Over.w (polyCofreeChildrenMor A P m_val))
      e
  let t_e : PolyFreeM
    (polyCofreeCarrier A P) P
    ((polyBetweenFamily X X P y
      m_val.head.2).hom e) :=
    polyFreeMPure (polyCofreeCarrier A P) P
      ⟨child_e, hchild_e_fib⟩
  have ih_e := ih t_e
  -- The LHS has the same coalgebra as ih_e's LHS
  -- (polyDistLaw_comul_lhsCoalg), same n, same
  -- fiber. The only difference is the input
  -- subtype. Since the input subtype has the same
  -- carrier type, equality of .val suffices.
  -- Use congrArg to transport ih_e's LHS to
  -- the goal's LHS, and similarly for the RHS.
  refine Eq.trans ?lhs_eq (Eq.trans ih_e ?rhs_eq)
  · -- LHS: show goal's input .val = ih_e's
    -- input .val.
    -- Reduce polyFreeMBind on polyFreeMPure via
    -- the monad left identity.
    congr 1
    apply Subtype.ext
    simp only [polyFreeMapAt,
      polyFreeMPure,
      polyCoalgUnit, polyCoalgUnitLeft,
      polyCofreeStrFamily, polyCofreeChildrenMor,
      Over.homMk_left,
      polyCofreeCoalg]
    -- Both sides are sigma pairs wrapping
    -- PolyCofreeM values. The LHS has
    -- .children of polyCoalgUnitAt at
    -- ⟨y, m_val⟩; the RHS has polyCoalgUnitAt
    -- at child_e. Use the children property
    -- of polyCoalgUnitAt.
    let β := polyCofreeCoalg A P
    have hfam :=
      polyCoalgUnit_family_eq P β ⟨y, m_val⟩
    have hfibEq :
      β.V.hom
        ((β.str.left ⟨y, m_val⟩).2.2.left e) =
      (polyBetweenFamily X X P (β.V.hom
          ⟨y, m_val⟩)
        ((polyCoalgUnitAt P β (β.V.hom
          ⟨y, m_val⟩) ⟨⟨y, m_val⟩, rfl⟩
          ).head.2)).hom
        (cast (congrArg (fun F => F.left)
          hfam) e) := by
      exact overType_hom_heq hfam e _ (cast_heq
        (congrArg (fun F => F.left) hfam)
        e).symm
    have hch :=
      polyCoalgUnitAt_children_heq P
        β ⟨y, m_val⟩ e hfibEq
    -- hch relates polyCoalgUnitAt at child
    -- with .children of parent at cast e.
    -- The sigma pair equality requires
    -- matching fibers and HEq of M-types.
    -- Reduce RHS polyFreeMBind on
    -- polyFreeMPure.
    simp only [polyFreeMBind, polyFreeMPure,
      t_e, polyCofreeStr, polyCoalgUnitAt]
    -- Now use the helper lemma with
    -- hch.symm (children on left) and
    -- hfibEq for the fiber.
    exact polyFreeMPure_cofree_sigma_eq
      (polyCofreeCarrier A P) P
      hfibEq hch.symm
  · -- RHS: show ih_e's output .val = goal's output .val
    -- This is the coalgebra hom property of the
    -- distributive law anamorphism.
    have hfst :=
      polyCofixUnfold_coalg_comm_child_fst_eq
        (polyScale (polyFreeMCarrier A P) P)
        (polyDistLawScaleCoalg A P)
        (⟨y, PolyFix.mk y
          (Sum.inl ⟨⟨y, m_val⟩, hc⟩) ch⟩ :
          (polyFreeMCarrier
            (polyCofreeCarrier A P) P).left)
        e e HEq.rfl
    have hch :=
      polyCofixUnfoldAt_children_heq
        (polyScale (polyFreeMCarrier A P) P)
        (polyDistLawScaleCoalg A P)
        (⟨y, PolyFix.mk y
          (Sum.inl ⟨⟨y, m_val⟩, hc⟩) ch⟩ :
          (polyFreeMCarrier
            (polyCofreeCarrier A P) P).left)
        e e HEq.rfl
    congr 1
    apply Subtype.ext
    simp only [polyCofreeStrFamily,
      polyCofreeChildrenMor,
      Over.homMk_left]
    exact Sigma.ext hfst hch

/-! ### Main comultiplication coherence lemma -/

set_option backward.isDefEq.respectTransparency false in
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

/-! ## Step 7: Comultiplication coherence (morphism level)

Lift `polyDistLaw_comul_approx` from approximation level
to a morphism equality via `PolyCofix.ext`.
-/

set_option backward.isDefEq.respectTransparency false in
/--
Comultiplication coherence:
`T.map(D.delta_A) ≫ dist_{DA} ≫ D.map(dist_A) =
  dist_A ≫ D.delta_{TA}`.
-/
lemma polyDistLaw_comul
    (A : Over X) (P : PolyEndo X) :
    polyFreeMap (polyCofreeCarrier A P)
      (polyCofreeCarrier
        (polyCofreeCarrier A P) P) P
      (polyCoalgUnit P (polyCofreeCoalg A P)) ≫
    polyDistLawMor (polyCofreeCarrier A P) P ≫
    polyCofreeMap
      (polyFreeMCarrier
        (polyCofreeCarrier A P) P)
      (polyCofreeCarrier
        (polyFreeMCarrier A P) P) P
      (polyDistLawMor A P) =
    polyDistLawMor A P ≫
    polyCoalgUnit P
      (polyCofreeCoalg
        (polyFreeMCarrier A P) P) := by
  apply Over.OverMorphism.ext
  funext ⟨x, t⟩
  simp only [Over.comp_left, types_comp_apply,
    polyFreeMap, Over.homMk_left,
    polyFreeMapLeft,
    polyDistLawMor, polyCofixUnfold,
    polyCofixUnfoldLeft,
    polyCofreeMap, polyCofreeMapLeft,
    polyCoalgUnit, polyCoalgUnitLeft]
  apply Sigma.ext
  · rfl
  · simp only [heq_eq_eq]
    apply PolyCofix.ext
    intro n
    simp only [polyCofreeMapAt,
      polyCofixUnfoldAt, polyCoalgUnitAt]
    erw [polyScaleReindex_approx]
    exact polyDistLaw_comul_approx A P t n

/-! ## Step 8: Multiplication Coherence

Multiplication coherence states:
```
T.μ.app (D.obj A) ≫ dist.app A =
  T.map(dist.app A) ≫ dist.app (T.obj A) ≫
  D.map(T.μ.app A)
```

Both sides are morphisms `T(T(D(A))) → D(T(A))`.

The LHS first flattens the outer T via monad multiplication,
then distributes.

The RHS first distributes each inner T(D(A))-leaf via
dist_A, then distributes over the entire structure, then
maps annotations by the monad multiplication.
-/

/--
Given a sigma pair equality `s = ⟨a, b⟩` and a proof
`h : s.1 = a`, the transported second component equals `b`.
-/
lemma sigma_snd_of_eq {α : Type u}
    {β : α → Type u}
    {s : (a : α) × β a} {a : α} {b : β a}
    (heq : s = ⟨a, b⟩)
    (h : s.1 = a) :
    h ▸ s.2 = b := by
  subst heq; rfl

/--
The monad multiplication at the fiber level.
Given a tree of trees, flatten by substituting each leaf
(which wraps a tree) with that tree.
-/
def polyFreeMJoinMor
    (A : Over X) (P : PolyEndo X) {x : X}
    (t : PolyFreeM (polyFreeMCarrier A P) P x) :
    PolyFreeM A P x :=
  polyFreeMBind (polyFreeMCarrier A P) A P t
    (fun _ ⟨⟨_, t'⟩, hy⟩ => hy ▸ t')

/--
`polyFreeMJoinMor` at a leaf extracts the inner tree,
transported to the fiber `x` via the fiber proof.
-/
lemma polyFreeMJoinMor_leaf
    (A : Over X) (P : PolyEndo X) {x : X}
    (a : { v : (polyFreeMCarrier A P).left //
      (polyFreeMCarrier A P).hom v = x }) :
    polyFreeMJoinMor A P
      (polyFreeMPure
        (polyFreeMCarrier A P) P a) =
    a.property ▸ a.val.2 := by
  simp only [polyFreeMJoinMor, polyFreeMPure,
    polyFreeMBind]
  obtain ⟨⟨fst, snd⟩, prop⟩ := a
  subst prop
  rfl


/--
`polyFreeMJoinMor` at a node: the result is
`polyFreeMBind` distributing the bind over children.
This is definitional.
-/
@[simp]
lemma polyFreeMJoinMor_node
    (A : Over X) (P : PolyEndo X) {x : X}
    (p : polyBetweenIndex X X P x)
    (ch : ∀ (e : (polyBetweenFamily X X
        (polyTranslate (polyFreeMCarrier A P) P)
        x (Sum.inr p)).left),
      PolyFix
        (polyTranslate (polyFreeMCarrier A P) P)
        ((polyBetweenFamily X X
          (polyTranslate (polyFreeMCarrier A P) P)
          x (Sum.inr p)).hom e)) :
    polyFreeMJoinMor A P
      (PolyFix.mk x (Sum.inr p) ch) =
    (PolyFix.mk x (Sum.inr p)
      (fun e => polyFreeMJoinMor A P (ch e)) :
      PolyFreeM A P x) := by
  rfl

/--
The monad multiplication `T.μ.app A` equals
`polyFreeCounitFold P (polyFreeAlg A P)`.
-/
lemma polyFreeMonad_mu_eq
    (A : Over X) (P : PolyEndo X) :
    (polyFreeMonad X P).μ.app A =
    polyFreeCounitFold P (polyFreeAlg A P) := by
  simp only [polyFreeMonad,
    Adjunction.toMonad_μ]
  rfl

/--
The monad functor map `T.map f` equals
`polyFreeMap ... f`.
-/
lemma polyFreeMonad_map_eq
    (A B : Over X) (P : PolyEndo X) (f : A ⟶ B) :
    (polyFreeMonad X P).toFunctor.map f =
    polyFreeMap A B P f := by
  simp only [polyFreeMonad,
    Adjunction.toMonad]
  rfl

/-! ### Abbreviations for multiplication coherence -/

/-- The T(A) carrier abbreviation. -/
abbrev polyDistLaw_TA (A : Over X) (P : PolyEndo X) :
    Over X :=
  polyFreeMCarrier A P

/--
The RHS coalgebra for multiplication coherence:
`polyDistLawScaleCoalg` at `T(A)` reindexed by `μ`.

This is a `polyScale(T(A), P)`-coalgebra on
`T(D(T(A)))`.
-/
abbrev polyDistLaw_mul_rhsCoalg
    (A : Over X) (P : PolyEndo X) :
    PolyCoalg (polyScale
      (polyDistLaw_TA A P) P) :=
  polyScaleReindexCoalg
    (polyDistLaw_TA (polyDistLaw_TA A P) P)
    (polyDistLaw_TA A P) P
    (polyFreeCounitFold P (polyFreeAlg A P))
    (polyDistLawScaleCoalg
      (polyDistLaw_TA A P) P)

/--
The monad multiplication `T.μ.app A` at the left
component equals the application of
`polyFreeMJoinMor`.
-/
lemma polyFreeMonad_mu_left_eq
    (A : Over X) (P : PolyEndo X)
    (w : (polyFreeMCarrier
      (polyFreeMCarrier A P) P).left) :
    ((polyFreeMonad X P).μ.app A).left w =
    ⟨w.1, polyFreeMJoinMor A P w.2⟩ := by
  obtain ⟨x, t⟩ := w
  change (polyFreeCounitFold P
    (polyFreeAlg A P)).left ⟨x, t⟩ = _
  simp only [polyFreeCounitFold,
    Over.homMk_left,
    polyFreeCounitFoldLeft]
  induction t with
  | mk y idx children ih =>
    cases idx with
    | inl a =>
      simp only [polyFreeCounitFoldAt,
        polyFreeMJoinMor, polyFreeMBind]
      obtain ⟨⟨fst, snd⟩, prop⟩ := a
      subst prop
      rfl
    | inr p =>
      simp only [polyFreeCounitFoldAt,
        polyFreeMJoinMor, polyFreeMBind]
      simp only [polyFreeAlg, polyFreeMStr,
        Over.homMk_left, polyFreeMStrLeft,
        polyFreeMStrFamily, pbefIndex,
        pbefMor, ptoefIndex, ccrEvalIndex,
        ptoefMor, ccrEvalMor]
      apply Sigma.ext
      · rfl
      · simp only [heq_eq_eq]
        congr 1
        funext e
        exact sigma_snd_of_eq (ih e) _

/--
Precomposition of a coalgebra morphism with the
terminal anamorphism: if `g : α ⟶ β` is a coalgebra
morphism, then `g.f ≫ polyCofixUnfold P β =
polyCofixUnfold P α`.
-/
lemma polyCofixUnfold_precomp (P : PolyEndo X)
    (α β : PolyCoalg P)
    (g : α ⟶ β) :
    g.f ≫ polyCofixUnfold P β =
    polyCofixUnfold P α := by
  have h : g ≫ polyCofixUnfoldHom P β =
    polyCofixUnfoldHom P α :=
    polyCofixUnfoldHom_unique P α
      (g ≫ polyCofixUnfoldHom P β)
  exact congrArg
    Endofunctor.Coalgebra.Hom.f h

set_option backward.isDefEq.respectTransparency false in
/--
Naturality of `polyFreeMJoinMor` with respect to
`polyFreeMapAt`: for any `f : A --> B`,
`T(f)(join(t)) = join(T(T(f))(t))`.

This is the pointwise version of `mu_A ≫ T(f) =
T(T(f)) ≫ mu_B`.
-/
lemma polyFreeMJoinMor_nat
    (A B : Over X) (P : PolyEndo X) (f : A ⟶ B)
    {x : X}
    (t : PolyFreeM
      (polyFreeMCarrier A P) P x) :
    polyFreeMapAt A B P f x
      (polyFreeMJoinMor A P t) =
    polyFreeMJoinMor B P
      (polyFreeMapAt
        (polyFreeMCarrier A P)
        (polyFreeMCarrier B P) P
        (polyFreeMap A B P f) x t) := by
  -- Both sides unfold to polyFreeMBind.
  -- Use bind associativity + pure_bind.
  unfold polyFreeMapAt polyFreeMJoinMor
  rw [polyFreeM_bind_assoc,
    polyFreeM_bind_assoc]
  congr 1
  funext y' ⟨⟨fst, snd⟩, prop⟩
  subst prop
  simp only [polyFreeM_pure_bind,
    polyFreeMapAt,
    polyFreeMap, Over.homMk_left,
    polyFreeMapLeft]

/-! ### Multiplication coherence via coalgebra morphisms

Both sides of the multiplication coherence equation
equal the anamorphism from a common
`polyScale(T(A), P)`-coalgebra on `T(T(D(A)))`.

The proof constructs a source coalgebra `gamma` and
shows that both `mu` and `T(dist)` are coalgebra
morphisms from `gamma`, then applies
`polyCofixUnfold_precomp` to conclude.
-/

/--
The `polyScale(T(A), P)`-coalgebra structure on
`T(T(D(A)))` at a fiber element.

The P-part is the P-coalgebra on `T(D(A))`
(from lifting the cofree P-coalgebra on `D(A)`)
further lifted to `T(T(D(A)))`.

The annotation is `T(eps_A)(mu(t))`.
-/
def polyDistLaw_mul_srcCoalgStrAt
    (A : Over X) (P : PolyEndo X)
    {x : X}
    (t : PolyFreeM
      (polyFreeMCarrier
        (polyCofreeCarrier A P) P) P x) :
    polyBetweenEvalFamily X X
      (polyScale (polyFreeMCarrier A P) P)
      (polyFreeMCarrier
        (polyFreeMCarrier
          (polyCofreeCarrier A P) P) P) x :=
  let DA := polyCofreeCarrier A P
  let TDA := polyFreeMCarrier DA P
  let pCoalg :=
    polyFreeMCoalgStrAt TDA P
      (polyFreeMCoalgStr DA P
        (polyCofreeStr A P)) t
  let mu_t : PolyFreeM DA P x :=
    polyFreeMJoinMor DA P t
  let ta : PolyFreeM A P x :=
    polyFreeMapAt DA A P
      (polyCofreeCounit A P) x mu_t
  ⟨(⟨⟨x, ta⟩, rfl⟩, pCoalg.1), pCoalg.2⟩

/--
The underlying function of the source coalgebra
structure map for multiplication coherence.
-/
def polyDistLaw_mul_srcCoalgStrLeft
    (A : Over X) (P : PolyEndo X) :
    (polyFreeMCarrier
      (polyFreeMCarrier
        (polyCofreeCarrier A P) P) P).left →
    ((polyEndoFunctor X
      (polyScale (polyFreeMCarrier A P) P)).obj
      (polyFreeMCarrier
        (polyFreeMCarrier
          (polyCofreeCarrier A P) P) P)).left :=
  fun ⟨x, t⟩ =>
    ⟨x, polyDistLaw_mul_srcCoalgStrAt A P t⟩

/--
The source coalgebra structure map commutes with
projections.
-/
lemma polyDistLaw_mul_srcCoalgStr_comm
    (A : Over X) (P : PolyEndo X) :
    polyDistLaw_mul_srcCoalgStrLeft A P ≫
    ((polyEndoFunctor X
      (polyScale (polyFreeMCarrier A P) P)).obj
      (polyFreeMCarrier
        (polyFreeMCarrier
          (polyCofreeCarrier A P) P) P)).hom =
    (polyFreeMCarrier
      (polyFreeMCarrier
        (polyCofreeCarrier A P) P) P).hom := rfl

/--
The `polyScale(T(A), P)`-coalgebra structure map
on `T(T(D(A)))`.
-/
def polyDistLaw_mul_srcCoalgStr
    (A : Over X) (P : PolyEndo X) :
    polyFreeMCarrier
      (polyFreeMCarrier
        (polyCofreeCarrier A P) P) P ⟶
    (polyEndoFunctor X
      (polyScale (polyFreeMCarrier A P) P)).obj
      (polyFreeMCarrier
        (polyFreeMCarrier
          (polyCofreeCarrier A P) P) P) :=
  Over.homMk
    (polyDistLaw_mul_srcCoalgStrLeft A P)
    (polyDistLaw_mul_srcCoalgStr_comm A P)

/--
The `polyScale(T(A), P)`-coalgebra on `T(T(D(A)))`:
the common source for both sides of the multiplication
coherence equation.
-/
def polyDistLaw_mul_srcCoalg
    (A : Over X) (P : PolyEndo X) :
    PolyCoalg
      (polyScale (polyFreeMCarrier A P) P) where
  V := polyFreeMCarrier
    (polyFreeMCarrier
      (polyCofreeCarrier A P) P) P
  str := polyDistLaw_mul_srcCoalgStr A P

set_option backward.isDefEq.respectTransparency false in
/--
Multiplication coherence:
`T.μ.app (D.obj A) ≫ dist.app A =
  T.map(dist.app A) ≫ dist.app (T.obj A) ≫
  D.map(T.μ.app A)`.
-/
lemma polyDistLaw_mul
    (A : Over X) (P : PolyEndo X) :
    let DA := polyCofreeCarrier A P
    let TA := polyFreeMCarrier A P
    let TDA := polyFreeMCarrier DA P
    polyFreeCounitFold P (polyFreeAlg DA P) ≫
    polyDistLawMor A P =
    polyFreeMap TDA
      (polyCofreeCarrier TA P) P
      (polyDistLawMor A P) ≫
    polyDistLawMor TA P ≫
    polyCofreeMap
      (polyFreeMCarrier TA P)
      TA P
      (polyFreeCounitFold P
        (polyFreeAlg A P)) := by
  -- Prove coalgebra morphism conditions as
  -- intermediate goals.
  have mu_hom_h :
    (polyDistLaw_mul_srcCoalg A P).str ≫
    (polyEndoFunctor X
      (polyScale (polyFreeMCarrier A P) P)).map
      (polyFreeCounitFold P
        (polyFreeAlg
          (polyCofreeCarrier A P) P)) =
    polyFreeCounitFold P
      (polyFreeAlg (polyCofreeCarrier A P) P) ≫
    (polyDistLawScaleCoalg A P).str := by
    apply Over.OverMorphism.ext
    funext ⟨x, t⟩
    simp only [Over.comp_left, types_comp_apply]
    induction t with
    | mk y idx children ih =>
      cases idx with
      | inr p =>
        -- The node case: both sides produce the
        -- same P-structure with the same annotation
        -- and children, related by
        -- `polyFreeMonad_mu_left_eq`.
        -- The fold (catamorphism) representation and
        -- the bind representation of `mu` agree.
        -- Use `polyFreeMonad_mu_left_eq` to rewrite
        -- `mu.left` at each child.
        have hmu : ∀ e,
            ((polyFreeCounitFold P
              (polyFreeAlg
                (polyCofreeCarrier A P) P)).left
              ⟨(polyBetweenFamily X X P y p).hom e,
                children e⟩) =
            ⟨(polyBetweenFamily X X P y p).hom e,
              polyFreeMJoinMor
                (polyCofreeCarrier A P) P
                (children e)⟩ := by
          intro e
          rw [← polyFreeMonad_mu_eq]
          exact polyFreeMonad_mu_left_eq
            (polyCofreeCarrier A P) P _
        -- Both sides, once `mu` is expressed via
        -- `joinMor`, agree definitionally.
        -- Express `mu.left ⟨y, node(p, ch)⟩` via
        -- `polyFreeMonad_mu_left_eq`.
        have hmu_node :
          (polyFreeCounitFold P
            (polyFreeAlg
              (polyCofreeCarrier A P) P)).left
            ⟨y, PolyFix.mk y
              (Sum.inr p) children⟩ =
          ⟨y, polyFreeMJoinMor
            (polyCofreeCarrier A P) P
            (PolyFix.mk y (Sum.inr p)
              children)⟩ := by
          rw [← polyFreeMonad_mu_eq]
          exact polyFreeMonad_mu_left_eq
            (polyCofreeCarrier A P) P _
        -- Rewrite `mu.left` on the RHS.
        rw [hmu_node]
        -- Now the RHS has `distLawScaleCoalg.str.left
        --   ⟨y, joinMor(node(p, ch))⟩`.
        -- `joinMor(node(p, ch))` reduces to
        -- `node(p, joinMor ∘ ch)`.
        -- The LHS has `(.map mu).left
        --   (srcCoalg.str.left ⟨y, node(p, ch)⟩)`.
        -- After unfolding srcCoalg at a node:
        -- annotation = T(eps_A)(joinMor(node(p, ch)))
        --            = T(eps_A)(node(p, joinMor ∘ ch))
        -- P-index = p
        -- children = ch (the TTDA children)
        -- Then `.map mu` maps each child by mu.
        -- `mu.left ⟨y_e, ch_e⟩ = ⟨y_e, joinMor ch_e⟩`
        -- by `hmu`.
        -- After unfolding distLawScaleCoalg at
        -- `⟨y, node(p, joinMor ∘ ch)⟩`:
        -- annotation = T(eps_A)(node(p, joinMor ∘ ch))
        -- P-index = p
        -- children = `e ↦ ⟨y_e, joinMor(ch_e)⟩`
        -- These match the LHS.
        -- Unfold and simplify everything.
        simp only [Over.homMk_left,
          polyDistLaw_mul_srcCoalg,
          polyDistLaw_mul_srcCoalgStr,
          polyDistLaw_mul_srcCoalgStrLeft,
          polyDistLaw_mul_srcCoalgStrAt,
          polyFreeMCoalgStrAt,
          polyFreeMCoalgStr,
          polyDistLawScaleCoalg,
          polyDistLawScaleCoalgStr,
          polyDistLawScaleCoalgStrLeft,
          polyDistLawScaleCoalgStrAt,
          polyEndoFunctor,
          polyBetweenEvalFunctor,
          polyToOverFunctor,
          polyToOverEvalMap,
          familySliceForward,
          familySliceForwardMap,
          polyToOverEvalFamilyMap,
          ccrEvalMap,
          polyFreeMJoinMor, polyFreeMBind,
          polyFreeCounitFold]
        -- The remaining difference is in the
        -- children morphism. The LHS composes
        -- `Over.homMk ... ≫ Over.homMk fold.left`,
        -- while the RHS directly applies joinMor.
        -- Simplify the composition and apply hmu.
        congr 1; congr 1
        apply Over.OverMorphism.ext
        funext e
        simp only [Over.comp_left,
          types_comp_apply,
          Over.homMk_left]
        change (polyFreeCounitFold P
          (polyFreeAlg
            (polyCofreeCarrier A P) P)).left
          ⟨(polyBetweenFamily X X P y p).hom e,
            children e⟩ = _
        rw [hmu e]
        simp only [polyFreeMJoinMor]
      | inl a =>
        -- Leaf case: `mu(pure(a)) = a`, so the
        -- P-coalgebra structure commutes.
        obtain ⟨⟨x_a, t_a⟩, ha⟩ := a
        subst ha
        -- Now `a = ⟨⟨x_a, t_a⟩, rfl⟩` and the
        -- tree is `polyFreeMPure ... a`.
        -- `mu.left ⟨x_a, pure(a)⟩ = ⟨x_a, t_a⟩`
        -- by monad left unit.
        -- Unfold both sides.
        simp only [Over.homMk_left,
          polyDistLaw_mul_srcCoalg,
          polyDistLaw_mul_srcCoalgStr,
          polyDistLaw_mul_srcCoalgStrLeft,
          polyDistLaw_mul_srcCoalgStrAt,
          polyFreeMCoalgStrAt,
          polyFreeMCoalgStr,
          polyFreeMJoinMor, polyFreeMBind,
          polyFreeMPure,
          polyDistLawScaleCoalg,
          polyDistLawScaleCoalgStr,
          polyDistLawScaleCoalgStrLeft,
          polyDistLawScaleCoalgStrAt,
          polyEndoFunctor,
          polyBetweenEvalFunctor,
          polyToOverFunctor,
          polyToOverEvalMap,
          familySliceForward,
          familySliceForwardMap,
          polyToOverEvalFamilyMap,
          ccrEvalMap,
          polyFreeCounitFold,
          polyFreeCounitFoldLeft,
          polyFreeCounitFoldAt,
          polyFreeAlg, polyFreeMStr]
        -- The goal depends on the structure of
        -- `t_a : PolyFreeM DA P x_a`.
        -- Case split on `t_a`.
        match t_a with
        | PolyFix.mk _ (Sum.inl c) _ =>
          -- `t_a` is a leaf in `T(DA)`, wrapping
          -- a cofree element `c`.
          -- `polyFreeMCoalgStrAt` at `inl c`
          -- delegates to `polyCofreeStr`.
          -- `mu(pure(pure(c))) = pure(c)` by
          -- monad left unit.
          -- After simp, both sides directly
          -- apply the cofree coalgebra to `c`.
          simp only [polyFreeMCoalgStrAt,
            polyFreeMCoalgStrLeft,
            polyFreeMPure]
          rfl
        | PolyFix.mk _ (Sum.inr p_inner)
            ch_inner =>
          -- `t_a` is a node in `T(DA)`.
          -- `polyFreeMCoalgStrAt` at `inr p_inner`
          -- returns `(p_inner, ch_inner)` directly.
          -- `mu(pure(node(p, ch))) = node(p, ch)`
          -- by monad left unit.
          simp only [polyFreeMCoalgStrAt,
            polyFreeMCoalgStrLeft]
          rfl
  have tdist_hom_h :
    (polyDistLaw_mul_srcCoalg A P).str ≫
    (polyEndoFunctor X
      (polyScale (polyFreeMCarrier A P) P)).map
      (polyFreeMap
        (polyFreeMCarrier
          (polyCofreeCarrier A P) P)
        (polyCofreeCarrier
          (polyFreeMCarrier A P) P) P
        (polyDistLawMor A P)) =
    polyFreeMap
      (polyFreeMCarrier
        (polyCofreeCarrier A P) P)
      (polyCofreeCarrier
        (polyFreeMCarrier A P) P) P
      (polyDistLawMor A P) ≫
    (polyDistLaw_mul_rhsCoalg A P).str := by
    apply Over.OverMorphism.ext
    funext ⟨x, t⟩
    simp only [Over.comp_left, types_comp_apply]
    induction t with
    | mk y idx children ih =>
      cases idx with
      | inr p =>
        -- Node case.
        -- Unfold srcCoalg.str at the node, then
        -- unfold polyEndoFunctor.map, polyFreeMap,
        -- polyFreeMapAt, rhsCoalg definitions, etc.
        simp only [
          polyDistLaw_mul_srcCoalg,
          polyDistLaw_mul_srcCoalgStr,
          Over.homMk_left,
          polyDistLaw_mul_srcCoalgStrLeft,
          polyDistLaw_mul_srcCoalgStrAt,
          polyFreeMCoalgStrAt,
          polyFreeMCoalgStr,
          polyDistLaw_mul_rhsCoalg,
          polyDistLawScaleCoalg,
          polyDistLawScaleCoalgStr,
          polyEndoFunctor,
          polyBetweenEvalFunctor,
          polyToOverFunctor,
          polyToOverEvalMap,
          familySliceForward,
          familySliceForwardMap,
          polyToOverEvalFamilyMap,
          ccrEvalMap,
          polyFreeMap, polyFreeMapLeft]
        -- The RHS involves T(dist)(node(p, ch))
        -- which by polyFreeMapAt/polyFreeMBind at
        -- Sum.inr reduces to node(p, T(dist) ∘ ch).
        -- Then polyFreeMCoalgStrAt at Sum.inr
        -- extracts (p, children) directly.
        dsimp only [
          polyFreeMapAt, polyFreeMBind,
          polyFreeMCoalgStrAt]
        -- Split the outer sigma structure.
        -- congr splits into annotation + children;
        -- children are closed automatically.
        congr 1; congr 1; congr 1
        -- The remaining goal is the annotation
        -- Subtype equality.
        -- Derive it from the morphism-level equation
        -- mu_DA ≫ T(eps_A) = T(T(eps_A)) ≫ mu_A
        -- evaluated at ⟨y, node(p, ch)⟩, combined
        -- with counit coherence T(eps_A) = dist ≫
        -- eps_{TA}.
        apply Subtype.ext
        -- Goal: ⟨y, T(eps_A)(join(node(p,ch)))⟩ =
        --       fold_A ⟨y,
        --         T(eps_{TA})(T(dist)(node(p,ch)))⟩
        -- Get the naturality equation:
        -- mu_DA ≫ T(eps_A) = T(T(eps_A)) ≫ mu_A
        have h_mu_nat :=
          ((polyFreeMonad X P).μ.naturality
            (polyCofreeCounit A P)).symm
        simp only [Functor.comp_map] at h_mu_nat
        rw [polyFreeMonad_mu_eq,
          polyFreeMonad_mu_eq,
          polyFreeMonad_map_eq,
          polyFreeMonad_map_eq] at h_mu_nat
        -- h_mu_nat :
        --   fold_DA ≫ T(eps_A) =
        --   T(T(eps_A)) ≫ fold_A
        -- Rewrite T(T(eps_A)) via counit coherence.
        rw [show polyFreeMap
          (polyCofreeCarrier A P) A P
          (polyCofreeCounit A P) =
          polyDistLawMor A P ≫
          polyCofreeCounit
            (polyFreeMCarrier A P) P
          from (polyDistLaw_counit A P).symm]
          at h_mu_nat
        rw [polyFreeMap_comp] at h_mu_nat
        -- h_mu_nat :
        --   fold_DA ≫ T(eps_A) =
        --   T(dist) ≫ T(eps_{TA}) ≫ fold_A
        -- Apply at ⟨y, node(p, ch)⟩.
        have h_eq := congrFun
          (congrArg CommaMorphism.left h_mu_nat)
          ⟨y, PolyFix.mk y (Sum.inr p) children⟩
        simp only [Over.comp_left,
          types_comp_apply] at h_eq
        -- Rewrite fold_DA to joinMor via
        -- polyFreeMonad_mu_left_eq.
        rw [show (polyFreeCounitFold P
          (polyFreeAlg
            (polyCofreeCarrier A P) P)).left
          ⟨y, PolyFix.mk y (Sum.inr p) children⟩ =
          ⟨y, polyFreeMJoinMor
            (polyCofreeCarrier A P) P
            (PolyFix.mk y (Sum.inr p) children)⟩
          from by
            rw [← polyFreeMonad_mu_eq]
            exact polyFreeMonad_mu_left_eq
              (polyCofreeCarrier A P) P _]
          at h_eq
        -- Unfold T(eps_A) on the LHS and
        -- T(dist) ≫ T(eps_{TA}) on the RHS of
        -- h_eq to match the goal.
        simp only [polyFreeMap] at h_eq
        exact h_eq
      | inl a =>
        -- Leaf case: the tree is pure(a) where
        -- a.val : T(DA).
        -- Use the anamorphism for dist
        -- at the morphism level.
        obtain ⟨⟨x_a, t_a⟩, ha⟩ := a
        subst ha
        -- Unfold structural definitions.
        simp only [
          polyDistLaw_mul_srcCoalg,
          polyDistLaw_mul_srcCoalgStr,
          Over.homMk_left,
          polyDistLaw_mul_srcCoalgStrLeft,
          polyDistLaw_mul_srcCoalgStrAt,
          polyFreeMCoalgStrAt,
          polyFreeMCoalgStr,
          polyScaleReindexCoalg,
          polyScaleReindexLeft,
          polyDistLawScaleCoalg,
          polyDistLawScaleCoalgStr,
          polyDistLawScaleCoalgStrLeft,
          polyDistLawScaleCoalgStrAt,
          polyEndoFunctor,
          polyBetweenEvalFunctor,
          polyToOverFunctor,
          polyToOverEvalMap,
          familySliceForward,
          familySliceForwardMap,
          polyToOverEvalFamilyMap,
          ccrEvalMap,
          polyFreeMap, polyFreeMapLeft,
          Over.comp_left, types_comp_apply,
          polyFreeMPure,
          polyCofreeCounit,
          polyCofreeStr, polyCofreeStrLeft,
          polyFreeMJoinMor, polyFreeMBind]
        dsimp only [
          polyFreeMapAt, polyFreeMBind,
          polyFreeMPure,
          polyFreeMCoalgStrAt,
          polyFreeMCoalgStr,
          polyFreeMCoalgStrLeft,
          polyCofreeStrFamily]
        -- The goal is:
        -- P.map(T(dist))(srcCoalg.str(
        --   pure(⟨x_a,t_a⟩)))
        -- = rhsCoalg.str(T(dist)(
        --   pure(⟨x_a,t_a⟩)))
        -- Both sides reduce to a polyScale
        -- value ⟨fiber, ⟨annot, pidx,
        --   children⟩⟩.
        -- The annotation on the LHS is
        -- T(eps_A)(⟨x_a, t_a⟩) and on the
        -- RHS is eps_{TA}(dist(⟨x_a,t_a⟩)).
        -- These are equal by counit
        -- coherence.
        -- The P-data on the LHS has children
        -- that are pure-wrapped, composed
        -- with T(dist). The P-data on the RHS
        -- is the cofree destruct of
        -- dist(⟨x_a,t_a⟩), also pure-wrapped.
        -- Both P-data components are related
        -- by the anamorphism for dist.
        --
        -- Strategy: construct a common value
        -- and show both sides equal it.
        -- The common value is:
        --   ⟨fiber, ⟨annot, pidx,
        --     pure ∘ cofixChildren⟩⟩
        -- where cofixChildren comes from
        -- cofixDest(dist(⟨x_a,t_a⟩)).
        --
        -- Split into annotation + children.
        -- First close the annotation and
        -- P-index, then handle children.
        congr 1; congr 1
        -- Remaining: children morphism
        -- equality. The LHS is
        -- rawChildren ≫ T(dist) and the
        -- RHS is cofixChildren, both as
        -- Over.homMk values. Use the
        -- anamorphism at ⟨x_a, t_a⟩.
        have h_ana :=
          polyCofixUnfold_coalg_comm
            (polyScale
              (polyFreeMCarrier A P) P)
            (polyDistLawScaleCoalg A P)
        have h_ana_at := congrFun
          (congrArg CommaMorphism.left
            h_ana)
          ⟨x_a, t_a⟩
        simp only [Over.comp_left,
          types_comp_apply] at h_ana_at
        -- h_ana_at :
        -- P.map(dist)(coalg.str(⟨x_a,t_a⟩))
        -- = cofixDest(dist(⟨x_a,t_a⟩))
        -- Unfold the coalg.str side.
        simp only [
          polyDistLawScaleCoalg,
          polyDistLawScaleCoalgStr,
          polyDistLawScaleCoalgStrLeft,
          polyDistLawScaleCoalgStrAt,
          polyEndoFunctor,
          polyBetweenEvalFunctor,
          polyToOverFunctor,
          polyToOverEvalMap,
          familySliceForward,
          familySliceForwardMap,
          polyToOverEvalFamilyMap,
          ccrEvalMap,
          polyCofixDest,
          polyCofixDestLeft,
          polyCofixDestFamily,
          polyCofreeStr,
          polyCofreeStrLeft,
          polyFreeMCoalgStrAt,
          Over.homMk_left]
          at h_ana_at
        -- h_ana_at is now:
        -- ⟨x_a, ⟨pidx, children ≫ dist⟩⟩
        -- = ⟨x_a, ⟨cofixPidx,
        --   cofixChildren⟩⟩
        -- Extract the children component
        -- (third level of the sigma).
        have h_snd :=
          (Sigma.mk.inj h_ana_at).2
        have h_inner :=
          eq_of_heq h_snd
        have h_ch :=
          eq_of_heq
            (Sigma.mk.inj h_inner).2
        -- h_ch : rawChildren ≫ dist =
        --   cofixChildren (as Over.homMk)
        -- The goal is:
        -- rawChildren_pure ≫ T(dist) =
        --   cofixChildren_pure
        -- where rawChildren_pure wraps
        -- each raw child in pure.
        -- Apply ext and funext.
        apply Over.OverMorphism.ext
        funext e_ch
        simp only [Over.comp_left,
          types_comp_apply,
          Over.homMk_left,
          polyFreeMapLeft,
          polyFreeMapAt,
          polyFreeMBind,
          polyFreeMPure]
        -- At each point, the LHS is
        -- ⟨fiber, T(dist)(pure(rawChild))⟩
        -- = ⟨fiber, pure(dist(rawChild))⟩
        -- and the RHS is
        -- ⟨fiber, pure(cofixChild)⟩.
        -- congr 1 splits the pair.
        congr 1
        -- The tree component remains.
        -- Extract h_ch at e_ch.
        have h_ch_at := congrFun
          (congrArg CommaMorphism.left
            h_ch) e_ch
        simp only [Over.comp_left,
          types_comp_apply]
          at h_ch_at
        -- h_ch_at gives us the equality
        -- between the D(TA)-level values
        -- on both sides.
        -- Both sides of the goal are
        -- PolyFix.mk with Sum.inl and empty
        -- children: pure leaf nodes whose
        -- content is given by h_ch_at.
        -- congr 1 on PolyFix.mk closes the
        -- fiber and children, leaving
        -- Sum.inl ⟨v1, _⟩ = Sum.inl ⟨v2, _⟩.
        congr 1
        -- congr 1 on Sum.inl leaves
        -- ⟨v1, _⟩ = ⟨v2, _⟩.
        congr 1
        -- Subtype.ext reduces to v1 = v2.
        apply Subtype.ext
        -- The goal is now:
        -- dist.left(rawChild(e_ch)) =
        -- cofixChild.val(e_ch)
        -- Use h_ch_at directly.
        exact h_ch_at
  have lhs_eq :
    polyFreeCounitFold P
      (polyFreeAlg (polyCofreeCarrier A P) P) ≫
    polyDistLawMor A P =
    polyCofixUnfold
      (polyScale (polyFreeMCarrier A P) P)
      (polyDistLaw_mul_srcCoalg A P) :=
    polyCofixUnfold_precomp
      (polyScale (polyFreeMCarrier A P) P)
      (polyDistLaw_mul_srcCoalg A P)
      (polyDistLawScaleCoalg A P)
      ⟨polyFreeCounitFold P
        (polyFreeAlg (polyCofreeCarrier A P) P),
       mu_hom_h⟩
  have rhs_eq1 :
    polyDistLawMor (polyFreeMCarrier A P) P ≫
    polyCofreeMap
      (polyFreeMCarrier
        (polyFreeMCarrier A P) P)
      (polyFreeMCarrier A P) P
      (polyFreeCounitFold P
        (polyFreeAlg A P)) =
    polyCofixUnfold
      (polyScale (polyFreeMCarrier A P) P)
      (polyDistLaw_mul_rhsCoalg A P) :=
    polyScaleReindex
      (polyFreeMCarrier (polyFreeMCarrier A P) P)
      (polyFreeMCarrier A P) P
      (polyFreeCounitFold P (polyFreeAlg A P))
      (polyDistLawScaleCoalg
        (polyFreeMCarrier A P) P)
  have rhs_eq2 :
    polyFreeMap
      (polyFreeMCarrier
        (polyCofreeCarrier A P) P)
      (polyCofreeCarrier
        (polyFreeMCarrier A P) P) P
      (polyDistLawMor A P) ≫
    polyCofixUnfold
      (polyScale (polyFreeMCarrier A P) P)
      (polyDistLaw_mul_rhsCoalg A P) =
    polyCofixUnfold
      (polyScale (polyFreeMCarrier A P) P)
      (polyDistLaw_mul_srcCoalg A P) :=
    polyCofixUnfold_precomp
      (polyScale (polyFreeMCarrier A P) P)
      (polyDistLaw_mul_srcCoalg A P)
      (polyDistLaw_mul_rhsCoalg A P)
      ⟨polyFreeMap
        (polyFreeMCarrier
          (polyCofreeCarrier A P) P)
        (polyCofreeCarrier
          (polyFreeMCarrier A P) P) P
        (polyDistLawMor A P),
       tdist_hom_h⟩
  dsimp only []
  rw [lhs_eq, rhs_eq1, rhs_eq2]

/--
The monad unit `T.η.app A` equals `polyFreeUnit A P`.
-/
lemma polyFreeMonad_eta_eq
    (A : Over X) (P : PolyEndo X) :
    (polyFreeMonad X P).η.app A =
    polyFreeUnit A P := by
  simp only [polyFreeMonad,
    Adjunction.toMonad_η]
  rfl

/--
The comonad counit `D.ε.app A` equals
`polyCofreeCounit A P`.
-/
lemma polyCofreeComonad_eps_eq
    (A : Over X) (P : PolyEndo X) :
    (polyCofreeComonad X P).ε.app A =
    polyCofreeCounit A P := by
  simp only [polyCofreeComonad,
    Adjunction.toComonad_ε]
  rfl

/--
The comonad comultiplication `D.δ.app A` equals
`polyCoalgUnit P (polyCofreeCoalg A P)`.
-/
lemma polyCofreeComonad_delta_eq
    (A : Over X) (P : PolyEndo X) :
    (polyCofreeComonad X P).δ.app A =
    polyCoalgUnit P (polyCofreeCoalg A P) := by
  simp only [polyCofreeComonad,
    Adjunction.toComonad_δ]
  rfl

/--
The comonad functor map `D.map f` equals
`polyCofreeMap ... f`.
-/
lemma polyCofreeComonad_map_eq
    (A B : Over X) (P : PolyEndo X) (f : A ⟶ B) :
    (polyCofreeComonad X P).toFunctor.map f =
    polyCofreeMap A B P f := by
  simp only [polyCofreeComonad,
    Adjunction.toComonad]
  rfl

/-! ## Step 9: Packaging as a Distributive Law

Package the four coherence lemmas and
naturality into a `DistributiveLaw` structure,
giving a distributive law of the free monad
`T = polyFreeMonad X P` over the cofree comonad
`D = polyCofreeComonad X P`.
-/

/--
The `T.toFunctor.obj` applied to `A` is
`polyFreeMCarrier A P`.
-/
lemma polyFreeMonad_obj_eq
    (A : Over X) (P : PolyEndo X) :
    (polyFreeMonad X P).toFunctor.obj A =
    polyFreeMCarrier A P := by
  simp only [polyFreeMonad,
    Adjunction.toMonad]
  rfl

/--
The `D.toFunctor.obj` applied to `A` is
`polyCofreeCarrier A P`.
-/
lemma polyCofreeComonad_obj_eq
    (A : Over X) (P : PolyEndo X) :
    (polyCofreeComonad X P).toFunctor.obj A =
    polyCofreeCarrier A P := by
  simp only [polyCofreeComonad,
    Adjunction.toComonad]
  rfl

/--
The distributive law natural transformation
`lambda : D ⋙ T ⟶ T ⋙ D` at each object.
-/
def polyDistLawNatApp
    (A : Over X) (P : PolyEndo X) :
    ((polyCofreeComonad X P).toFunctor ⋙
      (polyFreeMonad X P).toFunctor).obj A ⟶
    ((polyFreeMonad X P).toFunctor ⋙
      (polyCofreeComonad X P).toFunctor).obj A :=
  polyDistLawMor A P

/--
Naturality of the distributive law in terms of
the monad and comonad functors.
-/
lemma polyDistLawNat_naturality
    (A B : Over X) (P : PolyEndo X) (f : A ⟶ B) :
    ((polyCofreeComonad X P).toFunctor ⋙
      (polyFreeMonad X P).toFunctor).map f ≫
    polyDistLawNatApp B P =
    polyDistLawNatApp A P ≫
    ((polyFreeMonad X P).toFunctor ⋙
      (polyCofreeComonad X P).toFunctor).map f := by
  simp only [Functor.comp_map,
    polyFreeMonad_map_eq,
    polyCofreeComonad_map_eq]
  exact polyDistLaw_naturality A B P f

/--
The distributive law as a natural transformation
`D ⋙ T ⟶ T ⋙ D`.
-/
def polyDistLawNat (P : PolyEndo X) :
    (polyCofreeComonad X P).toFunctor ⋙
      (polyFreeMonad X P).toFunctor ⟶
    (polyFreeMonad X P).toFunctor ⋙
      (polyCofreeComonad X P).toFunctor where
  app := fun A => polyDistLawNatApp A P
  naturality := fun {A B} f =>
    polyDistLawNat_naturality A B P f

/--
The polynomial distributive law of the free monad
over the cofree comonad.
-/
def polyDistributiveLaw
    (P : PolyEndo X) :
    DistributiveLaw
      (polyFreeMonad X P)
      (polyCofreeComonad X P) where
  dist := polyDistLawNat P
  unit := fun A => by
    simp only [polyDistLawNat, polyDistLawNatApp,
      polyFreeMonad_eta_eq,
      polyCofreeComonad_map_eq]
    exact polyDistLaw_unit A P
  counit := fun A => by
    simp only [polyDistLawNat, polyDistLawNatApp,
      polyCofreeComonad_eps_eq,
      polyFreeMonad_map_eq]
    exact polyDistLaw_counit A P
  mul := fun A => by
    simp only [polyDistLawNat, polyDistLawNatApp,
      polyFreeMonad_mu_eq,
      polyFreeMonad_map_eq,
      polyCofreeComonad_map_eq]
    exact polyDistLaw_mul A P
  comul := fun A => by
    simp only [polyDistLawNat, polyDistLawNatApp,
      polyCofreeComonad_delta_eq,
      polyCofreeComonad_map_eq,
      polyFreeMonad_map_eq]
    exact polyDistLaw_comul A P

end GebLean
