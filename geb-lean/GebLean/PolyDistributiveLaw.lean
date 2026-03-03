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

end GebLean
