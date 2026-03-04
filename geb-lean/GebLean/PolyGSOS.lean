import GebLean.PolyDistributiveLaw
import GebLean.PolyUMorph
import GebLean.Utilities.GSOSRule
import GebLean.Utilities.LambdaBialgebra

namespace GebLean

open CategoryTheory

universe u

variable {X : Type u}

/--
The identity-behavior product as a polynomial endofunctor.
Given a behavior polynomial `Q : PolyEndo X`, the
polynomial `polyIdBehaviorPoly Q` evaluates to the functor
`A ↦ A ×_X Q(A)`: the binary product of the identity
polynomial with `Q` in the polynomial category.
-/
abbrev polyIdBehaviorPoly
    (Q : PolyEndo X) : PolyEndo X :=
  pbBinaryProdObj (polyBetweenId X) Q

/--
A GSOS rule for polynomial endofunctors on `Over X`,
expressed as a morphism in the polynomial category.

Given signature `P` and behavior `Q`, a GSOS rule is a
morphism `P ∘ (Id × Q) ⟶ Q ∘ T_P` in `PolyEndo X`,
where `Id × Q` is the identity-behavior polynomial and
`T_P = polyFreeMPoly P` is the free monad polynomial.

Applying `polyBetweenEvalCatFunctor` recovers the
natural transformation `P(A ×_X Q(A)) ⟶ Q(T_P(A))`.
-/
@[ext]
structure PolyGSOSRule (P Q : PolyEndo X) where
  rule :
    polyBetweenComp P (polyIdBehaviorPoly Q) ⟶
    polyBetweenComp Q (polyFreeMPoly P)

/--
The leaf handler for the GSOS parameterized fold.
Given a cofree comonad element `d : PolyCofreeM A Q x`,
produce a pair `(eta(d), Q(eta)(str(d)))` in the
product type `T_P(D_Q(A)) ×_X Q(T_P(D_Q(A)))`.
-/
def polyGSOSFoldLeafAt
    (A : Over X) (P Q : PolyEndo X) {x : X}
    (d : PolyCofreeM A Q x) :
    overPullbackType
      (polyFreeMCarrier
        (polyCofreeCarrier A Q) P)
      ((polyEndoFunctor X Q).obj
        (polyFreeMCarrier
          (polyCofreeCarrier A Q) P)) :=
  let DQ := polyCofreeCarrier A Q
  let TDQ := polyFreeMCarrier DQ P
  let fst : TDQ.left :=
    ⟨x, polyFreeMPure DQ P ⟨⟨x, d⟩, rfl⟩⟩
  let qIdx := d.head.2
  let childMor :
      polyBetweenFamily X X Q x qIdx ⟶ TDQ :=
    Over.homMk
      (fun e =>
        let y := (polyBetweenFamily X X Q x
          qIdx).hom e
        ⟨y, polyFreeMPure DQ P
          ⟨⟨y, d.children e⟩, rfl⟩⟩)
      rfl
  let snd :
      ((polyEndoFunctor X Q).obj TDQ).left :=
    ⟨x, ⟨qIdx, childMor⟩⟩
  ⟨(fst, snd), rfl⟩

/--
The leaf handler for the GSOS parameterized fold as an
`Over X` morphism from `D_Q(A)` to
`T_P(D_Q(A)) ×_X Q(T_P(D_Q(A)))`.
-/
def polyGSOSFoldLeaf
    (A : Over X) (P Q : PolyEndo X) :
    polyCofreeCarrier A Q ⟶
    overPullback
      (polyFreeMCarrier
        (polyCofreeCarrier A Q) P)
      ((polyEndoFunctor X Q).obj
        (polyFreeMCarrier
          (polyCofreeCarrier A Q) P)) :=
  Over.homMk
    (fun ⟨_, d⟩ => polyGSOSFoldLeafAt A P Q d)
    rfl

/--
The node handler for the GSOS parameterized fold.
Given a P-operation whose children are in the product
type, produce a new product element by reconstructing
the free monad node (first component) and applying the
GSOS rule then Q(mu) (second component).
-/
def polyGSOSFoldNodeAt
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) {x : X}
    (node : polyBetweenEvalFamily X X P
      (overPullback
        (polyFreeMCarrier
          (polyCofreeCarrier A Q) P)
        ((polyEndoFunctor X Q).obj
          (polyFreeMCarrier
            (polyCofreeCarrier A Q) P)))
      x) :
    overPullbackType
      (polyFreeMCarrier
        (polyCofreeCarrier A Q) P)
      ((polyEndoFunctor X Q).obj
        (polyFreeMCarrier
          (polyCofreeCarrier A Q) P)) :=
  let DQ := polyCofreeCarrier A Q
  let TDQ := polyFreeMCarrier DQ P
  let pIdx := pbefIndex node
  let childMor := pbefMor node
  let childFst :
      polyBetweenFamily X X P x pIdx ⟶ TDQ :=
    childMor ≫ overPullbackFst TDQ
      ((polyEndoFunctor X Q).obj TDQ)
  let fstElem :
      polyBetweenEvalFamily X X P TDQ x :=
    pbefMk pIdx childFst
  let fst : TDQ.left :=
    ⟨x, polyFreeMStrFamily DQ P x fstElem⟩
  let prodComp :
      overPullback TDQ
        ((polyEndoFunctor X Q).obj TDQ) ⟶
      (polyEndoFunctor X
        (polyIdBehaviorPoly Q)).obj TDQ :=
    Over.homMk
      (fun elem =>
        let t := elem.val.1
        let qEval := elem.val.2
        let y := qEval.1
        let qIdx := qEval.2.1
        let qChildMor := qEval.2.2
        let pos :
            ccrIndex ((polyIdBehaviorPoly Q) y) :=
          fun
            | Sum.inl _ => PUnit.unit
            | Sum.inr _ => qIdx
        let coprodMor :
            ccrFamily
              ((polyIdBehaviorPoly Q) y) pos ⟶
              TDQ :=
          Over.homMk
            (fun ⟨i, dir⟩ =>
              match i with
              | Sum.inl _ => t
              | Sum.inr _ => qChildMor.left dir)
            (by
              funext ⟨i, dir⟩
              match i with
              | Sum.inl _ =>
                exact elem.prop
              | Sum.inr _ =>
                exact congrFun
                  (Over.w qChildMor) dir)
        ⟨y, ⟨pos, coprodMor⟩⟩)
      (by
        funext elem
        exact elem.prop.symm)
  let nodeConv :=
    ccrEvalMap prodComp node
  let compInput :=
    (polyBetweenComp_eval_fiberEquiv
      P (polyIdBehaviorPoly Q) TDQ x).invFun
      nodeConv
  let rhoResult :=
    polyBetweenMorphEvalAt X X rho.rule
      TDQ x compInput
  let qAtTpTdq :=
    (polyBetweenComp_eval_fiberEquiv
      Q (polyFreeMPoly P) TDQ x).toFun
      rhoResult
  let join :
      polyBetweenEval X X
        (polyFreeMPoly P) TDQ ⟶ TDQ :=
    Over.homMk
      (fun ⟨x', evalElem⟩ =>
        let tree :=
          polyFreeMPolyEval_to_polyFreeM TDQ P
            evalElem
        ⟨x', polyFreeMBind TDQ DQ P tree
          (fun _ a => a.prop ▸ a.val.2)⟩)
      rfl
  let qAtTdq := ccrEvalMap join qAtTpTdq
  let snd :
      ((polyEndoFunctor X Q).obj TDQ).left :=
    ⟨x, qAtTdq⟩
  ⟨(fst, snd), rfl⟩

/--
The node handler for the GSOS parameterized fold as an
`Over X` morphism from `P(T_P(D_Q(A)) ×_X Q(T_P(D_Q(A))))`
to `T_P(D_Q(A)) ×_X Q(T_P(D_Q(A)))`.
-/
def polyGSOSFoldNode
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    (polyEndoFunctor X P).obj
      (overPullback
        (polyFreeMCarrier
          (polyCofreeCarrier A Q) P)
        ((polyEndoFunctor X Q).obj
          (polyFreeMCarrier
            (polyCofreeCarrier A Q) P))) ⟶
    overPullback
      (polyFreeMCarrier
        (polyCofreeCarrier A Q) P)
      ((polyEndoFunctor X Q).obj
        (polyFreeMCarrier
          (polyCofreeCarrier A Q) P)) :=
  Over.homMk
    (fun ⟨_, node⟩ =>
      polyGSOSFoldNodeAt A P Q rho node)
    rfl

/--
The GSOS fold with fiber proof: a catamorphism on
`PolyFreeM DQ P` that maps each free monad element to a
pair in `T_P(D_Q(A)) ×_X Q(T_P(D_Q(A)))` together with
a proof that the output fiber matches the input fiber.
-/
def polyGSOSFoldCataWithFiber
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) {x : X}
    (t : PolyFreeM (polyCofreeCarrier A Q) P x) :
    { result :
        overPullbackType
          (polyFreeMCarrier
            (polyCofreeCarrier A Q) P)
          ((polyEndoFunctor X Q).obj
            (polyFreeMCarrier
              (polyCofreeCarrier A Q) P)) //
      (polyFreeMCarrier
        (polyCofreeCarrier A Q) P).hom
        result.val.1 = x } :=
  match t with
  | PolyFix.mk _ (Sum.inl ⟨⟨_, d⟩, rfl⟩) _ =>
    ⟨polyGSOSFoldLeafAt A P Q d, rfl⟩
  | PolyFix.mk _ (Sum.inr pIdx) children =>
    let Prod :=
      overPullback
        (polyFreeMCarrier
          (polyCofreeCarrier A Q) P)
        ((polyEndoFunctor X Q).obj
          (polyFreeMCarrier
            (polyCofreeCarrier A Q) P))
    let childResults :
        polyBetweenFamily X X P x pIdx ⟶ Prod :=
      Over.homMk
        (fun e =>
          (polyGSOSFoldCataWithFiber
            A P Q rho (children e)).val)
        (funext fun e =>
          (polyGSOSFoldCataWithFiber
            A P Q rho (children e)).prop)
    let node :
        polyBetweenEvalFamily X X P Prod x :=
      pbefMk pIdx childResults
    ⟨polyGSOSFoldNodeAt A P Q rho node, rfl⟩

/--
The GSOS fold as a pointwise map from the free monad
carrier to the product type.
-/
def polyGSOSFoldCataAt
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) {x : X}
    (t : PolyFreeM (polyCofreeCarrier A Q) P x) :
    overPullbackType
      (polyFreeMCarrier
        (polyCofreeCarrier A Q) P)
      ((polyEndoFunctor X Q).obj
        (polyFreeMCarrier
          (polyCofreeCarrier A Q) P)) :=
  (polyGSOSFoldCataWithFiber A P Q rho t).val

/--
The GSOS fold as an `Over X` morphism from `T_P(D_Q(A))`
to `T_P(D_Q(A)) ×_X Q(T_P(D_Q(A)))`.
-/
def polyGSOSFoldCata
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    polyFreeMCarrier (polyCofreeCarrier A Q) P ⟶
    overPullback
      (polyFreeMCarrier
        (polyCofreeCarrier A Q) P)
      ((polyEndoFunctor X Q).obj
        (polyFreeMCarrier
          (polyCofreeCarrier A Q) P)) :=
  Over.homMk
    (fun ⟨_, t⟩ =>
      polyGSOSFoldCataAt A P Q rho t)
    (funext fun ⟨_, t⟩ =>
      (polyGSOSFoldCataWithFiber
        A P Q rho t).prop)

end GebLean
