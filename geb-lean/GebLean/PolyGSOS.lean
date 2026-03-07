import GebLean.PolyDistributiveLaw
import GebLean.PolyUMorph
import GebLean.Utilities.GSOSRule
import GebLean.Utilities.LambdaBialgebra

namespace GebLean

open CategoryTheory

universe u

variable {X : Type u}

@[simp]
lemma sigma_fst_eqRec {I : Type*}
    {F : I → Type*}
    {G : (i : I) → F i → Type*}
    {i₁ i₂ : I} (h : i₁ = i₂)
    (b : F i₁) (c : G i₁ b) :
    (h ▸ ⟨b, c⟩ :
      (a : F i₂) × G i₂ a).fst =
    (h ▸ b : F i₂) := by
  subst h; rfl

@[simp]
lemma ptoef_fst_eqRec
    {D : Type*} [Category D] {Y : Type*}
    (P : PolyToOverCat (D := D) Y) (A : D)
    {y₁ y₂ : Y} (h : y₁ = y₂)
    (ev : polyToOverEvalFamily Y P A y₁) :
    (h ▸ ev :
      polyToOverEvalFamily Y P A y₂).fst =
    h ▸ ev.fst := by
  subst h; rfl

@[simp]
lemma eqRec_dep_piApply
    {Y : Type*} {y₁ y₂ : Y}
    (h : y₁ = y₂)
    {I : Type*}
    {F : I → Y → Type*}
    (f : (i : I) → F i y₁) (i : I) :
    (h ▸ f : (i : I) → F i y₂) i =
    (h ▸ f i : F i y₂) := by
  subst h; rfl

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
The pairing morphism that identifies the fiber product
`A ×_X Q(A)` with the evaluation of the behavior
polynomial `(Id × Q)(A)`.

Given an element `(a, (y, qIdx, qMor))` of the pullback
(where `A.hom a = y`), produce the `(Id × Q)` evaluation
`(y, pos, coprodMor)` where `pos` selects `PUnit` for the
identity component and `qIdx` for the Q component, and
`coprodMor` routes identity directions to `a` and Q
directions to `qMor`.
-/
def overPullbackToIdQEval
    (Q : PolyEndo X) (A : Over X) :
    overPullback A
      ((polyEndoFunctor X Q).obj A) ⟶
    (polyEndoFunctor X
      (polyIdBehaviorPoly Q)).obj A :=
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
            A :=
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

/--
The join morphism for free monad evaluations: given a
Q-evaluation element `(x, (shape, mor))` where `mor`
maps leaf positions into `T_P(A)`, convert the shape
to a `T_P(T_P(A))` tree and join it to `T_P(A)`.

This is the evaluation-level version of the monadic
multiplication `mu : T_P(T_P(A)) → T_P(A)`.
-/
def polyFreeMJoinEval
    (A : Over X) (P : PolyEndo X) :
    polyBetweenEval X X (polyFreeMPoly P)
      (polyFreeMCarrier A P) ⟶
    polyFreeMCarrier A P :=
  Over.homMk
    (fun ⟨x, evalElem⟩ =>
      ⟨x, polyFreeMJoinMor A P
        (polyFreeMPolyEval_to_polyFreeM
          (polyFreeMCarrier A P) P
          evalElem)⟩)
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
  let nodeConv :=
    ccrEvalMap (overPullbackToIdQEval Q TDQ) node
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
  let qAtTdq :=
    ccrEvalMap (polyFreeMJoinEval DQ P) qAtTpTdq
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

/--
The `polyScale(T_P(A), Q)`-coalgebra structure on
`T_P(D_Q(A))` at a fiber element.  The annotation is
obtained by applying `T_P(epsilon_Q)` (mapping each
cofree leaf to its root annotation), and the Q-structure
comes from the GSOS fold's second projection.
-/
def polyGSOSScaleCoalgStrAt
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) {x : X}
    (t : PolyFreeM
      (polyCofreeCarrier A Q) P x) :
    polyBetweenEvalFamily X X
      (polyScale (polyFreeMCarrier A P) Q)
      (polyFreeMCarrier
        (polyCofreeCarrier A Q) P) x :=
  let DQ := polyCofreeCarrier A Q
  let TDQ := polyFreeMCarrier DQ P
  let TA := polyFreeMCarrier A P
  let foldWithFiber :=
    polyGSOSFoldCataWithFiber A P Q rho t
  let foldResult := foldWithFiber.val
  let fiberEq := foldWithFiber.prop
  let qEval := foldResult.val.2
  let qFiber := qEval.1
  let qFiberEq : qFiber = x :=
    foldResult.prop.symm.trans fiberEq
  let qEvalAtX :
      polyBetweenEvalFamily X X Q TDQ x :=
    qFiberEq ▸ qEval.2
  let annotation :
      { a : TA.left // TA.hom a = x } :=
    ⟨⟨x, polyFreeMapAt DQ A P
      (polyCofreeCounit A Q) x t⟩, rfl⟩
  ⟨(annotation, qEvalAtX.1), qEvalAtX.2⟩

/--
The `polyScale(T_P(A), Q)`-coalgebra structure map on
`T_P(D_Q(A))` as an `Over X` morphism.
-/
def polyGSOSScaleCoalgStr
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    polyFreeMCarrier (polyCofreeCarrier A Q) P ⟶
    (polyEndoFunctor X
      (polyScale (polyFreeMCarrier A P) Q)).obj
      (polyFreeMCarrier
        (polyCofreeCarrier A Q) P) :=
  Over.homMk
    (fun ⟨x, t⟩ =>
      ⟨x, polyGSOSScaleCoalgStrAt A P Q rho t⟩)
    rfl

/--
The `polyScale(T_P(A), Q)`-coalgebra on `T_P(D_Q(A))`
induced by a GSOS rule.
-/
def polyGSOSScaleCoalg
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    PolyCoalg
      (polyScale (polyFreeMCarrier A P) Q) where
  V := polyFreeMCarrier
    (polyCofreeCarrier A Q) P
  str := polyGSOSScaleCoalgStr A P Q rho

/--
The GSOS distributive law morphism at a given object
`A : Over X`.  Maps `T_P(D_Q(A))` to `D_Q(T_P(A))`
by unfolding the `polyScale` coalgebra into the cofree
comonad.
-/
def polyGSOSDistLawMor
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    polyFreeMCarrier (polyCofreeCarrier A Q) P ⟶
    polyCofreeCarrier (polyFreeMCarrier A P) Q :=
  polyCofixUnfold
    (polyScale (polyFreeMCarrier A P) Q)
    (polyGSOSScaleCoalg A P Q rho)

lemma polyGSOSDistLawMor_head_fst
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) {x : X}
    (t : PolyFreeM (polyCofreeCarrier A Q) P x) :
    let m := polyCofixUnfoldAt
      (polyScale (polyFreeMCarrier A P) Q)
      (polyGSOSScaleCoalg A P Q rho)
      x ⟨⟨x, t⟩, rfl⟩
    (polyCofreeExtract
      (polyFreeMCarrier A P) Q m).val =
    ⟨x, polyFreeMapAt
      (polyCofreeCarrier A Q) A P
      (polyCofreeCounit A Q) x t⟩ := by
  simp only [polyCofreeExtract, PolyCofix.head,
    polyCofixUnfoldAt, polyCofixUnfoldApprox]
  simp only [polyGSOSScaleCoalg,
    polyGSOSScaleCoalgStr, Over.homMk_left]
  simp only [PolyCofixApprox.getIndex,
    polyGSOSScaleCoalgStrAt]

lemma polyGSOSDistLaw_counit
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    polyGSOSDistLawMor A P Q rho ≫
    polyCofreeCounit (polyFreeMCarrier A P) Q =
    polyFreeMap
      (polyCofreeCarrier A Q) A P
      (polyCofreeCounit A Q) := by
  apply Over.OverMorphism.ext
  funext ⟨x, t⟩
  simp only [Over.comp_left, types_comp_apply,
    polyGSOSDistLawMor, polyCofixUnfold,
    Over.homMk_left, polyCofixUnfoldLeft,
    polyCofreeCounit, polyCofreeCounitLeft,
    polyFreeMap, polyFreeMapLeft]
  exact polyGSOSDistLawMor_head_fst A P Q rho t

lemma polyGSOSDistLaw_unit_approx
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) {x : X}
    (m : PolyCofreeM A Q x) (n : Nat) :
    polyCofixUnfoldApprox
      (polyScale (polyFreeMCarrier A P) Q)
      (polyGSOSScaleCoalg A P Q rho) n x
      ⟨⟨x, polyFreeMPure
        (polyCofreeCarrier A Q) P
        ⟨⟨x, m⟩, rfl⟩⟩, rfl⟩ =
    polyCofreeMapApprox A
      (polyFreeMCarrier A P) Q
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
      simp only [polyCofixUnfoldApprox,
        polyGSOSScaleCoalg,
        polyGSOSScaleCoalgStr,
        Over.homMk_left,
        polyGSOSScaleCoalgStrAt,
        polyGSOSFoldCataWithFiber,
        polyGSOSFoldLeafAt,
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

lemma polyGSOSDistLaw_unit
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) :
    polyFreeUnit (polyCofreeCarrier A Q) P ≫
    polyGSOSDistLawMor A P Q rho =
    polyCofreeMap A
      (polyFreeMCarrier A P) Q
      (polyFreeUnit A P) := by
  apply Over.OverMorphism.ext
  funext ⟨x, m⟩
  simp only [Over.comp_left, types_comp_apply,
    polyFreeUnit, Over.homMk_left,
    polyFreeUnitLeft,
    polyGSOSDistLawMor, polyCofixUnfold,
    polyCofixUnfoldLeft,
    polyCofreeMap, polyCofreeMapLeft]
  apply Sigma.ext
  · rfl
  · simp only [heq_eq_eq, polyCofreeMapAt]
    apply PolyCofix.ext
    intro n
    exact polyGSOSDistLaw_unit_approx
      A P Q rho m n

lemma polyGSOSDistLaw_annot_natural
    (A B : Over X) (P Q : PolyEndo X)
    (f : A ⟶ B) {x : X}
    (t : PolyFreeM (polyCofreeCarrier A Q) P x) :
    polyFreeMapAt
      (polyCofreeCarrier B Q) B P
      (polyCofreeCounit B Q) x
      (polyFreeMapAt
        (polyCofreeCarrier A Q)
        (polyCofreeCarrier B Q) P
        (polyCofreeMap A B Q f) x t) =
    polyFreeMapAt A B P f x
      (polyFreeMapAt
        (polyCofreeCarrier A Q) A P
        (polyCofreeCounit A Q) x t) := by
  rw [← polyFreeMapAt_comp]
  rw [← polyFreeMapAt_comp]
  congr 1
  exact polyCofreeCounit_naturality A B Q f

lemma polyGSOSFoldCata_snd_fst_eq
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) {x : X}
    (t : PolyFreeM (polyCofreeCarrier A Q) P x) :
    (polyGSOSFoldCataWithFiber
      A P Q rho t).val.val.2.1 = x :=
  match t with
  | PolyFix.mk _ (Sum.inl ⟨⟨_, _⟩, rfl⟩) _ => rfl
  | PolyFix.mk _ (Sum.inr _) _ => rfl

/--
The Q-index that the GSOS pipeline produces for a node,
computed purely from the P-index and per-child Q-indices.
This does not depend on the carrier `A`.
-/
def polyGSOSNodeQIdx
    (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) {x : X}
    (p : polyBetweenIndex X X P x)
    (childQIdx :
      (e : (ccrFamily (P x) p).left) →
      polyBetweenIndex X X Q
        ((ccrFamily (P x) p).hom e)) :
    polyBetweenIndex X X Q x :=
  let innerIdx :
      (e : (ccrFamily (P x) p).left) →
      ccrIndex ((polyIdBehaviorPoly Q)
        ((ccrFamily (P x) p).hom e)) :=
    fun e => fun
      | Sum.inl _ => PUnit.unit
      | Sum.inr _ => childQIdx e
  let compIdx :
      ccrIndex
        (polyBetweenComp P
          (polyIdBehaviorPoly Q) x) :=
    ⟨p, innerIdx⟩
  (ccrReindex (rho.rule x) compIdx).1

def polyGSOSFoldQIndex
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) {x : X}
    (t : PolyFreeM
      (polyCofreeCarrier A Q) P x) :
    polyBetweenIndex X X Q x :=
  (polyGSOSFoldCata_snd_fst_eq
    A P Q rho t) ▸
  (polyGSOSFoldCataWithFiber
    A P Q rho t).val.val.2.2.1

lemma polyGSOSFoldQIndex_leaf
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) {x : X}
    (d : PolyCofreeM A Q x) :
    polyGSOSFoldQIndex A P Q rho
      (polyFreeMPure
        (polyCofreeCarrier A Q) P
        ⟨⟨x, d⟩, rfl⟩) =
    d.head.2 := by
  simp only [polyGSOSFoldQIndex,
    polyFreeMPure,
    polyGSOSFoldCataWithFiber,
    polyGSOSFoldLeafAt]

lemma polyGSOSFoldQIndex_node_unfold
    (A : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) {x : X}
    (p : polyBetweenIndex X X P x)
    (children :
      (e : (ccrFamily (P x) p).left) →
        PolyFreeM
          (polyCofreeCarrier A Q) P
          ((ccrFamily (P x) p).hom e)) :
    polyGSOSFoldQIndex A P Q rho
      (PolyFix.mk x (Sum.inr p) children) =
    polyGSOSNodeQIdx P Q rho p
      (fun e => polyGSOSFoldQIndex A P Q rho
        (children e)) := by
  simp only [polyGSOSFoldQIndex,
    polyGSOSFoldCataWithFiber,
    polyGSOSNodeQIdx]
  dsimp only [polyGSOSFoldNodeAt,
    overPullbackToIdQEval,
    polyFreeMJoinEval,
    ccrEvalMap, ccrEvalMk,
    ccrEvalIndex, ccrEvalMor,
    polyBetweenComp_eval_fiberEquiv,
    polyBetweenComp_eval_fiberEquiv_toFun,
    polyBetweenComp_eval_fiberEquiv_invFun,
    polyBetweenMorphEvalAt,
    pbefMk, pbefIndex, pbefMor,
    ptoefMk, ptoefIndex, ptoefMor,
    ccrReindex, ccrFiberMor,
    mor_to_pbe_fiber_index,
    mor_to_ptoe_fiber_index,
    mor_to_ptoe_fiber,
    ptoeLeftFiber]
  simp only [ptoef_fst_eqRec]
  apply congrArg Sigma.fst
  apply congrArg (rho.rule x).base
  apply congrArg (Sigma.mk p)
  funext eg
  simp only [CategoryTheory.Over.comp_left,
    CategoryTheory.Over.homMk_left,
    CategoryTheory.types_comp,
    Function.comp_apply]
  funext i
  match i with
  | Sum.inl _ =>
    rfl
  | Sum.inr _ =>
    rw [eqRec_dep_piApply]

lemma polyGSOSFoldQIndex_eq_node
    (A B : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) (f : A ⟶ B)
    {x : X} (p : polyBetweenIndex X X P x)
    (children :
      (e : (ccrFamily (P x) p).left) →
        PolyFreeM
          (polyCofreeCarrier A Q) P
          ((ccrFamily (P x) p).hom e))
    (ih :
      ∀ (e : (ccrFamily (P x) p).left),
        polyGSOSFoldQIndex B P Q rho
          (polyFreeMapAt
            (polyCofreeCarrier A Q)
            (polyCofreeCarrier B Q) P
            (polyCofreeMap A B Q f)
            ((ccrFamily (P x) p).hom e)
            (children e)) =
        polyGSOSFoldQIndex A P Q rho
          (children e)) :
    polyGSOSFoldQIndex B P Q rho
      (polyFreeMapAt
        (polyCofreeCarrier A Q)
        (polyCofreeCarrier B Q) P
        (polyCofreeMap A B Q f) x
        (PolyFix.mk x (Sum.inr p) children)) =
    polyGSOSFoldQIndex A P Q rho
      (PolyFix.mk x (Sum.inr p) children) := by
  simp only [polyFreeMapAt, polyFreeMBind]
  rw [polyGSOSFoldQIndex_node_unfold B]
  rw [polyGSOSFoldQIndex_node_unfold A]
  congr 1
  funext e
  exact ih e

lemma polyGSOSFoldQIndex_eq
    (A B : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) (f : A ⟶ B)
    {x : X}
    (t : PolyFreeM
      (polyCofreeCarrier A Q) P x) :
    polyGSOSFoldQIndex B P Q rho
      (polyFreeMapAt
        (polyCofreeCarrier A Q)
        (polyCofreeCarrier B Q) P
        (polyCofreeMap A B Q f) x t) =
    polyGSOSFoldQIndex A P Q rho t := by
  induction t with
  | mk x i children ih =>
    match i with
    | Sum.inl ⟨⟨_, d⟩, rfl⟩ =>
      simp only [polyFreeMapAt, polyFreeMBind,
        polyGSOSFoldQIndex,
        polyGSOSFoldCataWithFiber,
        polyGSOSFoldLeafAt]
      exact polyCofreeMapAt_head_snd A B Q f d
    | Sum.inr p =>
      exact polyGSOSFoldQIndex_eq_node
        A B P Q rho f p children ih

private lemma polyFix_leaf_heq_of_val_eq
    {A : Over X} {P : PolyEndo X}
    {x y : X}
    (a : { v : A.left // A.hom v = x })
    (b : { v : A.left // A.hom v = y })
    (hab : a.val = b.val) :
    HEq
      (PolyFix.mk x (Sum.inl a)
        (fun e => PEmpty.elim e) :
        PolyFix (polyTranslate A P) x)
      (PolyFix.mk y (Sum.inl b)
        (fun e => PEmpty.elim e) :
        PolyFix (polyTranslate A P) y) := by
  have hxy : x = y := by
    rw [← a.property, ← b.property]
    exact congrArg A.hom hab
  subst hxy
  have : a = b := Subtype.ext hab
  subst this
  exact HEq.rfl

private lemma polyFreeMBind_cast
    (A B : Over X) (P : PolyEndo X)
    {x y : X} (h : x = y)
    (t : PolyFreeM A P x)
    (g : ∀ z,
      { a : A.left // A.hom a = z } →
        PolyFreeM B P z) :
    polyFreeMBind A B P (h ▸ t) g =
    h ▸ polyFreeMBind A B P t g := by
  subst h; rfl

private lemma polyFreeMStrFamily_natural
    (A B : Over X) (P : PolyEndo X)
    (f : A ⟶ B) (x : X)
    (p : polyBetweenIndex X X P x)
    (childFstA :
      polyBetweenFamily X X P x p ⟶
        polyFreeMCarrier A P) :
    polyFreeMStrFamily B P x
      (pbefMk p
        (childFstA ≫ polyFreeMap A B P f)) =
    polyFreeMapAt A B P f x
      (polyFreeMStrFamily A P x
        (pbefMk p childFstA)) := by
  simp only [polyFreeMStrFamily, pbefMk_mor]
  conv_rhs =>
    simp only [polyFreeMapAt, polyFreeMBind]
  congr 1
  funext e
  simp only [Over.comp_left, polyFreeMap,
    Over.homMk_left, types_comp_apply,
    polyFreeMapLeft, polyFreeMapAt]
  exact (polyFreeMBind_cast _ _ _ _ _ _).symm

private lemma polyGSOSFoldLeafAt_snd_natural
    (A B : Over X) (P Q : PolyEndo X)
    (f : A ⟶ B) {x : X}
    (d : PolyCofreeM A Q x) :
    let DQ_A := polyCofreeCarrier A Q
    let DQ_B := polyCofreeCarrier B Q
    let freeMap :=
      polyFreeMap DQ_A DQ_B P
        (polyCofreeMap A B Q f)
    ((polyEndoFunctor X Q).map freeMap).left
      (polyGSOSFoldLeafAt A P Q d).val.2 =
    (polyGSOSFoldLeafAt B P Q
      (polyCofreeMapAt A B Q f d)).val.2 := by
  simp only [polyGSOSFoldLeafAt,
    polyEndoFunctor, polyBetweenEvalFunctor,
    polyToOverFunctor, polyToOverEvalMap_left,
    ccrEvalMap]
  have hidx :=
    (polyCofreeMapAt_head_snd A B Q f d).symm
  exact Sigma.ext rfl (heq_of_eq
    (Sigma.ext hidx (by
      apply polyBetweenFamily_mor_heq rfl _ _
        (heq_of_eq hidx)
      simp only [Over.comp_left, Over.homMk_left,
        polyFreeMap]
      apply Function.hfunext
        (congrArg (fun q =>
          (polyBetweenFamily X X Q x q).left)
          hidx)
      intro e₁ e₂ he
      simp only [types_comp_apply]
      apply heq_of_eq
      simp only [polyFreeMapLeft,
        polyFreeMapAt, polyFreeM_pure_bind,
        polyCofreeMap]
      have hhom := overType_hom_heq
        (congrArg (polyBetweenFamily X X Q x)
          hidx)
        e₁ e₂ he
      have hchild :=
        polyCofreeMapAt_children_heq
          A B Q f d e₁ e₂ he
      dsimp only [Over.homMk_left,
        polyCofreeMapLeft]
      let mkLeaf :
          (polyCofreeCarrier B Q).left →
          (polyFreeMCarrier
            (polyCofreeCarrier B Q) P).left :=
        fun v =>
          ⟨(polyCofreeCarrier B Q).hom v,
            polyFreeMPure
              (polyCofreeCarrier B Q) P
              ⟨v, rfl⟩⟩
      have hval :=
        @Sigma.ext X
          (fun y => PolyCofreeM B Q y)
          ⟨_, polyCofreeMapAt A B Q f
            (PolyCofix.children d e₁)⟩
          ⟨_, PolyCofix.children
            (polyCofreeMapAt A B Q f d) e₂⟩
          hhom hchild
      convert congrArg mkLeaf hval using 1)))

private abbrev GSOSFreeMap
    (A B : Over X) (P Q : PolyEndo X)
    (f : A ⟶ B) :
    polyFreeMCarrier (polyCofreeCarrier A Q) P ⟶
    polyFreeMCarrier (polyCofreeCarrier B Q) P :=
  polyFreeMap (polyCofreeCarrier A Q)
    (polyCofreeCarrier B Q) P
    (polyCofreeMap A B Q f)

private abbrev GSOSQMap
    (A B : Over X) (P Q : PolyEndo X)
    (f : A ⟶ B) :
    (polyEndoFunctor X Q).obj
      (polyFreeMCarrier
        (polyCofreeCarrier A Q) P) ⟶
    (polyEndoFunctor X Q).obj
      (polyFreeMCarrier
        (polyCofreeCarrier B Q) P) :=
  (polyEndoFunctor X Q).map
    (GSOSFreeMap A B P Q f)

private abbrev GSOSNodeChildren
    (A : Over X) (P Q : PolyEndo X) {y : X}
    (p : polyBetweenIndex X X P y) :=
  (e : (polyBetweenFamily X X
      (polyTranslate
        (polyCofreeCarrier A Q) P)
      y (Sum.inr p)).left) →
    PolyFreeM (polyCofreeCarrier A Q) P
      ((polyBetweenFamily X X
        (polyTranslate
          (polyCofreeCarrier A Q) P)
        y (Sum.inr p)).hom e)

private lemma polyGSOSFoldFst_natural
    (A B : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) (f : A ⟶ B)
    {x : X}
    (t : PolyFreeM
      (polyCofreeCarrier A Q) P x) :
    (polyGSOSFoldCataWithFiber B P Q rho
      (polyFreeMapAt
        (polyCofreeCarrier A Q)
        (polyCofreeCarrier B Q) P
        (polyCofreeMap A B Q f) x t)).val.val.1 =
    (polyFreeMap
      (polyCofreeCarrier A Q)
      (polyCofreeCarrier B Q) P
      (polyCofreeMap A B Q f)).left
      (polyGSOSFoldCataWithFiber
        A P Q rho t).val.val.1 := by
  induction t with
  | mk y idx children ih =>
    match idx with
    | Sum.inl ⟨⟨_, d⟩, rfl⟩ =>
      simp only [polyFreeMapAt, polyFreeMBind,
        polyGSOSFoldCataWithFiber,
        polyGSOSFoldLeafAt,
        polyFreeMap, Over.homMk_left,
        polyFreeMapLeft]
      rw [polyFreeM_pure_bind]
      simp only [polyCofreeMap, Over.homMk_left,
        polyCofreeMapLeft]
      rfl
    | Sum.inr p =>
      simp only [polyGSOSFoldCataWithFiber,
        polyGSOSFoldNodeAt,
        polyFreeMap, Over.homMk_left,
        polyFreeMapLeft]
      apply congrArg (Sigma.mk y)
      simp only [pbefMk_index, pbefMk_mor]
      rw [← polyFreeMStrFamily_natural
        (polyCofreeCarrier A Q)
        (polyCofreeCarrier B Q) P
        (polyCofreeMap A B Q f) y p]
      congr 1; congr 1
      apply Over.OverMorphism.ext
      funext e
      simp only [Over.comp_left, types_comp_apply,
        polyFreeMap, Over.homMk_left,
        polyFreeMapLeft, overPullbackFst]
      have := ih e
      simp only [polyFreeMapAt, polyFreeMap,
        Over.homMk_left, polyFreeMapLeft] at this
      exact this

private lemma eqRec_sigma_fst_irrel
    {α : Type u} {I : α → Type u}
    {F : (a : α) → I a → Type u}
    {G : (a : α) → I a → Type u}
    {a b : α} {p₁ p₂ : a = b}
    {i : I a} {m₁ : F a i} {m₂ : G a i} :
    (@Eq.rec α a (fun x _ => Σ j : I x, F x j)
      ⟨i, m₁⟩ b p₁).fst =
    (@Eq.rec α a (fun x _ => Σ j : I x, G x j)
      ⟨i, m₂⟩ b p₂).fst := by
  subst p₁; rfl

private lemma subst_sigma_fst_irrel
    {α : Type u} {I : α → Type u}
    {F : (a : α) → I a → Type u}
    {G : (a : α) → I a → Type u}
    {a b : α} (p₁ p₂ : a = b)
    (i : I a) (m₁ : F a i) (m₂ : G a i) :
    (p₁ ▸ (⟨i, m₁⟩ : Σ j, F a j)).fst =
    (p₂ ▸ (⟨i, m₂⟩ : Σ j, G a j)).fst := by
  subst p₁; rfl

private lemma mor_to_pbe_fiber_index_postcomp
    (f : PolyEndo X) (A B : Over X)
    {C : Over X} (hMor : C ⟶ polyBetweenEval X X f A)
    (h : A ⟶ B) (c : C.left) :
    mor_to_pbe_fiber_index hMor c =
    mor_to_pbe_fiber_index
      (hMor ≫ polyToOverEvalMap X f h) c := by
  simp only [mor_to_pbe_fiber_index,
    mor_to_ptoe_fiber_index, ptoefIndex,
    ccrEvalIndex, mor_to_ptoe_fiber,
    ptoeLeftFiber, Over.comp_left,
    types_comp_apply, polyToOverEvalMap_left,
    ccrEvalMap]
  obtain ⟨i, m⟩ := (hMor.left c).snd
  simp only []
  simp only [ptoef_fst_eqRec]

private lemma ccrEvalMap_eqRec
    {Y : Type u}
    {F : Y → ↑(CoprodCovarRepCat (Over X))}
    {A B : Over X} (h : A ⟶ B) {y₁ y₂ : Y}
    (p : y₁ = y₂) (v : ccrEval (F y₁) A) :
    ccrEvalMap h (p ▸ v) = p ▸ ccrEvalMap h v := by
  subst p; rfl

private lemma mor_to_pbe_fiber_postcomp_eq
    (f : PolyEndo X) (A B : Over X)
    {C : Over X}
    (hMor : C ⟶ polyBetweenEval X X f A)
    (h : A ⟶ B) (c : C.left) :
    ccrEvalMap h (mor_to_pbe_fiber hMor c) =
    mor_to_pbe_fiber
      (hMor ≫ polyToOverEvalMap X f h) c := by
  unfold mor_to_pbe_fiber mor_to_ptoe_fiber
  generalize mor_to_ptoe_y X hMor c = p₁
  erw [ccrEvalMap_eqRec h p₁
    (ptoeLeftFiber X (hMor.left c))]
  rfl

private lemma polyBetweenComp_eval_invFun_natural
    (g f : PolyEndo X)
    (A B : Over X) (h : A ⟶ B) (z : X)
    (v : polyBetweenEvalFamily X X g
      (polyBetweenEval X X f A) z) :
    ccrEvalMap h
      ((polyBetweenComp_eval_fiberEquiv
        g f A z).invFun v) =
    (polyBetweenComp_eval_fiberEquiv
      g f B z).invFun
      (ccrEvalMap
        ((polyEndoFunctor X f).map h) v) := by
  obtain ⟨ig, hMor⟩ := v
  simp only [ccrEvalMap,
    polyEndoFunctor, polyBetweenEvalFunctor,
    polyToOverFunctor]
  unfold polyBetweenComp_eval_fiberEquiv
  simp only [polyBetweenComp_eval_fiberEquiv_invFun,
    pbefIndex, pbefMor, ptoefIndex, ptoefMor]
  simp only [ccrEvalIndex, ccrEvalMor]
  have h_fiber : ∀ eg,
      ccrEvalMap h (mor_to_pbe_fiber hMor eg) =
      mor_to_pbe_fiber
        (hMor ≫ polyToOverEvalMap X f h) eg :=
    fun eg =>
      mor_to_pbe_fiber_postcomp_eq f A B hMor h eg
  let build :
      (∀ (eg : (ccrFamily (g z) ig).left),
        polyBetweenEvalFamily X X f B
          ((ccrFamily (g z) ig).hom eg)) →
      ccrEval ((polyBetweenComp g f) z) B :=
    fun fiber =>
      ⟨⟨ig, fun eg => ptoefIndex X (fiber eg)⟩,
       Over.homMk
         (fun ⟨eg, ef⟩ =>
           (ptoefMor X (fiber eg)).left ef)
         (by
           funext ⟨eg, ef⟩
           exact congrFun
             (Over.w (ptoefMor X (fiber eg))) ef)⟩
  change build (fun eg =>
      ccrEvalMap h (mor_to_pbe_fiber hMor eg)) =
    build (fun eg =>
      mor_to_pbe_fiber
        (hMor ≫ polyToOverEvalMap X f h) eg)
  exact congrArg build (funext h_fiber)

private lemma ccrEvalMap_comp_apply
    {D : Type u} [Category D]
    {P : CoprodCovarRepCat D} {A B C : D}
    (f : A ⟶ B) (g : B ⟶ C)
    (x : ccrEval P A) :
    ccrEvalMap g (ccrEvalMap f x) =
    ccrEvalMap (f ≫ g) x :=
  (congrFun (ccrEvalMap_comp f g) x).symm

private lemma morphEvalAt_ccrEvalMap_comm
    {P Q : PolyFunctorBetweenCat X X}
    (α : P ⟶ Q)
    {A B : Over X} (h : A ⟶ B) (y : X)
    (v : polyBetweenEvalFamily X X P A y) :
    ccrEvalMap h
      (polyBetweenMorphEvalAt X X α A y v) =
    polyBetweenMorphEvalAt X X α B y
      (ccrEvalMap h v) := by
  obtain ⟨idx, mor⟩ := v
  simp only [polyBetweenMorphEvalAt,
    ccrEvalMap, ptoefMk, ptoefIndex, ptoefMor,
    ccrEvalMk, ccrEvalIndex, ccrEvalMor,
    ccrReindex, ccrFiberMor,
    CategoryTheory.Category.assoc]

private lemma polyBetweenComp_eval_toFun_natural
    (g f : PolyEndo X)
    (A B : Over X) (h : A ⟶ B) (z : X)
    (v : polyBetweenEvalFamily X X
      (polyBetweenComp g f) A z) :
    ccrEvalMap
      ((polyEndoFunctor X f).map h)
      ((polyBetweenComp_eval_fiberEquiv
        g f A z).toFun v) =
    (polyBetweenComp_eval_fiberEquiv
      g f B z).toFun
      (ccrEvalMap h v) := by
  obtain ⟨⟨ig, pf⟩, mor⟩ := v
  simp only [polyBetweenComp_eval_fiberEquiv,
    polyBetweenComp_eval_fiberEquiv_toFun,
    ccrEvalMap, polyEndoFunctor,
    polyBetweenEvalFunctor, polyToOverFunctor]
  congr 1

private lemma overPullbackToIdQEval_comm
    (Q : PolyEndo X) (A B : Over X) (g : A ⟶ B) :
    overPullbackToIdQEval Q A ≫
      (polyEndoFunctor X
        (polyIdBehaviorPoly Q)).map g =
    overPullbackMap g
      ((polyEndoFunctor X Q).map g) ≫
      overPullbackToIdQEval Q B := by
  apply Over.OverMorphism.ext
  funext ⟨⟨a, ⟨z, qIdx, qMor⟩⟩, hfib⟩
  simp only [Over.comp_left, types_comp_apply,
    overPullbackToIdQEval, Over.homMk_left,
    overPullbackMap, polyEndoFunctor,
    polyBetweenEvalFunctor, polyToOverFunctor,
    polyToOverEvalMap_left, ccrEvalMap]
  congr 1; congr 1
  apply Over.OverMorphism.ext
  funext ⟨i, dir⟩
  match i with
  | Sum.inl _ => rfl
  | Sum.inr _ => rfl

private lemma polyFreeMJoinEval_natural
    (A B : Over X) (P : PolyEndo X)
    (g : A ⟶ B) :
    polyFreeMJoinEval A P ≫
      polyFreeMap A B P g =
    (polyEndoFunctor X (polyFreeMPoly P)).map
      (polyFreeMap A B P g) ≫
    polyFreeMJoinEval B P := by
  apply Over.OverMorphism.ext
  funext ⟨x, eval⟩
  simp only [Over.comp_left, types_comp_apply,
    polyFreeMJoinEval, Over.homMk_left,
    polyFreeMap, polyFreeMapLeft,
    polyEndoFunctor, polyBetweenEvalFunctor,
    polyToOverFunctor, polyToOverEvalMap_left,
    ccrEvalMap]
  apply congrArg (Sigma.mk x)
  rw [polyFreeMJoinMor_nat]
  congr 1
  exact polyFreeMPolyEval_to_M_natural
    (polyFreeMCarrier A P)
    (polyFreeMCarrier B P)
    P (polyFreeMap A B P g) eval

private lemma polyGSOSFoldNodeAt_snd_natural
    (A B : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) (f : A ⟶ B)
    {y : X}
    (p : polyBetweenIndex X X P y)
    (children :
      GSOSNodeChildren A P Q p)
    (ih : ∀ (e : (polyBetweenFamily X X
        (polyTranslate
          (polyCofreeCarrier A Q) P)
        y (Sum.inr p)).left),
      (GSOSQMap A B P Q f).left
        (polyGSOSFoldCataWithFiber
          A P Q rho (children e)).val.val.2 =
      (polyGSOSFoldCataWithFiber
        B P Q rho
        (polyFreeMapAt
          (polyCofreeCarrier A Q)
          (polyCofreeCarrier B Q) P
          (polyCofreeMap A B Q f)
          _ (children e))).val.val.2) :
    (GSOSQMap A B P Q f).left
      (polyGSOSFoldNodeAt A P Q rho
        (pbefMk p (Over.homMk
          (fun e =>
            (polyGSOSFoldCataWithFiber
              A P Q rho (children e)).val)
          (funext fun e =>
            (polyGSOSFoldCataWithFiber
              A P Q rho
              (children e)).prop)))).val.2 =
    (polyGSOSFoldNodeAt B P Q rho
      (pbefMk p (Over.homMk
        (fun e =>
          (polyGSOSFoldCataWithFiber
            B P Q rho
            (polyFreeMapAt
              (polyCofreeCarrier A Q)
              (polyCofreeCarrier B Q) P
              (polyCofreeMap A B Q f)
              _ (children e))).val)
        (funext fun e =>
          (polyGSOSFoldCataWithFiber
            B P Q rho
            (polyFreeMapAt
              (polyCofreeCarrier A Q)
              (polyCofreeCarrier B Q) P
              (polyCofreeMap A B Q f)
              _ (children e))).prop)))).val.2 := by
  simp only [polyGSOSFoldNodeAt,
    GSOSQMap, polyEndoFunctor,
    polyBetweenEvalFunctor, polyToOverFunctor,
    polyToOverEvalMap_left]
  let DQ_A := polyCofreeCarrier A Q
  let DQ_B := polyCofreeCarrier B Q
  let TDQ_A := polyFreeMCarrier DQ_A P
  let TDQ_B := polyFreeMCarrier DQ_B P
  let freeMap := GSOSFreeMap A B P Q f
  congr 1
  -- Push ccrEvalMap freeMap backward through
  -- the pipeline: join, toFun, rho, invFun, prodComp.
  -- Step 1: join.
  rw [ccrEvalMap_comp_apply
    (polyFreeMJoinEval DQ_A P)
    (GSOSFreeMap A B P Q f)]
  conv_lhs =>
    rw [show (polyFreeMJoinEval DQ_A P ≫
        GSOSFreeMap A B P Q f) =
      ((polyEndoFunctor X (polyFreeMPoly P)).map
        (GSOSFreeMap A B P Q f) ≫
        polyFreeMJoinEval DQ_B P)
      from polyFreeMJoinEval_natural
        DQ_A DQ_B P (polyCofreeMap A B Q f)]
  rw [← ccrEvalMap_comp_apply
    ((polyEndoFunctor X (polyFreeMPoly P)).map
      (GSOSFreeMap A B P Q f))
    (polyFreeMJoinEval DQ_B P)]
  congr 1
  -- Step 2: toFun.
  rw [polyBetweenComp_eval_toFun_natural
    Q (polyFreeMPoly P) TDQ_A TDQ_B
    (GSOSFreeMap A B P Q f) y]
  congr 1
  -- Step 3: morphEvalAt.
  rw [morphEvalAt_ccrEvalMap_comm rho.rule
    (GSOSFreeMap A B P Q f) y]
  congr 1
  -- Step 4: invFun.
  rw [polyBetweenComp_eval_invFun_natural
    P (polyIdBehaviorPoly Q) TDQ_A TDQ_B
    (GSOSFreeMap A B P Q f) y]
  congr 1
  -- Step 5: prodComp.
  rw [ccrEvalMap_comp_apply
    (overPullbackToIdQEval Q TDQ_A)
    ((polyEndoFunctor X
      (polyIdBehaviorPoly Q)).map
      (GSOSFreeMap A B P Q f))]
  conv_lhs =>
    rw [show (overPullbackToIdQEval Q TDQ_A ≫
        (polyEndoFunctor X
          (polyIdBehaviorPoly Q)).map
          (GSOSFreeMap A B P Q f)) =
      (overPullbackMap (GSOSFreeMap A B P Q f)
        ((polyEndoFunctor X Q).map
          (GSOSFreeMap A B P Q f)) ≫
        overPullbackToIdQEval Q TDQ_B)
      from overPullbackToIdQEval_comm
        Q TDQ_A TDQ_B (GSOSFreeMap A B P Q f)]
  rw [← ccrEvalMap_comp_apply
    (overPullbackMap (GSOSFreeMap A B P Q f)
      ((polyEndoFunctor X Q).map
        (GSOSFreeMap A B P Q f)))
    (overPullbackToIdQEval Q TDQ_B)]
  congr 1
  -- Step 6: Children equality via ih and
  -- fst_natural.
  simp only [ccrEvalMap, pbefMk, ptoefMk,
    ccrEvalMk]
  congr 1
  apply Over.OverMorphism.ext
  funext e
  simp only [Over.comp_left, types_comp_apply,
    Over.homMk_left, overPullbackMap]
  apply Subtype.ext
  apply Prod.ext
  · exact (polyGSOSFoldFst_natural
      A B P Q rho f (children e)).symm
  · exact ih e

private lemma polyGSOSFoldQeval_natural
    (A B : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) (f : A ⟶ B)
    {x : X}
    (t : PolyFreeM
      (polyCofreeCarrier A Q) P x) :
    let DQ_A := polyCofreeCarrier A Q
    let DQ_B := polyCofreeCarrier B Q
    let freeMap :=
      polyFreeMap DQ_A DQ_B P
        (polyCofreeMap A B Q f)
    ((polyEndoFunctor X Q).map freeMap).left
      (polyGSOSFoldCataWithFiber
        A P Q rho t).val.val.2 =
    (polyGSOSFoldCataWithFiber
      B P Q rho
      (polyFreeMapAt DQ_A DQ_B P
        (polyCofreeMap A B Q f) x t)).val.val.2
    := by
  induction t with
  | mk y idx children ih =>
    match idx with
    | Sum.inl ⟨⟨_, d⟩, rfl⟩ =>
      simp only [polyFreeMapAt,
        polyGSOSFoldCataWithFiber]
      exact polyGSOSFoldLeafAt_snd_natural
        A B P Q f d
    | Sum.inr p =>
      simp only [polyFreeMapAt,
        polyGSOSFoldCataWithFiber,
        polyFreeMBind]
      exact polyGSOSFoldNodeAt_snd_natural
        A B P Q rho f p children ih

private lemma polyBetweenEvalMap_mor_apply
    (P : PolyEndo X) {A B : Over X} (f : A ⟶ B)
    (eval_a :
      (polyBetweenEval X X P A).left)
    (eval_b :
      (polyBetweenEval X X P B).left)
    (h : ((polyEndoFunctor X P).map f).left
      eval_a = eval_b)
    {e₁ : (polyBetweenFamily X X P
      eval_a.1 eval_a.2.1).left}
    {e₂ : (polyBetweenFamily X X P
      eval_b.1 eval_b.2.1).left}
    (he : e₁ ≍ e₂) :
    f.left (eval_a.2.2.left e₁) =
    eval_b.2.2.left e₂ := by
  obtain ⟨z_a, idx_a, mor_a⟩ := eval_a
  obtain ⟨z_b, idx_b, mor_b⟩ := eval_b
  simp only [polyEndoFunctor,
    polyBetweenEvalFunctor,
    polyToOverFunctor,
    polyToOverEvalMap_left,
    ccrEvalMap] at h
  obtain ⟨rfl, h₂⟩ := Sigma.mk.inj h
  obtain ⟨rfl, h₃⟩ :=
    Sigma.mk.inj (eq_of_heq h₂)
  simp only at he
  have he' := eq_of_heq he
  subst he'
  exact congrFun
    (congrArg CommaMorphism.left
      (eq_of_heq h₃))
    e₁

lemma polyGSOSScaleCoalg_morphism_h
    (A B : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) (f : A ⟶ B) :
    (polyScaleReindexCoalg
      (polyFreeMCarrier A P)
      (polyFreeMCarrier B P) Q
      (polyFreeMap A B P f)
      (polyGSOSScaleCoalg A P Q rho)).str ≫
    (polyEndoFunctor X
      (polyScale (polyFreeMCarrier B P) Q)).map
      (polyFreeMap
        (polyCofreeCarrier A Q)
        (polyCofreeCarrier B Q) P
        (polyCofreeMap A B Q f)) =
    polyFreeMap
      (polyCofreeCarrier A Q)
      (polyCofreeCarrier B Q) P
      (polyCofreeMap A B Q f) ≫
    (polyGSOSScaleCoalg B P Q rho).str := by
  apply Over.OverMorphism.ext
  funext ⟨x, t⟩
  simp only [Over.comp_left, types_comp_apply]
  induction t with
  | mk y idx children ih =>
    match idx with
    | Sum.inl ⟨⟨_, d⟩, rfl⟩ =>
      simp only [Over.comp_left, types_comp_apply,
        polyScaleReindexCoalg,
        polyGSOSScaleCoalg,
        polyGSOSScaleCoalgStr, Over.homMk_left,
        polyGSOSScaleCoalgStrAt,
        polyGSOSFoldCataWithFiber,
        polyGSOSFoldLeafAt,
        polyScaleReindexLeft,
        polyCofreeCounit, polyCofreeCounitLeft,
        polyFreeMap, polyFreeMapLeft,
        polyFreeMapAt, polyFreeMBind,
        polyCofreeMap, polyCofreeMapLeft,
        polyFreeMPure,
        polyEndoFunctor,
        polyBetweenEvalFunctor,
        polyToOverFunctor,
        polyToOverEvalMap_left,
        ccrEvalMap]
      have hannot :
          f.left (polyCofreeExtract A Q d).val =
          (polyCofreeExtract B Q
            (polyCofreeMapAt A B Q f d)).val :=
        (polyCofreeExtract_mapAt_val
          A B Q f d).symm
      have hqidx :
          d.head.2 =
          (polyCofreeMapAt A B Q f d).head.2 :=
        (polyCofreeMapAt_head_snd
          A B Q f d).symm
      congr 1; congr 1
      · congr 1
        apply Subtype.ext
        exact Sigma.ext rfl
          (heq_of_eq (eq_of_heq
            (polyFix_leaf_heq_of_val_eq _ _ hannot)))
      · -- Q-children HEq
        apply polyBetweenFamily_mor_heq
          rfl _ _ (heq_of_eq hqidx)
        simp only [Over.comp_left, types_comp,
          Over.homMk_left]
        apply Function.hfunext
        · exact congrArg
            (fun q => (polyBetweenFamily
              X X Q y q).left) hqidx
        · intro e₁ e₂ he
          simp only [Function.comp_apply,
            polyFreeMapLeft, polyFreeMapAt,
            polyFreeMBind, polyFreeMPure]
          have hfib := overType_hom_heq
            (congrArg (polyBetweenFamily X X Q y)
              hqidx) e₁ e₂ he
          exact heq_of_eq_of_heq
            (Sigma.ext rfl (heq_of_eq rfl))
            (heq_of_eq (Sigma.ext hfib
              (polyFix_leaf_heq_of_val_eq _ _
                (Sigma.ext hfib
                  (polyCofreeMapAt_children_heq
                    A B Q f d
                    e₁ e₂ he)))))
    | Sum.inr p =>
      simp only [Over.comp_left, types_comp_apply,
        polyScaleReindexCoalg,
        polyScaleReindexLeft,
        polyGSOSScaleCoalg,
        polyGSOSScaleCoalgStr,
        Over.homMk_left,
        polyGSOSScaleCoalgStrAt,
        polyEndoFunctor,
        polyBetweenEvalFunctor,
        polyToOverFunctor,
        polyToOverEvalMap_left,
        ccrEvalMap,
        polyFreeMap, Over.homMk_left,
        polyFreeMapLeft]
      have hqidx : (polyGSOSFoldCataWithFiber
            A P Q rho
            (PolyFix.mk y (Sum.inr p)
              children)).val.val.2.snd.fst =
          (polyGSOSFoldCataWithFiber
            B P Q rho
            (polyFreeMapAt
              (polyCofreeCarrier A Q)
              (polyCofreeCarrier B Q) P
              (polyCofreeMap A B Q f) y
              (PolyFix.mk y (Sum.inr p)
                children))).val.val.2.snd.fst := by
        have := polyGSOSFoldQIndex_eq
          A B P Q rho f
          (PolyFix.mk y (Sum.inr p) children)
        simp only [polyGSOSFoldQIndex] at this
        exact this.symm
      congr 1; congr 1
      · congr 1
        apply Subtype.ext
        exact Sigma.ext rfl
          (heq_of_eq
            (polyGSOSDistLaw_annot_natural
              A B P Q f
              (PolyFix.mk y (Sum.inr p)
                children)).symm)
      · apply polyBetweenFamily_mor_heq
          rfl _ _ (heq_of_eq hqidx)
        simp only [Over.comp_left, types_comp]
        apply Function.hfunext
        · exact congrArg
            (fun q => (polyBetweenFamily
              X X Q y q).left) hqidx
        · intro e₁ e₂ he
          simp only [Over.homMk_left,
            Function.comp]
          apply heq_of_eq
          exact polyBetweenEvalMap_mor_apply
            Q (GSOSFreeMap A B P Q f)
            (polyGSOSFoldCataWithFiber
              A P Q rho
              (PolyFix.mk y (Sum.inr p)
                children)).val.val.2
            (polyGSOSFoldCataWithFiber
              B P Q rho
              (polyFreeMapAt
                (polyCofreeCarrier A Q)
                (polyCofreeCarrier B Q) P
                (polyCofreeMap A B Q f) y
                (PolyFix.mk y (Sum.inr p)
                  children))).val.val.2
            (polyGSOSFoldQeval_natural
              A B P Q rho f
              (PolyFix.mk y (Sum.inr p)
                children))
            he

lemma polyGSOSDistLaw_naturality
    (A B : Over X) (P Q : PolyEndo X)
    (rho : PolyGSOSRule P Q) (f : A ⟶ B) :
    polyFreeMap
      (polyCofreeCarrier A Q)
      (polyCofreeCarrier B Q) P
      (polyCofreeMap A B Q f) ≫
    polyGSOSDistLawMor B P Q rho =
    polyGSOSDistLawMor A P Q rho ≫
    polyCofreeMap
      (polyFreeMCarrier A P)
      (polyFreeMCarrier B P) Q
      (polyFreeMap A B P f) := by
  have rhs_eq :=
    polyScaleReindex
      (polyFreeMCarrier A P)
      (polyFreeMCarrier B P) Q
      (polyFreeMap A B P f)
      (polyGSOSScaleCoalg A P Q rho)
  have lhs_eq :=
    polyCofixUnfold_precomp
      (polyScale (polyFreeMCarrier B P) Q)
      (polyScaleReindexCoalg
        (polyFreeMCarrier A P)
        (polyFreeMCarrier B P) Q
        (polyFreeMap A B P f)
        (polyGSOSScaleCoalg A P Q rho))
      (polyGSOSScaleCoalg B P Q rho)
      ⟨polyFreeMap
        (polyCofreeCarrier A Q)
        (polyCofreeCarrier B Q) P
        (polyCofreeMap A B Q f),
       polyGSOSScaleCoalg_morphism_h
        A B P Q rho f⟩
  simp only [polyGSOSDistLawMor]
  rw [rhs_eq, lhs_eq]

end GebLean
