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
      _
    | Sum.inr p =>
      _

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
