import GebLean.PshRelDouble

/-!
# Exponential Structure of the Edge Category

The vertical edge category `PshRelEdge C` of the double
category of presheaf relations is cartesian closed. The
exponential of two edges `(A₁, B₁, R)` and `(A₂, B₂, T)`
is `(A₁.functorHom A₂, B₁.functorHom B₂, pshArrowRel R T)`.

## Main definitions

* `pshRelProd`: product of two presheaf relations
* `pshRelEdgeProd`: product in `PshRelEdge C`
* `pshRelEdgeExp`: exponential in `PshRelEdge C`
* `pshRelEdgeCurry`: currying for `PshRelEdge C`
* `pshRelEdgeUncurry`: uncurrying for `PshRelEdge C`
* `pshRelEdgeEval`: evaluation morphism
* `pshRelEdgeUncurry_curry`: left inverse
* `pshRelEdgeCurry_uncurry`: right inverse
-/

namespace GebLean

open CategoryTheory Limits

universe u v w

variable {C : Type u} [Category.{v} C]

section PshRelProd

variable {P₁ Q₁ P₂ Q₂ : Cᵒᵖ ⥤ Type w}

/-- The product of two presheaf relations. Given
`R₁ : PshRel P₁ Q₁` and `R₂ : PshRel P₂ Q₂`,
the product relation at stage `c` consists of
pairs `((p₁, p₂), (q₁, q₂))` such that
`(p₁, q₁) ∈ R₁(c)` and `(p₂, q₂) ∈ R₂(c)`. -/
def pshRelProd
    (R₁ : PshRel P₁ Q₁)
    (R₂ : PshRel P₂ Q₂) :
    PshRel (pshProdPresheaf P₁ P₂)
      (pshProdPresheaf Q₁ Q₂) where
  obj c :=
    { pq : (P₁.obj c × P₂.obj c) ×
           (Q₁.obj c × Q₂.obj c) |
      (pq.1.1, pq.2.1) ∈ R₁.obj c ∧
      (pq.1.2, pq.2.2) ∈ R₂.obj c }
  map {c d} f := by
    intro ⟨pq₁, pq₂⟩ ⟨h₁, h₂⟩
    exact ⟨R₁.map f h₁, R₂.map f h₂⟩

/-- The first projection preserves the product
relation: mapping by `pshProdFst` on both
components sends `pshRelProd`-related pairs to
`R₁`-related pairs. -/
theorem pshRelProd_related_fst
    (R₁ : PshRel P₁ Q₁)
    (R₂ : PshRel P₂ Q₂) :
    pshRelRelated
      (pshProdFst P₁ P₂) (pshProdFst Q₁ Q₂)
      (pshRelProd R₁ R₂) R₁ :=
  fun _ _ _ h => h.1

/-- The second projection preserves the product
relation. -/
theorem pshRelProd_related_snd
    (R₁ : PshRel P₁ Q₁)
    (R₂ : PshRel P₂ Q₂) :
    pshRelRelated
      (pshProdSnd P₁ P₂) (pshProdSnd Q₁ Q₂)
      (pshRelProd R₁ R₂) R₂ :=
  fun _ _ _ h => h.2

end PshRelProd

section PshRelEdgeProdExp

/-- The product of two edges in `PshRelEdge C`.
Given edges `E₁ = (P₁, Q₁, R₁)` and
`E₂ = (P₂, Q₂, R₂)`, the product edge is
`(P₁ × P₂, Q₁ × Q₂, pshRelProd R₁ R₂)`. -/
def pshRelEdgeProd
    (E₁ E₂ : PshRelEdge.{u, v, w} C) :
    PshRelEdge.{u, v, w} C :=
  { src := pshProdPresheaf E₁.src E₂.src
    tgt := pshProdPresheaf E₁.tgt E₂.tgt
    edge := pshRelProd E₁.edge E₂.edge }

/-- First projection morphism from the product
edge to the first component. -/
def pshRelEdgeProdFst
    (E₁ E₂ : PshRelEdge.{u, v, w} C) :
    pshRelEdgeProd E₁ E₂ ⟶ E₁ :=
  { srcMap := pshProdFst E₁.src E₂.src
    tgtMap := pshProdFst E₁.tgt E₂.tgt
    sq := pshRelProd_related_fst
      E₁.edge E₂.edge }

/-- Second projection morphism from the product
edge to the second component. -/
def pshRelEdgeProdSnd
    (E₁ E₂ : PshRelEdge.{u, v, w} C) :
    pshRelEdgeProd E₁ E₂ ⟶ E₂ :=
  { srcMap := pshProdSnd E₁.src E₂.src
    tgtMap := pshProdSnd E₁.tgt E₂.tgt
    sq := pshRelProd_related_snd
      E₁.edge E₂.edge }

/-- The exponential of two edges in `PshRelEdge C`.
Given edges `A = (A₁, B₁, R)` and
`B = (A₂, B₂, T)`, the exponential edge is
`(A₁.functorHom A₂, B₁.functorHom B₂,
  pshArrowRel R T)`.

This is the presheaf-level analogue of Wadler's
relational interpretation of function types. -/
def pshRelEdgeExp
    (A B : PshRelEdge.{u, v, max u v} C) :
    PshRelEdge.{u, v, max u v} C :=
  { src := A.src.functorHom B.src
    tgt := A.tgt.functorHom B.tgt
    edge := pshArrowRel A.edge B.edge }

end PshRelEdgeProdExp

section PshRelEdgeCurryUncurry

variable {E A B : PshRelEdge.{u, v, max u v} C}

/-- The curried source `HomObj`: given a natural
transformation `φ : E × A ⟶ B`, produce the
corresponding `HomObj A B E` whose application
at `(d, e, a)` is `φ d (e, a)`. -/
def pshRelEdgeCurrySrcHomObj
    (φ : pshProdPresheaf E.src A.src ⟶ B.src) :
    Functor.HomObj A.src B.src E.src where
  app d e a := φ.app d (e, a)
  naturality {d d'} f e := by
    ext a
    exact congr_fun (φ.naturality f) (e, a)

/-- The curried source natural transformation:
given `φ : E × A ⟶ B`, produce the natural
transformation `E ⟶ A.functorHom B` via the
internal hom adjunction. -/
def pshRelEdgeCurrySrcMap
    (φ : pshProdPresheaf E.src A.src ⟶ B.src) :
    E.src ⟶ A.src.functorHom B.src :=
  (Functor.functorHomEquiv A.src B.src E.src).invFun
    (pshRelEdgeCurrySrcHomObj φ)

/-- The curried target `HomObj`. -/
def pshRelEdgeCurryTgtHomObj
    (ψ : pshProdPresheaf E.tgt A.tgt ⟶ B.tgt) :
    Functor.HomObj A.tgt B.tgt E.tgt where
  app d e' a' := ψ.app d (e', a')
  naturality {d d'} f e' := by
    ext a'
    exact congr_fun (ψ.naturality f) (e', a')

/-- The curried target natural transformation. -/
def pshRelEdgeCurryTgtMap
    (ψ : pshProdPresheaf E.tgt A.tgt ⟶ B.tgt) :
    E.tgt ⟶ A.tgt.functorHom B.tgt :=
  (Functor.functorHomEquiv
    A.tgt B.tgt E.tgt).invFun
    (pshRelEdgeCurryTgtHomObj ψ)

/-- Curry a morphism `f : E × A ⟶ B` in
`PshRelEdge C` to a morphism `E ⟶ [A, B]`. -/
def pshRelEdgeCurry
    (f : pshRelEdgeProd E A ⟶ B) :
    E ⟶ pshRelEdgeExp A B :=
  { srcMap := pshRelEdgeCurrySrcMap f.srcMap
    tgtMap := pshRelEdgeCurryTgtMap f.tgtMap
    sq := by
      intro c e e' hee'
      apply pshArrowRel_intro
      intro d k a₁ a₂ ha
      dsimp [pshRelEdgeCurrySrcMap,
        pshRelEdgeCurryTgtMap,
        Functor.functorHomEquiv,
        pshRelEdgeCurrySrcHomObj,
        pshRelEdgeCurryTgtHomObj]
      exact f.sq d
        (E.src.map k e, a₁)
        (E.tgt.map k e', a₂)
        ⟨E.edge.map k hee', ha⟩ }

/-- The uncurried source natural transformation:
given `α : E ⟶ A.functorHom B`, produce the
natural transformation
`E × A ⟶ B` by evaluating at the identity. -/
def pshRelEdgeUncurrySrcMap
    (α : E.src ⟶ A.src.functorHom B.src) :
    pshProdPresheaf E.src A.src ⟶ B.src where
  app c ea := (α.app c ea.1).app c (𝟙 c) ea.2
  naturality {c d} f := by
    ext ⟨e, a⟩
    simp only [types_comp_apply,
      FunctorToTypes.prod]
    have hα : α.app d (E.src.map f e) =
      (A.src.functorHom B.src).map f
        (α.app c e) :=
      congr_fun (α.naturality f) e
    have hmap : ((A.src.functorHom B.src).map
      f (α.app c e)).app d (𝟙 d) =
      (α.app c e).app d f := by
      dsimp [Functor.functorHom,
        Functor.homObjFunctor]
      simp only [Category.comp_id]
    have hobj :=
      congr_fun ((α.app c e).naturality f
        (𝟙 c)) a
    simp only [types_comp_apply] at hobj
    change (α.app d (E.src.map f e)).app d
      (𝟙 d) (A.src.map f a) =
      B.src.map f
        ((α.app c e).app c (𝟙 c) a)
    rw [show (α.app d (E.src.map f e)).app d
        (𝟙 d) = (α.app c e).app d f from
      by rw [hα, hmap]]
    convert hobj using 2
    dsimp [Functor.functorHom,
      Functor.homObjFunctor]
    simp only [Category.id_comp]

/-- The uncurried target natural transformation. -/
def pshRelEdgeUncurryTgtMap
    (β : E.tgt ⟶ A.tgt.functorHom B.tgt) :
    pshProdPresheaf E.tgt A.tgt ⟶ B.tgt where
  app c ea := (β.app c ea.1).app c (𝟙 c) ea.2
  naturality {c d} f := by
    ext ⟨e', a'⟩
    simp only [types_comp_apply,
      FunctorToTypes.prod]
    have hβ : β.app d (E.tgt.map f e') =
      (A.tgt.functorHom B.tgt).map f
        (β.app c e') :=
      congr_fun (β.naturality f) e'
    have hmap : ((A.tgt.functorHom B.tgt).map
      f (β.app c e')).app d (𝟙 d) =
      (β.app c e').app d f := by
      dsimp [Functor.functorHom,
        Functor.homObjFunctor]
      simp only [Category.comp_id]
    have hobj :=
      congr_fun ((β.app c e').naturality f
        (𝟙 c)) a'
    simp only [types_comp_apply] at hobj
    change (β.app d (E.tgt.map f e')).app d
      (𝟙 d) (A.tgt.map f a') =
      B.tgt.map f
        ((β.app c e').app c (𝟙 c) a')
    rw [show (β.app d (E.tgt.map f e')).app d
        (𝟙 d) = (β.app c e').app d f from
      by rw [hβ, hmap]]
    convert hobj using 2
    dsimp [Functor.functorHom,
      Functor.homObjFunctor]
    simp only [Category.id_comp]

/-- Uncurry a morphism `g : E ⟶ [A, B]` in
`PshRelEdge C` to a morphism `E × A ⟶ B`. -/
def pshRelEdgeUncurry
    (g : E ⟶ pshRelEdgeExp A B) :
    pshRelEdgeProd E A ⟶ B :=
  { srcMap := pshRelEdgeUncurrySrcMap g.srcMap
    tgtMap := pshRelEdgeUncurryTgtMap g.tgtMap
    sq := by
      intro c ⟨e, a⟩ ⟨e', a'⟩ ⟨hee', haa'⟩
      dsimp [pshRelEdgeUncurrySrcMap,
        pshRelEdgeUncurryTgtMap]
      exact pshArrowRel_apply
        (g.sq c e e' hee') (𝟙 c) haa' }

/-- Pairing morphism: given morphisms `f₁ : E ⟶ A`
and `f₂ : E ⟶ B` in `PshRelEdge C`, produce a
morphism `E ⟶ A × B`. -/
def pshRelEdgePair
    {E A B : PshRelEdge.{u, v, w} C}
    (f₁ : E ⟶ A) (f₂ : E ⟶ B) :
    E ⟶ pshRelEdgeProd A B :=
  { srcMap :=
      pshProdLift f₁.srcMap f₂.srcMap
    tgtMap :=
      pshProdLift f₁.tgtMap f₂.tgtMap
    sq := fun c p q h =>
      ⟨f₁.sq c p q h, f₂.sq c p q h⟩ }

/-- Uncurrying the curry of `f` recovers `f`. -/
theorem pshRelEdgeUncurry_curry
    (f : pshRelEdgeProd E A ⟶ B) :
    pshRelEdgeUncurry (pshRelEdgeCurry f) = f := by
  apply VertEdgeHom.ext
  · ext c ⟨e, a⟩
    dsimp [pshRelEdgeUncurry,
      pshRelEdgeUncurrySrcMap,
      pshRelEdgeCurry,
      pshRelEdgeCurrySrcMap,
      Functor.functorHomEquiv,
      pshRelEdgeCurrySrcHomObj]
    simp [FunctorToTypes.map_id_apply]
  · ext c ⟨e', a'⟩
    dsimp [pshRelEdgeUncurry,
      pshRelEdgeUncurryTgtMap,
      pshRelEdgeCurry,
      pshRelEdgeCurryTgtMap,
      Functor.functorHomEquiv,
      pshRelEdgeCurryTgtHomObj]
    simp [FunctorToTypes.map_id_apply]

/-- Currying the uncurry of `g` recovers `g`. -/
theorem pshRelEdgeCurry_uncurry_src_app
    (g : E ⟶ pshRelEdgeExp A B)
    (c : Cᵒᵖ) (e : E.src.obj c) :
    (pshRelEdgeCurrySrcMap
      (pshRelEdgeUncurrySrcMap g.srcMap)).app
      c e = g.srcMap.app c e := by
  apply Functor.functorHom_ext
  intro d k
  dsimp [pshRelEdgeCurrySrcMap,
    Functor.functorHomEquiv,
    pshRelEdgeCurrySrcHomObj,
    pshRelEdgeUncurrySrcMap]
  have hα : g.srcMap.app d (E.src.map k e) =
    (A.src.functorHom B.src).map k
      (g.srcMap.app c e) :=
    congr_fun (g.srcMap.naturality k) e
  ext a
  change (g.srcMap.app d
    (E.src.map k e)).app d (𝟙 d) a =
    (g.srcMap.app c e).app d k a
  rw [hα]
  dsimp [Functor.functorHom,
    Functor.homObjFunctor]
  simp only [Category.comp_id]

theorem pshRelEdgeCurry_uncurry
    (g : E ⟶ pshRelEdgeExp A B) :
    pshRelEdgeCurry (pshRelEdgeUncurry g) = g := by
  apply VertEdgeHom.ext
  · ext c e
    exact pshRelEdgeCurry_uncurry_src_app g c e
  · ext c e'
    apply Functor.functorHom_ext
    intro d k
    dsimp [pshRelEdgeCurry,
      pshRelEdgeCurryTgtMap,
      Functor.functorHomEquiv,
      pshRelEdgeCurryTgtHomObj,
      pshRelEdgeUncurry,
      pshRelEdgeUncurryTgtMap]
    have hβ : g.tgtMap.app d (E.tgt.map k e') =
      (A.tgt.functorHom B.tgt).map k
        (g.tgtMap.app c e') :=
      congr_fun (g.tgtMap.naturality k) e'
    ext a'
    change (g.tgtMap.app d
      (E.tgt.map k e')).app d (𝟙 d) a' =
      (g.tgtMap.app c e').app d k a'
    rw [hβ]
    dsimp [Functor.functorHom,
      Functor.homObjFunctor]
    simp only [Category.comp_id]

/-- The evaluation morphism
`[A, B] × A ⟶ B` in `PshRelEdge C`:
the uncurry of the identity on `[A, B]`. -/
def pshRelEdgeEval
    (A B : PshRelEdge.{u, v, max u v} C) :
    pshRelEdgeProd (pshRelEdgeExp A B) A ⟶ B :=
  pshRelEdgeUncurry (𝟙 (pshRelEdgeExp A B))

end PshRelEdgeCurryUncurry

end GebLean
