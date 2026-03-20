import GebLean.PshRelEdgeSeparation
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Functor.KanExtension.Dense
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Representable embedding and density for PshRelEdge

The representable embedding sends each pair
`(i : WalkingSpan, c : Cᵒᵖ)` to the separated
representable edge `pshRelEdgeRepresentable i c`.
This embedding is contravariant (Yoneda-like) and
factors through the span presheaf category via the
separation functor.
-/

namespace GebLean

open CategoryTheory Category Limits Opposite Presheaf

universe u v

variable {C : Type u} [Category.{v} C]

section SpanRepresentableFunctor

/-- The span representable embedding as a
contravariant functor from the small index
category to the span presheaf category.
A morphism `op(i₀,c₀) ⟶ op(i₁,c₁)` (i.e.,
`(i₁,c₁) ⟶ (i₀,c₀)` = `(φ : i₁ ⟶ i₀,
g : c₁ ⟶ c₀)`) maps `spanRep(i₀,c₀)` to
`spanRep(i₁,c₁)` by precomposition. -/
def spanRepresentableFunctor :
    (WalkingSpan × Cᵒᵖ)ᵒᵖ ⥤
      (WalkingSpan ⥤
        Cᵒᵖ ⥤ Type (max u v)) where
  obj ic :=
    spanRepresentable ic.unop.1 ic.unop.2
  map {ic₁ ic₂} f :=
    let φ := f.unop.1
    let g := f.unop.2
    { app := fun j =>
        { app := fun c' sp =>
            (φ ≫ sp.1, ⟨g ≫ sp.2.down⟩)
          naturality := fun {_ _} h => by
            funext ⟨a, ⟨b⟩⟩
            exact Prod.ext rfl
              (ULift.ext _ _
                (Category.assoc _ _ _).symm) }
      naturality := fun {_ _} ψ => by
        apply NatTrans.ext; funext c'
        funext ⟨a, ⟨b⟩⟩
        exact Prod.ext
          (Category.assoc _ _ _).symm rfl }
  map_id ic := by
    apply NatTrans.ext; funext j
    apply NatTrans.ext; funext c'
    funext ⟨h, ⟨k⟩⟩
    dsimp
    exact Prod.ext (Category.id_comp _)
      (ULift.ext _ _ (Category.id_comp _))
  map_comp {ic₁ ic₂ ic₃} f g := by
    apply NatTrans.ext; funext j
    apply NatTrans.ext; funext c'
    funext ⟨h, ⟨k⟩⟩
    dsimp
    exact Prod.ext
      (Category.assoc _ _ _)
      (ULift.ext _ _
        (Category.assoc _ _ _))

/-- The representable embedding as a functor
from the small index category
`(WalkingSpan × Cᵒᵖ)ᵒᵖ` to `PshRelEdge C`,
defined as the span representable functor
composed with the separation functor. -/
def pshRelEdgeRepresentableFunctor :
    (WalkingSpan × Cᵒᵖ)ᵒᵖ ⥤
      PshRelEdge.{u, v, max u v} C :=
  spanRepresentableFunctor ⋙
    pshRelEdgeSepFunctor C

end SpanRepresentableFunctor

section Density

private def spanRepFunctorUncurryIso :
    spanRepresentableFunctor (C := C) ⋙
      Functor.uncurry ≅
    uliftCoyoneda.{max u v}
      (C := WalkingSpan × Cᵒᵖ) :=
  NatIso.ofComponents
    (fun ic => NatIso.ofComponents
      (fun jc =>
        { hom := fun sp => ⟨(sp.1, sp.2.down)⟩
          inv := fun sp => (sp.down.1, ⟨sp.down.2⟩)
          hom_inv_id := funext fun ⟨_, ⟨_⟩⟩ => rfl
          inv_hom_id := funext fun ⟨⟨_, _⟩⟩ => rfl })
      (fun {jc₁ jc₂} f => by
        funext ⟨a, ⟨b⟩⟩
        simp only [spanRepresentableFunctor, Functor.uncurry,
          types_comp_apply,
          spanRepresentable,
          uliftCoyoneda, uliftYoneda]
        rfl))
    (fun {ic₁ ic₂} f => by
      apply NatTrans.ext; funext jc
      funext ⟨a, ⟨b⟩⟩
      simp only [spanRepresentableFunctor, Functor.uncurry,
        spanRepresentable,
        uliftCoyoneda, uliftYoneda]
      rfl)

private instance uliftYonedaOpIsDense :
    (uliftYoneda.{max u v}
        (C := (WalkingSpan × Cᵒᵖ)ᵒᵖ)).IsDense where
  isDenseAt P := ⟨isColimitTautologicalCocone' P⟩

private instance uliftCoyonedaIsDense :
    (uliftCoyoneda.{max u v}
        (C := WalkingSpan × Cᵒᵖ)).IsDense := by
  have comm : (uliftYoneda.{max u v}
      (C := (WalkingSpan × Cᵒᵖ)ᵒᵖ) ⋙
      (Functor.whiskeringLeft _ _ _).obj
        (opOp (WalkingSpan × Cᵒᵖ))).IsDense :=
    Functor.IsDense.comp_right_iff_of_isEquivalence _ _ |>.mpr
      uliftYonedaOpIsDense
  have iso : uliftYoneda.{max u v} (C := (WalkingSpan × Cᵒᵖ)ᵒᵖ) ⋙
      (Functor.whiskeringLeft _ _ _).obj
        (opOp (WalkingSpan × Cᵒᵖ)) ≅
      uliftCoyoneda.{max u v} (C := WalkingSpan × Cᵒᵖ) :=
    NatIso.ofComponents
      (fun ic => NatIso.ofComponents
        (fun (jc : WalkingSpan × Cᵒᵖ) =>
          (Equiv.ulift.trans
            ((opEquiv (op jc) ic).trans
              Equiv.ulift.symm)).toIso)
        (fun {jc₁ jc₂} f => by
          funext ⟨a⟩
          simp [opEquiv, uliftYoneda, uliftCoyoneda,
            Functor.whiskeringLeft, opOp]))
      (fun {ic₁ ic₂} f => by
        apply NatTrans.ext; funext jc
        funext ⟨a⟩
        simp [opEquiv, uliftYoneda, uliftCoyoneda,
          Functor.whiskeringLeft, opOp])
  exact Functor.IsDense.iff_of_iso iso |>.mp comm

private instance spanRepresentableFunctorIsDense :
    (spanRepresentableFunctor (C := C)).IsDense := by
  haveI : (Functor.uncurry (C := WalkingSpan)
      (D := Cᵒᵖ) (E := Type (max u v))).IsEquivalence :=
    Equivalence.isEquivalence_functor Functor.currying
  exact (Functor.IsDense.comp_right_iff_of_isEquivalence
    spanRepresentableFunctor
    Functor.uncurry).mp
    (Functor.IsDense.of_iso spanRepFunctorUncurryIso.symm)

private def costrArrAdjBwd (E : PshRelEdge.{u, v, max u v} C) :
    CostructuredArrow pshRelEdgeRepresentableFunctor E ⥤
      CostructuredArrow spanRepresentableFunctor
        ((pshRelEdgeInclusionFunctor C).obj E) where
  obj j := CostructuredArrow.mk
    ((pshRelEdgeSepAdjunction C).homEquiv
      (spanRepresentableFunctor.obj j.left) E j.hom)
  map {j k} φ := CostructuredArrow.homMk φ.left (by
    simp only [CostructuredArrow.mk_hom_eq_self]
    rw [← CostructuredArrow.w φ]
    simp only [pshRelEdgeRepresentableFunctor, Functor.comp_map]
    exact ((pshRelEdgeSepAdjunction C).homEquiv_naturality_left
      (spanRepresentableFunctor.map φ.left) k.hom).symm)
  map_id j := CostructuredArrow.hom_ext _ _ rfl
  map_comp _ _ := CostructuredArrow.hom_ext _ _ rfl

private def costrArrAdjFwd (E : PshRelEdge.{u, v, max u v} C) :
    CostructuredArrow spanRepresentableFunctor
        ((pshRelEdgeInclusionFunctor C).obj E) ⥤
      CostructuredArrow pshRelEdgeRepresentableFunctor E where
  obj j := CostructuredArrow.mk
    ((pshRelEdgeSepAdjunction C).homEquiv
      (spanRepresentableFunctor.obj j.left) E |>.symm j.hom)
  map {j k} φ := CostructuredArrow.homMk φ.left (by
    simp only [CostructuredArrow.mk_hom_eq_self]
    rw [← CostructuredArrow.w φ]
    simp only [pshRelEdgeRepresentableFunctor, Functor.comp_map]
    exact ((pshRelEdgeSepAdjunction C).homEquiv_naturality_left_symm
      (spanRepresentableFunctor.map φ.left) k.hom).symm)
  map_id j := CostructuredArrow.hom_ext _ _ rfl
  map_comp _ _ := CostructuredArrow.hom_ext _ _ rfl

private def costrArrAdjEquiv (E : PshRelEdge.{u, v, max u v} C) :
    CostructuredArrow pshRelEdgeRepresentableFunctor E ≌
      CostructuredArrow spanRepresentableFunctor
        ((pshRelEdgeInclusionFunctor C).obj E) :=
  CategoryTheory.Equivalence.mk
    (costrArrAdjBwd E) (costrArrAdjFwd E)
    (NatIso.ofComponents (fun j =>
      CostructuredArrow.isoMk (Iso.refl _) (by
        simp only [costrArrAdjFwd, costrArrAdjBwd,
          Functor.comp_obj, Functor.id_obj,
          CostructuredArrow.mk_hom_eq_self]
        dsimp [pshRelEdgeRepresentableFunctor]
        simp [Equiv.symm_apply_apply])))
    (NatIso.ofComponents (fun j =>
      CostructuredArrow.isoMk (Iso.refl _) (by
        simp only [costrArrAdjFwd, costrArrAdjBwd,
          Functor.comp_obj, Functor.id_obj,
          CostructuredArrow.mk_hom_eq_self]
        dsimp [pshRelEdgeRepresentableFunctor]
        simp [Equiv.apply_symm_apply])))

/-- The density instance for
`pshRelEdgeRepresentableFunctor`:
every `E : PshRelEdge C` is a canonical colimit
of the representable edges. -/
instance pshRelEdgeRepresentableIsDense :
    (pshRelEdgeRepresentableFunctor (C := C)).IsDense
    where
  isDenseAt E := by
    rw [Functor.isDenseAt_iff]
    obtain ⟨h₁⟩ := spanRepresentableFunctorIsDense.isDenseAt
      ((pshRelEdgeInclusionFunctor C).obj E)
    have h₂ : IsColimit ((pshRelEdgeSepFunctor C).mapCocone
        ((Functor.LeftExtension.mk (𝟭 _)
            spanRepresentableFunctor.rightUnitor.inv).coconeAt
          ((pshRelEdgeInclusionFunctor C).obj E))) := by
      have comm := (pshRelEdgeSepAdjunction C).leftAdjoint_preservesColimits
      haveI : PreservesColimit
          (CostructuredArrow.proj spanRepresentableFunctor
            ((pshRelEdgeInclusionFunctor C).obj E) ⋙
            spanRepresentableFunctor)
          (pshRelEdgeSepFunctor C) :=
        comm.preservesColimitsOfShape.preservesColimit
      exact isColimitOfPreserves (pshRelEdgeSepFunctor C) h₁
    let counitIso : (pshRelEdgeSepFunctor C).obj
          ((pshRelEdgeInclusionFunctor C).obj E) ≅ E :=
      asIso ((pshRelEdgeSepAdjunction C).counit.app E)
    have h₃ := IsColimit.ofIsoColimit h₂
      (Cocone.extendIso _ counitIso)
    have h₄ : IsColimit
        ((Functor.LeftExtension.mk (𝟭 (PshRelEdge C))
            pshRelEdgeRepresentableFunctor.rightUnitor.inv).coconeAt E) :=
      IsColimit.ofWhiskerEquivalence (costrArrAdjEquiv E).symm
        (IsColimit.ofIsoColimit h₃ (Cocone.ext (Iso.refl _) (fun j => by
          dsimp [Cocone.extend, Cocone.extensions,
            Functor.mapCocone, costrArrAdjFwd,
            costrArrAdjEquiv, CategoryTheory.Equivalence.mk,
            Functor.LeftExtension.coconeAt,
            pshRelEdgeRepresentableFunctor]
          rw [Adjunction.homEquiv_counit]
          simp [counitIso, asIso_hom])))
    exact ⟨h₄⟩

end Density

section EndoFunctorClosed

open MonoidalCategory MonoidalClosed

/-- The uncurry at a representable edge: given
`μ : H ⟶ [F, G]`, compose `μ.app(y) ≫ proj`
to get `H(y) → [F(y), G(y)]`, then apply the
object-level uncurry to get
`F(y) ⊗ H(y) → G(y)`. -/
def endoIhomUncurryAtRep
    {C : Type u} [Category.{v} C]
    (F H G :
      PshRelEdge.{u, v, max u v} C ⥤
        PshRelEdge.{u, v, max u v} C)
    (μ : H ⟶ (endoIhomFunctor F).obj G)
    (i : WalkingSpan) (c : Cᵒᵖ) :
    ((tensorLeft F).obj H).obj
      (pshRelEdgeRepresentable i c) ⟶
    G.obj (pshRelEdgeRepresentable i c) :=
  (Closed.adj
    (X := F.obj
      (pshRelEdgeRepresentable i c))
    |>.homEquiv _ _).symm
    (μ.app (pshRelEdgeRepresentable i c) ≫
      endoIhomProj F G i c)

-- The adjunction `tensorLeft F ⊣ endoIhomFunctor F`
-- requires extending the uncurry from representables
-- to all edges via the density colimit (using
-- `Functor.denseAt` / `IsColimit.desc`). These
-- mathlib definitions are not computable. The
-- proof should be stated as a `Prop`-valued theorem
-- (`Nonempty (Closed F)`) using our density instance
-- `pshRelEdgeRepresentableIsDense` and the
-- computable `endoIhomCurry` + `endoIhomUncurryAtRep`.
--
-- Note: mathlib's generic
-- `MonoidalClosed.FunctorCategory.closed` cannot be
-- used here due to a universe gap: it requires ends
-- over `Under j` for `j` an endofunctor, whose
-- objects are at `Type (max (u+1) (v+1))`, while
-- `pshRelEdgeHasLimitsOfSize` provides limits at
-- `{max u v, max u v}`. Our `endoIhomFunctor`
-- avoids this gap via the Yoneda reduction over the
-- small index `WalkingSpan × Cᵒᵖ`.

end EndoFunctorClosed

end GebLean
