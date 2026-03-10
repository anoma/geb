import GebLean.PshRelEdgeLimits

/-!
# Identity Extension for the Edge Category

The identity section functor
`pshRelIdentFunctor : PSh(C) ⥤ PshRelEdge C`
preserves exponentials, products, and the terminal
object. These results express the identity extension
property (IEP) as a cartesian closed functor
property.

## Main results

* `pshRelId_unit`: the identity relation on the unit
  presheaf equals the full relation
* `pshRelId_prod`: the identity relation on a product
  presheaf equals the product of identity relations
* `pshRelIdentFunctor_preserves_exp`: the identity
  section functor preserves exponentials
* `pshRelIdentFunctor_preserves_prod`: the identity
  section functor preserves products
* `pshRelIdentFunctor_preserves_terminal`: the
  identity section functor preserves the terminal
  object
-/

namespace GebLean

open CategoryTheory Limits

universe u v w

section UnitAndProd

variable (C : Type u) [Category.{v} C]

/-- The identity relation on the unit presheaf
equals the full relation: since `ULift PUnit`
has a unique element, every pair satisfies
the diagonal condition. -/
theorem pshRelId_unit :
    pshRelId (pshUnitPresheaf.{u, v, w} C) =
      pshRelFull C := by
  ext c ⟨u₁, u₂⟩
  simp only [pshRelId, pshRelFull,
    Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact ULift.ext _ _
    (Subsingleton.elim _ _)

variable {C}

/-- The identity relation on a product presheaf
equals the product of identity relations: a pair
of pairs is in the diagonal iff both components
are in their respective diagonals. -/
theorem pshRelId_prod
    (A B : Cᵒᵖ ⥤ Type w) :
    pshRelId (pshProdPresheaf A B) =
      pshRelProd (pshRelId A) (pshRelId B) := by
  ext c ⟨⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩
  simp only [pshRelId, pshRelProd,
    Set.mem_setOf_eq]
  exact (Prod.mk.injEq a₁ b₁ a₂ b₂).symm ▸
    Iff.rfl

end UnitAndProd

section Preservation

variable {C : Type u} [Category.{v} C]

/-- The identity section functor preserves
exponentials: `I(A.functorHom B) = [I(A), I(B)]`
in `PshRelEdge C`. This is the identity extension
property for function types: the diagonal
relation on the internal hom equals the arrow
relation of the diagonal relations. -/
theorem pshRelIdentFunctor_preserves_exp
    (A B : Cᵒᵖ ⥤ Type (max u v)) :
    pshRelIdentFunctor.obj (A.functorHom B) =
      pshRelEdgeExp
        (pshRelIdentFunctor.obj A)
        (pshRelIdentFunctor.obj B) :=
  congrArg (VertEdge.mk _ _)
    (pshArrowRel_id A B).symm

/-- The identity section functor preserves
products: `I(A × B) = I(A) × I(B)` in
`PshRelEdge C`. This is the identity extension
property for product types: the diagonal
relation on a product equals the product of the
diagonal relations. -/
theorem pshRelIdentFunctor_preserves_prod
    (A B : Cᵒᵖ ⥤ Type w) :
    pshRelIdentFunctor.obj
      (pshProdPresheaf A B) =
      pshRelEdgeProd
        (pshRelIdentFunctor.obj A)
        (pshRelIdentFunctor.obj B) :=
  congrArg (VertEdge.mk _ _)
    (pshRelId_prod A B)

/-- The identity section functor preserves the
terminal object: `I(1) = (1, 1, full)` in
`PshRelEdge C`. The identity relation on the
unit presheaf is the full relation since the
unit type has a unique element. -/
theorem pshRelIdentFunctor_preserves_terminal
    (C : Type u) [Category.{v} C] :
    pshRelIdentFunctor.obj
      (pshUnitPresheaf.{u, v, w} C) =
      pshRelEdgeTerminal C :=
  congrArg (VertEdge.mk _ _)
    (pshRelId_unit C)

/-- The identity relation on an equalizer presheaf
equals the equalizer relation of the identity
section functor applied to the morphisms: two
subtype elements are in the diagonal iff their
underlying values are. -/
theorem pshRelId_equalizer
    {P Q : Cᵒᵖ ⥤ Type w}
    (α β : P ⟶ Q) :
    pshRelId (pshEqualizerPresheaf α β) =
      pshRelEqualizer
        (pshRelIdentFunctor.map α)
        (pshRelIdentFunctor.map β) := by
  ext c ⟨⟨p₁, h₁⟩, ⟨p₂, h₂⟩⟩
  simp only [pshRelId, pshRelEqualizer,
    pshRelIdentFunctor, Set.mem_setOf_eq]
  exact ⟨fun h => congrArg Subtype.val h,
    fun h => Subtype.ext h⟩

/-- The identity section functor preserves
equalizers: `I(eq(α, β)) = eq(I(α), I(β))`
in `PshRelEdge C`. -/
theorem pshRelIdentFunctor_preserves_equalizer
    {P Q : Cᵒᵖ ⥤ Type w}
    (α β : P ⟶ Q) :
    pshRelIdentFunctor.obj
      (pshEqualizerPresheaf α β) =
      pshRelEdgeEqualizer
        (pshRelIdentFunctor.map α)
        (pshRelIdentFunctor.map β) :=
  congrArg (VertEdge.mk _ _)
    (pshRelId_equalizer α β)

end Preservation

end GebLean
