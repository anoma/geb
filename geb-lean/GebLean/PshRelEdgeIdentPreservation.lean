import GebLean.PshRelEdgeLimits

/-!
# Identity Extension for the Edge Category

The identity section functor
`pshRelIdentFunctor : PSh(C) ⥤ PshRelEdge C`
preserves exponentials, all finite limits, and
all finite colimits. These results express the
identity extension property (IEP) as a cartesian
closed functor property that also preserves
colimits.

The preservation of colimits is a consequence of
the diagonal relation being determined by the
equality structure of the presheaf, which
commutes with all (co)limit constructions.

## Main results

### Limits and exponentials

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

### Colimits

* `pshRelId_empty`: the identity relation on the
  empty presheaf equals the empty relation
* `pshRelId_coprod`: the identity relation on a
  coproduct presheaf equals the coproduct of
  identity relations
* `pshRelId_coequalizer`: the identity relation on
  a coequalizer presheaf equals the coequalizer
  relation
* `pshRelIdentFunctor_preserves_initial`: the
  identity section functor preserves the initial
  object
* `pshRelIdentFunctor_preserves_coprod`: the
  identity section functor preserves coproducts
* `pshRelIdentFunctor_preserves_coequalizer`: the
  identity section functor preserves coequalizers
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

/-- The identity relation on the empty presheaf
equals the empty relation: the empty type has no
pairs, so both the diagonal and the empty relation
are vacuously the empty set. -/
theorem pshRelId_empty :
    pshRelId (pshEmptyPresheaf.{u, v, w} C) =
      pshRelEmpty C := by
  ext c ⟨e, _⟩
  exact (e.down).elim

/-- The identity relation on a coproduct presheaf
equals the coproduct of identity relations:
`inl(a₁) = inl(a₂)` iff `a₁ = a₂`,
`inr(b₁) = inr(b₂)` iff `b₁ = b₂`, and mixed
pairs are never equal. -/
theorem pshRelId_coprod
    (A B : Cᵒᵖ ⥤ Type w) :
    pshRelId (pshCoprodPresheaf A B) =
      pshRelCoprod (pshRelId A)
        (pshRelId B) := by
  ext c ⟨p, q⟩
  change p = q ↔ _
  constructor
  · rintro rfl
    cases p with
    | inl => exact rfl
    | inr => exact rfl
  · intro h
    cases p with
    | inl a₁ => cases q with
      | inl a₂ => exact congrArg Sum.inl h
      | inr => exact h.elim
    | inr b₁ => cases q with
      | inl => exact h.elim
      | inr b₂ => exact congrArg Sum.inr h

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

/-- The identity section functor preserves the
initial object: `I(0) = (0, 0, empty)` in
`PshRelEdge C`. -/
theorem pshRelIdentFunctor_preserves_initial
    (C : Type u) [Category.{v} C] :
    pshRelIdentFunctor.obj
      (pshEmptyPresheaf.{u, v, w} C) =
      pshRelEdgeInitial C :=
  congrArg (VertEdge.mk _ _)
    (pshRelId_empty (C := C))

/-- The identity section functor preserves
coproducts: `I(A ⊕ B) = I(A) ⊕ I(B)` in
`PshRelEdge C`. This is the identity extension
property for sum types: the diagonal relation
on a coproduct decomposes into the coproduct of
the diagonal relations, with mixed pairs never
equal. -/
theorem pshRelIdentFunctor_preserves_coprod
    (A B : Cᵒᵖ ⥤ Type w) :
    pshRelIdentFunctor.obj
      (pshCoprodPresheaf A B) =
      pshRelEdgeCoprod
        (pshRelIdentFunctor.obj A)
        (pshRelIdentFunctor.obj B) :=
  congrArg (VertEdge.mk _ _)
    (pshRelId_coprod A B)

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

/-- The identity relation on a coequalizer presheaf
equals the coequalizer relation of the identity
section functor applied to the morphisms: two
quotient elements are in the diagonal iff they
have a common representative. -/
theorem pshRelId_coequalizer
    {P Q : Cᵒᵖ ⥤ Type w}
    (α β : P ⟶ Q) :
    pshRelId (pshCoequalizerPresheaf α β) =
      pshRelCoequalizer
        (pshRelIdentFunctor.map α)
        (pshRelIdentFunctor.map β) := by
  ext c ⟨q₁, q₂⟩
  change q₁ = q₂ ↔ _
  simp only [pshRelCoequalizer,
    pshRelIdentFunctor, pshRelId,
    Set.mem_setOf_eq]
  constructor
  · intro h
    induction q₁ using Quot.ind with
    | mk s => exact ⟨s, s, rfl, rfl, h⟩
  · rintro ⟨s, t, hst, hs, ht⟩
    change s = t at hst
    rw [← hs, ← ht, hst]

/-- The identity section functor preserves
coequalizers:
`I(coeq(α, β)) = coeq(I(α), I(β))`
in `PshRelEdge C`. -/
theorem pshRelIdentFunctor_preserves_coequalizer
    {P Q : Cᵒᵖ ⥤ Type w}
    (α β : P ⟶ Q) :
    pshRelIdentFunctor.obj
      (pshCoequalizerPresheaf α β) =
      pshRelEdgeCoequalizer
        (pshRelIdentFunctor.map α)
        (pshRelIdentFunctor.map β) :=
  congrArg (VertEdge.mk _ _)
    (pshRelId_coequalizer α β)

end Preservation

end GebLean
