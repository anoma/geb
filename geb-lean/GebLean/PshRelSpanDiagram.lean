import GebLean.PshRelDouble
import GebLean.RelSpanDiagram
import GebLean.Utilities.Profunctors
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Presheaf Relational Span Category

The diagram category `PshRelSpanObj` generalizes
`RelSpanObj` from `Type`/`Prop` to presheaves on
an arbitrary category `C`, using `PshRel P Q`
(subfunctors of the product presheaf) as
relations.

`RelSpanObj` is the special case where `C` is the
terminal category.
-/

open CategoryTheory

namespace GebLean

universe u v w u' v' w' u'' v''

variable (C : Type u) [Category.{v} C]

/-- Objects of the presheaf relational span
category: either a type-node for a presheaf
`P : Cᵒᵖ ⥤ Type w`, or a relation-node for a
pair of presheaves with a `PshRel` between
them. -/
inductive PshRelSpanObj :
    Type (max u v (w + 1)) where
  | typeNode : (Cᵒᵖ ⥤ Type w) → PshRelSpanObj
  | relNode :
    (P Q : Cᵒᵖ ⥤ Type w) →
    PshRel P Q → PshRelSpanObj

/-- Morphisms of the presheaf relational span
category: identity morphisms for each object,
and a pair of projections from each
relation-node to its endpoint type-nodes. -/
inductive PshRelSpanHom :
    PshRelSpanObj C →
    PshRelSpanObj C →
    Type (max u v (w + 1)) where
  | id : (X : PshRelSpanObj C) →
    PshRelSpanHom X X
  | fstProj :
    (P Q : Cᵒᵖ ⥤ Type w) →
    (R : PshRel P Q) →
    PshRelSpanHom (.relNode P Q R)
      (.typeNode P)
  | sndProj :
    (P Q : Cᵒᵖ ⥤ Type w) →
    (R : PshRel P Q) →
    PshRelSpanHom (.relNode P Q R)
      (.typeNode Q)

/-- Composition of morphisms in
`PshRelSpanObj`. No composable pair of
non-identity morphisms exists, since all
generators map from relation-nodes to
type-nodes. -/
def PshRelSpanHom.comp :
    {X Y Z : PshRelSpanObj C} →
    PshRelSpanHom C X Y →
    PshRelSpanHom C Y Z →
    PshRelSpanHom C X Z
  | _, _, _, .id _, g => g
  | _, _, _, f, .id _ => f

instance PshRelSpanCatStruct :
    CategoryStruct
      (PshRelSpanObj.{u, v, w} C) where
  Hom := PshRelSpanHom C
  id X := PshRelSpanHom.id X
  comp := PshRelSpanHom.comp C

theorem PshRelSpanHom.id_comp
    {X Y : PshRelSpanObj C}
    (f : PshRelSpanHom C X Y) :
    PshRelSpanHom.comp C (.id X) f = f := by
  cases f <;> rfl

theorem PshRelSpanHom.comp_id
    {X Y : PshRelSpanObj C}
    (f : PshRelSpanHom C X Y) :
    PshRelSpanHom.comp C f (.id Y) = f := by
  cases f <;> rfl

theorem PshRelSpanHom.assoc
    {W X Y Z : PshRelSpanObj C}
    (f : PshRelSpanHom C W X)
    (g : PshRelSpanHom C X Y)
    (h : PshRelSpanHom C Y Z) :
    PshRelSpanHom.comp C
      (PshRelSpanHom.comp C f g) h =
    PshRelSpanHom.comp C f
      (PshRelSpanHom.comp C g h) := by
  cases f <;> cases g <;> cases h <;> rfl

instance PshRelSpanCat :
    SmallCategory.{max u v (w + 1)} (PshRelSpanObj.{u, v, w} C) where
  id_comp := PshRelSpanHom.id_comp C
  comp_id := PshRelSpanHom.comp_id C
  assoc := PshRelSpanHom.assoc C

/-- Functors from `PshRelSpanObj C` to an
arbitrary target category `E`. -/
abbrev PshParametricFunctor
    (E : Type u'') [Category.{v''} E] :=
  PshRelSpanObj.{u, v, w} C ⥤ E

/-- Copresheaf-valued parametric functors on
`PshRelSpanObj C`: `PshParametricFunctor`
specialized to the presheaf category
`Dᵒᵖ ⥤ Type w'`.

By uncurrying, this is equivalent to
`(PshRelSpanObj C × D)ᵒᵖ ⥤ Type w'`, a
presheaf topos. The case `D` = discrete
unit category recovers `Type w'`-valued
parametric functors. -/
abbrev PshParametricCopresheaf
    (D : Type u') [Category.{v'} D] :=
  PshParametricFunctor.{u, v, w, max u' v' (w' + 1), max u' w'}
    C (Dᵒᵖ ⥤ Type w')

/-- The currying equivalence identifying
copresheaf-valued parametric functors with
copresheaves on the product category
`PshRelSpanObj C × Dᵒᵖ`. -/
def pshParametricCatAsCopresheaf
    (D : Type u') [Category.{v'} D] :
    (PshParametricCopresheaf C D) ≌
    (PshRelSpanObj.{u, v, w} C × Dᵒᵖ ⥤
      Type w') :=
  Functor.currying

/-- The presheaf-category equivalence: the
category of copresheaf-valued parametric
functors is equivalent to a presheaf
topos on `(PshRelSpanObj C)ᵒᵖ × D`.

Constructed by composing the currying
equivalence with precomposition by
`pshRelSpanProdOpFwd`. -/
def pshParametricCatAsPresheaf
    (D : Type u') [Category.{v'} D] :
    (PshParametricCopresheaf C D) ≌
    (((PshRelSpanObj.{u, v, w} C)ᵒᵖ × D)ᵒᵖ ⥤
      Type w') :=
  CategoryTheory.Equivalence.trans
    (pshParametricCatAsCopresheaf C D)
    ((opProdOpProdOpEquiv.{max u v (w + 1),
        max u v (w + 1), v', u'}
      (PshRelSpanObj C) D).congrLeft
        (E := Type w')).symm

section RelSpanPshRelSpanEquiv

/-- Convert a `Prop`-valued relation to a
`TypeRel`, i.e., a subfunctor of the product
presheaf over `Discrete PUnit`. The subfunctor
assigns `{ p | R p.1 p.2 }` at every object;
the restriction condition is trivial since the
only morphism in `(Discrete PUnit)ᵒᵖ` is the
identity. -/
def propRelToTypeRel {I₀ I₁ : Type}
    (R : I₀ → I₁ → Prop) :
    TypeRel I₀ I₁ where
  obj _ := { p | R p.1 p.2 }
  map {U V} i x hx := by
    have hi : i = 𝟙 U := by
      obtain ⟨⟨⟩⟩ := U
      obtain ⟨⟨⟩⟩ := V
      exact Subsingleton.elim _ _
    subst hi
    simp only [Set.mem_preimage]
    exact hx

/-- Convert a `TypeRel` (subfunctor of the
product presheaf over `Discrete PUnit`) back to
a `Prop`-valued relation by evaluating at the
single object `op ⟨PUnit.unit⟩`. -/
def typeRelToPropRel {I₀ I₁ : Type}
    (S : TypeRel I₀ I₁) :
    I₀ → I₁ → Prop :=
  fun a b =>
    (a, b) ∈ S.obj (Opposite.op ⟨PUnit.unit⟩)

@[simp]
theorem typeRelToPropRel_propRelToTypeRel
    {I₀ I₁ : Type}
    (R : I₀ → I₁ → Prop) :
    typeRelToPropRel (propRelToTypeRel R) = R :=
  rfl

@[simp]
theorem propRelToTypeRel_typeRelToPropRel
    {I₀ I₁ : Type}
    (S : TypeRel I₀ I₁) :
    propRelToTypeRel (typeRelToPropRel S) = S := by
  ext ⟨⟨⟩⟩
  rfl

/-- Functor embedding `RelSpanObj` into
`PshRelSpanObj (Discrete PUnit)` by sending
each type to its constant presheaf and each
`Prop`-valued relation to the corresponding
subfunctor via `propRelToTypeRel`. -/
def relSpanToPshRelSpan :
    RelSpanObj ⥤
    PshRelSpanObj.{0, 0, 0}
      (Discrete PUnit) where
  obj
    | .typeNode I =>
      .typeNode (typeToPsh.obj I)
    | .relNode I₀ I₁ R =>
      .relNode _ _ (propRelToTypeRel R)
  map {X Y} f :=
    match X, Y, f with
    | _, _, .id _ => .id _
    | _, _, .fstProj I₀ I₁ R =>
      .fstProj _ _ (propRelToTypeRel R)
    | _, _, .sndProj I₀ I₁ R =>
      .sndProj _ _ (propRelToTypeRel R)
  map_id X := by cases X <;> rfl
  map_comp {X Y Z} f g := by
    cases f <;> cases g <;> rfl

/-- Extract a `Prop`-valued relation from a
`PshRel` over `Discrete PUnit` by evaluating
the subfunctor at the single object. -/
def pshRelToPropRel
    {P Q : (Discrete PUnit)ᵒᵖ ⥤ Type}
    (R : PshRel P Q) :
    typeEvalUnit.obj P →
    typeEvalUnit.obj Q → Prop :=
  fun a b =>
    (a, b) ∈
      R.obj (Opposite.op ⟨PUnit.unit⟩)

/-- Functor from
`PshRelSpanObj (Discrete PUnit)` to
`RelSpanObj`, sending each presheaf to its
evaluation at the single object and each
`PshRel` to its extracted `Prop`-valued
relation. -/
def pshRelSpanToRelSpan :
    PshRelSpanObj.{0, 0, 0}
      (Discrete PUnit) ⥤
    RelSpanObj where
  obj
    | .typeNode P =>
      .typeNode (typeEvalUnit.obj P)
    | .relNode P Q R =>
      .relNode _ _ (pshRelToPropRel R)
  map {X Y} f :=
    match X, Y, f with
    | _, _, .id _ => .id _
    | _, _, .fstProj P Q R =>
      .fstProj _ _ (pshRelToPropRel R)
    | _, _, .sndProj P Q R =>
      .sndProj _ _ (pshRelToPropRel R)
  map_id X := by cases X <;> rfl
  map_comp {X Y Z} f g := by
    cases f <;> cases g <;> rfl

/-- The round-trip
`relSpanToPshRelSpan ⋙ pshRelSpanToRelSpan`
acts as the identity on objects of
`RelSpanObj`. -/
theorem relSpanPshRelSpan_unitObj
    (X : RelSpanObj) :
    pshRelSpanToRelSpan.obj
      (relSpanToPshRelSpan.obj X) = X := by
  cases X with
  | typeNode I => rfl
  | relNode I₀ I₁ R => rfl

/-- A presheaf on `(Discrete PUnit)ᵒᵖ` is
equal to the constant presheaf at its value
on the single object. -/
theorem pshOnUnit_eq_const
    (P : (Discrete PUnit)ᵒᵖ ⥤ Type) :
    typeToPsh.obj (typeEvalUnit.obj P) = P :=
  _root_.CategoryTheory.Functor.ext
    (fun ⟨⟨⟨⟩⟩⟩ => rfl)
    (fun ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩ f => by
      simp only [eqToHom_refl,
        Category.id_comp, Category.comp_id]
      have : f = 𝟙 _ := Subsingleton.elim _ _
      rw [this, P.map_id]; rfl)

/-- Congruence lemma for `PshRelSpanObj.relNode`
with heterogeneous equality for the relation
argument. -/
theorem PshRelSpanObj.relNode_heq_congr
    {P₁ P₂ Q₁ Q₂ :
      (Discrete PUnit)ᵒᵖ ⥤ Type}
    {R₁ : PshRel P₁ Q₁}
    {R₂ : PshRel P₂ Q₂}
    (hP : P₁ = P₂) (hQ : Q₁ = Q₂)
    (hR : HEq R₁ R₂) :
    PshRelSpanObj.relNode P₁ Q₁ R₁ =
    PshRelSpanObj.relNode P₂ Q₂ R₂ := by
  cases hP; cases hQ; cases hR; rfl

theorem relSpanPshRelSpan_counitObj
    (X : PshRelSpanObj.{0, 0, 0}
      (Discrete PUnit)) :
    relSpanToPshRelSpan.obj
      (pshRelSpanToRelSpan.obj X) = X := by
  cases X with
  | typeNode P =>
    exact congrArg PshRelSpanObj.typeNode
      (pshOnUnit_eq_const P)
  | relNode P Q R =>
    change PshRelSpanObj.relNode
      (typeToPsh.obj (typeEvalUnit.obj P))
      (typeToPsh.obj (typeEvalUnit.obj Q))
      (propRelToTypeRel (pshRelToPropRel R))
    = PshRelSpanObj.relNode P Q R
    exact @Eq.ndrec _
      (typeToPsh.obj (typeEvalUnit.obj P))
      (fun X => ∀ (S : PshRel X Q),
        PshRelSpanObj.relNode
          (typeToPsh.obj
            (typeEvalUnit.obj X))
          (typeToPsh.obj
            (typeEvalUnit.obj Q))
          (propRelToTypeRel
            (pshRelToPropRel S))
        = PshRelSpanObj.relNode X Q S)
      (@Eq.ndrec _
        (typeToPsh.obj
          (typeEvalUnit.obj Q))
        (fun Y =>
          ∀ (S : PshRel
            (typeToPsh.obj
              (typeEvalUnit.obj P)) Y),
          PshRelSpanObj.relNode
            (typeToPsh.obj
              (typeEvalUnit.obj
                (typeToPsh.obj
                  (typeEvalUnit.obj P))))
            (typeToPsh.obj
              (typeEvalUnit.obj Y))
            (propRelToTypeRel
              (pshRelToPropRel S))
          = PshRelSpanObj.relNode
            (typeToPsh.obj
              (typeEvalUnit.obj P)) Y S)
        (fun S => congrArg
          (PshRelSpanObj.relNode _ _)
          (propRelToTypeRel_typeRelToPropRel
            S))
        Q
        (pshOnUnit_eq_const Q))
      P
      (pshOnUnit_eq_const P)
      R

/-- The equivalence
`RelSpanObj ≌ PshRelSpanObj (Discrete PUnit)`,
witnessing that `RelSpanObj` is the special
case of the presheaf relational span category
over the terminal category. -/
theorem relSpanPshRelSpan_unit :
    relSpanToPshRelSpan ⋙
      pshRelSpanToRelSpan = 𝟭 _ :=
  _root_.CategoryTheory.Functor.ext
    relSpanPshRelSpan_unitObj
    (fun {X Y} f => by
      cases f with
      | id X => cases X <;> rfl
      | fstProj => rfl
      | sndProj => rfl)

/-- `fstProj` is invariant under propositional
equality of its arguments. -/
theorem PshRelSpanHom.fstProj_heq
    {P₁ P₂ Q₁ Q₂ :
      (Discrete PUnit)ᵒᵖ ⥤ Type}
    {R₁ : PshRel P₁ Q₁}
    {R₂ : PshRel P₂ Q₂}
    (hP : P₁ = P₂) (hQ : Q₁ = Q₂)
    (hR : HEq R₁ R₂) :
    HEq (PshRelSpanHom.fstProj P₁ Q₁ R₁)
      (PshRelSpanHom.fstProj P₂ Q₂ R₂) := by
  cases hP; cases hQ; cases hR; rfl

/-- `sndProj` is invariant under propositional
equality of its arguments. -/
theorem PshRelSpanHom.sndProj_heq
    {P₁ P₂ Q₁ Q₂ :
      (Discrete PUnit)ᵒᵖ ⥤ Type}
    {R₁ : PshRel P₁ Q₁}
    {R₂ : PshRel P₂ Q₂}
    (hP : P₁ = P₂) (hQ : Q₁ = Q₂)
    (hR : HEq R₁ R₂) :
    HEq (PshRelSpanHom.sndProj P₁ Q₁ R₁)
      (PshRelSpanHom.sndProj P₂ Q₂ R₂) := by
  cases hP; cases hQ; cases hR; rfl

/-- The `HEq` between `propRelToTypeRel
(pshRelToPropRel R)` and `R`, used for the
counit morphism compatibility. -/
theorem propRelToTypeRel_pshRelToPropRel_heq
    (P Q : (Discrete PUnit)ᵒᵖ ⥤ Type)
    (R : PshRel P Q) :
    HEq (propRelToTypeRel (pshRelToPropRel R))
      R := by
  have hP := pshOnUnit_eq_const P
  have hQ := pshOnUnit_eq_const Q
  exact @Eq.ndrec _
    (typeToPsh.obj (typeEvalUnit.obj P))
    (fun X => ∀ (S : PshRel X Q),
      HEq (propRelToTypeRel
        (pshRelToPropRel S)) S)
    (@Eq.ndrec _
      (typeToPsh.obj (typeEvalUnit.obj Q))
      (fun Y => ∀ (S : PshRel
          (typeToPsh.obj
            (typeEvalUnit.obj P)) Y),
        HEq (propRelToTypeRel
          (pshRelToPropRel S)) S)
      (fun S => heq_of_eq
        (propRelToTypeRel_typeRelToPropRel S))
      Q hQ)
    P hP R

@[simp]
theorem counit_map_fstProj
    (P Q : (Discrete PUnit)ᵒᵖ ⥤ Type)
    (R : PshRel P Q) :
    relSpanToPshRelSpan.map
      (pshRelSpanToRelSpan.map
        (PshRelSpanHom.fstProj P Q R)) =
    PshRelSpanHom.fstProj _ _
      (propRelToTypeRel
        (pshRelToPropRel R)) := rfl

@[simp]
theorem counit_map_sndProj
    (P Q : (Discrete PUnit)ᵒᵖ ⥤ Type)
    (R : PshRel P Q) :
    relSpanToPshRelSpan.map
      (pshRelSpanToRelSpan.map
        (PshRelSpanHom.sndProj P Q R)) =
    PshRelSpanHom.sndProj _ _
      (propRelToTypeRel
        (pshRelToPropRel R)) := rfl

/-- The round-trip
`pshRelSpanToRelSpan ⋙ relSpanToPshRelSpan`
acts as the identity on morphisms of
`PshRelSpanObj (Discrete PUnit)`, up to
`eqToHom` transport from the object-level
equality. -/
theorem relSpanPshRelSpan_counit_map
    {X Y : PshRelSpanObj.{0, 0, 0}
      (Discrete PUnit)}
    (f : X ⟶ Y) :
    relSpanToPshRelSpan.map
      (pshRelSpanToRelSpan.map f) =
    eqToHom
      (relSpanPshRelSpan_counitObj X) ≫
      f ≫
      eqToHom
        (relSpanPshRelSpan_counitObj Y).symm
      := by
  match X, Y, f with
  | _, _, .id (.typeNode P) =>
    symm
    rw [← heq_iff_comp_eqToHom_comp]
    exact congr_arg_heq PshRelSpanHom.id
      (relSpanPshRelSpan_counitObj
        (.typeNode P)).symm
  | _, _, .id (.relNode P Q R) =>
    symm
    rw [← heq_iff_comp_eqToHom_comp]
    exact congr_arg_heq PshRelSpanHom.id
      (relSpanPshRelSpan_counitObj
        (.relNode P Q R)).symm
  | _, _, .fstProj P Q R =>
    simp only [counit_map_fstProj]
    symm
    rw [← heq_iff_comp_eqToHom_comp]
    exact PshRelSpanHom.fstProj_heq
      (pshOnUnit_eq_const P).symm
      (pshOnUnit_eq_const Q).symm
      (propRelToTypeRel_pshRelToPropRel_heq
        P Q R).symm
  | _, _, .sndProj P Q R =>
    simp only [counit_map_sndProj]
    symm
    rw [← heq_iff_comp_eqToHom_comp]
    exact PshRelSpanHom.sndProj_heq
      (pshOnUnit_eq_const P).symm
      (pshOnUnit_eq_const Q).symm
      (propRelToTypeRel_pshRelToPropRel_heq
        P Q R).symm

theorem relSpanPshRelSpan_counit :
    pshRelSpanToRelSpan ⋙
      relSpanToPshRelSpan =
    𝟭 (PshRelSpanObj.{0, 0, 0}
      (Discrete PUnit)) :=
  _root_.CategoryTheory.Functor.ext
    relSpanPshRelSpan_counitObj
    (fun {_ _} f =>
      relSpanPshRelSpan_counit_map f)

/-- `RelSpanObj` is categorically isomorphic
to `PshRelSpanObj (Discrete PUnit)`. -/
def relSpanPshRelSpanIso :
    RelSpanObj ≅Cat
    PshRelSpanObj.{0, 0, 0}
      (Discrete PUnit) where
  hom := relSpanToPshRelSpan.toCatHom
  inv := pshRelSpanToRelSpan.toCatHom
  hom_inv_id := by
    change (relSpanToPshRelSpan ⋙
      pshRelSpanToRelSpan).toCatHom =
      (𝟭 _).toCatHom
    congr 1
    exact relSpanPshRelSpan_unit
  inv_hom_id := by
    change (pshRelSpanToRelSpan ⋙
      relSpanToPshRelSpan).toCatHom =
      (𝟭 _).toCatHom
    congr 1
    exact relSpanPshRelSpan_counit

/-- The equivalence between
`ParametricFunctor E` and
`PshParametricFunctor (Discrete PUnit) E`,
obtained from the categorical isomorphism
`relSpanPshRelSpanIso` between `RelSpanObj`
and `PshRelSpanObj (Discrete PUnit)`. -/
def parametricFunctorEquiv
    (E : Type u'') [Category.{v''} E] :
    ParametricFunctor E ≌
    PshParametricFunctor.{0, 0, 0}
      (Discrete PUnit) E :=
  (Cat.equivOfIso
    relSpanPshRelSpanIso).congrLeft (E := E)

/-- The equivalence between
`ParametricCopresheaf` (`RelSpanObj ⥤ Type 1`)
and `PshParametricCopresheaf` over the terminal
category, obtained by chaining:
1. `parametricFunctorEquiv` (source categories)
2. The presheaf-type equivalence on `Type 1`
   (target category). -/
def parametricCopresheafEquiv :
    ParametricCopresheaf ≌
    PshParametricCopresheaf.{0, 0, 0, 0, 0, 1}
      (Discrete PUnit) (Discrete PUnit) :=
  (parametricFunctorEquiv (Type 1)).trans
    (((Discrete.opposite PUnit).congrLeft
      (E := Type 1) |>.trans
      (CategoryTheory.Functor.equiv
        (C := Type 1))).symm.congrRight
      (E := PshRelSpanObj.{0, 0, 0}
        (Discrete PUnit)))

end RelSpanPshRelSpanEquiv

section PshCovariantEmbedding

variable {C : Type u} [Category.{v} C]

/-- The covariant embedding maps an
endofunctor `G` on `PSh(C)` to a parametric
functor `PshRelSpanObj C ⥤ (Cᵒᵖ ⥤ Type w)`.
Type-nodes map to `G.obj P`; relation-nodes
map to `(pshBarrLiftSkel G R).toFunctor`.
Projections are the subfunctor inclusion
composed with the product projections. -/
def pshCovariantEmbedding :
    ((Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) ⥤
    PshParametricFunctor.{u, v, w}
      C (Cᵒᵖ ⥤ Type w) where
  obj G :=
    { obj := fun X =>
        match X with
        | .typeNode P => G.obj P
        | .relNode P Q R =>
          (pshBarrLiftSkel G R).toFunctor
      map := fun {X Y} f =>
        match X, Y, f with
        | _, _, .id _ => 𝟙 _
        | _, _, .fstProj P Q R =>
          (pshBarrLiftSkel G R).ι ≫
            pshProdFst (G.obj P) (G.obj Q)
        | _, _, .sndProj P Q R =>
          (pshBarrLiftSkel G R).ι ≫
            pshProdSnd (G.obj P) (G.obj Q)
      map_id := by
        intro X; cases X <;> rfl
      map_comp := by
        intro X Y Z f g
        cases f <;> cases g <;> rfl }
  map {G H} α :=
    { app := fun X =>
        match X with
        | .typeNode P => α.app P
        | .relNode P Q R =>
          pshBarrLiftSkelMap α R
      naturality := by
        intro X Y f
        match X, Y, f with
        | _, _, .id _ => simp
        | _, _, .fstProj P Q R =>
          simp [pshBarrLiftSkelMap_ι_fst]
        | _, _, .sndProj P Q R =>
          simp [pshBarrLiftSkelMap_ι_snd] }
  map_id G := by
    apply NatTrans.ext; funext X
    cases X with
    | typeNode P => simp
    | relNode P Q R => simp
  map_comp {G H K} α β := by
    apply NatTrans.ext; funext X
    cases X with
    | typeNode P => simp
    | relNode P Q R => simp

/-- The preimage extracts `typeNode` components
from a natural transformation between
embedded endofunctors. Naturality uses
`pshRelGraph` and `pshBarrLiftSkel_graph`
to connect the projections. -/
def pshCovariantEmbedding_fullyFaithful :
    (pshCovariantEmbedding
      (C := C)).FullyFaithful where
  preimage {G H} β :=
    { app := fun P => β.app (.typeNode P)
      naturality := fun {P Q} f => by
        have nf :=
          β.naturality
            (.fstProj P Q (pshRelGraph f))
        have ns :=
          β.naturality
            (.sndProj P Q (pshRelGraph f))
        dsimp [pshCovariantEmbedding]
          at nf ns
        ext c x
        simp only [NatTrans.comp_app,
          types_comp_apply]
        let w := (G.map
          (pshRelGraph_ι_fst_iso f).inv
          ).app c x
        have hw :
          (pshBarrLift G (Over.mk
            (pshRelGraph f).ι)).hom.app
            c w =
          (x, (G.map f).app c x) := by
          apply Prod.ext
          · change (G.map ((pshRelGraph f).ι ≫
              pshProdFst P Q)).app c w = x
            exact congr_fun (congr_app
              (G.mapIso
                (pshRelGraph_ι_fst_iso f)
              ).inv_hom_id c) x
          · change (G.map ((pshRelGraph f).ι ≫
              pshProdSnd P Q)).app c w =
              (G.map f).app c x
            rw [pshRelGraph_ι_snd]
            let gIso := pshRelGraph_ι_fst_iso f
            exact congr_fun (congr_app
              (show G.map gIso.inv ≫
                G.map (gIso.hom ≫ f) =
                G.map f from by
                rw [G.map_comp,
                  ← Category.assoc,
                  ← G.map_comp,
                  gIso.inv_hom_id,
                  G.map_id,
                  Category.id_comp])
              c) x
        let e : (pshBarrLiftSkel G
          (pshRelGraph f)).toFunctor.obj
            c :=
          ⟨(x, (G.map f).app c x), w, hw⟩
        let m := (β.app (.relNode P Q
          (pshRelGraph f))).app c e
        have hfst :=
          congr_fun (congr_app nf c) e
        have hsnd :=
          congr_fun (congr_app ns c) e
        simp only [NatTrans.comp_app,
          types_comp_apply] at hfst hsnd
        dsimp [pshProdFst, pshProdSnd,
          FunctorToTypes.prod.fst,
          FunctorToTypes.prod.snd]
          at hfst hsnd
        have hgraph :=
          congr_fun (congr_app
            (pshBarrLiftSkel_graph_ι_snd
              H f) c) m
        dsimp [pshProdFst, pshProdSnd,
          FunctorToTypes.prod.fst,
          FunctorToTypes.prod.snd]
          at hgraph
        rw [hsnd, hfst, ← hgraph]
    }
  map_preimage {G H} β := by
    apply NatTrans.ext; funext X
    cases X with
    | typeNode P => rfl
    | relNode P Q R =>
      dsimp [pshCovariantEmbedding]
      apply (cancel_mono
        (pshBarrLiftSkel H R).ι).mp
      apply pshProdPresheaf_hom_ext
      · simp only [Category.assoc,
          pshBarrLiftSkelMap_ι_fst]
        have := β.naturality
          (.fstProj P Q R)
        dsimp [pshCovariantEmbedding]
          at this
        simp only [Category.assoc]
          at this
        exact this
      · simp only [Category.assoc,
          pshBarrLiftSkelMap_ι_snd]
        have := β.naturality
          (.sndProj P Q R)
        dsimp [pshCovariantEmbedding]
          at this
        simp only [Category.assoc]
          at this
        exact this

end PshCovariantEmbedding

end GebLean
