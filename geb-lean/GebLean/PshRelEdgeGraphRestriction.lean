import GebLean.PshRelDouble
import GebLean.PshRelEdgeLimits
import Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# Graph Restriction for PshRelEdge

When presheaf relations are restricted to graph
relations, the parametricity condition
(`pshRelRelated`) reduces to a commutativity
condition (naturality square). This is the
presheaf-level analogue of Wadler's observation
(Sections 3.1, 3.5, 6) that parametricity
specialized to functions yields naturality.

## Main results

* `pshBarrLiftRel_graph_related_iff`: the
  parametricity condition for the Barr extension
  at a graph relation is equivalent to a
  commutativity condition (naturality square)
* `pshBarrLiftRel_graph_related_hetero_iff`:
  heterogeneous version for two different graph
  relations
* `pshBarrLiftRel_id_related_iff`: the
  parametricity condition for the Barr extension
  at an identity relation is equivalent to
  equality of the two morphism components
* `arrowEndofunctor`: the endofunctor on the arrow
  category induced by a presheaf endofunctor
* `pshBarrLiftEdge_graphNatIso`: the Barr lift
  edge functor restricted to graphs agrees with
  `arrowEndofunctor` followed by the graph functor
* `pshBarrLiftEdge_identNatIso`: the Barr lift
  edge functor composed with the identity section
  agrees with `G` composed with the identity
  section
* `natTransToBarrMap` / `barrMapToNatTrans`:
  bijection between endofunctor natural
  transformations `F ⟶ G` and natural
  transformations between Barr embeddings
  `pshBarrEmbedding F ⟶ pshBarrEmbedding G`
* `pshBarrEmbeddingFunctor`: the Barr embedding
  as a functor from endofunctors on `PSh(C)` to
  functors `PSh(C) ⥤ PshRelEdge C`
* `pshBarrEmbeddingFunctor_fullyFaithful`: the
  Barr embedding functor is fully faithful
* `natTransToBarrEndo` / `barrEndoToNatTrans`:
  specializations to the endomorphism case `F = G`
  (the rearrangement free theorem)
* `MapFamily`: natural transformation type for
  map-like operations `(P ⟶ Q) → (G P ⟶ G Q)`
* `mapFamilyDecompLeft` / `mapFamilyDecompRight`:
  every map family decomposes as its identity
  component composed with the functor action
  (Wadler Section 3.5)
* `mapFamilyToNatTrans` / `natTransToMapFamily`:
  bijection between map families and natural
  transformations `G ⟶ G`
* `IsGraphEdge`: predicate for edges whose
  relation is a graph
* `pshRelEdgeGraphSubcatFunctor`: lift of the
  graph functor to the full subcategory
* `pshRelEdgeGraphSubcatFullyFaithful`: the
  lifted functor is fully faithful
* `pshRelEdgeGraphSubcat_essSurj`: the lifted
  functor is essentially surjective

## Sections and Yoneda extension

* `ParametricCone`: cone over the Barr-lifted
  edge functor with terminal vertex
* `PresheafSection`: natural transformation
  from the terminal presheaf endofunctor to `G`
* `parametricConeEquivPresheafSection`:
  parametric cones biject with presheaf sections
* `presheafSectionEquivInitial`: presheaf
  sections are determined by their value at the
  initial presheaf
* `RepresentableSection`: section restricted to
  the image of an embedding `Y : C ⥤ PSh(C)`
* `presheafSectionEquivRepresentable`: full
  equivalence under weak initiality
* `presheafSection_empty_of_initial`: no
  sections when `G(∅)` is initial
* `presheafSection_unique_of_terminal`:
  sections are unique when `G(∅)` is terminal
-/

universe u v w

namespace GebLean

open CategoryTheory

variable {C : Type u} [Category.{v} C]

section GraphRestriction

/-- The parametricity condition for the Barr
extension at a graph relation reduces to
commutativity of the naturality square. Given
`σ_P : G(P) ⟶ G(P)` and `σ_Q : G(Q) ⟶ G(Q)`,
the relatedness condition
`pshRelRelated σ_P σ_Q
  (pshBarrLiftRel G (pshRelGraph α))
  (pshBarrLiftRel G (pshRelGraph α))`
holds iff `σ_P ≫ G.map α = G.map α ≫ σ_Q`. -/
theorem pshBarrLiftRel_graph_related_iff
    {P Q : Cᵒᵖ ⥤ Type w}
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (α : P ⟶ Q)
    {σ_P : G.obj P ⟶ G.obj P}
    {σ_Q : G.obj Q ⟶ G.obj Q} :
    pshRelRelated σ_P σ_Q
      (pshBarrLiftRel G (pshRelGraph α))
      (pshBarrLiftRel G (pshRelGraph α)) ↔
    σ_P ≫ G.map α = G.map α ≫ σ_Q := by
  rw [pshBarrLiftRel_graph]
  exact (pshRelRelated_graph_iff
    (G.map α) (G.map α) σ_P σ_Q).trans
    ⟨Eq.symm, Eq.symm⟩

/-- Heterogeneous graph restriction: the
parametricity condition for the Barr extension
between two (possibly different) graph relations
reduces to commutativity of a naturality square
in the presheaf category. -/
theorem pshBarrLiftRel_graph_related_hetero_iff
    {P₁ P₂ Q₁ Q₂ : Cᵒᵖ ⥤ Type w}
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (α : P₁ ⟶ P₂) (β : Q₁ ⟶ Q₂)
    {f : G.obj P₁ ⟶ G.obj Q₁}
    {g : G.obj P₂ ⟶ G.obj Q₂} :
    pshRelRelated f g
      (pshBarrLiftRel G (pshRelGraph α))
      (pshBarrLiftRel G (pshRelGraph β)) ↔
    G.map α ≫ g = f ≫ G.map β := by
  rw [pshBarrLiftRel_graph, pshBarrLiftRel_graph]
  exact pshRelRelated_graph_iff
    (G.map α) (G.map β) f g

/-- The parametricity condition for the Barr
extension at an identity relation reduces to
equality of the two morphism components. -/
theorem pshBarrLiftRel_id_related_iff
    {P Q : Cᵒᵖ ⥤ Type w}
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    {f g : G.obj P ⟶ G.obj Q} :
    pshRelRelated f g
      (pshBarrLiftRel G (pshRelId P))
      (pshBarrLiftRel G (pshRelId Q)) ↔
    f = g := by
  rw [pshBarrLiftRel_id, pshBarrLiftRel_id]
  exact ⟨pshRelRelated_id_eq,
    fun h => h ▸ pshRelRelatedSqVertId f⟩

end GraphRestriction

section ArrowEndofunctor

/-- The endofunctor on `Arrow(PSh(C))` induced by
a presheaf endofunctor `G`. Sends an arrow
`α : P ⟶ Q` to `G.map α : G(P) ⟶ G(Q)`, and
a commutative square `(f, g)` to
`(G.map f, G.map g)`. -/
def arrowEndofunctor
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) :
    Arrow (Cᵒᵖ ⥤ Type w) ⥤
    Arrow (Cᵒᵖ ⥤ Type w) where
  obj f := Arrow.mk (G.map f.hom)
  map {f g} sq := by
    refine Arrow.homMk
      (G.map sq.left) (G.map sq.right) ?_
    change G.map sq.left ≫ G.map g.hom =
      G.map f.hom ≫ G.map sq.right
    rw [← G.map_comp, ← G.map_comp]
    exact congrArg G.map sq.w
  map_id f := by
    apply CommaMorphism.ext
    · exact G.map_id f.left
    · exact G.map_id f.right
  map_comp {f g h} sq₁ sq₂ := by
    apply CommaMorphism.ext
    · exact G.map_comp sq₁.left sq₂.left
    · exact G.map_comp sq₁.right sq₂.right

end ArrowEndofunctor

section GraphRestrictionFunctor

/-- Edge isomorphism from propositional equality of
the relation component. When two edges share the
same source and target presheaves but differ only
in the relation, an equality of relations yields
an isomorphism with identity components. -/
def pshRelEdgeEqIso
    {P Q : Cᵒᵖ ⥤ Type w}
    {R S : PshRel P Q}
    (h : R = S) :
    ({ src := P, tgt := Q, edge := R } :
      PshRelEdge.{u, v, w} C) ≅
    { src := P, tgt := Q, edge := S } where
  hom :=
    { srcMap := 𝟙 P
      tgtMap := 𝟙 Q
      sq := h ▸ pshRelRelatedSqHorId R }
  inv :=
    { srcMap := 𝟙 P
      tgtMap := 𝟙 Q
      sq := h ▸ pshRelRelatedSqHorId S }
  hom_inv_id := VertEdgeHom.ext
    (Category.comp_id _) (Category.comp_id _)
  inv_hom_id := VertEdgeHom.ext
    (Category.comp_id _) (Category.comp_id _)

@[simp]
theorem pshRelEdgeEqIso_hom_srcMap
    {P Q : Cᵒᵖ ⥤ Type w}
    {R S : PshRel P Q} (h : R = S) :
    (pshRelEdgeEqIso (C := C) h).hom.srcMap =
    𝟙 P := rfl

@[simp]
theorem pshRelEdgeEqIso_hom_tgtMap
    {P Q : Cᵒᵖ ⥤ Type w}
    {R S : PshRel P Q} (h : R = S) :
    (pshRelEdgeEqIso (C := C) h).hom.tgtMap =
    𝟙 Q := rfl

/-- The Barr lift edge functor restricted to the
graph subcategory agrees with the arrow
endofunctor followed by the graph functor. -/
def pshBarrLiftEdge_graphNatIso
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) :
    (pshRelEdgeGraphFunctor (C := C) :
      Arrow (Cᵒᵖ ⥤ Type w) ⥤
        PshRelEdge.{u, v, w} C) ⋙
      pshBarrLiftEdgeFunctor G ≅
    arrowEndofunctor G ⋙
      pshRelEdgeGraphFunctor :=
  NatIso.ofComponents
    (fun f => pshRelEdgeEqIso
      (pshBarrLiftRel_graph G f.hom))
    (fun {f g} sq => by
      apply VertEdgeHom.ext
      · change G.map sq.left ≫ 𝟙 _ =
          𝟙 _ ≫ G.map sq.left
        simp
      · change G.map sq.right ≫ 𝟙 _ =
          𝟙 _ ≫ G.map sq.right
        simp)

/-- The Barr lift edge functor composed with the
identity section is naturally isomorphic to the
endofunctor `G` composed with the identity
section. -/
def pshBarrLiftEdge_identNatIso
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) :
    (pshRelIdentFunctor :
      (Cᵒᵖ ⥤ Type w) ⥤
        PshRelEdge.{u, v, w} C) ⋙
      pshBarrLiftEdgeFunctor G ≅
    G ⋙ pshRelIdentFunctor :=
  NatIso.ofComponents
    (fun P => pshRelEdgeEqIso
      (pshBarrLiftRel_id G))
    (fun {P Q} α => by
      apply VertEdgeHom.ext
      · change G.map α ≫ 𝟙 _ = 𝟙 _ ≫ G.map α
        simp
      · change G.map α ≫ 𝟙 _ = 𝟙 _ ≫ G.map α
        simp)

/-- The contravariant Barr lift edge functor
composed with the opposite of the identity
section is naturally isomorphic to `F` composed
with the identity section. -/
def pshContraBarrLiftEdge_identNatIso
    (F :
      (Cᵒᵖ ⥤ Type w)ᵒᵖ ⥤
        (Cᵒᵖ ⥤ Type w)) :
    (pshRelIdentFunctor :
      (Cᵒᵖ ⥤ Type w) ⥤
        PshRelEdge.{u, v, w} C).op ⋙
      pshContraBarrLiftEdgeFunctor F ≅
    F ⋙ pshRelIdentFunctor :=
  NatIso.ofComponents
    (fun P => pshRelEdgeEqIso
      (pshContraBarrLiftRel_id F))
    (fun {P Q} α => by
      apply VertEdgeHom.ext
      · change F.map α.unop.op ≫ 𝟙 _ =
          𝟙 _ ≫ F.map α.unop.op
        simp
      · change F.map α.unop.op ≫ 𝟙 _ =
          𝟙 _ ≫ F.map α.unop.op
        simp)

end GraphRestrictionFunctor

section BarrEmbeddings

/-- The covariant Barr embedding of a presheaf
endofunctor `G` into `PshRelEdge C`. Sends `P`
to `(G P, G P, pshBarrLiftRel G (pshRelId P))`.
This is the composition
`pshRelIdentFunctor ⋙ pshBarrLiftEdgeFunctor G`,
and is naturally isomorphic to
`G ⋙ pshRelIdentFunctor` via
`pshBarrLiftEdge_identNatIso`. -/
abbrev pshBarrEmbedding
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) :
    (Cᵒᵖ ⥤ Type w) ⥤
    PshRelEdge.{u, v, w} C :=
  pshRelIdentFunctor ⋙ pshBarrLiftEdgeFunctor G

/-- The contravariant Barr embedding of a
contravariant presheaf endofunctor `F` into
`PshRelEdge C`. Sends `op P` to
`(F(op P), F(op P),
  pshContraBarrLiftRel F (pshRelId P))`.
This is the composition of the opposite of the
identity section with
`pshContraBarrLiftEdgeFunctor F`, and is
naturally isomorphic to
`F ⋙ pshRelIdentFunctor` via
`pshContraBarrLiftEdge_identNatIso`. -/
abbrev pshContraBarrEmbedding
    (F :
      (Cᵒᵖ ⥤ Type w)ᵒᵖ ⥤
        (Cᵒᵖ ⥤ Type w)) :
    (Cᵒᵖ ⥤ Type w)ᵒᵖ ⥤
    PshRelEdge.{u, v, w} C :=
  (pshRelIdentFunctor :
    (Cᵒᵖ ⥤ Type w) ⥤
      PshRelEdge.{u, v, w} C).op ⋙
    pshContraBarrLiftEdgeFunctor F

end BarrEmbeddings

section BarrLiftProjections

/-- The Barr lift edge functor commutes with the
source projection: `pshBarrLiftEdgeFunctor G ⋙
pshRelSrcFunctor = pshRelSrcFunctor ⋙ G`. -/
theorem pshBarrLiftEdgeFunctor_src
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) :
    pshBarrLiftEdgeFunctor (C := C) G ⋙
      pshRelSrcFunctor =
    pshRelSrcFunctor ⋙ G :=
  _root_.CategoryTheory.Functor.ext
    (fun _ => rfl)

/-- The Barr lift edge functor commutes with the
target projection: `pshBarrLiftEdgeFunctor G ⋙
pshRelTgtFunctor = pshRelTgtFunctor ⋙ G`. -/
theorem pshBarrLiftEdgeFunctor_tgt
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) :
    pshBarrLiftEdgeFunctor (C := C) G ⋙
      pshRelTgtFunctor =
    pshRelTgtFunctor ⋙ G :=
  _root_.CategoryTheory.Functor.ext
    (fun _ => rfl)

/-- The source projection of the Barr embedding
recovers the endofunctor:
`pshBarrEmbedding G ⋙ pshRelSrcFunctor = G`. -/
theorem pshBarrEmbedding_src
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) :
    pshBarrEmbedding (C := C) G ⋙
      pshRelSrcFunctor = G :=
  _root_.CategoryTheory.Functor.ext
    (fun _ => rfl)

/-- The target projection of the Barr embedding
recovers the endofunctor:
`pshBarrEmbedding G ⋙ pshRelTgtFunctor = G`. -/
theorem pshBarrEmbedding_tgt
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) :
    pshBarrEmbedding (C := C) G ⋙
      pshRelTgtFunctor = G :=
  _root_.CategoryTheory.Functor.ext
    (fun _ => rfl)

end BarrLiftProjections

section BarrEmbeddingFunctoriality

/-- A natural transformation `σ : F ⟶ G` between
endofunctors induces a natural transformation
between Barr embeddings. The component at `P`
has both srcMap and tgtMap equal to `σ.app P`.

This generalizes `natTransToBarrEndo` (the
endomorphism case `F = G`).
`pshBarrEmbedding` is functorial: see
`pshBarrEmbeddingFunctor`. -/
def natTransToBarrMap
    {F G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (σ : F ⟶ G) :
    pshBarrEmbedding (C := C) F ⟶
    pshBarrEmbedding G where
  app P :=
    { srcMap := σ.app P
      tgtMap := σ.app P
      sq := by
        change pshRelRelated (σ.app P) (σ.app P)
          (pshBarrLiftRel F (pshRelId P))
          (pshBarrLiftRel G (pshRelId P))
        rw [pshBarrLiftRel_id, pshBarrLiftRel_id]
        exact pshRelRelatedSqVertId (σ.app P) }
  naturality {P Q} α :=
    VertEdgeHom.ext (σ.naturality α)
      (σ.naturality α)

/-- A natural transformation between Barr
embeddings yields a natural transformation
between the underlying endofunctors, by
extracting the srcMap component.  Naturality
in `PshRelEdge` implies the commutativity
`σ_P ≫ G.map α = F.map α ≫ σ_Q`.

This generalizes `barrEndoToNatTrans` (the
endomorphism case `F = G`). -/
def barrMapToNatTrans
    {F G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (τ : pshBarrEmbedding (C := C) F ⟶
      pshBarrEmbedding G) :
    F ⟶ G where
  app P := (τ.app P).srcMap
  naturality _ _ α :=
    congrArg VertEdgeHom.srcMap (τ.naturality α)

/-- `natTransToBarrMap ∘ barrMapToNatTrans`
is the identity.  The tgtMap component equals
srcMap because the Barr lift at the identity
relation forces equality
(`pshRelRelated_id_eq`). -/
theorem natTransToBarrMap_barrMapToNatTrans
    {F G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (τ : pshBarrEmbedding (C := C) F ⟶
      pshBarrEmbedding G) :
    natTransToBarrMap
      (barrMapToNatTrans τ) = τ := by
  ext P
  apply VertEdgeHom.ext
  · rfl
  · have hsq := (τ.app P).sq
    change pshRelRelated _ _
      (pshBarrLiftRel F (pshRelId P))
      (pshBarrLiftRel G (pshRelId P)) at hsq
    rw [pshBarrLiftRel_id, pshBarrLiftRel_id]
      at hsq
    exact pshRelRelated_id_eq hsq

/-- `barrMapToNatTrans ∘ natTransToBarrMap`
is the identity. -/
theorem barrMapToNatTrans_natTransToBarrMap
    {F G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (σ : F ⟶ G) :
    barrMapToNatTrans (C := C)
      (natTransToBarrMap σ) = σ := rfl

/-- The Barr embedding is a functor from
endofunctors on `PSh(C)` to functors
`PSh(C) ⥤ PshRelEdge C`.

On objects: `G ↦ pshBarrEmbedding G`.
On morphisms: `(σ : F ⟶ G) ↦ natTransToBarrMap σ`.

This functor is fully faithful
(`pshBarrEmbeddingFunctor_fullyFaithful`). -/
def pshBarrEmbeddingFunctor :
    ((Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) ⥤
    ((Cᵒᵖ ⥤ Type w) ⥤
      PshRelEdge.{u, v, w} C) where
  obj G := pshBarrEmbedding G
  map σ := natTransToBarrMap σ
  map_id _ := by
    ext P
    exact VertEdgeHom.ext rfl rfl
  map_comp _ _ := by
    ext P
    exact VertEdgeHom.ext rfl rfl

/-- `pshBarrEmbeddingFunctor` is fully
faithful: the Barr embedding bijectively maps
natural transformations between endofunctors
to natural transformations between their
Barr embeddings. -/
def pshBarrEmbeddingFunctor_fullyFaithful :
    (pshBarrEmbeddingFunctor :
      ((Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) ⥤
      ((Cᵒᵖ ⥤ Type w) ⥤
        PshRelEdge.{u, v, w} C)
    ).FullyFaithful where
  preimage τ := barrMapToNatTrans τ
  map_preimage τ :=
    natTransToBarrMap_barrMapToNatTrans τ
  preimage_map σ :=
    barrMapToNatTrans_natTransToBarrMap σ

/-- Specialization: a natural endomorphism
`σ : G ⟶ G` induces a natural endomorphism of
`pshBarrEmbedding G`. -/
abbrev natTransToBarrEndo
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (σ : G ⟶ G) :
    pshBarrEmbedding (C := C) G ⟶
    pshBarrEmbedding G :=
  natTransToBarrMap σ

/-- Specialization: extracting a natural
endomorphism from a Barr embedding endomorphism.
This is the rearrangement free theorem: the
endomorphism's naturality in `PshRelEdge`
implies the commutativity
`σ_P ≫ G.map α = G.map α ≫ σ_Q`. -/
abbrev barrEndoToNatTrans
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (τ : pshBarrEmbedding (C := C) G ⟶
      pshBarrEmbedding G) :
    G ⟶ G :=
  barrMapToNatTrans τ

theorem natTransToBarrEndo_barrEndoToNatTrans
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (τ : pshBarrEmbedding (C := C) G ⟶
      pshBarrEmbedding G) :
    natTransToBarrEndo G
      (barrEndoToNatTrans G τ) = τ :=
  natTransToBarrMap_barrMapToNatTrans τ

theorem barrEndoToNatTrans_natTransToBarrEndo
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (σ : G ⟶ G) :
    barrEndoToNatTrans (C := C) G
      (natTransToBarrEndo G σ) = σ :=
  barrMapToNatTrans_natTransToBarrMap σ

end BarrEmbeddingFunctoriality

section MapDecomposition

/-- A map family for an endofunctor `G` assigns to each
arrow `α : P ⟶ Q` a morphism `G.obj P ⟶ G.obj Q`,
naturally in the arrow category. -/
abbrev MapFamily
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) :=
  (Arrow.leftFunc (C := Cᵒᵖ ⥤ Type w)) ⋙ G ⟶
  (Arrow.rightFunc (C := Cᵒᵖ ⥤ Type w)) ⋙ G

/-- Left decomposition: `m(α) = m(𝟙_P) ≫ G.map α`.
Presheaf-level generalization of Wadler Section 3.5:
`m(f) = m(id) ∘ f*`. The proof specializes the
naturality of the map family at the arrow square
`(𝟙_P, α) : 𝟙_P → α`. -/
theorem mapFamilyDecompLeft
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (τ : MapFamily (C := C) G)
    {P Q : Cᵒᵖ ⥤ Type w} (α : P ⟶ Q) :
    τ.app (Arrow.mk α) =
    τ.app (Arrow.mk (𝟙 P)) ≫ G.map α := by
  have h := τ.naturality
    (Arrow.homMk (𝟙 P) α (by simp) :
      Arrow.mk (𝟙 P) ⟶ Arrow.mk α)
  dsimp [Arrow.leftFunc, Arrow.rightFunc] at h
  rw [G.map_id, Category.id_comp] at h
  exact h

/-- Right decomposition: `m(α) = G.map α ≫ m(𝟙_Q)`.
Equivalent to `m(f) = f* ∘ m(id_Q)`. The proof
specializes the naturality of the map family at the
arrow square `(α, 𝟙_Q) : α → 𝟙_Q`. -/
theorem mapFamilyDecompRight
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (τ : MapFamily (C := C) G)
    {P Q : Cᵒᵖ ⥤ Type w} (α : P ⟶ Q) :
    τ.app (Arrow.mk α) =
    G.map α ≫ τ.app (Arrow.mk (𝟙 Q)) := by
  have h := τ.naturality
    (Arrow.homMk α (𝟙 Q) (by simp) :
      Arrow.mk α ⟶ Arrow.mk (𝟙 Q))
  dsimp [Arrow.leftFunc, Arrow.rightFunc] at h
  rw [G.map_id, Category.comp_id] at h
  exact h.symm

/-- Extract a natural transformation `G ⟶ G` from a
map family by evaluating at identity arrows. The
identity components `τ.app (Arrow.mk (𝟙 P))` form a
natural transformation because the two decompositions
`mapFamilyDecompLeft` and `mapFamilyDecompRight`
imply commutativity with `G.map`. -/
def mapFamilyToNatTrans
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (τ : MapFamily (C := C) G) :
    G ⟶ G where
  app P := τ.app (Arrow.mk (𝟙 P))
  naturality _ _ α :=
    (mapFamilyDecompRight G τ α).symm.trans
      (mapFamilyDecompLeft G τ α)

/-- Construct a map family from a natural transformation
`σ : G ⟶ G`. The component at arrow `α : P ⟶ Q` is
`σ.app P ≫ G.map α`. -/
def natTransToMapFamily
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (σ : G ⟶ G) :
    MapFamily (C := C) G where
  app f := σ.app f.left ≫ G.map f.hom
  naturality {f g} sq := by
    dsimp [Arrow.leftFunc, Arrow.rightFunc]
    simp only [Category.assoc]
    rw [reassoc_of% (σ.naturality sq.left)]
    simp only [← G.map_comp]
    exact congrArg (σ.app f.left ≫ G.map ·) sq.w

/-- The roundtrip `mapFamilyToNatTrans ∘
natTransToMapFamily` is the identity. -/
theorem mapFamilyToNatTrans_natTransToMapFamily
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (σ : G ⟶ G) :
    mapFamilyToNatTrans (C := C) G
      (natTransToMapFamily G σ) = σ := by
  ext P
  dsimp [mapFamilyToNatTrans, natTransToMapFamily]
  simp

/-- The roundtrip `natTransToMapFamily ∘
mapFamilyToNatTrans` is the identity, using
the left decomposition. -/
theorem natTransToMapFamily_mapFamilyToNatTrans
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (τ : MapFamily (C := C) G) :
    natTransToMapFamily G
      (mapFamilyToNatTrans G τ) = τ := by
  apply NatTrans.ext
  funext f
  dsimp [natTransToMapFamily, mapFamilyToNatTrans]
  exact (mapFamilyDecompLeft G τ f.hom).symm

end MapDecomposition

section GraphSubcategory

/-- An edge in `PshRelEdge C` is a graph edge when
its relation component is the graph of some
morphism. -/
def IsGraphEdge
    (e : PshRelEdge.{u, v, w} C) : Prop :=
  ∃ α : e.src ⟶ e.tgt, e.edge = pshRelGraph α

/-- The graph functor sends every arrow to a graph
edge. -/
theorem pshRelEdgeGraphFunctor_isGraphEdge
    (f : Arrow (Cᵒᵖ ⥤ Type w)) :
    IsGraphEdge
      (C := C) (pshRelEdgeGraphFunctor.obj f) :=
  ⟨f.hom, rfl⟩

/-- The graph functor lifted to the full subcategory
of graph edges. -/
def pshRelEdgeGraphSubcatFunctor :
    Arrow (Cᵒᵖ ⥤ Type w) ⥤
    ObjectProperty.FullSubcategory
      (IsGraphEdge (C := C)) where
  obj f :=
    ⟨pshRelEdgeGraphFunctor.obj f,
     pshRelEdgeGraphFunctor_isGraphEdge f⟩
  map sq := ⟨pshRelEdgeGraphFunctor.map sq⟩
  map_id _ := by
    apply ObjectProperty.hom_ext
    exact pshRelEdgeGraphFunctor.map_id _
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact pshRelEdgeGraphFunctor.map_comp f g

/-- The lifted graph functor to the full subcategory
is fully faithful (inherited from
`pshRelEdgeGraphFullyFaithful`). -/
def pshRelEdgeGraphSubcatFullyFaithful :
    (pshRelEdgeGraphSubcatFunctor :
      Arrow (Cᵒᵖ ⥤ Type w) ⥤
        ObjectProperty.FullSubcategory
          (IsGraphEdge (C := C))).FullyFaithful where
  preimage {f g} h :=
    pshRelEdgeGraphFullyFaithful.preimage h.hom
  map_preimage h := by
    apply ObjectProperty.hom_ext
    exact pshRelEdgeGraphFullyFaithful.map_preimage
      h.hom
  preimage_map sq := by
    exact pshRelEdgeGraphFullyFaithful.preimage_map
      sq

/-- The lifted graph functor is essentially surjective
onto the graph subcategory: every graph edge is in
the image. -/
instance pshRelEdgeGraphSubcat_essSurj :
    (pshRelEdgeGraphSubcatFunctor :
      Arrow (Cᵒᵖ ⥤ Type w) ⥤
        ObjectProperty.FullSubcategory
          (IsGraphEdge (C := C))).EssSurj where
  mem_essImage e :=
    let ⟨α, hα⟩ := e.property
    ⟨Arrow.mk α, ⟨{
      hom := ⟨(pshRelEdgeEqIso hα.symm).hom⟩
      inv := ⟨(pshRelEdgeEqIso hα.symm).inv⟩
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        exact (pshRelEdgeEqIso hα.symm).hom_inv_id
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        exact (pshRelEdgeEqIso hα.symm).inv_hom_id
    }⟩⟩

/-- The graph restriction functor: precomposition with
the graph embedding. Takes a copresheaf on
`PshRelEdge C` (a parametric family) to a
copresheaf on `Arrow(PSh C)` (a natural family).
This forgets parametricity data beyond
naturality. -/
abbrev graphRestrictionFunctor
    (D : Type*) [Category D] :
    ((PshRelEdge.{u, v, w} C)ᵒᵖ ⥤ D) ⥤
    ((Arrow (Cᵒᵖ ⥤ Type w))ᵒᵖ ⥤ D) :=
  (Functor.whiskeringLeft _ _ D).obj
    (pshRelEdgeGraphFunctor (C := C)).op

/-- Graph restriction of the Barr lift edge
functor is naturally isomorphic to the arrow
endofunctor followed by the graph functor.
This expresses that restricting parametric data
to graph edges recovers naturality data. -/
def graphRestriction_barrLiftNatIso
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) :
    (pshRelEdgeGraphFunctor (C := C)) ⋙
      pshBarrLiftEdgeFunctor G ≅
    arrowEndofunctor G ⋙
      pshRelEdgeGraphFunctor :=
  pshBarrLiftEdge_graphNatIso G

end GraphSubcategory

section FreeTheoremViaGraphs

/-- A natural endomorphism of `G` is
parametrically related at any Barr-lifted graph
relation. This is the free theorem: naturality
of `σ` entails relatedness at every graph edge
in `PshRelEdge C`. -/
theorem natTrans_pshRelRelated_barrLiftGraph
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (σ : G ⟶ G)
    {P Q : Cᵒᵖ ⥤ Type w} (α : P ⟶ Q) :
    pshRelRelated (σ.app P) (σ.app Q)
      (pshBarrLiftRel G (pshRelGraph α))
      (pshBarrLiftRel G (pshRelGraph α)) := by
  rw [pshBarrLiftRel_graph,
    pshRelRelated_graph_iff]
  exact σ.naturality α

/-- Converse direction: if `σ.app P` and
`σ.app Q` are related at
`pshBarrLiftRel G (pshRelGraph α)` for every
`α`, then `σ` is natural. -/
theorem pshRelRelated_barrLiftGraph_implies_nat
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (σP : (P : Cᵒᵖ ⥤ Type w) → G.obj P ⟶ G.obj P)
    (h : ∀ {P Q : Cᵒᵖ ⥤ Type w}
      (α : P ⟶ Q),
      pshRelRelated (σP P) (σP Q)
        (pshBarrLiftRel G (pshRelGraph α))
        (pshBarrLiftRel G (pshRelGraph α)))
    {P Q : Cᵒᵖ ⥤ Type w} (α : P ⟶ Q) :
    σP P ≫ G.map α = G.map α ≫ σP Q := by
  have hr := h α
  rw [pshBarrLiftRel_graph] at hr
  rw [pshRelRelated_graph_iff] at hr
  exact hr.symm

end FreeTheoremViaGraphs

section BarrLiftEdgeEndo

/-- Lift a natural endomorphism `σ : G ⟶ G` to
a natural endomorphism of the Barr lift edge
functor `pshBarrLiftEdgeFunctor G`, acting at
every edge `(P, Q, R)` as `(σ_P, σ_Q)`.

The relatedness condition
`natTrans_pshRelRelated_barrLiftRel` ensures
that `(σ_P, σ_Q)` preserves the Barr-lifted
relation at every edge. -/
def natTransToBarrLiftEdgeEndo
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (σ : G ⟶ G) :
    pshBarrLiftEdgeFunctor (C := C) G ⟶
    pshBarrLiftEdgeFunctor G where
  app R :=
    { srcMap := σ.app R.src
      tgtMap := σ.app R.tgt
      sq :=
        natTrans_pshRelRelated_barrLiftRel
          G σ R.edge }
  naturality {_ _} f :=
    VertEdgeHom.ext
      (σ.naturality f.srcMap)
      (σ.naturality f.tgtMap)

/-- Extract a natural endomorphism `G ⟶ G` from
a natural endomorphism of the Barr lift edge
functor, by restricting to identity edges and
taking the source component. -/
def barrLiftEdgeEndoToNatTrans
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (τ :
      pshBarrLiftEdgeFunctor (C := C) G ⟶
      pshBarrLiftEdgeFunctor G) :
    G ⟶ G where
  app P :=
    (τ.app (pshRelIdentFunctor.obj P)).srcMap
  naturality _ _ α :=
    congrArg VertEdgeHom.srcMap
      (τ.naturality
        (pshRelIdentFunctor.map α))

/-- `barrLiftEdgeEndoToNatTrans` is a left
inverse of `natTransToBarrLiftEdgeEndo`. -/
theorem barrLiftEdgeEndoToNatTrans_natTransTo
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (σ : G ⟶ G) :
    barrLiftEdgeEndoToNatTrans (C := C) G
      (natTransToBarrLiftEdgeEndo G σ) =
    σ := rfl

/-- The edge endomorphism at an identity edge
equals the embedding endomorphism:
`natTransToBarrLiftEdgeEndo` applied to
`pshRelIdentFunctor.obj P` equals
`natTransToBarrEndo` applied to `P`. -/
theorem natTransToBarrLiftEdgeEndo_restrict
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (σ : G ⟶ G) (P : Cᵒᵖ ⥤ Type w) :
    (natTransToBarrLiftEdgeEndo (C := C) G
      σ).app (pshRelIdentFunctor.obj P) =
    (natTransToBarrEndo G σ).app P := rfl

end BarrLiftEdgeEndo

section FoldFreeTheorem

open Endofunctor in
/-- The fold free theorem at graph relations:
the catamorphism of an initial algebra commutes
with algebra homomorphisms.

Given an initial `F`-algebra `μ` and algebras
`A`, `B` with an algebra homomorphism `f`,
`cata(A) ≫ f = cata(B)` where `cata(X)` is the
unique algebra morphism from `μ` to `X`.

Expressed as `pshRelRelated` at graph edges:
the catamorphism components are related at
`pshRelGraph f` given that the algebra
structures are related at
`pshBarrLiftRel F (pshRelGraph f)`. -/
theorem foldFreeTheorem_graph
    (F :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    {μ : Algebra F}
    (hInit : Limits.IsInitial μ)
    (A B : Algebra F) (f : A ⟶ B) :
    (hInit.to A).f ≫ f.f =
      (hInit.to B).f := by
  have h : (hInit.to A) ≫ f = hInit.to B :=
    hInit.hom_ext _ _
  exact congrArg Algebra.Hom.f h

open Endofunctor in
/-- The fold free theorem expressed via
`pshRelRelated` at graph relations: the
catamorphism is related at the graph of any
algebra homomorphism, with the domain relation
being the identity on the initial algebra
carrier. -/
theorem foldFreeTheorem_pshRelRelated_graph
    (F :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    {μ : Algebra F}
    (hInit : Limits.IsInitial μ)
    (A B : Algebra F)
    (f : A ⟶ B) :
    pshRelRelated
      (hInit.to A).f (hInit.to B).f
      (pshRelId μ.a)
      (pshRelGraph f.f) := by
  intro c p q (hId : p = q)
  subst hId
  exact congr_fun
    (congr_app (foldFreeTheorem_graph F hInit
      A B f) c) p

open Endofunctor in
/-- The fold free theorem expressed as
a `pshRelRelated` condition at Barr-lifted
graph relations, combining the algebra
homomorphism hypothesis with the catamorphism
conclusion.

If `f` is an algebra homomorphism (expressed
as relatedness of algebra structures at the
Barr-lifted graph), then the catamorphisms
are related at the graph of `f`. -/
theorem foldFreeTheorem_barrLift_graph
    (F :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    {μ : Algebra F}
    (hInit : Limits.IsInitial μ)
    (A B : Algebra F)
    (f : A.a ⟶ B.a)
    (hAlg :
      pshRelRelated A.str B.str
        (pshBarrLiftRel F (pshRelGraph f))
        (pshRelGraph f)) :
    pshRelRelated
      (hInit.to A).f (hInit.to B).f
      (pshRelId μ.a)
      (pshRelGraph f) := by
  rw [pshBarrLiftRel_graph,
    pshRelRelated_graph_iff] at hAlg
  exact foldFreeTheorem_pshRelRelated_graph
    F hInit A B ⟨f, hAlg⟩

end FoldFreeTheorem

section ParametricityAsTautology

/-- A parametric section of an endofunctor
`G : PshRelEdge C ⥤ PshRelEdge C` is a cone
over `G` with vertex the terminal edge.
This is mathlib's `Limits.Cone G` specialized to
`pt = pshRelEdgeTerminal C`.

Concretely: for each edge `e`, a morphism
`⊤ ⟶ G(e)` in `PshRelEdge C`, such that for
each `f : e₁ ⟶ e₂`, the cone condition
`π e₁ ≫ G.map f = π e₂` holds (where
`π = cone.π.app`).

For `G = pshBarrLiftEdgeFunctor H`, this
recovers Wadler's parametricity: `π e` picks
a pair of elements of `H(e.src)` and `H(e.tgt)`
that are `pshBarrLiftRel H e.rel`-related,
and the cone condition says these choices are
compatible across all edge morphisms.  The
limit of such a cone is the universal type
`∀X. H(X)` as an object of `PshRelEdge C`. -/
abbrev ParametricCone
    (G : PshRelEdge.{u, v, w} C ⥤
      PshRelEdge.{u, v, w} C) :=
  constTerminal
    (PshRelEdge.{u, v, w} C)
    (pshRelEdgeIsTerminal C) ⟶ G

open Limits in
/-- Forward direction of the equivalence
`ParametricCone G ≃ (⊤ ⟶ s.pt)` for a limit
cone `s`: extract the limit morphism from a
parametric cone via the limit lift. -/
def parametricConeToLimitHom
    (G : PshRelEdge.{u, v, w} C ⥤
      PshRelEdge.{u, v, w} C)
    {s : Cone G} (hs : IsLimit s)
    (pc : ParametricCone G) :
    pshRelEdgeTerminal C ⟶ s.pt :=
  hs.lift ⟨_, pc⟩

open Limits in
/-- Backward direction of the equivalence
`ParametricCone G ≃ (⊤ ⟶ s.pt)`: build a
parametric cone from a morphism `⊤ ⟶ s.pt`
by composing with each limit projection. -/
def limitHomToParametricCone
    (G : PshRelEdge.{u, v, w} C ⥤
      PshRelEdge.{u, v, w} C)
    {s : Cone G}
    (f : pshRelEdgeTerminal C ⟶ s.pt) :
    ParametricCone G :=
  { app := fun e => f ≫ s.π.app e
    naturality := fun {e₁ e₂} g => by
      simp only [Functor.const_obj_obj,
        Functor.const_obj_map,
        Category.id_comp, Category.assoc]
      rw [s.w g] }

open Limits in
/-- Roundtrip: `limitHom → cone → limitHom`
is the identity. -/
theorem limitHom_parametricCone_roundtrip
    (G : PshRelEdge.{u, v, w} C ⥤
      PshRelEdge.{u, v, w} C)
    {s : Cone G} (hs : IsLimit s)
    (f : pshRelEdgeTerminal C ⟶ s.pt) :
    parametricConeToLimitHom G hs
      (limitHomToParametricCone G f) = f := by
  simp only [parametricConeToLimitHom,
    limitHomToParametricCone]
  exact hs.hom_ext (fun e => hs.fac _ e)

open Limits in
/-- Roundtrip: `cone → limitHom → cone`
is the identity. -/
theorem parametricCone_limitHom_roundtrip
    (G : PshRelEdge.{u, v, w} C ⥤
      PshRelEdge.{u, v, w} C)
    {s : Cone G} (hs : IsLimit s)
    (pc : ParametricCone G) :
    limitHomToParametricCone G
      (parametricConeToLimitHom G hs pc) =
    pc := by
  ext e
  simp only [limitHomToParametricCone,
    parametricConeToLimitHom]
  exact hs.fac ⟨_, pc⟩ e

open Limits in
/-- The equivalence between parametric cones
(cones over `G` with vertex `⊤`) and morphisms
`⊤ ⟶ s.pt` for any limit cone `s`. -/
def parametricConeEquiv
    (G : PshRelEdge.{u, v, w} C ⥤
      PshRelEdge.{u, v, w} C)
    {s : Cone G} (hs : IsLimit s) :
    ParametricCone G ≃
    (pshRelEdgeTerminal C ⟶ s.pt) where
  toFun := parametricConeToLimitHom G hs
  invFun := limitHomToParametricCone G
  left_inv :=
    parametricCone_limitHom_roundtrip G hs
  right_inv :=
    limitHom_parametricCone_roundtrip G hs

end ParametricityAsTautology

section IdentityEdgeRecovery

/-- A presheaf section of an endofunctor
`G : PSh(C) ⥤ PSh(C)` is a cone over `G` with
vertex the terminal presheaf `pshUnitPresheaf C`.
Concretely: for each presheaf `P`, a morphism
`pshUnitPresheaf C ⟶ G.obj P`, natural in `P`.
This is the presheaf-level analogue of
`ParametricCone` at the edge level. -/
abbrev PresheafSection
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) :=
  constTerminal (Cᵒᵖ ⥤ Type w)
    (pshUnitPresheafIsTerminal.{u, v, w} C) ⟶
    G

/-- Build a `PresheafSection` from a family of
morphisms from the terminal presheaf satisfying
the cone condition. -/
def PresheafSection.mk'
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (s : (P : Cᵒᵖ ⥤ Type w) →
      (pshUnitPresheaf C ⟶ G.obj P))
    (hs : ∀ {P Q : Cᵒᵖ ⥤ Type w}
      (α : P ⟶ Q),
      s P ≫ G.map α = s Q) :
    PresheafSection G :=
  { app := fun P => s P
    naturality := fun {P Q} α => by
      simp only [Functor.const_obj_obj,
        Functor.const_obj_map,
        Category.id_comp]
      exact (hs α).symm }

/-- Extract a presheaf section from a parametric
cone of `pshBarrLiftEdgeFunctor G` by restricting
to identity edges and taking the source component.

At identity edges, `pshBarrLiftRel_id` forces
`srcMap = tgtMap`, and the source components
`π.app(pshRelIdentFunctor.obj P).srcMap` form a
natural family `pshUnitPresheaf C ⟶ G.obj P`
indexed by presheaves `P`. -/
def parametricConeSrcSection
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (pc : ParametricCone
      (pshBarrLiftEdgeFunctor (C := C) G)) :
    PresheafSection G :=
  PresheafSection.mk' G
    (fun P =>
      (pc.app
        (pshRelIdentFunctor.obj P)).srcMap)
    (fun {P Q} α => by
      have h := congrArg VertEdgeHom.srcMap
        (pc.naturality
          (pshRelIdentFunctor.map α))
      simp only [Functor.const_obj_obj,
        Functor.const_obj_map,
        Category.id_comp] at h
      exact h.symm)

/-- A presheaf section is parametrically related
at every edge: the source and target components
are `(pshRelFull, pshBarrLiftRel G R)`-related.
The witness is the section applied to the domain
`R.toFunctor` of the relation, with naturality
at the two projections providing the component
equalities. -/
theorem presheafSection_related
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (σ : (P : Cᵒᵖ ⥤ Type w) →
      (pshUnitPresheaf C ⟶ G.obj P))
    (hσ : ∀ {P Q : Cᵒᵖ ⥤ Type w}
      (f : P ⟶ Q),
      σ P ≫ G.map f = σ Q)
    (e : PshRelEdge.{u, v, w} C) :
    pshRelRelated (σ e.src) (σ e.tgt)
      (pshRelFull C)
      (pshBarrLiftRel G e.edge) := by
  intro c a b _
  have hab : a = b :=
    ULift.ext _ _ (Subsingleton.elim _ _)
  subst hab
  simp only [pshBarrLiftRel, pshBarrLift,
    pshProdOverToRel, Subfunctor.range,
    Set.mem_range, Over.mk_hom]
  refine
    ⟨(σ e.edge.toFunctor).app c a, ?_⟩
  dsimp [pshProdLift, FunctorToTypes.prod]
  have hfst := congr_fun (congr_app
    (hσ (e.edge.ι ≫
      pshProdFst e.src e.tgt)) c) a
  have hsnd := congr_fun (congr_app
    (hσ (e.edge.ι ≫
      pshProdSnd e.src e.tgt)) c) a
  simp only [NatTrans.comp_app,
    types_comp_apply] at hfst hsnd
  exact Prod.ext hfst hsnd

/-- Build a parametric cone of
`pshBarrLiftEdgeFunctor G` from a presheaf
section of `G`. At each edge
`e = ⟨P, Q, R⟩`, the cone component sends
the terminal edge to
`⟨G.obj P, G.obj Q, pshBarrLiftRel G R⟩`
via the section components `σ P` and `σ Q`,
with relatedness witnessed by `σ R.toFunctor`.
Naturality follows from the presheaf-level
cone condition. -/
def presheafSectionToParametricCone
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (ps : PresheafSection G) :
    ParametricCone
      (pshBarrLiftEdgeFunctor
        (C := C) G) :=
  { app := fun e =>
      { srcMap := ps.app e.src
        tgtMap := ps.app e.tgt
        sq :=
          presheafSection_related G
            (fun P => ps.app P)
            (fun f => by
              have h := ps.naturality f
              simp only [Functor.const_obj_obj,
                Functor.const_obj_map,
                Category.id_comp] at h
              exact h.symm)
            e }
    naturality := fun {e₁ e₂} f => by
      simp only [Functor.const_obj_obj,
        Functor.const_obj_map,
        Category.id_comp]
      apply VertEdgeHom.ext
      · dsimp [pshBarrLiftEdgeFunctor]
        have h := ps.naturality f.srcMap
        simp only [Functor.const_obj_obj,
          Functor.const_obj_map,
          Category.id_comp] at h
        exact h
      · dsimp [pshBarrLiftEdgeFunctor]
        have h := ps.naturality f.tgtMap
        simp only [Functor.const_obj_obj,
          Functor.const_obj_map,
          Category.id_comp] at h
        exact h }

/-- Extracting then rebuilding a presheaf section
is the identity. -/
theorem presheafSection_roundtrip
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (ps : PresheafSection G) :
    parametricConeSrcSection G
      (presheafSectionToParametricCone
        G ps) =
    ps := by
  ext P
  dsimp [parametricConeSrcSection,
    presheafSectionToParametricCone,
    PresheafSection.mk',
    pshRelIdentFunctor]

/-- The projection morphism from the identity edge
on `R.toFunctor` to the edge `⟨P, Q, R⟩`,
with source and target maps given by the two
projections of the relation inclusion `R.ι`. -/
def pshRelIdentToEdgeProj
    {P Q : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q) :
    pshRelIdentFunctor.obj R.toFunctor ⟶
    (⟨P, Q, R⟩ :
      PshRelEdge.{u, v, w} C) :=
  { srcMap := R.ι ≫ pshProdFst P Q
    tgtMap := R.ι ≫ pshProdSnd P Q
    sq := fun c r r' hrr' => by
      have h : r = r' := hrr'
      subst h
      simp only [NatTrans.comp_app,
        types_comp_apply]
      convert r.prop using 1 }

/-- For a parametric cone `pc` over
`pshBarrLiftEdgeFunctor G`, the `srcMap`
component at edge `e` equals the `srcMap`
component at the identity edge on `e.src`.
The proof uses cone naturality at the
projection morphism
`pshRelIdentFunctor.obj e.edge.toFunctor ⟶ e`
and at
`pshRelIdentFunctor.map (e.edge.ι ≫ π₁)`. -/
theorem parametricCone_srcMap_eq
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (π : (Functor.const
        (PshRelEdge.{u, v, w} C)).obj
      (pshRelEdgeTerminal C) ⟶
      pshBarrLiftEdgeFunctor (C := C) G)
    (e : PshRelEdge.{u, v, w} C) :
    (π.app e).srcMap =
    (π.app
      (pshRelIdentFunctor.obj e.src)).srcMap :=
  by
  have h₁ := congrArg VertEdgeHom.srcMap
    ((Limits.Cone.mk _ π).w
      (pshRelIdentToEdgeProj e.edge))
  have h₂ := congrArg VertEdgeHom.srcMap
    ((Limits.Cone.mk _ π).w
      (pshRelIdentFunctor.map
        (e.edge.ι ≫
          pshProdFst e.src e.tgt)))
  dsimp [pshBarrLiftEdgeFunctor,
    pshRelIdentFunctor,
    pshRelIdentToEdgeProj] at h₁ h₂
  exact h₁.symm.trans h₂

/-- If `f` and `g` are
`(pshRelFull, pshRelId)`-related, then
`f = g`. The full relation makes the
hypothesis unconditional, and the identity
relation forces equal outputs. -/
theorem pshRelRelated_full_id_eq
    {Q : Cᵒᵖ ⥤ Type w}
    {f g : pshUnitPresheaf C ⟶ Q}
    (h : pshRelRelated f g
      (pshRelFull C)
      (pshRelId Q)) :
    f = g := by
  ext c a
  exact h c a a (Set.mem_univ _)

/-- At an identity edge, the Barr-lifted
relatedness forces `srcMap = tgtMap`:
a morphism from the terminal edge to
`(G P, G P, pshBarrLiftRel G (pshRelId P))`
has equal source and target components. -/
theorem vertEdgeHom_srcEqTgt_at_ident
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (P : Cᵒᵖ ⥤ Type w)
    (f : pshRelEdgeTerminal C ⟶
      (pshBarrLiftEdgeFunctor (C := C) G).obj
        (pshRelIdentFunctor.obj P)) :
    f.srcMap = f.tgtMap := by
  apply pshRelRelated_full_id_eq
  change pshRelRelated f.srcMap f.tgtMap
    (pshRelFull C) (pshRelId (G.obj P))
  rw [← pshBarrLiftRel_id G]
  exact f.sq

/-- Analogous to `parametricCone_srcMap_eq`
for `tgtMap`: the target component at edge `e`
equals the `srcMap` component at the identity
edge on `e.tgt`. -/
theorem parametricCone_tgtMap_eq
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (π : (Functor.const
        (PshRelEdge.{u, v, w} C)).obj
      (pshRelEdgeTerminal C) ⟶
      pshBarrLiftEdgeFunctor (C := C) G)
    (e : PshRelEdge.{u, v, w} C) :
    (π.app e).tgtMap =
    (π.app
      (pshRelIdentFunctor.obj e.tgt)).srcMap :=
  by
  have h₁ :
      (π.app (pshRelIdentFunctor.obj
        e.edge.toFunctor)).tgtMap ≫
      ((pshBarrLiftEdgeFunctor (C := C) G).map
        (pshRelIdentToEdgeProj
          e.edge)).tgtMap =
      (π.app e).tgtMap :=
    congrArg VertEdgeHom.tgtMap
      ((Limits.Cone.mk _ π).w
        (pshRelIdentToEdgeProj e.edge))
  have h₂ :
      (π.app (pshRelIdentFunctor.obj
        e.edge.toFunctor)).srcMap ≫
      ((pshBarrLiftEdgeFunctor (C := C) G).map
        (pshRelIdentFunctor.map
          (e.edge.ι ≫
            pshProdSnd
              e.src e.tgt))).srcMap =
      (π.app
        (pshRelIdentFunctor.obj
          e.tgt)).srcMap :=
    congrArg VertEdgeHom.srcMap
      ((Limits.Cone.mk _ π).w
        (pshRelIdentFunctor.map
          (e.edge.ι ≫
            pshProdSnd e.src e.tgt)))
  have h₃ :=
    vertEdgeHom_srcEqTgt_at_ident G
      e.edge.toFunctor
      (π.app (pshRelIdentFunctor.obj
        e.edge.toFunctor))
  dsimp [pshBarrLiftEdgeFunctor,
    pshRelIdentFunctor,
    pshRelIdentToEdgeProj] at h₁ h₂ h₃
  rw [← h₃] at h₁
  exact h₁.symm.trans h₂

/-- Building a presheaf section from a parametric
cone and then rebuilding the cone recovers
the original. -/
theorem parametricCone_roundtrip
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (pc : ParametricCone
      (pshBarrLiftEdgeFunctor
        (C := C) G)) :
    presheafSectionToParametricCone G
      (parametricConeSrcSection G pc) =
    pc := by
  ext e
  apply VertEdgeHom.ext
  · dsimp [presheafSectionToParametricCone,
      parametricConeSrcSection,
      PresheafSection.mk']
    exact
      (parametricCone_srcMap_eq G pc e).symm
  · dsimp [presheafSectionToParametricCone,
      parametricConeSrcSection,
      PresheafSection.mk']
    exact
      (parametricCone_tgtMap_eq G pc e).symm

/-- The type of parametric cones over the
Barr-lifted edge functor of `G` is equivalent
to the type of presheaf-level sections of `G`.
This realizes the presheaf-level end as the
limit over identity edges: a cone over
`pshBarrLiftEdgeFunctor G` (which tests
parametricity at every edge) is determined by
its values at identity edges, which form a
section of `G`. -/
def parametricConeEquivPresheafSection
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) :
    ParametricCone
      (pshBarrLiftEdgeFunctor
        (C := C) G) ≃
    PresheafSection G where
  toFun := parametricConeSrcSection G
  invFun := presheafSectionToParametricCone G
  left_inv := parametricCone_roundtrip G
  right_inv := presheafSection_roundtrip G

end IdentityEdgeRecovery

section LimitRecovery

open Limits in
/-- The composed equivalence: global sections of
the limit of `pshBarrLiftEdgeFunctor G` in
`PshRelEdge C` biject with presheaf sections
of `G`. Restricting the edge-level limit to
identity edges recovers the presheaf-level end
`∫_P G(P)`. -/
def limitSectionEquivPresheafSection
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    {s : Cone
      (pshBarrLiftEdgeFunctor (C := C) G)}
    (hs : IsLimit s) :
    (pshRelEdgeTerminal C ⟶ s.pt) ≃
    PresheafSection G :=
  (parametricConeEquiv
    (pshBarrLiftEdgeFunctor G) hs).symm.trans
    (parametricConeEquivPresheafSection G)

open Limits in
/-- Direction 1 of `limitSectionEquivPresheafSection`:
extract a presheaf section from a global section
of the limit. The section assigns to each presheaf
`P` the `srcMap` at the identity edge
`(P, P, pshRelId P)`. -/
def limitSectionToPresheafSection
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    {s : Cone
      (pshBarrLiftEdgeFunctor (C := C) G)}
    (hs : IsLimit s)
    (f : pshRelEdgeTerminal C ⟶ s.pt) :
    PresheafSection G :=
  (limitSectionEquivPresheafSection G hs) f

open Limits in
/-- Direction 2 of `limitSectionEquivPresheafSection`:
build a global section of the limit from a
presheaf section. -/
def presheafSectionToLimitSection
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    {s : Cone
      (pshBarrLiftEdgeFunctor (C := C) G)}
    (hs : IsLimit s)
    (ps : PresheafSection G) :
    pshRelEdgeTerminal C ⟶ s.pt :=
  (limitSectionEquivPresheafSection G hs).symm
    ps

open Limits in
/-- Roundtrip: extracting then rebuilding a
limit section recovers the original. -/
theorem limitSection_roundtrip
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    {s : Cone
      (pshBarrLiftEdgeFunctor (C := C) G)}
    (hs : IsLimit s)
    (f : pshRelEdgeTerminal C ⟶ s.pt) :
    presheafSectionToLimitSection G hs
      (limitSectionToPresheafSection G hs f) =
    f :=
  (limitSectionEquivPresheafSection G hs).symm_apply_apply f

open Limits in
/-- Roundtrip: rebuilding then extracting a
presheaf section recovers the original. -/
theorem presheafSection_limitRoundtrip
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    {s : Cone
      (pshBarrLiftEdgeFunctor (C := C) G)}
    (hs : IsLimit s)
    (ps : PresheafSection G) :
    limitSectionToPresheafSection G hs
      (presheafSectionToLimitSection
        G hs ps) =
    ps :=
  (limitSectionEquivPresheafSection G hs).apply_symm_apply ps

end LimitRecovery

section WadlerRelatedness

/-- For a parametric cone over
`pshBarrLiftEdgeFunctor G`, the source and
target projections at an identity edge agree.
At edge `(P, P, pshRelId P)`, the Barr lift
gives `pshRelId (G.obj P)`, so the relatedness
condition forces `srcMap = tgtMap`. -/
theorem parametricCone_ident_srcEqTgt
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (pc : ParametricCone
      (pshBarrLiftEdgeFunctor (C := C) G))
    (P : Cᵒᵖ ⥤ Type w) :
    (pc.app
      (pshRelIdentFunctor.obj P)).srcMap =
    (pc.app
      (pshRelIdentFunctor.obj P)).tgtMap :=
  vertEdgeHom_srcEqTgt_at_ident G P
    (pc.app (pshRelIdentFunctor.obj P))

/-- Wadler's relatedness characterization for
parametric cones: two limit projections at
edge `e = (P, Q, R)` yield elements that are
`(pshBarrLiftRel G R)`-related.

For a parametric cone `pc` and any edge `e`,
the pair `(srcMap, tgtMap)` of
`pc.app e : ⊤ ⟶ (G P, G Q, pshBarrLiftRel G R)`
satisfies the relatedness condition of the
Barr-lifted relation. This is Wadler's
condition that `(g_P, g'_Q) ∈ G(R)` for every
relation `R : P ↔ Q`. -/
theorem parametricCone_wadlerRelated
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (pc : ParametricCone
      (pshBarrLiftEdgeFunctor (C := C) G))
    (e : PshRelEdge.{u, v, w} C) :
    pshRelRelated
      (pc.app e).srcMap
      (pc.app e).tgtMap
      (pshRelFull C)
      (pshBarrLiftRel G e.edge) :=
  (pc.app e).sq

/-- Converse of `parametricCone_wadlerRelated`:
given a presheaf section `σ`, the parametric
cone built from `σ` satisfies Wadler's
relatedness at every edge. The source and
target components are `σ.app e.src` and
`σ.app e.tgt`. -/
theorem presheafSection_wadlerRelated
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (σ : PresheafSection G)
    (e : PshRelEdge.{u, v, w} C) :
    pshRelRelated
      (σ.app e.src)
      (σ.app e.tgt)
      (pshRelFull C)
      (pshBarrLiftRel G e.edge) :=
  (presheafSectionToParametricCone G σ).app e
    |>.sq

/-- Wadler's relatedness at graph edges
specializes to naturality: for a parametric
cone `pc` and a presheaf morphism `α : P ⟶ Q`,
the source projections satisfy
`srcMap_P ≫ G.map α = srcMap_Q`.

At graph edges, `pshBarrLiftRel_graph` reduces
the Barr-lifted graph relation to
`pshRelGraph (G.map α)`, so the cone condition
becomes the naturality condition for the
extracted presheaf section. -/
theorem parametricCone_graph_naturality
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (pc : ParametricCone
      (pshBarrLiftEdgeFunctor (C := C) G))
    {P Q : Cᵒᵖ ⥤ Type w} (α : P ⟶ Q) :
    (pc.app
      (pshRelIdentFunctor.obj P)).srcMap ≫
      G.map α =
    (pc.app
      (pshRelIdentFunctor.obj Q)).srcMap := by
  have h :=
    (parametricConeSrcSection G pc).naturality α
  simp only [Functor.const_obj_obj,
    Functor.const_obj_map,
    Category.id_comp] at h
  exact h.symm

end WadlerRelatedness

section QuantificationHierarchy

/-- The quantification hierarchy collapse: the
three levels of section types — identity edges,
graph edges, and all edges — are equivalent for
`pshBarrLiftEdgeFunctor G`.

- **Identity-restricted**: `PresheafSection G`
  (natural family `∀P, ⊤ ⟶ G(P)`)
- **Graph-restricted**: the graph functor is
  fully faithful
  (`pshRelEdgeGraphSubcatFullyFaithful`), so
  the graph cone condition is equivalent to
  naturality of the presheaf section
- **Full parametric**: `ParametricCone` (Wadler
  relatedness at all edges, including non-graph)

The equivalence `ParametricCone ≃ PresheafSection`
(`parametricConeEquivPresheafSection`) shows
that the full parametric condition collapses
to naturality, because the relatedness witnesses
at general edges are determined by naturality at
identity edges via `presheafSection_related`.

This is the formal statement that for covariant
endofunctors `G`, the parametricity condition
adds nothing beyond naturality. The hierarchy
becomes genuinely stratified for conditional
quantification (where only edges satisfying a
predicate are tested; see
`conditional_freeTheorem_graph`). -/
def hierarchyCollapse
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) :
    ParametricCone
      (pshBarrLiftEdgeFunctor
        (C := C) G) ≃
    PresheafSection G :=
  parametricConeEquivPresheafSection G

open Limits in
/-- The hierarchy collapse at the limit level:
global sections of the limit of
`pshBarrLiftEdgeFunctor G` in `PshRelEdge C`
biject with presheaf sections of `G`. -/
def hierarchyCollapseLimit
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    {s : Cone
      (pshBarrLiftEdgeFunctor (C := C) G)}
    (hs : IsLimit s) :
    (pshRelEdgeTerminal C ⟶ s.pt) ≃
    PresheafSection G :=
  limitSectionEquivPresheafSection G hs

end QuantificationHierarchy

section ConditionalFreeTheorem

/-- A conditional free theorem at graph
relations. Given a family of endomorphisms
`σP : G.obj P ⟶ G.obj P` that is natural on a
subclass of morphisms determined by `P`, if
`α : A ⟶ B` satisfies `P`, then `σP` commutes
with `G.map α`.

The free theorem for `sort` is an instance: `P`
is "monotone", and the conclusion is
`G.map α ≫ σP B = σP A ≫ G.map α` for monotone
`α`. Wadler Section 3.3 derives this for types
of the form `∀a. Ctx a ⇒ F a → G a`. -/
theorem conditional_freeTheorem_graph
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (σP :
      (P : Cᵒᵖ ⥤ Type w) → G.obj P ⟶ G.obj P)
    (P : ∀ {A B : Cᵒᵖ ⥤ Type w},
      (A ⟶ B) → Prop)
    (hNat : ∀ {A B : Cᵒᵖ ⥤ Type w}
      (α : A ⟶ B), P α →
      σP A ≫ G.map α = G.map α ≫ σP B) :
    ∀ {A B : Cᵒᵖ ⥤ Type w} (α : A ⟶ B),
      P α →
      pshRelRelated (σP A) (σP B)
        (pshBarrLiftRel G (pshRelGraph α))
        (pshBarrLiftRel G (pshRelGraph α)) := by
  intro A B α hα
  rw [pshBarrLiftRel_graph,
    pshRelRelated_graph_iff]
  exact (hNat α hα).symm

/-- Converse of `conditional_freeTheorem_graph`:
if `σP` is related at the Barr-lifted graph
of every morphism satisfying `P`, then `σP`
commutes with `G.map α` for such morphisms. -/
theorem conditional_graph_implies_nat
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (σP :
      (P : Cᵒᵖ ⥤ Type w) → G.obj P ⟶ G.obj P)
    (P : ∀ {A B : Cᵒᵖ ⥤ Type w},
      (A ⟶ B) → Prop)
    (h : ∀ {A B : Cᵒᵖ ⥤ Type w} (α : A ⟶ B),
      P α →
      pshRelRelated (σP A) (σP B)
        (pshBarrLiftRel G (pshRelGraph α))
        (pshBarrLiftRel G (pshRelGraph α))) :
    ∀ {A B : Cᵒᵖ ⥤ Type w} (α : A ⟶ B),
      P α →
      σP A ≫ G.map α = G.map α ≫ σP B := by
  intro A B α hα
  have hr := h α hα
  rw [pshBarrLiftRel_graph] at hr
  rw [pshRelRelated_graph_iff] at hr
  exact hr.symm

/-- A conditional free theorem at the edge level:
given a family `σP` and a predicate `P` on
`PshRelEdge` edges, if `σP` is parametrically
related at every edge satisfying `P`, then it
commutes with `G.map α` for every morphism `α`
whose graph edge satisfies `P`.

This generalizes `conditional_graph_implies_nat`
from predicates on morphisms to predicates on
edges: an edge predicate `P` restricts
which relations (not just which graphs) the
family is required to respect. -/
theorem conditional_edge_freeTheorem
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (σP :
      (P : Cᵒᵖ ⥤ Type w) → G.obj P ⟶ G.obj P)
    (P : PshRelEdge.{u, v, w} C → Prop)
    (h : ∀ (e : PshRelEdge.{u, v, w} C),
      P e →
      pshRelRelated (σP e.src) (σP e.tgt)
        (pshBarrLiftRel G e.edge)
        (pshBarrLiftRel G e.edge))
    {A B : Cᵒᵖ ⥤ Type w} (α : A ⟶ B)
    (hα : P ⟨A, B, pshRelGraph α⟩) :
    σP A ≫ G.map α = G.map α ≫ σP B := by
  have hr := h ⟨A, B, pshRelGraph α⟩ hα
  rw [pshBarrLiftRel_graph] at hr
  rw [pshRelRelated_graph_iff] at hr
  exact hr.symm

end ConditionalFreeTheorem

section EqualityImpossibility

variable {β : Type*}

/-- The parametric constant lemma: any family
of functions `σ : ∀P c, P.obj c → P.obj c → β`
that is natural in `P` (at graphs) is constant
in both arguments.

That is, for any `a b : P.obj c`,
`σ P c a b = σ P c a a`.

The proof specializes to the terminal
presheaf: the unique map `P ⟶ pshTerminal C`
collapses all elements, so naturality forces
`σ` to factor through the terminal presheaf,
making it independent of both arguments.

(Wadler Section 3.4: parametric polymorphism
precludes polymorphic equality. An element of
`∀X. X → X → Bool` that is natural at all
graphs must return the same value regardless
of whether its arguments are equal.) -/
theorem parametric_constant
    (σ : (P : Cᵒᵖ ⥤ Type (max u v)) →
      (c : Cᵒᵖ) → P.obj c → P.obj c → β)
    (hNat :
      ∀ {P Q : Cᵒᵖ ⥤ Type (max u v)}
        (f : P ⟶ Q)
        (c : Cᵒᵖ) (a b : P.obj c),
        σ P c a b =
          σ Q c (f.app c a) (f.app c b))
    (P : Cᵒᵖ ⥤ Type (max u v))
    (c : Cᵒᵖ) (a b : P.obj c) :
    σ P c a b = σ P c a a := by
  let bang := (pshTerminalUnique (C := C) P).default
  have h1 := hNat bang c a b
  have h2 := hNat bang c a a
  have heq : bang.app c b = bang.app c a :=
    PUnit.ext _ _
  rw [h1, heq, ← h2]

/-- The parametric constant value lemma: any
parametric family `σ` returns the same value
at all presheaves, objects, and elements. All
values equal `σ (pshTerminal C) c ⟨⟩ ⟨⟩`. -/
theorem parametric_constant_value
    (σ : (P : Cᵒᵖ ⥤ Type (max u v)) →
      (c : Cᵒᵖ) → P.obj c → P.obj c → β)
    (hNat :
      ∀ {P Q : Cᵒᵖ ⥤ Type (max u v)}
        (f : P ⟶ Q)
        (c : Cᵒᵖ) (a b : P.obj c),
        σ P c a b =
          σ Q c (f.app c a) (f.app c b))
    (P : Cᵒᵖ ⥤ Type (max u v))
    (c : Cᵒᵖ) (a b : P.obj c) :
    σ P c a b =
      σ (pshTerminal C) c PUnit.unit
        PUnit.unit :=
  hNat (pshTerminalUnique (C := C) P).default
    c a b

/-- No parametric family
`σ : ∀P c, P.obj c → P.obj c → Bool` can
implement decidable equality on all presheaves.

If `σ` is natural and there exists a presheaf
`P`, an object `c`, and two distinct elements
`a b : P.obj c` such that `a ≠ b`, then either
`σ` returns `true` on unequal elements (fails to
witness inequality) or `σ` returns `false` on
equal elements (fails to witness equality). -/
theorem no_parametric_equality
    (σ : (P : Cᵒᵖ ⥤ Type (max u v)) →
      (c : Cᵒᵖ) → P.obj c → P.obj c → Bool)
    (hNat :
      ∀ {P Q : Cᵒᵖ ⥤ Type (max u v)}
        (f : P ⟶ Q)
        (c : Cᵒᵖ) (a b : P.obj c),
        σ P c a b =
          σ Q c (f.app c a) (f.app c b))
    (P : Cᵒᵖ ⥤ Type (max u v))
    (c : Cᵒᵖ) (a b : P.obj c) :
    σ P c a b = σ P c a a :=
  parametric_constant σ hNat P c a b

end EqualityImpossibility

section YonedaViaParametricity

/-- The Yoneda lemma via parametricity at the
presheaf level: a family
`σ : ∀(P : PSh C), (A ⟶ P) → ∀ c, P.obj c`
that is natural in `P` at graphs is determined
by `σ A (𝟙 A)`.

Naturality says: for `α : P ⟶ Q` and
`f : A ⟶ P`, `α.app c (σ P f c) = σ Q (f ≫ α) c`.

Setting `P = A`, `f = 𝟙 A`, `α = g`:
`g.app c (σ A (𝟙 A) c) = σ Q (𝟙 A ≫ g) c
                        = σ Q g c`. -/
theorem yoneda_via_parametricity
    (A : Cᵒᵖ ⥤ Type (max u v))
    (σ : (P : Cᵒᵖ ⥤ Type (max u v)) →
      (A ⟶ P) → (c : Cᵒᵖ) → P.obj c)
    (hNat :
      ∀ {P Q : Cᵒᵖ ⥤ Type (max u v)}
        (α : P ⟶ Q) (f : A ⟶ P) (c : Cᵒᵖ),
        α.app c (σ P f c) =
          σ Q (f ≫ α) c)
    (Q : Cᵒᵖ ⥤ Type (max u v))
    (g : A ⟶ Q) (c : Cᵒᵖ) :
    σ Q g c = g.app c (σ A (𝟙 A) c) := by
  have h := hNat g (𝟙 A) c
  simp only [Category.id_comp] at h
  exact h.symm

/-- The Yoneda embedding via parametricity:
every element `a : A.obj c` determines a
parametric family via `fun P f c => f.app c a`.
This family is natural because `f` is a natural
transformation. -/
theorem yoneda_embedding_natural
    (A : Cᵒᵖ ⥤ Type (max u v))
    (a : (c : Cᵒᵖ) → A.obj c)
    {P Q : Cᵒᵖ ⥤ Type (max u v)}
    (α : P ⟶ Q) (f : A ⟶ P) (c : Cᵒᵖ) :
    α.app c (f.app c (a c)) =
      (f ≫ α).app c (a c) := rfl

/-- The Yoneda bijection via parametricity:
parametric families of type
`∀P, (A ⟶ P) → ∀c, P.obj c` that are natural
at `c` (i.e., compatible with presheaf maps)
correspond bijectively to global sections of `A`.

For a global section `s` (a natural
transformation `𝟙 ⟶ A`), the induced family
is `fun P f c => f.app c (s.app c ⟨⟩)`.
The inverse extracts `σ A (𝟙 A)`. -/
theorem yoneda_parametricity_inverse
    (A : Cᵒᵖ ⥤ Type (max u v))
    (σ : (P : Cᵒᵖ ⥤ Type (max u v)) →
      (A ⟶ P) → (c : Cᵒᵖ) → P.obj c)
    (hNat :
      ∀ {P Q : Cᵒᵖ ⥤ Type (max u v)}
        (α : P ⟶ Q) (f : A ⟶ P) (c : Cᵒᵖ),
        α.app c (σ P f c) =
          σ Q (f ≫ α) c)
    (Q : Cᵒᵖ ⥤ Type (max u v))
    (g : A ⟶ Q) (c : Cᵒᵖ) :
    σ Q g c = g.app c (σ A (𝟙 A) c) :=
  yoneda_via_parametricity A σ hNat Q g c

end YonedaViaParametricity

section YonedaExtensionOfSections

variable {C : Type u} [Category.{v} C]

/-- A representable section of an endofunctor
`G : PSh(C) ⥤ PSh(C)` relative to an embedding
`Y : C ⥤ PSh(C)` is a natural family of morphisms
`pshUnitPresheaf C ⟶ G.obj (Y.obj X)` indexed by
`X : C`. When `Y` is the Yoneda embedding, this
is the restriction of a `PresheafSection` to
representable presheaves. -/
abbrev RepresentableSection
    (Y : C ⥤ (Cᵒᵖ ⥤ Type w))
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) :=
  constTerminal C
    (pshUnitPresheafIsTerminal.{u, v, w} C) ⟶
    Y ⋙ G

/-- Build a `RepresentableSection` from a family
of morphisms from the terminal presheaf satisfying
the naturality condition. -/
def RepresentableSection.mk'
    (Y : C ⥤ (Cᵒᵖ ⥤ Type w))
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (s : (X : C) →
      (pshUnitPresheaf C ⟶ G.obj (Y.obj X)))
    (hs : ∀ {X X' : C} (f : X ⟶ X'),
      s X ≫ G.map (Y.map f) = s X') :
    RepresentableSection Y G :=
  { app := fun X => s X
    naturality := fun {X X'} f => by
      simp only [Functor.const_obj_obj,
        Functor.const_obj_map,
        Functor.comp_obj, Functor.comp_map,
        Category.id_comp]
      exact (hs f).symm }

/-- The component of a `RepresentableSection`
at `X : C` is a morphism
`pshUnitPresheaf C ⟶ G.obj (Y.obj X)`. -/
@[simp]
theorem RepresentableSection.mk'_app
    (Y : C ⥤ (Cᵒᵖ ⥤ Type w))
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (s : (X : C) →
      (pshUnitPresheaf C ⟶ G.obj (Y.obj X)))
    (hs : ∀ {X X' : C} (f : X ⟶ X'),
      s X ≫ G.map (Y.map f) = s X')
    (X : C) :
    (RepresentableSection.mk' Y G s hs).app X =
      s X :=
  rfl

/-- Restriction of a presheaf section to an
embedding `Y : C ⥤ PSh(C)`: precomposition with
`Y` restricts from all presheaves to those in the
image of `Y`. -/
def presheafSectionRestrict
    (Y : C ⥤ (Cᵒᵖ ⥤ Type w))
    {G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (σ : PresheafSection G) :
    RepresentableSection Y G where
  app X := σ.app (Y.obj X)
  naturality {X X'} f := by
    have h := σ.naturality (Y.map f)
    simp only [Functor.const_obj_obj,
      Functor.const_obj_map,
      Category.id_comp] at h
    simp only [Functor.const_obj_obj,
      Functor.const_obj_map,
      Functor.comp_obj, Functor.comp_map,
      Category.id_comp]
    exact h

/-- The restriction map evaluates to the
presheaf section at the image of `Y`. -/
@[simp]
theorem presheafSectionRestrict_app
    (Y : C ⥤ (Cᵒᵖ ⥤ Type w))
    {G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (σ : PresheafSection G)
    (X : C) :
    (presheafSectionRestrict Y σ).app X =
      σ.app (Y.obj X) :=
  rfl

/-- A presheaf section `σ` is determined by its
value at the initial presheaf: `σ_P` equals
`σ_∅ ≫ G.map(!_P)` where `!_P : ∅ → P` is
the unique morphism from the initial presheaf. -/
theorem presheafSection_eq_via_initial
    {G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (σ : PresheafSection G)
    (P : Cᵒᵖ ⥤ Type w) :
    σ.app P =
      σ.app (pshEmptyPresheaf C) ≫
        G.map (pshEmptyMap P) := by
  have h := σ.naturality (pshEmptyMap P)
  simp only [Functor.const_obj_obj,
    Functor.const_obj_map,
    Category.id_comp] at h
  exact h

/-- Construct a presheaf section from a morphism
`⊤ → G(∅)` by postcomposing with `G.map(!_P)`.
Naturality follows from the uniqueness of the
morphism from the initial presheaf. -/
def presheafSectionOfInitial
    {G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (τ : pshUnitPresheaf C ⟶
      G.obj (pshEmptyPresheaf C)) :
    PresheafSection G :=
  PresheafSection.mk' G
    (fun P => τ ≫ G.map (pshEmptyMap P))
    (fun {P Q} α => by
      simp only [Category.assoc, ← G.map_comp]
      have h : pshEmptyMap P ≫ α =
          pshEmptyMap Q :=
        pshEmptyMap_unique
          (pshEmptyMap P ≫ α)
      rw [h])

/-- Round-trip: constructing a presheaf section
from its initial-presheaf value recovers the
original section. -/
theorem presheafSectionOfInitial_restrict
    {G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (σ : PresheafSection G) :
    presheafSectionOfInitial
      (σ.app (pshEmptyPresheaf C)) = σ := by
  apply NatTrans.ext
  funext P
  simp only [presheafSectionOfInitial,
    PresheafSection.mk']
  exact (presheafSection_eq_via_initial σ P).symm

/-- Round-trip: extracting the initial-presheaf
value from a constructed section recovers the
original morphism. -/
theorem presheafSectionOfInitial_app_empty
    {G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (τ : pshUnitPresheaf C ⟶
      G.obj (pshEmptyPresheaf C)) :
    (presheafSectionOfInitial τ).app
      (pshEmptyPresheaf C) = τ := by
  simp only [presheafSectionOfInitial,
    PresheafSection.mk']
  have h : pshEmptyMap (pshEmptyPresheaf C) =
      𝟙 (pshEmptyPresheaf.{u, v, w} C) :=
    (pshEmptyMap_unique
      (𝟙 (pshEmptyPresheaf C))).symm
  rw [h, G.map_id, Category.comp_id]

/-- Presheaf sections of `G` are equivalent to
morphisms from the terminal presheaf to `G`
applied to the initial presheaf. The forward
direction evaluates at `∅`; the reverse extends
via `G.map(!_P)`. -/
def presheafSectionEquivInitial
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) :
    PresheafSection G ≃
      (pshUnitPresheaf C ⟶
        G.obj (pshEmptyPresheaf C)) where
  toFun σ := σ.app (pshEmptyPresheaf C)
  invFun τ := presheafSectionOfInitial τ
  left_inv σ :=
    presheafSectionOfInitial_restrict σ
  right_inv τ :=
    presheafSectionOfInitial_app_empty τ

/-- The restriction map factors through the
initial-presheaf value: the component
`(presheafSectionRestrict Y σ).app X` equals
`σ_∅ ≫ G.map(!_{Y(X)})`. -/
theorem presheafSectionRestrict_via_initial
    (Y : C ⥤ (Cᵒᵖ ⥤ Type w))
    {G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (σ : PresheafSection G)
    (X : C) :
    (presheafSectionRestrict Y σ).app X =
      σ.app (pshEmptyPresheaf C) ≫
        G.map (pshEmptyMap (Y.obj X)) := by
  simp only [presheafSectionRestrict_app]
  exact presheafSection_eq_via_initial σ
    (Y.obj X)

/-- Injectivity of restriction holds when the
maps `G.map(!_{Y(X)}) : G(∅) → G(Y(X))` are
jointly monic: if two morphisms `τ₁, τ₂ : ⊤ → G(∅)`
agree after postcomposing with all
`G.map(!_{Y(X)})`, then `τ₁ = τ₂`. -/
theorem presheafSectionRestrict_injective
    (Y : C ⥤ (Cᵒᵖ ⥤ Type w))
    {G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (hMono : ∀ (τ₁ τ₂ :
        pshUnitPresheaf C ⟶
          G.obj (pshEmptyPresheaf C)),
      (∀ X : C,
        τ₁ ≫ G.map (pshEmptyMap (Y.obj X)) =
        τ₂ ≫ G.map (pshEmptyMap (Y.obj X))) →
      τ₁ = τ₂)
    {σ₁ σ₂ : PresheafSection G}
    (hEq : presheafSectionRestrict Y σ₁ =
      presheafSectionRestrict Y σ₂) :
    σ₁ = σ₂ := by
  have hInit : σ₁.app (pshEmptyPresheaf C) =
      σ₂.app (pshEmptyPresheaf C) := by
    apply hMono
    intro X
    have h₁ := presheafSectionRestrict_via_initial
      Y σ₁ X
    have h₂ := presheafSectionRestrict_via_initial
      Y σ₂ X
    have hApp : (presheafSectionRestrict Y σ₁).app
        X =
        (presheafSectionRestrict Y σ₂).app X :=
      congr_fun (congr_arg NatTrans.app hEq) X
    rw [h₁] at hApp
    rw [h₂] at hApp
    exact hApp
  rw [← presheafSectionOfInitial_restrict σ₁,
    ← presheafSectionOfInitial_restrict σ₂,
    hInit]

/-- Given a witness `X₀ : C` whose image under
`Y` is isomorphic to the initial presheaf, extend
a representable section to a full presheaf section
by extracting the initial-presheaf value through
the isomorphism. -/
def representableSectionExtend
    (Y : C ⥤ (Cᵒᵖ ⥤ Type w))
    {G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (X₀ : C)
    (i : Y.obj X₀ ≅ pshEmptyPresheaf C)
    (ρ : RepresentableSection Y G) :
    PresheafSection G :=
  presheafSectionOfInitial
    (ρ.app X₀ ≫ G.map i.hom)

/-- Restrict-then-extend recovers the original
presheaf section. -/
theorem representableSectionExtend_restrict
    (Y : C ⥤ (Cᵒᵖ ⥤ Type w))
    {G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (X₀ : C)
    (i : Y.obj X₀ ≅ pshEmptyPresheaf C)
    (σ : PresheafSection G) :
    representableSectionExtend Y X₀ i
      (presheafSectionRestrict Y σ) = σ := by
  simp only [representableSectionExtend,
    presheafSectionRestrict_app]
  rw [presheafSection_eq_via_initial σ
    (Y.obj X₀)]
  simp only [Category.assoc, ← G.map_comp]
  have h : pshEmptyMap (Y.obj X₀) ≫ i.hom =
      𝟙 (pshEmptyPresheaf.{u, v, w} C) :=
    (pshEmptyMap_unique _).trans
      (pshEmptyMap_unique _).symm
  rw [h, G.map_id, Category.comp_id]
  exact presheafSectionOfInitial_restrict σ

/-- The representable section obtained by
extending and then restricting agrees at the
witness object `X₀` with the original, up to
the isomorphism `i`. -/
theorem representableSectionExtend_app_X₀
    (Y : C ⥤ (Cᵒᵖ ⥤ Type w))
    {G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (X₀ : C)
    (i : Y.obj X₀ ≅ pshEmptyPresheaf C)
    (ρ : RepresentableSection Y G) :
    (presheafSectionRestrict Y
      (representableSectionExtend Y X₀ i ρ)
    ).app X₀ =
      ρ.app X₀ ≫ G.map i.hom ≫
        G.map (pshEmptyMap (Y.obj X₀)) := by
  simp only [presheafSectionRestrict_app,
    representableSectionExtend,
    presheafSectionOfInitial,
    PresheafSection.mk']
  rfl

/-- When `Y.obj X₀ ≅ ∅` and `G` maps `i.inv`
followed by `i.hom` to the identity on
`G(Y.obj X₀)`, the extend-then-restrict round-trip
at `X₀` recovers the original component. -/
theorem representableSectionExtend_roundtrip_X₀
    (Y : C ⥤ (Cᵒᵖ ⥤ Type w))
    {G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (X₀ : C)
    (i : Y.obj X₀ ≅ pshEmptyPresheaf C)
    (ρ : RepresentableSection Y G)
    (hInit :
      pshEmptyMap (Y.obj X₀) = i.inv) :
    (presheafSectionRestrict Y
      (representableSectionExtend Y X₀ i ρ)
    ).app X₀ = ρ.app X₀ := by
  rw [representableSectionExtend_app_X₀]
  simp only [← G.map_comp, hInit,
    i.hom_inv_id, G.map_id]
  exact Category.comp_id _

/-- Any morphism from a presheaf isomorphic to `∅`
equals the composition through the initial
presheaf, because morphisms from the initial
presheaf are unique. -/
theorem morphism_from_pshEmpty_unique
    {P Q : Cᵒᵖ ⥤ Type w}
    (i : P ≅ pshEmptyPresheaf C)
    (g : P ⟶ Q) :
    g = i.hom ≫ pshEmptyMap Q := by
  have h : i.inv ≫ g = pshEmptyMap Q :=
    pshEmptyMap_unique (i.inv ≫ g)
  calc g = (i.hom ≫ i.inv) ≫ g := by
        rw [i.hom_inv_id, Category.id_comp]
    _ = i.hom ≫ pshEmptyMap Q := by
        rw [Category.assoc, h]

/-- Extend-then-restrict recovers the original
representable section when `X₀` is weakly
initial (every `X` receives a morphism from
`X₀`). This works because `Y(X₀) ≅ ∅` forces
any morphism `Y(X₀) → Y(X)` to be unique, so
`Y.map f = i.hom ≫ pshEmptyMap(Y(X))` for any
`f : X₀ → X`, and naturality of `ρ` at `f`
gives the result. -/
theorem representableSectionExtend_section
    (Y : C ⥤ (Cᵒᵖ ⥤ Type w))
    {G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (X₀ : C)
    (i : Y.obj X₀ ≅ pshEmptyPresheaf C)
    (hInit : ∀ X : C, X₀ ⟶ X)
    (ρ : RepresentableSection Y G) :
    presheafSectionRestrict Y
      (representableSectionExtend Y X₀ i ρ) =
        ρ := by
  apply NatTrans.ext
  funext X
  simp only [presheafSectionRestrict_app,
    representableSectionExtend,
    presheafSectionOfInitial,
    PresheafSection.mk']
  rw [Category.assoc, ← G.map_comp]
  have hf : Y.map (hInit X) =
      i.hom ≫ pshEmptyMap (Y.obj X) :=
    morphism_from_pshEmpty_unique i (Y.map _)
  rw [← hf]
  have hnat := ρ.naturality (hInit X)
  simp only [Functor.const_obj_obj,
    Functor.const_obj_map, Functor.comp_obj,
    Functor.comp_map, Category.id_comp] at hnat
  exact hnat.symm

/-- When `Y(X₀) ≅ ∅` and `X₀` is weakly initial,
presheaf sections and representable sections are
equivalent. The forward map restricts to the image
of `Y`; the inverse extends via the initial
presheaf. -/
def presheafSectionEquivRepresentable
    (Y : C ⥤ (Cᵒᵖ ⥤ Type w))
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (X₀ : C)
    (i : Y.obj X₀ ≅ pshEmptyPresheaf C)
    (hInit : ∀ X : C, X₀ ⟶ X) :
    PresheafSection G ≃
      RepresentableSection Y G where
  toFun := presheafSectionRestrict Y
  invFun := representableSectionExtend Y X₀ i
  left_inv σ :=
    representableSectionExtend_restrict Y X₀ i σ
  right_inv ρ :=
    representableSectionExtend_section
      Y X₀ i hInit ρ

/-- Parametric cones of `pshBarrLiftEdgeFunctor G`
are equivalent to morphisms from the terminal
presheaf to `G` applied to the initial presheaf.
Composes `parametricConeEquivPresheafSection`
with `presheafSectionEquivInitial`. -/
def parametricConeEquivInitial
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) :
    ParametricCone
      (pshBarrLiftEdgeFunctor (C := C) G) ≃
      (pshUnitPresheaf C ⟶
        G.obj (pshEmptyPresheaf C)) :=
  (parametricConeEquivPresheafSection G).trans
    (presheafSectionEquivInitial G)

open Limits in
/-- Global sections of the limit of
`pshBarrLiftEdgeFunctor G` are equivalent to
morphisms `⊤ → G(∅)`. Composes
`limitSectionEquivPresheafSection` with
`presheafSectionEquivInitial`. -/
def limitSectionEquivInitial
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    {s : Cone
      (pshBarrLiftEdgeFunctor (C := C) G)}
    (hs : IsLimit s) :
    (pshRelEdgeTerminal C ⟶ s.pt) ≃
      (pshUnitPresheaf C ⟶
        G.obj (pshEmptyPresheaf C)) :=
  (limitSectionEquivPresheafSection G hs).trans
    (presheafSectionEquivInitial G)

/-- There is no morphism from the terminal
presheaf to the initial presheaf when `C` is
nonempty: the terminal presheaf has an element
at every component, while the initial presheaf
is empty everywhere. -/
theorem no_morphism_terminal_to_initial
    [Nonempty C]
    (f : pshUnitPresheaf.{u, v, w} C ⟶
      pshEmptyPresheaf C) :
    False :=
  let ⟨c⟩ := ‹Nonempty C›
  (f.app (Opposite.op c)
    ⟨PUnit.unit⟩).down.elim

/-- If `G(∅)` is initial and `C` is nonempty,
there are no presheaf sections of `G`, because a
section would require a morphism `⊤ → G(∅) ≅ ∅`,
but `⊤` is inhabited while `∅` is not. -/
theorem presheafSection_empty_of_initial
    [Nonempty C]
    {G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (hI : Limits.IsInitial
      (G.obj (pshEmptyPresheaf C)))
    (σ : PresheafSection G) : False := by
  let τ := (presheafSectionEquivInitial G) σ
  exact no_morphism_terminal_to_initial
    (τ ≫ Limits.IsInitial.to hI
      (pshEmptyPresheaf.{u, v, w} C))

/-- If `G(∅)` is terminal, then any two
presheaf sections of `G` are equal, because
both map to the unique morphism `⊤ → G(∅) ≅ ⊤`
under `presheafSectionEquivInitial`. -/
theorem presheafSection_unique_of_terminal
    {G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (hT : Limits.IsTerminal
      (G.obj (pshEmptyPresheaf C)))
    (σ₁ σ₂ : PresheafSection G) :
    σ₁ = σ₂ := by
  apply (presheafSectionEquivInitial G).injective
  exact Limits.IsTerminal.hom_ext hT _ _

end YonedaExtensionOfSections

end GebLean
