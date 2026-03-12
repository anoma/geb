import GebLean.PshRelDouble
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
* `natTransToBarrEndo` / `barrEndoToNatTrans`:
  bijection between natural transformations
  `G ⟶ G` and natural endomorphisms of the
  covariant Barr embedding (rearrangement)
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

section Rearrangement

/-- A natural transformation `σ : G ⟶ G` induces
a natural endomorphism of the covariant Barr
embedding `pshBarrEmbedding G`. The component at
`P` has both srcMap and tgtMap equal to
`σ.app P`. -/
def natTransToBarrEndo
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (σ : G ⟶ G) :
    pshBarrEmbedding (C := C) G ⟶
    pshBarrEmbedding G where
  app P :=
    { srcMap := σ.app P
      tgtMap := σ.app P
      sq := by
        change pshRelRelated (σ.app P) (σ.app P)
          (pshBarrLiftRel G (pshRelId P))
          (pshBarrLiftRel G (pshRelId P))
        rw [pshBarrLiftRel_id]
        exact pshRelRelatedSqVertId (σ.app P) }
  naturality {P Q} α :=
    VertEdgeHom.ext (σ.naturality α)
      (σ.naturality α)

/-- A natural endomorphism of the covariant Barr
embedding yields a natural transformation
`G ⟶ G` by extracting the srcMap component.
This is the rearrangement free theorem: the
endomorphism's naturality in `PshRelEdge`
implies the commutativity
`σ_P ≫ G.map α = G.map α ≫ σ_Q`. -/
def barrEndoToNatTrans
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (τ : pshBarrEmbedding (C := C) G ⟶
      pshBarrEmbedding G) :
    G ⟶ G where
  app P := (τ.app P).srcMap
  naturality _ _ α :=
    congrArg VertEdgeHom.srcMap (τ.naturality α)

/-- The roundtrip
`natTransToBarrEndo ∘ barrEndoToNatTrans`
is the identity. -/
theorem natTransToBarrEndo_barrEndoToNatTrans
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (τ : pshBarrEmbedding (C := C) G ⟶
      pshBarrEmbedding G) :
    natTransToBarrEndo G
      (barrEndoToNatTrans G τ) = τ := by
  ext P
  apply VertEdgeHom.ext
  · rfl
  · exact (pshBarrLiftRel_id_related_iff G).mp
      (τ.app P).sq

/-- The roundtrip
`barrEndoToNatTrans ∘ natTransToBarrEndo`
is the identity. -/
theorem barrEndoToNatTrans_natTransToBarrEndo
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (σ : G ⟶ G) :
    barrEndoToNatTrans (C := C) G
      (natTransToBarrEndo G σ) = σ := rfl

end Rearrangement

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

/-- A section of a copresheaf on `PshRelEdge C` is
a family assigning an element of `F.obj (op e)` to
each edge `e`, contravariantly natural in the edge
morphisms. The naturality condition at an edge
morphism `(α, β, sq) : e₁ ⟶ e₂` says:
`F.map (α, β, sq).op (s e₂) = s e₁`.

This IS the parametricity condition: naturality at
a morphism in `PshRelEdge C` encodes that the
section respects the relatedness structure of the
edge. Wadler's Parametricity Theorem (Section 6)
proves this inductively on type structure; in
`PshRelEdge C`, it holds by definition (naturality
of a section). -/
def IsParametricSection
    (F : (PshRelEdge.{u, v, w} C)ᵒᵖ ⥤ Type w)
    (s : (e : PshRelEdge.{u, v, w} C) →
      F.obj (Opposite.op e)) : Prop :=
  ∀ {e₁ e₂ : PshRelEdge.{u, v, w} C}
    (f : e₁ ⟶ e₂),
    F.map f.op (s e₂) = s e₁

/-- A natural transformation from the terminal
copresheaf determines a parametric section.
The naturality of the section is exactly the
parametricity condition. -/
theorem natTrans_isParametricSection
    (F : (PshRelEdge.{u, v, w} C)ᵒᵖ ⥤ Type w)
    (σ :
      (Functor.const
        (PshRelEdge.{u, v, w} C)ᵒᵖ).obj
        PUnit ⟶ F) :
    IsParametricSection F
      (fun e => σ.app (Opposite.op e) ⟨⟩) := by
  intro e₁ e₂ f
  have h := congr_fun (σ.naturality f.op) ⟨⟩
  simp [Functor.const_obj_map] at h
  exact h.symm

/-- Parametricity for sections of copresheaves
on `PshRelEdge C` is tautological: the
parametricity condition at an edge morphism
`f : e₁ ⟶ e₂` is definitionally equivalent to
the naturality condition of the section. The
proof is `hs f`, i.e., direct application of
the naturality hypothesis. -/
theorem isParametricSection_at
    (F : (PshRelEdge.{u, v, w} C)ᵒᵖ ⥤ Type w)
    (s : (e : PshRelEdge.{u, v, w} C) →
      F.obj (Opposite.op e))
    (hs : IsParametricSection F s)
    {e₁ e₂ : PshRelEdge.{u, v, w} C}
    (f : e₁ ⟶ e₂) :
    F.map f.op (s e₂) = s e₁ :=
  hs f

/-- The converse of `natTrans_isParametricSection`:
a parametric section determines a natural
transformation from the terminal copresheaf. -/
def parametricSectionToNatTrans
    (F : (PshRelEdge.{u, v, w} C)ᵒᵖ ⥤ Type w)
    (s : (e : PshRelEdge.{u, v, w} C) →
      F.obj (Opposite.op e))
    (hs : IsParametricSection F s) :
    (Functor.const
      (PshRelEdge.{u, v, w} C)ᵒᵖ).obj
      PUnit ⟶ F where
  app e _ := s e.unop
  naturality {e₁ e₂} f := by
    funext _
    simp only [Functor.const_obj_obj,
      Functor.const_obj_map, types_comp_apply]
    exact (hs f.unop).symm

end ParametricityAsTautology

end GebLean
