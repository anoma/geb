import GebLean.PolyPresentation
import Mathlib.CategoryTheory.Elements

/-!
# Equivalence Between Polynomial Presentations and Copresheaves

This module proves that the localized category of polynomial presentations
`PolyPresentationLoc D` is equivalent to the category of copresheaves `D ⥤ Type`.

## Main Definitions

* `densityPresentation` - Constructs a canonical polynomial presentation from
  any copresheaf using the category of elements
* `densityPresentationFunctor` - The functor `(D ⥤ Type) ⥤ PolyPresentationLoc D`
* `polyPresentationLocEquiv` - The equivalence `PolyPresentationLoc D ≌ (D ⥤ Type)`

## Mathematical Background

The density formula (co-Yoneda lemma) states that every copresheaf F : D → Type
is a colimit of representable functors indexed by the category of elements:

```
F ≅ colim_{(d, x) ∈ ∫F} D(d, -)
```

Any colimit can be expressed as a coequalizer of coproducts:

```
colim D ≅ coeq( ∐_{f : j → k} D(j)  ⇉  ∐_{j} D(j) )
```

Combining these, every copresheaf is isomorphic to a coequalizer of polynomial
functors, which is exactly what a polynomial presentation represents.

-/

namespace GebLean

open CategoryTheory

universe u v w

variable {D : Type u} [Category.{v} D]

/-! ## Density Presentation

The density presentation of a copresheaf F uses the category of elements ∫F
to construct a canonical polynomial presentation whose coequalizer is F.

-/

section DensityPresentation

variable (F : D ⥤ Type (max u w v))

/-! ### Index Types

The target polynomial is indexed by objects of F.Elements (pairs (d, x)).
The source polynomial is indexed by morphisms in F.Elementsᵒᵖ, which are
morphisms (q → p) in F.Elements (going "backward").
-/

/--
The index type for morphisms in F.Elementsᵒᵖ. This is the type of triples
(p, q, f) where p, q : F.Elements and f : q ⟶ p in F.Elements.
-/
def DensityMorphismIndex : Type (max u w v) :=
  Σ (p q : F.Elements), (q ⟶ p)

/--
Extract the target element from a morphism index.
-/
def DensityMorphismIndex.tgt (m : DensityMorphismIndex F) : F.Elements :=
  m.fst

/--
Extract the source element from a morphism index.
-/
def DensityMorphismIndex.src (m : DensityMorphismIndex F) : F.Elements :=
  m.snd.fst

/--
Extract the morphism from a morphism index.
-/
def DensityMorphismIndex.hom (m : DensityMorphismIndex F) :
    m.src ⟶ m.tgt :=
  m.snd.snd

/-! ### Target Polynomial

The target polynomial Q is indexed by F.Elements with family p ↦ p.fst.
This represents ∐_{(d,x) ∈ ∫F} D(d, -).
-/

/--
The target polynomial of the density presentation.
Indexed by elements of F, with family mapping (d, x) to d.
-/
def densityTgt : CoprodCovarRepCat'.{u, v, max u w v} D :=
  ccrObjMk (fun (p : F.Elements) => p.fst)

@[simp]
theorem densityTgt_index :
    ccrIndex (densityTgt F) = F.Elements := rfl

@[simp]
theorem densityTgt_family (p : F.Elements) :
    ccrFamily (densityTgt F) p = p.fst := rfl

/-! ### Source Polynomial

The source polynomial P is indexed by morphisms in F.Elementsᵒᵖ (i.e.,
reversed morphisms in F.Elements) with family (p, q, f : q → p) ↦ p.fst.
This represents ∐_{f ∈ mor(∫F)ᵒᵖ} D(tgt(f), -).
-/

/--
The source polynomial of the density presentation.
Indexed by morphisms (q → p) in F.Elements, with family mapping to p.fst.
-/
def densitySrc : CoprodCovarRepCat'.{u, v, max u w v} D :=
  ccrObjMk (fun (m : DensityMorphismIndex F) => m.tgt.fst)

@[simp]
theorem densitySrc_index :
    ccrIndex (densitySrc F) = DensityMorphismIndex F := rfl

@[simp]
theorem densitySrc_family (m : DensityMorphismIndex F) :
    ccrFamily (densitySrc F) m = m.tgt.fst := rfl

/-! ### Parallel Morphisms

The two parallel morphisms α, β : P → Q encode the colimit structure:
- α (source map): includes component at target of morphism, fiber is identity
- β (target map): includes component at source of morphism, fiber is the morphism
-/

/--
The first parallel morphism (source map) of the density presentation.
Maps morphism index (p, q, f : q → p) to element p with identity fiber.
-/
def densityFst : densitySrc F ⟶ densityTgt F :=
  ccrHomMk
    (fun m => m.tgt)
    (fun m => 𝟙 m.tgt.fst)

@[simp]
theorem densityFst_reindex (m : DensityMorphismIndex F) :
    ccrReindex (densityFst F) m = m.tgt := rfl

@[simp]
theorem densityFst_fiberMor (m : DensityMorphismIndex F) :
    ccrFiberMor (densityFst F) m = 𝟙 m.tgt.fst := rfl

/--
The second parallel morphism (target map) of the density presentation.
Maps morphism index (p, q, f : q → p) to element q with fiber f.val.
-/
def densitySnd : densitySrc F ⟶ densityTgt F :=
  ccrHomMk
    (fun m => m.src)
    (fun m => m.hom.val)

@[simp]
theorem densitySnd_reindex (m : DensityMorphismIndex F) :
    ccrReindex (densitySnd F) m = m.src := rfl

@[simp]
theorem densitySnd_fiberMor (m : DensityMorphismIndex F) :
    ccrFiberMor (densitySnd F) m = m.hom.val := rfl

/-! ### The Density Presentation -/

/--
The density presentation of a copresheaf F : D ⥤ Type.

This is the canonical polynomial presentation whose coequalizer is
isomorphic to F. The construction uses the category of elements:
- Target polynomial: indexed by elements (d, x) ∈ ∫F, family p ↦ d
- Source polynomial: indexed by morphisms in (∫F)ᵒᵖ, family m ↦ tgt(m).fst
- α: source map (identity fibers)
- β: target map (morphism fibers)
-/
def densityPresentation : PolyPresentation.{u, v, max u w v} D where
  src := densitySrc F
  tgt := densityTgt F
  fst := densityFst F
  snd := densitySnd F

@[simp]
theorem densityPresentation_src :
    (densityPresentation F).src = densitySrc F := rfl

@[simp]
theorem densityPresentation_tgt :
    (densityPresentation F).tgt = densityTgt F := rfl

@[simp]
theorem densityPresentation_fst :
    (densityPresentation F).fst = densityFst F := rfl

@[simp]
theorem densityPresentation_snd :
    (densityPresentation F).snd = densitySnd F := rfl

end DensityPresentation

/-! ## Density Isomorphism

The coequalizer of the density presentation is naturally isomorphic to F.
This is the content of the density formula (co-Yoneda lemma).
-/

section DensityIsomorphism

variable (F : D ⥤ Type (max u w v))

/-! ### The Forward Map

The map from the coequalizer to F: given an element (p, g) where p = (d, x)
and g : d ⟶ A, we compute F.map g x : F.obj A.
-/

/--
The underlying map from the target polynomial evaluation to F.
Maps (p, g) where p = (d, x) : F.Elements and g : d ⟶ A to F.map g x.
-/
def densityToFunctorApp (A : D) :
    ccrEval (densityTgt F) A → F.obj A :=
  fun ⟨p, g⟩ => F.map g p.snd

/--
The map `densityToFunctorApp` coequalizes the parallel pair.
-/
theorem densityToFunctorApp_coequalizes (A : D) :
    densityToFunctorApp F A ∘ (ccrToFunctorMap (densityFst F)).app A =
    densityToFunctorApp F A ∘ (ccrToFunctorMap (densitySnd F)).app A := by
  funext ⟨m, g⟩
  -- Goal: densityToFunctorApp F A ((ccrToFunctorMap fst) ⟨m, g⟩) =
  --       densityToFunctorApp F A ((ccrToFunctorMap snd) ⟨m, g⟩)
  -- LHS evaluates to F.map (𝟙 ≫ g) m.tgt.snd = F.map g m.tgt.snd
  -- RHS evaluates to F.map (m.hom.val ≫ g) m.src.snd
  change F.map (𝟙 m.tgt.fst ≫ g) m.tgt.snd = F.map (m.hom.val ≫ g) m.src.snd
  rw [Category.id_comp, F.map_comp]
  simp only [types_comp_apply]
  rw [CategoryOfElements.map_snd m.hom]

set_option backward.isDefEq.respectTransparency false in
/--
The forward natural transformation from the coequalizer to F.
-/
def densityToFunctorNatTrans :
    (densityPresentation F).toCopresheaf ⟶ F :=
  CoequalizerData.desc
    (ccrToFunctorMap (densityPresentation F).fst)
    (ccrToFunctorMap (densityPresentation F).snd)
    { app := densityToFunctorApp F
      naturality := fun {A B} f => by
        ext ⟨p, g⟩
        simp only [types_comp_apply]
        dsimp only [densityToFunctorApp, ccrToFunctor, ccrEvalMap]
        rw [F.map_comp, types_comp_apply] }
    (by
      ext A ⟨m, g⟩
      exact congrFun (densityToFunctorApp_coequalizes F A) ⟨m, g⟩)

/-! ### The Inverse Map

The map from F to the coequalizer: given y : F.obj A, we use the canonical
element (A, y) : F.Elements with identity morphism 𝟙 A.
-/

/--
The underlying map from F to the target polynomial evaluation.
Maps y : F.obj A to ((A, y), 𝟙 A).
-/
def functorToDensityApp (A : D) :
    F.obj A → ccrEval (densityTgt F) A :=
  fun y => ⟨⟨A, y⟩, 𝟙 A⟩

set_option backward.isDefEq.respectTransparency false in
/--
The inverse natural transformation from F to the coequalizer.
-/
def functorToDensityNatTrans :
    F ⟶ (densityPresentation F).toCopresheaf where
  app := fun A => (densityPresentation F).toCopresheafπ.app A ∘
    functorToDensityApp F A
  naturality := fun {A B} f => by
        ext y
        simp only [types_comp_apply, Function.comp_apply]
        unfold functorToDensityApp
        have hnat := congrFun ((densityPresentation F).toCopresheafπ.naturality f)
            ⟨⟨A, y⟩, 𝟙 A⟩
        simp only [types_comp_apply, ccrToFunctor, ccrEvalMap] at hnat
        rw [← hnat]
        let mIdx : DensityMorphismIndex F := ⟨⟨B, F.map f y⟩, ⟨A, y⟩, ⟨f, rfl⟩⟩
        let x : ccrEval (densitySrc F) B := ⟨mIdx, 𝟙 B⟩
        have hcond := congrFun (congrArg (·.app B)
          (densityPresentation F).toCopresheaf_condition.symm) x
        simp only [NatTrans.comp_app, types_comp_apply, ccrToFunctorMap_app,
          ccrToFunctorMapApp, ccrEvalIndex, ccrEvalMor,
          densityPresentation_fst, densityPresentation_snd,
          densityFst_reindex, densityFst_fiberMor, densitySnd_reindex,
          densitySnd_fiberMor, DensityMorphismIndex.tgt, DensityMorphismIndex.src,
          DensityMorphismIndex.hom, x, mIdx] at hcond
        convert hcond.symm using 2
        · simp [ccrEvalMk, Category.id_comp]
        · refine Sigma.ext rfl ?_
          simp only [heq_eq_eq, ccrEvalMk]
          calc 𝟙 A ≫ f = f := Category.id_comp f
            _ = f ≫ 𝟙 B := (Category.comp_id f).symm

/-! ### The Isomorphism -/

/--
Round-trip: densityToFunctor ∘ functorToDensity = id.
-/
theorem densityToFunctor_functorToDensity (A : D) (y : F.obj A) :
    densityToFunctorApp F A (functorToDensityApp F A y) = y := by
  simp only [densityToFunctorApp, functorToDensityApp]
  exact congrFun (F.map_id A) y

set_option backward.isDefEq.respectTransparency false in
/--
Round-trip: functorToDensity ∘ densityToFunctor = id (up to quotient).
-/
theorem functorToDensity_densityToFunctor (A : D)
    (x : ccrEval (densityTgt F) A) :
    (densityPresentation F).toCopresheafπ.app A (functorToDensityApp F A
      (densityToFunctorApp F A x)) =
    (densityPresentation F).toCopresheafπ.app A x := by
  obtain ⟨p, g⟩ := x
  simp only [densityToFunctorApp, functorToDensityApp]
  -- Goal: π(⟨⟨A, F.map g p.snd⟩, 𝟙 A⟩) = π(⟨p, g⟩)
  -- where p = (d, y) for some d : D and y : F.obj d
  -- Use the morphism g : d ⟶ A which gives an Elements morphism
  -- (d, y) ⟶ (A, F.map g y) via ⟨g, rfl⟩
  let pElem : F.Elements := p
  let elemMor : pElem ⟶ ⟨A, F.map g p.snd⟩ := ⟨g, rfl⟩
  let mIdx : DensityMorphismIndex F := ⟨⟨A, F.map g p.snd⟩, pElem, elemMor⟩
  have heq1 : (ccrToFunctorMap (densityFst F)).app A ⟨mIdx, 𝟙 A⟩ =
      ⟨⟨A, F.map g p.snd⟩, 𝟙 A⟩ := by
    simp only [ccrToFunctorMap_app, ccrToFunctorMapApp, mIdx,
      DensityMorphismIndex.tgt, densityFst_reindex, densityFst_fiberMor,
      ccrEvalIndex, ccrEvalMor, ccrEvalMk]
    refine Sigma.ext rfl ?_
    simp only [heq_eq_eq]
    exact Category.id_comp _
  have heq2 : (ccrToFunctorMap (densitySnd F)).app A ⟨mIdx, 𝟙 A⟩ =
      ⟨p, g ≫ 𝟙 A⟩ := by
    simp only [ccrToFunctorMap_app, ccrToFunctorMapApp]
    simp only [mIdx, DensityMorphismIndex.src, DensityMorphismIndex.hom,
      densitySnd_reindex, densitySnd_fiberMor, ccrEvalIndex, ccrEvalMor,
      ccrEvalMk, pElem, elemMor]
  have hcond := congrFun
    (congrArg (·.app A) (densityPresentation F).toCopresheaf_condition.symm)
    (⟨mIdx, 𝟙 A⟩ : ccrEval (densitySrc F) A)
  simp only [NatTrans.comp_app, types_comp_apply,
    PolyPresentation.toCopresheafπ, densityPresentation_fst,
    densityPresentation_snd] at hcond
  rw [heq1, heq2, Category.comp_id] at hcond
  exact hcond.symm

set_option backward.isDefEq.respectTransparency false in
/--
The density isomorphism: the coequalizer of the density presentation
is naturally isomorphic to F.
-/
def densityIso : (densityPresentation F).toCopresheaf ≅ F :=
  NatIso.ofComponents
    (fun A => {
      hom := CoequalizerData.desc _ _ (densityToFunctorApp F A)
        (densityToFunctorApp_coequalizes F A)
      inv := (densityPresentation F).toCopresheafπ.app A ∘
        functorToDensityApp F A
      hom_inv_id := by
        ext x
        revert x
        apply Quot.ind
        intro ⟨p, g⟩
        simp only [types_comp_apply, types_id_apply, Function.comp_apply,
          PolyPresentation.toCopresheaf, CoequalizerData.coeq, functorCoeq,
          CoequalizerData.desc, typeCoeqDesc,
          CoequalizerData.π, typeCoeqπ]
        -- Goal: π(functorToDensityApp(densityToFunctorApp(p, g))) = π(p, g)
        exact functorToDensity_densityToFunctor F A ⟨p, g⟩
      inv_hom_id := by
        ext y
        simp only [types_comp_apply, types_id_apply]
        exact densityToFunctor_functorToDensity F A y })
    (fun {A B} f => by
      ext x
      revert x
      apply Quot.ind
      intro ⟨p, g⟩
      simp only [types_comp_apply,
        PolyPresentation.toCopresheaf, CoequalizerData.coeq,
        functorCoeq, CoequalizerData.desc,
        CoequalizerData.π, typeCoeqπ, typeCoeqDesc,
        densityToFunctorApp, ccrToFunctor, ccrEvalMap]
      rw [F.map_comp]
      rfl)

end DensityIsomorphism

/-! ## Density Presentation Functor

The density presentation construction is functorial: a natural transformation
α : F ⟶ G induces a morphism densityPresentation F → densityPresentation G
in PolyPresentationLoc.
-/

section DensityFunctor

variable {F G : D ⥤ Type (max u w v)}

/-! ### Induced Map on Elements

A natural transformation α : F ⟶ G induces a functor F.Elements → G.Elements
via (d, x) ↦ (d, α.app d x).
-/

/--
Map on element objects induced by a natural transformation.
-/
def densityElementsObj (α : F ⟶ G) (p : F.Elements) : G.Elements :=
  ⟨p.fst, α.app p.fst p.snd⟩

/--
Map on element morphisms induced by a natural transformation.
Given f : (d, x) → (e, y) in F.Elements, we get a morphism
(d, α x) → (e, α y) in G.Elements using naturality.
-/
def densityElementsHom (α : F ⟶ G) {p q : F.Elements} (f : p ⟶ q) :
    densityElementsObj α p ⟶ densityElementsObj α q :=
  ⟨f.val, by
    simp only [densityElementsObj]
    have nat := congrFun (α.naturality f.val).symm p.snd
    simp only [types_comp_apply] at nat
    rw [nat, CategoryOfElements.map_snd f]⟩

@[simp]
theorem densityElementsHom_val (α : F ⟶ G) {p q : F.Elements} (f : p ⟶ q) :
    (densityElementsHom α f).val = f.val := rfl

/--
Map on morphism indices induced by a natural transformation.
-/
def densityMorphismIndexMap (α : F ⟶ G)
    (m : DensityMorphismIndex F) : DensityMorphismIndex G :=
  ⟨densityElementsObj α m.tgt,
   densityElementsObj α m.src,
   densityElementsHom α m.hom⟩

/-! ### Induced Morphism on Target Polynomial -/

/--
The morphism on target polynomials induced by α.
Maps (d, x) to (d, α x) with identity fibers.
-/
def densityTgtMap (α : F ⟶ G) : densityTgt F ⟶ densityTgt G :=
  ccrHomMk
    (densityElementsObj α)
    (fun _ => 𝟙 _)

@[simp]
theorem densityTgtMap_reindex (α : F ⟶ G) (p : F.Elements) :
    ccrReindex (densityTgtMap α) p = densityElementsObj α p := rfl

@[simp]
theorem densityTgtMap_fiberMor (α : F ⟶ G) (p : F.Elements) :
    ccrFiberMor (densityTgtMap α) p = 𝟙 p.fst := rfl

/-! ### Induced Morphism on Source Polynomial -/

/--
The morphism on source polynomials induced by α.
Maps morphism index m to the corresponding index in G with identity fibers.
-/
def densitySrcMap (α : F ⟶ G) : densitySrc F ⟶ densitySrc G :=
  ccrHomMk
    (densityMorphismIndexMap α)
    (fun _ => 𝟙 _)

@[simp]
theorem densitySrcMap_reindex (α : F ⟶ G) (m : DensityMorphismIndex F) :
    ccrReindex (densitySrcMap α) m = densityMorphismIndexMap α m := rfl

@[simp]
theorem densitySrcMap_fiberMor (α : F ⟶ G) (m : DensityMorphismIndex F) :
    ccrFiberMor (densitySrcMap α) m = 𝟙 m.tgt.fst := rfl

/-! ### Compatibility with Parallel Morphisms -/

/--
The induced maps commute with the first parallel morphism.
-/
theorem densityMap_fst_comm (α : F ⟶ G) :
    densitySrcMap α ≫ densityFst G = densityFst F ≫ densityTgtMap α := rfl

set_option backward.isDefEq.respectTransparency false in
/--
The induced maps commute with the second parallel morphism.
-/
theorem densityMap_snd_comm (α : F ⟶ G) :
    densitySrcMap α ≫ densitySnd G = densitySnd F ≫ densityTgtMap α := by
  refine ccrHom_ext _ _ ?hbase ?hfiber
  case hbase => rfl
  case hfiber =>
    simp only [eqToHom_refl, Category.comp_id]
    funext m
    change (GrothendieckContra'.comp (densitySrcMap α) (densitySnd G)).fiber m =
           (GrothendieckContra'.comp (densitySnd F) (densityTgtMap α)).fiber m
    unfold GrothendieckContra'.comp
    simp only [densitySrcMap, densitySnd, densityTgtMap, ccrHomMk,
      densityMorphismIndexMap, eqToHom_refl, Category.comp_id]
    rw [piOp'_comp_at_idx, piOp'_comp_at_idx]
    dsimp only [Functor.comp_map, familyFunctor', familyMap', Cat.opFunctor',
      Functor.op', functorOp'Obj, ccrFamily, DensityMorphismIndex.hom,
      densityMorphismIndexMap, densityTgt, densitySrc, densityElementsObj,
      DensityMorphismIndex.src, ccrObjMk, DensityMorphismIndex.tgt]
    unfold Cat.Hom.toFunctor
    unfold Functor.toCatHom
    simp only [densityElementsHom_val, Category.comp_id]
    exact (Category.id_comp _).symm

/-! ### The Induced Morphism of Presentations -/

/--
The morphism of polynomial presentations induced by α : F ⟶ G.
-/
def densityPresentationMap (α : F ⟶ G) :
    densityPresentation F ⟶ densityPresentation G :=
  { srcHom := densitySrcMap α
    tgtHom := densityTgtMap α
    fst_comm := densityMap_fst_comm α
    snd_comm := densityMap_snd_comm α }

@[simp]
theorem densityPresentationMap_srcHom (α : F ⟶ G) :
    (densityPresentationMap α).srcHom = densitySrcMap α := rfl

@[simp]
theorem densityPresentationMap_tgtHom (α : F ⟶ G) :
    (densityPresentationMap α).tgtHom = densityTgtMap α := rfl

/-! ### Functor Laws -/

variable (F)

set_option backward.isDefEq.respectTransparency false in
/--
The identity natural transformation induces the identity morphism.
-/
theorem densityPresentationMap_id :
    densityPresentationMap (𝟙 F) = 𝟙 (densityPresentation F) := by
  apply PolyPresentation.Hom.ext
  · refine ccrHom_ext _ _ ?_ ?_
    · ext m
      simp only [densityPresentationMap_srcHom, PolyPresentation.id_srcHom']
      rfl
    · funext m
      simp only [densityPresentationMap_srcHom, PolyPresentation.id_srcHom',
        eqToHom_refl, Category.comp_id]
      rfl
  · refine ccrHom_ext _ _ ?_ ?_
    · ext p
      simp only [densityPresentationMap_tgtHom, PolyPresentation.id_tgtHom']
      rfl
    · funext p
      simp only [densityPresentationMap_tgtHom, PolyPresentation.id_tgtHom',
        eqToHom_refl, Category.comp_id]
      rfl

variable {F}

set_option backward.isDefEq.respectTransparency false in
/--
Composition of natural transformations induces composition of morphisms.
-/
theorem densityPresentationMap_comp {H : D ⥤ Type (max u w v)} (α : F ⟶ G) (β : G ⟶ H) :
    densityPresentationMap (α ≫ β) =
    densityPresentationMap α ≫ densityPresentationMap β := by
  apply PolyPresentation.Hom.ext
  · refine ccrHom_ext _ _ ?_ ?_
    · ext m
      simp only [densityPresentationMap_srcHom, PolyPresentation.comp_srcHom']
      rfl
    · funext m
      simp only [densityPresentationMap_srcHom, PolyPresentation.comp_srcHom',
        eqToHom_refl, Category.comp_id]
      change (densitySrcMap (α ≫ β)).fiber m =
             (GrothendieckContra'.comp (densitySrcMap α) (densitySrcMap β)).fiber m
      unfold GrothendieckContra'.comp
      simp only [densitySrcMap, ccrHomMk, eqToHom_refl, Category.comp_id]
      rw [piOp'_comp_at_idx]
      dsimp only [Functor.comp_map, familyFunctor', familyMap', Cat.opFunctor',
        Functor.op', functorOp'Obj, ccrFamily, densityMorphismIndexMap,
        densitySrc, ccrObjMk, DensityMorphismIndex.src, DensityMorphismIndex.tgt,
        densityElementsObj]
      exact (Category.id_comp _).symm
  · refine ccrHom_ext _ _ ?_ ?_
    · ext p
      simp only [densityPresentationMap_tgtHom, PolyPresentation.comp_tgtHom']
      rfl
    · funext p
      simp only [densityPresentationMap_tgtHom, PolyPresentation.comp_tgtHom',
        eqToHom_refl, Category.comp_id]
      change (densityTgtMap (α ≫ β)).fiber p =
             (GrothendieckContra'.comp (densityTgtMap α) (densityTgtMap β)).fiber p
      unfold GrothendieckContra'.comp
      simp only [densityTgtMap, ccrHomMk, eqToHom_refl, Category.comp_id]
      rw [piOp'_comp_at_idx]
      dsimp only [Functor.comp_map, familyFunctor', familyMap', Cat.opFunctor',
        Functor.op', functorOp'Obj, ccrFamily, densityElementsObj,
        densityTgt, ccrObjMk]
      exact (Category.id_comp _).symm

end DensityFunctor

/-! ## The Density Functor to Localized Category

We now construct the functor from copresheaves to the localized category
of polynomial presentations.
-/

section DensityPresentationFunctor

variable (D)

/--
The density presentation functor maps copresheaves to their canonical
polynomial presentations in the localized category.

For a copresheaf F, we get densityPresentation F whose coequalizer is
isomorphic to F via the density isomorphism.
-/
def densityPresentationFunctor :
    (D ⥤ Type (max u w v)) ⥤ PolyPresentationLoc.{u, v, max u w v} D where
  obj F := PolyPresentationLoc.ofPres (densityPresentation F)
  map {F G} α :=
    let m : PolyPresentation.Hom (densityPresentation F) (densityPresentation G) :=
      densityPresentationMap α
    PolyPresentationLoc.Hom.mk' m.toQHom
  map_id F := by
    apply Quot.sound
    unfold PolyPresentationQ.Hom.equiv
    simp only [densityPresentationMap_id]
    rfl
  map_comp α β := by
    apply Quot.sound
    unfold PolyPresentationQ.Hom.equiv
    simp only [densityPresentationMap_comp]
    rfl

end DensityPresentationFunctor

/-! ## The Equivalence

We now construct the equivalence between the localized category of polynomial
presentations and the category of copresheaves.

The strategy:
1. Define comparison morphism `X → densityPresentation(X.toCopresheaf)`
2. Show the induced map on coequalizers is the inverse of `densityIso`
3. Use faithfulness of evaluation to deduce it's an isomorphism
4. Assemble unit and counit into an equivalence
-/

section Equivalence

variable {D : Type u} [Category.{v} D]

/-! ### Comparison Morphism

For any presentation X, we construct a morphism to its density presentation.
Each index i of X.tgt maps to an element of (X.toCopresheaf).Elements via the
coequalizer projection.
-/

variable (X : PolyPresentation.{u, v, max u w v} D)

/--
Map an index of X.tgt to an element of (X.toCopresheaf).Elements.
We use the canonical element ⟨i, 𝟙⟩ and project to the coequalizer.
-/
def comparisonTgtReindex (i : ccrIndex X.tgt) :
    (X.toCopresheaf).Elements :=
  ⟨ccrFamily X.tgt i, X.toCopresheafπ.app _ ⟨i, 𝟙 _⟩⟩

/--
The morphism on target polynomials for the comparison.
Maps each index i to the element (ccrFamily i, π⟨i, 𝟙⟩).
-/
def comparisonTgtHom : X.tgt ⟶ densityTgt X.toCopresheaf :=
  ccrHomMk
    (comparisonTgtReindex X)
    (fun _ => 𝟙 _)

@[simp]
theorem comparisonTgtHom_reindex (i : ccrIndex X.tgt) :
    ccrReindex (comparisonTgtHom X) i = comparisonTgtReindex X i := rfl

@[simp]
theorem comparisonTgtHom_fiberMor (i : ccrIndex X.tgt) :
    ccrFiberMor (comparisonTgtHom X) i = 𝟙 _ := rfl

/--
Helper: elements with equal images under densityToFunctorApp are equal
in the density coequalizer.
-/
theorem densityCoeq_eq_of_toFunctor_eq (F : D ⥤ Type (max u w v)) (A : D)
    (x y : ccrEval (densityTgt F) A)
    (h : densityToFunctorApp F A x = densityToFunctorApp F A y) :
    (densityPresentation F).toCopresheafπ.app A x =
    (densityPresentation F).toCopresheafπ.app A y := by
  -- densityIso.hom ∘ π = densityToFunctorApp (by definition via desc)
  -- Since densityIso.hom is an isomorphism, it's injective
  -- So h implies π(x) = π(y)
  have hinj : Function.Injective ((densityIso F).hom.app A) := by
    intro a b hab
    have h1 : (densityIso F).inv.app A ((densityIso F).hom.app A a) = a := by
      have := congrFun (congrArg NatTrans.app (densityIso F).hom_inv_id) A
      simp only [NatTrans.comp_app, NatTrans.id_app] at this
      exact congrFun this a
    have h2 : (densityIso F).inv.app A ((densityIso F).hom.app A b) = b := by
      have := congrFun (congrArg NatTrans.app (densityIso F).hom_inv_id) A
      simp only [NatTrans.comp_app, NatTrans.id_app] at this
      exact congrFun this b
    rw [← h1, ← h2, hab]
  apply hinj
  simp only [densityIso, NatIso.ofComponents_hom_app]
  -- The hom is defined via CoequalizerData.desc, which satisfies
  -- desc ∘ π = the original map (densityToFunctorApp)
  -- Unfold toCopresheafπ to get the component-level π
  -- functorCoequalizerData.π unfolds to functorCoeqπ which applies
  -- the Type-level π at each component
  simp only [PolyPresentation.toCopresheafπ]
  have hfac := CoequalizerData.fac
    ((ccrToFunctorMap (densityPresentation F).fst).app A)
    ((ccrToFunctorMap (densityPresentation F).snd).app A)
    (densityToFunctorApp F A)
    (densityToFunctorApp_coequalizes F A)
  have h1 := congrFun hfac x
  have h2 := congrFun hfac y
  simp only [types_comp_apply] at h1 h2
  have h1' : ∀ z, (CoequalizerData.π
    (ccrToFunctorMap (densityPresentation F).fst)
    (ccrToFunctorMap (densityPresentation F).snd)
    ).app A z =
    CoequalizerData.π
    ((ccrToFunctorMap (densityPresentation F).fst).app A)
    ((ccrToFunctorMap (densityPresentation F).snd).app A)
    z := fun _ => rfl
  rw [h1' x, h1' y, h1, h2]
  exact h

set_option backward.isDefEq.respectTransparency false in
/--
The comparison morphism respects the coequalizer structure.
-/
theorem comparisonTgtHom_respects :
    ccrToFunctorMap X.fst ≫ ccrToFunctorMap (comparisonTgtHom X) ≫
      (densityPresentation X.toCopresheaf).toCopresheafπ =
    ccrToFunctorMap X.snd ≫ ccrToFunctorMap (comparisonTgtHom X) ≫
      (densityPresentation X.toCopresheaf).toCopresheafπ := by
  ext A ⟨j, g⟩
  simp only [NatTrans.comp_app, types_comp_apply, ccrToFunctorMap_app,
    ccrToFunctorMapApp, ccrEvalMk, comparisonTgtHom_reindex,
    comparisonTgtHom_fiberMor, Category.id_comp, comparisonTgtReindex]
  -- Apply the helper: show images under densityToFunctorApp are equal
  apply densityCoeq_eq_of_toFunctor_eq
  -- Now show densityToFunctorApp gives equal results
  simp only [densityToFunctorApp, ccrEvalMor, ccrEvalIndex]
  -- LHS: F.map (ccrFiberMor X.fst j ≫ g) (π⟨ccrReindex X.fst j, 𝟙⟩)
  -- RHS: F.map (ccrFiberMor X.snd j ≫ g) (π⟨ccrReindex X.snd j, 𝟙⟩)
  -- By naturality of π and the coequalizer condition for X
  rw [X.toCopresheaf.map_comp, X.toCopresheaf.map_comp]
  simp only [types_comp_apply]
  -- The inner maps are π composed with the polynomial maps
  have hπ_nat_fst : X.toCopresheaf.map (ccrFiberMor X.fst j)
      (X.toCopresheafπ.app _ ⟨ccrReindex X.fst j, 𝟙 _⟩) =
      X.toCopresheafπ.app _ ⟨ccrReindex X.fst j, ccrFiberMor X.fst j⟩ := by
    have := congrFun (X.toCopresheafπ.naturality (ccrFiberMor X.fst j))
      ⟨ccrReindex X.fst j, 𝟙 _⟩
    simp only [ccrToFunctor, ccrEvalMap, Category.id_comp,
      types_comp_apply] at this
    exact this.symm
  have hπ_nat_snd : X.toCopresheaf.map (ccrFiberMor X.snd j)
      (X.toCopresheafπ.app _ ⟨ccrReindex X.snd j, 𝟙 _⟩) =
      X.toCopresheafπ.app _ ⟨ccrReindex X.snd j, ccrFiberMor X.snd j⟩ := by
    have := congrFun (X.toCopresheafπ.naturality (ccrFiberMor X.snd j))
      ⟨ccrReindex X.snd j, 𝟙 _⟩
    simp only [ccrToFunctor, ccrEvalMap, Category.id_comp,
      types_comp_apply] at this
    exact this.symm
  rw [hπ_nat_fst, hπ_nat_snd]
  -- Now use naturality again with g
  have hπ_nat_fst' := congrFun (X.toCopresheafπ.naturality g)
      ⟨ccrReindex X.fst j, ccrFiberMor X.fst j⟩
  have hπ_nat_snd' := congrFun (X.toCopresheafπ.naturality g)
      ⟨ccrReindex X.snd j, ccrFiberMor X.snd j⟩
  simp only [ccrToFunctor, ccrEvalMap, types_comp_apply] at hπ_nat_fst' hπ_nat_snd'
  rw [← hπ_nat_fst', ← hπ_nat_snd']
  -- Now the goal is: π⟨fstIdx, fstFiber ≫ g⟩ = π⟨sndIdx, sndFiber ≫ g⟩
  -- This is exactly X.toCopresheaf_condition at ⟨j, g⟩
  have hXcomp := congrFun (congrArg NatTrans.app X.toCopresheaf_condition) A
  have hX := congrFun hXcomp (⟨j, g⟩ : ccrEval X.src A)
  simp only [NatTrans.comp_app, types_comp_apply, ccrToFunctorMap_app,
    ccrToFunctorMapApp] at hX
  exact hX

/--
The comparison morphism from X to its density presentation as a
PolyPresentationQ morphism.
-/
def comparisonMorphismQ :
    PolyPresentationQ.Hom X.toQ (densityPresentation X.toCopresheaf).toQ where
  tgtHom := comparisonTgtHom X
  respects := comparisonTgtHom_respects X

set_option backward.isDefEq.respectTransparency false in
/--
The induced map on coequalizers from the comparison morphism is the
inverse of the density isomorphism.
-/
theorem comparisonMorphismQ_toInducedMap :
    (comparisonMorphismQ X).toInducedMap = (densityIso X.toCopresheaf).inv := by
  symm
  apply CoequalizerData.uniq
  -- Goal: X.toCopresheafπ ≫ densityIso.inv =
  --       ccrToFunctorMap tgtHom ≫ density.toCopresheafπ
  ext A ⟨i, g⟩
  simp only [NatTrans.comp_app, types_comp_apply, densityIso,
    NatIso.ofComponents_inv_app, Function.comp_apply,
    ccrToFunctorMap_app, ccrToFunctorMapApp, comparisonMorphismQ,
    comparisonTgtHom_reindex, comparisonTgtHom_fiberMor,
    comparisonTgtReindex, functorToDensityApp]
  apply densityCoeq_eq_of_toFunctor_eq
  simp only [densityToFunctorApp, ccrEvalMk, ccrEvalIndex, ccrEvalMor, densityTgt_family]
  rw [X.toCopresheaf.map_id]
  simp only [types_id_apply]
  have hnat := congrFun (X.toCopresheafπ.naturality g) ⟨i, 𝟙 _⟩
  simp only [types_comp_apply, ccrToFunctor, ccrEvalMap, Category.id_comp] at hnat
  rw [show 𝟙 (ccrFamily X.tgt i) ≫ g = g from Category.id_comp g]
  exact hnat

/--
The comparison morphism in the localized category.
-/
def comparisonMorphism :
    (PolyPresentationLoc.ofPres X) ⟶
    (PolyPresentationLoc.ofPres (densityPresentation X.toCopresheaf)) :=
  PolyPresentationLoc.Hom.mk' (comparisonMorphismQ X)

/--
The comparison morphism induces an isomorphism on coequalizers.
-/
theorem comparisonMorphism_isIso :
    IsIso (polyPresentationLocEvalFunctor.map (comparisonMorphism X)) := by
  change IsIso (PolyPresentationLoc.Hom.toInducedMap' (comparisonMorphism X))
  change IsIso (PolyPresentationLoc.Hom.toInducedMap'
    (PolyPresentationLoc.Hom.mk' (comparisonMorphismQ X)))
  change IsIso ((comparisonMorphismQ X).toInducedMap)
  rw [comparisonMorphismQ_toInducedMap]
  infer_instance

/-! ### Naturality of the Comparison

The comparison morphism is natural in X.
-/

variable {X}

set_option backward.isDefEq.respectTransparency false in
/--
The comparison morphism is natural: for f : X → Y, the square commutes.
-/
theorem comparisonMorphism_naturality {Y : PolyPresentation.{u, v, max u w v} D}
    (f : X ⟶ Y) :
    let fQ : PolyPresentationQ.Hom X.toQ Y.toQ :=
      ⟨f.tgtHom, PolyPresentation.Hom.respectsCoequalization f⟩
    comparisonMorphism X ≫
      PolyPresentationLoc.Hom.mk' (PolyPresentation.Hom.toQHom
        (densityPresentationMap
          (polyPresentationLocEvalFunctor.map
            (PolyPresentationLoc.Hom.mk' fQ)))) =
    PolyPresentationLoc.Hom.mk' fQ ≫ comparisonMorphism Y := by
  apply Quot.sound
  unfold PolyPresentationQ.Hom.equiv
  simp only [comparisonMorphismQ, PolyPresentationQ.Hom.comp,
    PolyPresentationQ.Hom.toInducedMap]
  congr 1
  simp only [ccrToFunctorMap_comp, Category.assoc]
  -- Goal: show both paths from ccrToFunctor X.tgt to density coequalizer are equal
  ext A ⟨i, g⟩
  simp only [NatTrans.comp_app, types_comp_apply, ccrToFunctorMap_app, ccrToFunctorMapApp]
  -- Reduce to showing densityToFunctorApp gives same result on both elements
  apply densityCoeq_eq_of_toFunctor_eq
  simp only [densityToFunctorApp, ccrEvalMk, ccrEvalIndex, ccrEvalMor]
  -- LHS: Y.toCopresheaf.map g (induced.app _ (π⟨i, 𝟙⟩))
  -- RHS: Y.toCopresheaf.map (ccrFiberMor f.tgtHom i ≫ g) (π⟨ccrReindex f.tgtHom i, 𝟙⟩)
  -- Use the factorization property of the induced map
  let induced := (PolyPresentationLoc.Hom.mk'
      (⟨f.tgtHom, PolyPresentation.Hom.respectsCoequalization f⟩ :
       PolyPresentationQ.Hom X.toQ Y.toQ)).toInducedMap'
  have hfac : X.toCopresheafπ ≫ induced = ccrToFunctorMap f.tgtHom ≫ Y.toCopresheafπ := by
    apply PolyPresentationQ.Hom.toInducedMap_fac
  -- Extract component at ccrFamily i
  have hfac_pt : induced.app (ccrFamily X.tgt i)
      (X.toCopresheafπ.app (ccrFamily X.tgt i) ⟨i, 𝟙 _⟩) =
      Y.toCopresheafπ.app (ccrFamily X.tgt i)
        ⟨ccrReindex f.tgtHom i, ccrFiberMor f.tgtHom i⟩ := by
    have := congrFun (congrArg NatTrans.app hfac) (ccrFamily X.tgt i)
    have h2 := congrFun this ⟨i, 𝟙 _⟩
    simp only [NatTrans.comp_app, types_comp_apply, ccrToFunctorMap_app,
      ccrToFunctorMapApp, ccrEvalMk, ccrEvalIndex, ccrEvalMor] at h2
    rw [Category.comp_id] at h2
    exact h2
  -- The goal involves polyPresentationLocEvalFunctor which evaluates to toCopresheaf
  -- Simplify functor application
  simp only [polyPresentationLocEvalFunctor, PolyPresentationLoc.ofPres] at *
  change Y.toCopresheaf.map (𝟙 _ ≫ 𝟙 _ ≫ g)
      (induced.app (ccrFamily X.tgt i)
        (X.toCopresheafπ.app (ccrFamily X.tgt i) ⟨i, 𝟙 _⟩)) =
    Y.toCopresheaf.map (𝟙 _ ≫ ccrFiberMor f.tgtHom i ≫ g)
      (Y.toCopresheafπ.app (ccrFamily Y.tgt (ccrReindex f.tgtHom i))
        ⟨ccrReindex f.tgtHom i, 𝟙 _⟩)
  -- Simplify identity compositions
  simp only [Category.id_comp]
  -- Apply factorization: induced.app _ (π⟨i, 𝟙⟩) = π⟨ccrReindex f.tgtHom i, ccrFiberMor f.tgtHom i⟩
  rw [hfac_pt]
  -- Use naturality of Y.toCopresheafπ to rewrite both sides
  -- Naturality: F.map(g)(π(source)(⟨j, fiber⟩)) = π(A)(⟨j, fiber ≫ g⟩)
  -- For LHS: F.map(g)(π(⟨j, fiber⟩)) → π(A)(⟨j, fiber ≫ g⟩)
  have hπnat_lhs := congrFun (Y.toCopresheafπ.naturality g)
      ⟨ccrReindex f.tgtHom i, ccrFiberMor f.tgtHom i⟩
  simp only [ccrToFunctor, ccrEvalMap, types_comp_apply] at hπnat_lhs
  -- For RHS: F.map(fiber ≫ g)(π(⟨j, 𝟙⟩)) → π(A)(⟨j, 𝟙 ≫ fiber ≫ g⟩) = π(A)(⟨j, fiber ≫ g⟩)
  have hπnat_rhs := congrFun (Y.toCopresheafπ.naturality (ccrFiberMor f.tgtHom i ≫ g))
      ⟨ccrReindex f.tgtHom i, 𝟙 _⟩
  simp only [ccrToFunctor, ccrEvalMap, types_comp_apply, Category.id_comp] at hπnat_rhs
  -- Both sides equal Y.toCopresheafπ.app A ⟨ccrReindex ..., ccrFiberMor ... ≫ g⟩
  -- Use transitivity through the common term
  trans Y.toCopresheafπ.app A ⟨ccrReindex f.tgtHom i, ccrFiberMor f.tgtHom i ≫ g⟩
  · exact hπnat_lhs.symm
  · exact hπnat_rhs

/-! ### Counit Naturality

The density isomorphism is natural with respect to natural transformations,
making it the counit of the adjunction.
-/

set_option backward.isDefEq.respectTransparency false in
/--
The counit of the adjunction: E ∘ S → Id.
This is just the density isomorphism assembled into a natural isomorphism.
-/
def counitIso :
    polyPresentationLocEvalFunctor.{u, v, max u w v} (D := D) ⋙
    densityPresentationFunctor.{u, v, w} D ⋙
    polyPresentationLocEvalFunctor.{u, v, max u w v} ≅
    polyPresentationLocEvalFunctor.{u, v, max u w v} := by
  refine NatIso.ofComponents (fun X => ?_) (fun f => ?_)
  · -- Component at X: (densityPresentation X.toCopresheaf).toCopresheaf ≅ X.toCopresheaf
    exact densityIso X.toPres.toCopresheaf
  · -- Naturality
    ext A x
    simp only [Functor.comp_obj, Functor.comp_map,
      NatTrans.comp_app, types_comp_apply]
    simp only [densityPresentationFunctor, polyPresentationLocEvalFunctor,
      densityIso, NatIso.ofComponents_hom_app]
    induction f using Quot.ind with
    | _ f' =>
      revert x
      apply Quot.ind
      intro x'
      -- Naturality: densityIso.hom ≫ induced = densityPresentationMap induced ≫ densityIso.hom
      -- x' = ⟨(B, y), f⟩ where y : X.toCopresheaf.obj B and f : B → A
      -- LHS: density(Y).hom (π(B, induced y), f) = Y.map f (induced y)
      -- RHS: induced (density(X).hom (π(B, y), f)) = induced (X.map f y) = Y.map f (induced y)
      -- Both equal by naturality of induced
      obtain ⟨⟨B, y⟩, g⟩ := x'
      -- First decompose y as Quot.mk to allow reduction
      induction y using Quot.ind with
      | mk y' =>
        -- The goal is: densityIso(Y).hom ∘ (densityPresentationMap f'.toInducedMap).toInducedMap
        --            = f'.toInducedMap ∘ densityIso(X).hom
        -- Both sides reduce to: G.map g (α.app B y') = α.app A (F.map g y')
        -- which is naturality of α = f'.toInducedMap
        -- Reduce functorCoeqDesc and CoequalizerData.desc using dsimp
        dsimp only [functorCoeqDesc, CoequalizerData.desc, CoequalizerData.π, typeCoeqπ,
          densityPresentationFunctor, polyPresentationLocEvalFunctor,
          PolyPresentationLoc.toPres, PolyPresentationLoc.ofPres]
        -- Reduce typeCoeqDesc ... (Quot.mk ...) on RHS
        simp only [typeCoeqDesc_mk]
        -- Reduce toInducedMap' which is defined via Quot.lift
        unfold PolyPresentationLoc.Hom.toInducedMap' PolyPresentationLoc.Hom.mk'
        -- Reduce PolyPresentationQ.Hom.toInducedMap, PolyPresentation.Hom.toQHom
        dsimp only [PolyPresentation.Hom.toQHom, PolyPresentationQ.Hom.toInducedMap,
          functorCoeqDesc, CoequalizerData.desc, PolyPresentationQ.toPres,
          PolyPresentationLoc.toQ, PolyPresentation.toQ]
        simp only [typeCoeqDesc_mk]
        -- Unfold densityToFunctorApp and densityPresentationMap
        dsimp only [densityToFunctorApp, densityPresentationMap_tgtHom,
          PolyPresentation.toCopresheaf, functorCoeq, CoequalizerData.π, typeCoeqπ,
          PolyPresentation.toCopresheafπ, CoequalizerData.coeq, CoequalizerData.desc,
          ccrToFunctorMap, densityTgtMap, ccrHomMk, ccrReindex, ccrFiberMor,
          densityElementsObj, functorCoeqπ, NatTrans.comp_app, types_comp_apply,
          ccrFamily, densityTgt, CategoryTheory.Functor.Elements]
        simp only [typeCoeqDesc_mk]
        -- Reduce densityToFunctorApp and ccrToFunctorMapApp
        dsimp only [densityToFunctorApp, ccrToFunctorMapApp, densityElementsObj,
          ccrObjMk, CategoryTheory.Functor.Elements]
        simp only [typeCoeqDesc_mk]
        -- Reduce ccrEvalMk, ccrEvalIndex, ccrEvalMor, ccrReindex to simplify the match
        dsimp only [ccrEvalMk, ccrEvalIndex, ccrEvalMor, ccrReindex, ccrFiberMor]
        -- Unfold densityElementsObj: densityElementsObj α ⟨d, x⟩ = ⟨d, α.app d x⟩
        -- And densityTgt_family: ccrFamily (densityTgt F) ⟨d, x⟩ = d
        dsimp only [densityElementsObj, densityTgt_family]
        -- Reduce the inner typeCoeqDesc ... (Quot.mk ... y')
        simp only [typeCoeqDesc_mk]
        -- Reduce (f ≫ Quot.mk) y' to Quot.mk (f y')
        dsimp only [types_comp_apply]
        -- Reduce typeCoeqDesc ... (Quot.mk ... x) on both sides
        simp only [typeCoeqDesc_mk]
        -- Reduce function application (f ≫ g) x = g (f x)
        dsimp only [types_comp_apply]
        -- Both sides are Quot.mk with same relation, reduce to inner equality
        apply congrArg
        -- Reduce 𝟙 B ≫ g to g
        have hg : 𝟙 B ≫ g = g := Category.id_comp g
        rw [hg]
        -- Apply naturality of ccrToFunctorMap f'.tgtHom
        exact congrFun ((ccrToFunctorMap f'.tgtHom).naturality g).symm y'

end Equivalence

/-! ## Setoid-Valued Density Presentation

The constructive alternative to the Type-valued equivalence uses Setoid-valued
copresheaves. This avoids noncomputability by keeping the
pre-quotient structure.

For F : D ⥤ SetoidBundle, the density presentation uses:
- Target indexed by Σ A, (F.obj A).carrier (pre-quotient elements)
- Source indexed by morphisms in the pre-quotient category of elements
- Parallel morphisms as before

The coequalizer of this presentation gives a setoid whose quotient is the
colimit in Type.
-/

section SetoidDensityPresentation

variable {D : Type u} [Category.{v} D]

/-! ### Setoid Element Types

The pre-quotient category of elements has objects (A, x) where x is in the
carrier of F.obj A, and morphisms f : A → B such that (F.map f).toFun x is
setoid-equivalent to y.
-/

/--
Pre-quotient elements of a Setoid-valued functor.
-/
def SetoidElements (F : D ⥤ SetoidBundle.{max u v}) : Type (max u v) :=
  Σ (A : D), (F.obj A).carrier

/--
Extract the object from a setoid element.
-/
def SetoidElements.obj {F : D ⥤ SetoidBundle.{max u v}}
    (p : SetoidElements F) : D :=
  p.fst

/--
Extract the carrier element from a setoid element.
-/
def SetoidElements.elem {F : D ⥤ SetoidBundle.{max u v}}
    (p : SetoidElements F) : (F.obj p.obj).carrier :=
  p.snd

/--
Morphisms between pre-quotient elements: f : A → B such that F.map(f)(x) ≈ y.
-/
structure SetoidElementsHom {F : D ⥤ SetoidBundle.{max u v}}
    (p q : SetoidElements F) where
  hom : p.obj ⟶ q.obj
  compat : (F.obj q.obj).rel.r ((F.map hom).toFun p.elem) q.elem

/--
The morphism index type for the setoid density presentation.
-/
def SetoidMorphismIndex (F : D ⥤ SetoidBundle.{max u v}) : Type (max u v) :=
  Σ (p q : SetoidElements F), SetoidElementsHom q p

/--
Extract the target element from a setoid morphism index.
-/
def SetoidMorphismIndex.tgt {F : D ⥤ SetoidBundle.{max u v}}
    (m : SetoidMorphismIndex F) : SetoidElements F :=
  m.fst

/--
Extract the source element from a setoid morphism index.
-/
def SetoidMorphismIndex.src {F : D ⥤ SetoidBundle.{max u v}}
    (m : SetoidMorphismIndex F) : SetoidElements F :=
  m.snd.fst

/--
Extract the morphism data from a setoid morphism index.
-/
def SetoidMorphismIndex.homData {F : D ⥤ SetoidBundle.{max u v}}
    (m : SetoidMorphismIndex F) : SetoidElementsHom m.src m.tgt :=
  m.snd.snd

/-! ### Setoid Density Target Polynomial -/

/--
The target polynomial of the setoid density presentation.
Indexed by pre-quotient elements, with family mapping (A, x) to A.
-/
def setoidDensityTgt (F : D ⥤ SetoidBundle.{max u v}) :
    CoprodCovarRepCat'.{u, v, max u v} D :=
  ccrObjMk (fun (p : SetoidElements F) => p.obj)

@[simp]
theorem setoidDensityTgt_index (F : D ⥤ SetoidBundle.{max u v}) :
    ccrIndex (setoidDensityTgt F) = SetoidElements F := rfl

@[simp]
theorem setoidDensityTgt_family (F : D ⥤ SetoidBundle.{max u v})
    (p : SetoidElements F) :
    ccrFamily (setoidDensityTgt F) p = p.obj := rfl

/-! ### Setoid Density Source Polynomial -/

/--
The source polynomial of the setoid density presentation.
Indexed by morphisms in the pre-quotient category of elements.
-/
def setoidDensitySrc (F : D ⥤ SetoidBundle.{max u v}) :
    CoprodCovarRepCat'.{u, v, max u v} D :=
  ccrObjMk (fun (m : SetoidMorphismIndex F) => m.tgt.obj)

@[simp]
theorem setoidDensitySrc_index (F : D ⥤ SetoidBundle.{max u v}) :
    ccrIndex (setoidDensitySrc F) = SetoidMorphismIndex F := rfl

@[simp]
theorem setoidDensitySrc_family (F : D ⥤ SetoidBundle.{max u v})
    (m : SetoidMorphismIndex F) :
    ccrFamily (setoidDensitySrc F) m = m.tgt.obj := rfl

/-! ### Setoid Density Parallel Morphisms -/

/--
The first parallel morphism of the setoid density presentation.
Maps morphism index m to the target element with identity fiber.
-/
def setoidDensityFst (F : D ⥤ SetoidBundle.{max u v}) :
    setoidDensitySrc F ⟶ setoidDensityTgt F :=
  ccrHomMk
    (fun m => m.tgt)
    (fun _ => 𝟙 _)

@[simp]
theorem setoidDensityFst_reindex (F : D ⥤ SetoidBundle.{max u v})
    (m : SetoidMorphismIndex F) :
    ccrReindex (setoidDensityFst F) m = m.tgt := rfl

@[simp]
theorem setoidDensityFst_fiberMor (F : D ⥤ SetoidBundle.{max u v})
    (m : SetoidMorphismIndex F) :
    ccrFiberMor (setoidDensityFst F) m = 𝟙 m.tgt.obj := rfl

/--
The second parallel morphism of the setoid density presentation.
Maps morphism index m to the source element with the underlying morphism as fiber.
-/
def setoidDensitySnd (F : D ⥤ SetoidBundle.{max u v}) :
    setoidDensitySrc F ⟶ setoidDensityTgt F :=
  ccrHomMk
    (fun m => m.src)
    (fun m => m.homData.hom)

@[simp]
theorem setoidDensitySnd_reindex (F : D ⥤ SetoidBundle.{max u v})
    (m : SetoidMorphismIndex F) :
    ccrReindex (setoidDensitySnd F) m = m.src := rfl

@[simp]
theorem setoidDensitySnd_fiberMor (F : D ⥤ SetoidBundle.{max u v})
    (m : SetoidMorphismIndex F) :
    ccrFiberMor (setoidDensitySnd F) m = m.homData.hom := rfl

/-! ### The Setoid Density Presentation -/

/--
The setoid density presentation of a Setoid-valued copresheaf F : D ⥤ SetoidBundle.

This is the canonical polynomial presentation whose setoid coequalizer
reconstructs F. The construction uses pre-quotient elements:
- Target polynomial: indexed by (A, x) with x ∈ (F.obj A).carrier
- Source polynomial: indexed by morphisms (q, p, f : q → p with compat)
- fst: target map (identity fibers)
- snd: source map (morphism fibers)
-/
def setoidDensityPresentation (F : D ⥤ SetoidBundle.{max u v}) :
    PolyPresentation.{u, v, max u v} D where
  src := setoidDensitySrc F
  tgt := setoidDensityTgt F
  fst := setoidDensityFst F
  snd := setoidDensitySnd F

@[simp]
theorem setoidDensityPresentation_src (F : D ⥤ SetoidBundle.{max u v}) :
    (setoidDensityPresentation F).src = setoidDensitySrc F := rfl

@[simp]
theorem setoidDensityPresentation_tgt (F : D ⥤ SetoidBundle.{max u v}) :
    (setoidDensityPresentation F).tgt = setoidDensityTgt F := rfl

@[simp]
theorem setoidDensityPresentation_fst (F : D ⥤ SetoidBundle.{max u v}) :
    (setoidDensityPresentation F).fst = setoidDensityFst F := rfl

@[simp]
theorem setoidDensityPresentation_snd (F : D ⥤ SetoidBundle.{max u v}) :
    (setoidDensityPresentation F).snd = setoidDensitySnd F := rfl

end SetoidDensityPresentation

/-! ## Constructive Inverse for Setoid Equivalence

For a polynomial presentation X, we construct an inverse morphism from
setoidDensityPresentation(X.toSetoidCopresheaf) back to X.

Elements of X.toSetoidCopresheaf.obj A are pairs ⟨i, h⟩ where
i : ccrIndex X.tgt and h : ccrFamily X.tgt i ⟶ A.  We can directly
extract the index i without quotient elimination.
-/

section SetoidConstructiveInverse

variable {D : Type u} [Category.{v} D]
variable (X : PolyPresentation.{u, v, max u v} D)

/-! ### Element Structure for Setoid Copresheaves

The elements of X.toSetoidCopresheaf are pairs (A, ⟨i, h⟩) where we have
direct access to the index i and the morphism h.
-/

/--
Extract the index from a setoid element of X.toSetoidCopresheaf.
This is the constructive core: we directly access the index without
quotient extraction.
-/
def setoidInverseTgtBase
    (p : SetoidElements X.toSetoidCopresheaf) : ccrIndex X.tgt :=
  p.elem.fst

/--
Extract the morphism from a setoid element of X.toSetoidCopresheaf.
-/
def setoidInverseTgtFiber
    (p : SetoidElements X.toSetoidCopresheaf) :
    ccrFamily X.tgt (setoidInverseTgtBase X p) ⟶ p.obj :=
  p.elem.snd

/--
The morphism on target polynomials for the inverse.
Maps (A, ⟨i, h⟩) to i with fiber h.
-/
def setoidInverseTgtHom :
    setoidDensityTgt X.toSetoidCopresheaf ⟶ X.tgt :=
  ccrHomMk
    (setoidInverseTgtBase X)
    (setoidInverseTgtFiber X)

@[simp]
theorem setoidInverseTgtHom_reindex
    (p : SetoidElements X.toSetoidCopresheaf) :
    ccrReindex (setoidInverseTgtHom X) p = setoidInverseTgtBase X p := rfl

@[simp]
theorem setoidInverseTgtHom_fiberMor
    (p : SetoidElements X.toSetoidCopresheaf) :
    ccrFiberMor (setoidInverseTgtHom X) p = setoidInverseTgtFiber X p := rfl

/-! ### Respects Coequalization

For a Q-morphism, we only need to show that the target polynomial map
respects the coequalizer relation. We don't need a source polynomial map.
-/

set_option backward.isDefEq.respectTransparency false in
/--
The inverse target map respects the setoid coequalizer relation.

Given (A, ⟨i, h⟩) and (A, ⟨j, g⟩) in the same equivalence class under
the setoid density coequalizer, their images under setoidInverseTgtHom
must be in the same equivalence class under X's coequalizer.
-/
theorem setoidInverseTgtHom_respects :
    ccrToFunctorMap (setoidDensityFst X.toSetoidCopresheaf) ≫
      ccrToFunctorMap (setoidInverseTgtHom X) ≫ X.toCopresheafπ =
    ccrToFunctorMap (setoidDensitySnd X.toSetoidCopresheaf) ≫
      ccrToFunctorMap (setoidInverseTgtHom X) ≫ X.toCopresheafπ := by
  ext A ⟨m, g⟩
  simp only [NatTrans.comp_app, types_comp_apply, ccrToFunctorMap_app,
    ccrToFunctorMapApp]
  -- m : SetoidMorphismIndex X.toSetoidCopresheaf
  -- g : m.tgt.obj ⟶ A
  -- LHS computes to: π(⟨m.tgt.elem.fst, m.tgt.elem.snd ≫ g⟩)
  -- RHS computes to: π(⟨m.src.elem.fst, m.src.elem.snd ≫ m.homData.hom ≫ g⟩)
  -- The compat condition gives us the setoid relation we need
  -- The compat condition says:
  -- (X.toSetoidCopresheaf.obj m.tgt.obj).rel.r
  --   ((X.toSetoidCopresheaf.map m.homData.hom).toFun m.src.elem) m.tgt.elem
  -- Unfold to see this is X.coeqSetoidAt relation
  have compat : (X.coeqSetoidAt m.tgt.obj).r
      (ccrEvalMap m.homData.hom m.src.elem) m.tgt.elem := by
    have h := m.homData.compat
    simp only [PolyPresentation.toSetoidCopresheaf, PolyPresentation.toSetoidBundleAt,
      PolyPresentation.toSetoidCopresheafMap, PolyPresentation.toSetoidCopresheafMapFun] at h
    exact h
  -- Transport to object A using coeqSetoidAt_map
  have transported := X.coeqSetoidAt_map g compat
  -- transported : (X.coeqSetoidAt A).r
  --   (ccrEvalMap g (ccrEvalMap m.homData.hom m.src.elem))
  --   (ccrEvalMap g m.tgt.elem)
  -- Unfold toCopresheafπ to get Quot.mk
  unfold PolyPresentation.toCopresheafπ PolyPresentation.toCopresheaf
  simp only [functorCoeqπ, CoequalizerData.π, typeCoeqπ, ccrToFunctorMap_app]
  -- Apply Quot.eqvGen_sound - we need to show EqvGen of typeCoeqRel
  -- The relations typeCoeqRel and coeqRelAt are definitionally equal
  apply Quot.eqvGen_sound
  -- Simplify both sides
  simp only [setoidDensityFst_reindex, setoidDensityFst_fiberMor,
    setoidDensitySnd_reindex, setoidDensitySnd_fiberMor,
    setoidInverseTgtHom_reindex, setoidInverseTgtHom_fiberMor,
    setoidInverseTgtBase, setoidInverseTgtFiber,
    SetoidElements.obj, SetoidElements.elem,
    SetoidMorphismIndex.tgt, SetoidMorphismIndex.src, SetoidMorphismIndex.homData,
    ccrEvalIndex, ccrEvalMor, ccrEvalMk]
  -- The goal has match expressions that need to be unfolded
  -- First, establish how the relations match up
  -- ccrToFunctorMapApp X.fst A = (ccrToFunctor X.fst).app A
  -- typeCoeqRel f g y₁ y₂ = ∃ x, f x = y₁ ∧ g x = y₂
  -- coeqRelAt A y₁ y₂ = ∃ x, ccrToFunctorMapApp X.fst A x = y₁ ∧
  --                           ccrToFunctorMapApp X.snd A x = y₂
  -- These are definitionally equal
  -- Use Quot.eqvGen_sound via the coeqRelAt relation
  simp only [ccrEvalMap] at transported
  -- The goal is to show EqvGen of typeCoeqRel, but transported gives EqvGen of coeqRelAt
  -- These relations are the same, so we need to bridge them
  -- First simplify the match expressions by casing on the sigma pairs
  rcases m with ⟨⟨tgt_obj, ⟨tgt_idx, tgt_mor⟩⟩, ⟨⟨src_obj, ⟨src_idx, src_mor⟩⟩, hom_data⟩⟩
  simp only [SetoidMorphismIndex.tgt, SetoidMorphismIndex.src, SetoidMorphismIndex.homData,
    SetoidElements.obj, SetoidElements.elem] at compat transported ⊢
  -- Now the goal has concrete indices
  -- Goal: EqvGen (typeCoeqRel ...) ⟨tgt_idx, tgt_mor ≫ 𝟙 tgt_obj ≫ g⟩
  --                                ⟨src_idx, src_mor ≫ hom_data.hom ≫ g⟩
  -- transported: EqvGen (coeqRelAt A) ⟨src_idx, (src_mor ≫ hom_data.hom) ≫ g⟩
  --                                   ⟨tgt_idx, tgt_mor ≫ g⟩
  -- Need to: 1) handle id_comp, 2) handle assoc, 3) swap LHS/RHS, 4) match relations
  -- The types ccrFamily ... tgt_obj ⟶ A match with morphisms, so need tgt_obj to match
  have goal_lhs_eq : (⟨tgt_idx, tgt_mor ≫ 𝟙 tgt_obj ≫ g⟩ : ccrEval X.tgt A) =
      ⟨tgt_idx, tgt_mor ≫ g⟩ := by
    simp only [Category.id_comp]
  have goal_rhs_eq : (⟨src_idx, src_mor ≫ hom_data.hom ≫ g⟩ : ccrEval X.tgt A) =
      ⟨src_idx, (src_mor ≫ hom_data.hom) ≫ g⟩ := by
    simp only [Category.assoc]
  rw [goal_lhs_eq, goal_rhs_eq]
  -- Now goal matches transported.symm, just need to show relations are equal
  -- coeqRelAt and typeCoeqRel are definitionally equal
  exact transported.symm

/-! ### The Setoid Inverse Q-Morphism

Combining the target morphism with the respects theorem to form a Q-morphism.
-/

/--
The constructive inverse as a Q-morphism from the setoid density presentation
of X.toSetoidCopresheaf back to X.
-/
def setoidInverseQ :
    PolyPresentationQ.Hom (setoidDensityPresentation X.toSetoidCopresheaf).toQ X.toQ where
  tgtHom := setoidInverseTgtHom X
  respects := setoidInverseTgtHom_respects X

/-! ### Induced Map is Isomorphism

The setoid inverse induces a map on Type-valued coequalizers. We show this
map is an isomorphism by constructing its inverse from the density isomorphism.
-/

/--
The induced map from the setoid inverse Q-morphism.
This maps from the coequalizer of the setoid density presentation to X.toCopresheaf.
-/
def setoidInverseInducedMap :
    (setoidDensityPresentation X.toSetoidCopresheaf).toCopresheaf ⟶ X.toCopresheaf :=
  (setoidInverseQ X).toInducedMap

/-! ### Forward Embedding

The inverse of the setoid inverse map. Given an element (i, g) of X's target
polynomial at A, we embed it as ((A, (i, g)), id_A) in the setoid density
presentation.
-/

/--
Forward embedding at pre-quotient level.
Maps (i, g) to ((A, (i, g)), id_A) in the setoid density target.
-/
def setoidForwardApp (A : D) (p : ccrEval X.tgt A) :
    ccrEval (setoidDensityTgt X.toSetoidCopresheaf) A :=
  ⟨⟨A, p⟩, 𝟙 A⟩

set_option backward.isDefEq.respectTransparency false in
/--
The forward embedding respects X's coequalizer relation.
If p₁ and p₂ are related by the coequalizer relation, their images are also
related in the setoid density presentation.
-/
theorem setoidForwardApp_respects (A : D) :
    ∀ p₁ p₂ : ccrEval X.tgt A,
      typeCoeqRel ((ccrToFunctorMap X.fst).app A) ((ccrToFunctorMap X.snd).app A)
        p₁ p₂ →
      typeCoeqRel
        ((ccrToFunctorMap (setoidDensityPresentation X.toSetoidCopresheaf).fst).app A)
        ((ccrToFunctorMap (setoidDensityPresentation X.toSetoidCopresheaf).snd).app A)
        (setoidForwardApp X A p₁) (setoidForwardApp X A p₂) := by
  intro ⟨i₁, g₁⟩ ⟨i₂, g₂⟩ ⟨j, hfst, hsnd⟩
  let srcElem : SetoidElements X.toSetoidCopresheaf := ⟨A, ⟨i₂, g₂⟩⟩
  let tgtElem : SetoidElements X.toSetoidCopresheaf := ⟨A, ⟨i₁, g₁⟩⟩
  have base_rel : (X.toSetoidCopresheaf.obj A).rel.r ⟨i₁, g₁⟩ ⟨i₂, g₂⟩ :=
    Relation.EqvGen.rel _ _ ⟨j, hfst, hsnd⟩
  have sym_rel : (X.toSetoidCopresheaf.obj A).rel.r ⟨i₂, g₂⟩ ⟨i₁, g₁⟩ :=
    Relation.EqvGen.symm _ _ base_rel
  have map_id_eq : (X.toSetoidCopresheaf.map (𝟙 A)).toFun srcElem.elem = srcElem.elem := by
    have h : X.toSetoidCopresheaf.map (𝟙 A) = 𝟙 _ := X.toSetoidCopresheaf.map_id A
    rw [h]
    rfl
  have hom_compat : (X.toSetoidCopresheaf.obj tgtElem.obj).rel.r
      ((X.toSetoidCopresheaf.map (𝟙 A)).toFun srcElem.elem) tgtElem.elem := by
    rw [map_id_eq]
    exact sym_rel
  let homData : SetoidElementsHom srcElem tgtElem := ⟨𝟙 A, hom_compat⟩
  let mIdx : SetoidMorphismIndex X.toSetoidCopresheaf := ⟨tgtElem, srcElem, homData⟩
  let witness : ccrEval (setoidDensitySrc X.toSetoidCopresheaf) A := ⟨mIdx, 𝟙 A⟩
  refine ⟨witness, ?_, ?_⟩
  · simp only [ccrToFunctorMap_app, ccrToFunctorMapApp, setoidForwardApp,
      setoidDensityPresentation, setoidDensityFst, ccrReindex, ccrFiberMor,
      ccrHomMk, Category.id_comp, ccrEvalMk, SetoidMorphismIndex.tgt,
      ccrEvalIndex, ccrEvalMor]
    rfl
  · simp only [ccrToFunctorMap_app, ccrToFunctorMapApp, setoidForwardApp,
      setoidDensityPresentation, setoidDensitySnd, ccrReindex, ccrFiberMor,
      ccrHomMk, ccrEvalMk, SetoidMorphismIndex.src, SetoidMorphismIndex.homData,
      ccrEvalIndex, ccrEvalMor]
    apply Sigma.ext
    · rfl
    · simp only [heq_eq_eq]
      have h1 : witness.fst.snd.snd.hom = 𝟙 A := rfl
      have h2 : witness.snd = 𝟙 A := rfl
      rw [h1, h2]
      exact Category.id_comp (𝟙 A)

/--
The forward embedding descends to the quotient.
-/
def setoidForwardQuotApp (A : D) :
    X.toCopresheaf.obj A →
    (setoidDensityPresentation X.toSetoidCopresheaf).toCopresheaf.obj A := by
  apply Quot.lift (fun p => Quot.mk _ (setoidForwardApp X A p))
  intro p₁ p₂ rel
  apply Quot.sound
  exact setoidForwardApp_respects X A p₁ p₂ rel

set_option backward.isDefEq.respectTransparency false in
/--
The forward embedding is natural.
-/
theorem setoidForwardQuotApp_natural {A B : D} (f : A ⟶ B) :
    X.toCopresheaf.map f ≫ setoidForwardQuotApp X B =
    setoidForwardQuotApp X A ≫
      (setoidDensityPresentation X.toSetoidCopresheaf).toCopresheaf.map f := by
  ext x
  revert x
  apply Quot.ind
  intro ⟨i, g⟩
  simp only [types_comp_apply, PolyPresentation.toCopresheaf,
    CoequalizerData.coeq, functorCoeq, ccrToFunctorMap_app]
  unfold setoidForwardQuotApp
  -- LHS: Quot.mk ((B, ⟨i, g ≫ f⟩), id_B)
  -- RHS: Quot.mk ((A, ⟨i, g⟩), id_A ≫ f) = Quot.mk ((A, ⟨i, g⟩), f)
  apply Quot.sound
  -- Witness: morphism from (A, ⟨i,g⟩) to (B, ⟨i, g ≫ f⟩) with hom = f
  let srcElem : SetoidElements X.toSetoidCopresheaf := ⟨A, ⟨i, g⟩⟩
  let tgtElem : SetoidElements X.toSetoidCopresheaf := ⟨B, ⟨i, g ≫ f⟩⟩
  have hom_compat : (X.toSetoidCopresheaf.obj B).rel.r
      ((X.toSetoidCopresheaf.map f).toFun ⟨i, g⟩) ⟨i, g ≫ f⟩ := by
    simp only [PolyPresentation.toSetoidCopresheaf, PolyPresentation.toSetoidBundleAt,
      PolyPresentation.toSetoidCopresheafMap, PolyPresentation.toSetoidCopresheafMapFun,
      ccrEvalMap]
    exact Relation.EqvGen.refl _
  let homData : SetoidElementsHom srcElem tgtElem := ⟨f, hom_compat⟩
  let mIdx : SetoidMorphismIndex X.toSetoidCopresheaf := ⟨tgtElem, srcElem, homData⟩
  let witness : ccrEval (setoidDensitySrc X.toSetoidCopresheaf) B := ⟨mIdx, 𝟙 B⟩
  use witness
  have hIdx : ccrEvalIndex witness = mIdx := rfl
  have hMor : ccrEvalMor witness = 𝟙 B := rfl
  have hHomData : SetoidMorphismIndex.homData mIdx = homData := rfl
  have hHom : homData.hom = f := rfl
  constructor
  · simp only [ccrToFunctorMap_app, ccrToFunctorMapApp, setoidDensityPresentation,
      setoidDensityFst, ccrReindex, ccrFiberMor, ccrHomMk, ccrEvalMk,
      setoidForwardApp, ccrToFunctor, ccrEvalMap, Category.id_comp]
    apply Sigma.ext
    · rfl
    · simp only [heq_eq_eq, hMor]
  · simp only [ccrToFunctorMap_app, ccrToFunctorMapApp, setoidDensityPresentation,
      setoidDensitySnd, ccrReindex, ccrFiberMor, ccrHomMk, ccrEvalMk,
      setoidForwardApp, ccrToFunctor, ccrEvalMap]
    apply Sigma.ext
    · rfl
    · simp only [heq_eq_eq, hMor]
      change f ≫ 𝟙 B = 𝟙 A ≫ f
      simp only [Category.comp_id, Category.id_comp]

/--
The forward embedding as a natural transformation.
-/
def setoidForwardMap :
    X.toCopresheaf ⟶
    (setoidDensityPresentation X.toSetoidCopresheaf).toCopresheaf where
  app := setoidForwardQuotApp X
  naturality := fun _ _ f => setoidForwardQuotApp_natural X f

/-! ### Round-Trip Identities -/

set_option backward.isDefEq.respectTransparency false in
/--
The composition setoidInverseInducedMap ≫ setoidForwardMap is the identity
on the setoid density presentation's coequalizer.
-/
theorem setoidInverse_forward_id :
    setoidInverseInducedMap X ≫ setoidForwardMap X = 𝟙 _ := by
  ext A x
  revert x
  apply Quot.ind
  intro ⟨⟨B, ⟨i, h⟩⟩, g⟩
  simp only [NatTrans.id_app, NatTrans.comp_app, types_comp_apply, types_id_apply]
  unfold setoidForwardMap setoidInverseInducedMap
  simp only [PolyPresentationQ.Hom.toInducedMap,
    PolyPresentation.toCopresheaf]
  simp only [ccrToFunctorMap_app]
  dsimp only [PolyPresentationQ.Hom.toInducedMap, setoidInverseQ,
    CoequalizerData.desc, typeCoeqDesc, PolyPresentationQ.toPres,
    PolyPresentation.toCopresheafπ, functorCoeqπ, functorCoeqDesc,
    CoequalizerData.π, typeCoeqπ]
  simp only [NatTrans.comp_app, types_comp_apply]
  simp only [ccrToFunctorMap_app, ccrToFunctorMapApp, setoidInverseTgtHom_reindex,
    setoidInverseTgtHom_fiberMor, setoidInverseTgtBase, setoidInverseTgtFiber,
    SetoidElements.obj, SetoidElements.elem]
  unfold setoidForwardQuotApp
  simp only [setoidForwardApp]
  dsimp only [ccrEvalIndex, ccrEvalMor, ccrEvalMk]
  apply Quot.sound
  unfold typeCoeqRel
  let tgtElem : SetoidElements X.toSetoidCopresheaf := ⟨A, ⟨i, h ≫ g⟩⟩
  let srcElem : SetoidElements X.toSetoidCopresheaf := ⟨B, ⟨i, h⟩⟩
  have hom_compat : (X.toSetoidCopresheaf.obj A).rel.r
      ((X.toSetoidCopresheaf.map g).toFun ⟨i, h⟩) ⟨i, h ≫ g⟩ := by
    simp only [PolyPresentation.toSetoidCopresheaf, PolyPresentation.toSetoidBundleAt,
      PolyPresentation.toSetoidCopresheafMap, PolyPresentation.toSetoidCopresheafMapFun,
      ccrEvalMap]
    exact Relation.EqvGen.refl _
  let homData : SetoidElementsHom srcElem tgtElem := ⟨g, hom_compat⟩
  let mIdx : SetoidMorphismIndex X.toSetoidCopresheaf := ⟨tgtElem, srcElem, homData⟩
  let witness : ccrEval (setoidDensitySrc X.toSetoidCopresheaf) A := ⟨mIdx, 𝟙 A⟩
  use witness
  constructor
  · dsimp only [setoidDensityFst, ccrHomMk, ccrEvalIndex, ccrEvalMor,
      SetoidMorphismIndex.tgt, SetoidElements.obj, ccrToFunctorMap,
      ccrToFunctorMapApp, setoidDensityPresentation, PolyPresentation.fst,
      ccrReindex, ccrFiberMor, ccrEvalMk, witness, mIdx, tgtElem, ccrFamily,
      setoidDensityTgt]
    simp only [Category.id_comp]
  · dsimp only [setoidDensitySnd, ccrHomMk, ccrEvalIndex, ccrEvalMor,
      SetoidMorphismIndex.src, SetoidMorphismIndex.homData, SetoidElementsHom.hom,
      SetoidElements.obj, ccrToFunctorMap, ccrToFunctorMapApp,
      setoidDensityPresentation, PolyPresentation.snd, ccrReindex, ccrFiberMor,
      ccrEvalMk, witness, mIdx, srcElem, homData, ccrFamily, setoidDensityTgt]
    congr 1
    exact Category.comp_id g

/--
The composition setoidForwardMap ≫ setoidInverseInducedMap is the identity
on X.toCopresheaf.
-/
theorem setoidForward_inverse_id :
    setoidForwardMap X ≫ setoidInverseInducedMap X = 𝟙 _ := by
  ext A x
  revert x
  apply Quot.ind
  intro ⟨i, g⟩
  simp only [NatTrans.comp_app, types_comp_apply, NatTrans.id_app, types_id_apply]
  unfold setoidForwardMap setoidForwardQuotApp setoidInverseInducedMap
  dsimp only [setoidForwardApp, PolyPresentationQ.Hom.toInducedMap,
    PolyPresentation.toCopresheaf, CoequalizerData.desc, typeCoeqDesc,
    functorCoeqDesc]
  simp only [NatTrans.comp_app, types_comp_apply]
  dsimp only [ccrToFunctorMap_app, ccrToFunctorMapApp, ccrEvalMk, ccrHomMk,
    setoidInverseQ, setoidInverseTgtHom, setoidInverseTgtBase, setoidInverseTgtFiber,
    PolyPresentationQ.toPres, SetoidElements.obj, SetoidElements.elem,
    ccrReindex, ccrFiberMor, ccrEvalIndex, ccrEvalMor,
    PolyPresentation.toCopresheafπ, functorCoeqπ, CoequalizerData.π, typeCoeqπ,
    PolyPresentation.toQ]
  congr 1
  exact Sigma.ext rfl (heq_of_eq (Category.comp_id g))

/--
The quotient of the setoid density target is isomorphic to X.toCopresheaf.
-/
def setoidInverseIso :
    (setoidDensityPresentation X.toSetoidCopresheaf).toCopresheaf ≅ X.toCopresheaf :=
  { hom := setoidInverseInducedMap X
    inv := setoidForwardMap X
    hom_inv_id := setoidInverse_forward_id X
    inv_hom_id := setoidForward_inverse_id X }

/--
The induced map from the setoid inverse is an isomorphism.
-/
theorem setoidInverseInducedMap_isIso :
    IsIso (setoidInverseInducedMap X) :=
  (setoidInverseIso X).isIso_hom

/-! ### Comparison Morphism (Setoid Version)

We construct a morphism in PolyPresentationLoc from X to
setoidDensityPresentation(X.toSetoidCopresheaf). Together with setoidInverseQ,
this forms an isomorphism in PolyPresentationLoc.
-/

/--
Map an index of X.tgt to a SetoidElement of X.toSetoidCopresheaf.
We use the canonical element ⟨i, 𝟙⟩.
-/
def setoidComparisonTgtReindex (i : ccrIndex X.tgt) :
    SetoidElements X.toSetoidCopresheaf :=
  ⟨ccrFamily X.tgt i, ⟨i, 𝟙 _⟩⟩

/--
The morphism on target polynomials for the setoid comparison.
Maps each index i to the element (ccrFamily i, ⟨i, 𝟙⟩).
-/
def setoidComparisonTgtHom :
    X.tgt ⟶ setoidDensityTgt X.toSetoidCopresheaf :=
  ccrHomMk
    (setoidComparisonTgtReindex X)
    (fun _ => 𝟙 _)

@[simp]
theorem setoidComparisonTgtHom_reindex (i : ccrIndex X.tgt) :
    ccrReindex (setoidComparisonTgtHom X) i = setoidComparisonTgtReindex X i :=
  rfl

@[simp]
theorem setoidComparisonTgtHom_fiberMor (i : ccrIndex X.tgt) :
    ccrFiberMor (setoidComparisonTgtHom X) i = 𝟙 _ := rfl

set_option backward.isDefEq.respectTransparency false in
/--
The comparison composed with densityπ, followed by the inverse, equals X.toCopresheafπ.
This is a helper for the main factorization theorem.
-/
theorem setoidComparisonTgtHom_inverse_eq :
    ccrToFunctorMap (setoidComparisonTgtHom X) ≫
      (setoidDensityPresentation X.toSetoidCopresheaf).toCopresheafπ ≫
      setoidInverseInducedMap X = X.toCopresheafπ := by
  ext A ⟨i, h⟩
  simp only [NatTrans.comp_app, types_comp_apply, ccrToFunctorMap_app,
    ccrToFunctorMapApp, setoidComparisonTgtHom_reindex, setoidComparisonTgtHom_fiberMor,
    ccrEvalMk, ccrEvalIndex, ccrEvalMor, Category.id_comp, setoidComparisonTgtReindex]
  unfold PolyPresentation.toCopresheafπ PolyPresentation.toCopresheaf
  simp only [functorCoeqπ, CoequalizerData.π, typeCoeqπ]
  unfold setoidInverseInducedMap PolyPresentationQ.Hom.toInducedMap
  simp only [PolyPresentation.toCopresheaf, CoequalizerData.desc, typeCoeqDesc,
    functorCoeqDesc, NatTrans.comp_app, types_comp_apply]
  simp only [ccrToFunctorMap_app, ccrToFunctorMapApp, ccrEvalMk]
  unfold setoidInverseQ PolyPresentation.toQ PolyPresentationQ.toPres
  simp only [setoidInverseTgtHom, ccrHomMk, ccrReindex, ccrFiberMor,
    setoidInverseTgtBase, setoidInverseTgtFiber,
    SetoidElements.elem, SetoidElements.obj, ccrEvalIndex, ccrEvalMor,
    Category.id_comp]
  unfold PolyPresentation.toCopresheafπ
  simp only [functorCoeqπ, CoequalizerData.π, typeCoeqπ, ccrToFunctorMap_app]

/--
The factorization: comparison ≫ densityπ = X.toCopresheafπ ≫ setoidForwardMap.

We prove this by showing both sides become equal after composing with
setoidInverseInducedMap (which is an isomorphism), then cancelling.
-/
theorem setoidComparisonTgtHom_factor :
    ccrToFunctorMap (setoidComparisonTgtHom X) ≫
      (setoidDensityPresentation X.toSetoidCopresheaf).toCopresheafπ =
      X.toCopresheafπ ≫ setoidForwardMap X := by
  have h1 : ccrToFunctorMap (setoidComparisonTgtHom X) ≫
      (setoidDensityPresentation X.toSetoidCopresheaf).toCopresheafπ ≫
      setoidInverseInducedMap X = X.toCopresheafπ :=
    setoidComparisonTgtHom_inverse_eq X
  have hIso : IsIso (setoidInverseInducedMap X) := by
    constructor
    use setoidForwardMap X
    constructor
    · exact setoidInverse_forward_id X
    · exact setoidForward_inverse_id X
  calc ccrToFunctorMap (setoidComparisonTgtHom X) ≫
        (setoidDensityPresentation X.toSetoidCopresheaf).toCopresheafπ
    _ = (ccrToFunctorMap (setoidComparisonTgtHom X) ≫
        (setoidDensityPresentation X.toSetoidCopresheaf).toCopresheafπ ≫
        setoidInverseInducedMap X) ≫ inv (setoidInverseInducedMap X) := by
          simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    _ = X.toCopresheafπ ≫ inv (setoidInverseInducedMap X) := by rw [h1]
    _ = X.toCopresheafπ ≫ setoidForwardMap X := by
          congr 1
          symm
          exact IsIso.eq_inv_of_hom_inv_id (setoidInverse_forward_id X)

/--
The comparison morphism respects the coequalizer structure.

For elements ⟨j, g⟩ in X.src evaluated at A, the images under X.fst and X.snd
followed by the comparison map project to the same element in the setoid
density coequalizer.
-/
theorem setoidComparisonTgtHom_respects :
    ccrToFunctorMap X.fst ≫ ccrToFunctorMap (setoidComparisonTgtHom X) ≫
      (setoidDensityPresentation X.toSetoidCopresheaf).toCopresheafπ =
    ccrToFunctorMap X.snd ≫ ccrToFunctorMap (setoidComparisonTgtHom X) ≫
      (setoidDensityPresentation X.toSetoidCopresheaf).toCopresheafπ := by
  simp only [setoidComparisonTgtHom_factor, ← Category.assoc]
  rw [X.toCopresheaf_condition]

/-! ### Comparison Morphism in PolyPresentationQ -/

/--
The comparison morphism from X to setoidDensityPresentation(X.toSetoidCopresheaf)
in the quotient category PolyPresentationQ.
-/
def setoidComparisonQ :
    PolyPresentation.toQ D X ⟶
    PolyPresentation.toQ D (setoidDensityPresentation X.toSetoidCopresheaf) :=
  ⟨setoidComparisonTgtHom X, setoidComparisonTgtHom_respects X⟩

/--
The induced map of setoidComparisonQ equals setoidForwardMap.
This follows from uniqueness of the coequalizer factorization.
-/
theorem setoidComparisonQ_toInducedMap :
    (setoidComparisonQ X).toInducedMap = setoidForwardMap X := by
  symm
  apply CoequalizerData.uniq
  simp only [setoidComparisonQ, PolyPresentation.toQ, PolyPresentationQ.toPres]
  exact (setoidComparisonTgtHom_factor X).symm

set_option backward.isDefEq.respectTransparency false in
/--
The composition setoidComparisonQ ≫ setoidInverseQ is equivalent to the identity.
This means they induce the same map on coequalizers.
-/
theorem setoidComparisonQ_inverseQ_equiv :
    (setoidComparisonQ X ≫ setoidInverseQ X).equiv
      (PolyPresentationQ.Hom.id X.toQ) := by
  unfold PolyPresentationQ.Hom.equiv
  calc (setoidComparisonQ X ≫ setoidInverseQ X).toInducedMap
      = (setoidComparisonQ X).toInducedMap ≫
          (setoidInverseQ X).toInducedMap := by
        rw [PolyPresentationQ.Hom.toInducedMap_comp]
    _ = setoidForwardMap X ≫ setoidInverseInducedMap X := by
        rw [setoidComparisonQ_toInducedMap]; rfl
    _ = 𝟙 X.toCopresheaf := setoidForward_inverse_id X
    _ = PolyPresentationQ.Hom.toInducedMap (𝟙 X.toQ) := by
        simp only [PolyPresentationQ.Hom.toInducedMap_id, PolyPresentation.toQ,
          PolyPresentationQ.toPres]
    _ = (PolyPresentationQ.Hom.id X.toQ).toInducedMap := rfl

set_option backward.isDefEq.respectTransparency false in
/--
The composition setoidInverseQ ≫ setoidComparisonQ is equivalent to the identity.
This means they induce the same map on coequalizers.
-/
theorem setoidInverseQ_comparisonQ_equiv :
    (setoidInverseQ X ≫ setoidComparisonQ X).equiv
      (PolyPresentationQ.Hom.id
        (setoidDensityPresentation X.toSetoidCopresheaf).toQ) := by
  unfold PolyPresentationQ.Hom.equiv
  calc (setoidInverseQ X ≫ setoidComparisonQ X).toInducedMap
      = (setoidInverseQ X).toInducedMap ≫
          (setoidComparisonQ X).toInducedMap := by
        rw [PolyPresentationQ.Hom.toInducedMap_comp]
    _ = setoidInverseInducedMap X ≫ setoidForwardMap X := by
        rw [setoidComparisonQ_toInducedMap]; rfl
    _ = 𝟙 (setoidDensityPresentation X.toSetoidCopresheaf).toCopresheaf :=
        setoidInverse_forward_id X
    _ = PolyPresentationQ.Hom.toInducedMap
          (𝟙 (setoidDensityPresentation X.toSetoidCopresheaf).toQ) := by
        simp only [PolyPresentationQ.Hom.toInducedMap_id, PolyPresentation.toQ,
          PolyPresentationQ.toPres]
    _ = (PolyPresentationQ.Hom.id
          (setoidDensityPresentation X.toSetoidCopresheaf).toQ).toInducedMap := rfl

/-!
### Localized Category Morphisms

Now we lift the morphisms from PolyPresentationQ to PolyPresentationLoc, where
equivalent morphisms become equal.
-/

/--
The source object in the localized category.
-/
abbrev setoidComparisonSrc : PolyPresentationLoc D :=
  PolyPresentationLoc.ofPres X

/--
The target object in the localized category.
-/
abbrev setoidComparisonTgt : PolyPresentationLoc D :=
  PolyPresentationLoc.ofPres (setoidDensityPresentation X.toSetoidCopresheaf)

/--
The comparison morphism in the localized category PolyPresentationLoc.
-/
def setoidComparisonLoc :
    setoidComparisonSrc X ⟶ setoidComparisonTgt X :=
  PolyPresentationLoc.Hom.mk' (setoidComparisonQ X)

/--
The inverse morphism in the localized category PolyPresentationLoc.
-/
def setoidInverseLoc :
    setoidComparisonTgt X ⟶ setoidComparisonSrc X :=
  PolyPresentationLoc.Hom.mk' (setoidInverseQ X)

/--
The composition setoidComparisonLoc ≫ setoidInverseLoc equals the identity.
This follows from the equivalence at the Q level.
-/
theorem setoidComparisonLoc_inverseLoc_id :
    setoidComparisonLoc X ≫ setoidInverseLoc X = 𝟙 (setoidComparisonSrc X) := by
  unfold setoidComparisonLoc setoidInverseLoc setoidComparisonSrc
  unfold PolyPresentationLoc.Hom.mk'
  dsimp only [CategoryStruct.comp, CategoryStruct.id,
    PolyPresentationLoc.category]
  apply Quot.sound
  exact setoidComparisonQ_inverseQ_equiv X

/--
The composition setoidInverseLoc ≫ setoidComparisonLoc equals the identity.
This follows from the equivalence at the Q level.
-/
theorem setoidInverseLoc_comparisonLoc_id :
    setoidInverseLoc X ≫ setoidComparisonLoc X = 𝟙 (setoidComparisonTgt X) := by
  unfold setoidInverseLoc setoidComparisonLoc setoidComparisonTgt
  unfold PolyPresentationLoc.Hom.mk'
  dsimp only [CategoryStruct.comp, CategoryStruct.id,
    PolyPresentationLoc.category]
  apply Quot.sound
  exact setoidInverseQ_comparisonQ_equiv X

/--
The comparison morphism is an isomorphism in PolyPresentationLoc.
-/
def setoidComparisonIso :
    setoidComparisonSrc X ≅ setoidComparisonTgt X where
  hom := setoidComparisonLoc X
  inv := setoidInverseLoc X
  hom_inv_id := setoidComparisonLoc_inverseLoc_id X
  inv_hom_id := setoidInverseLoc_comparisonLoc_id X

end SetoidConstructiveInverse

/-! ## Setoid Counit Construction

The counit of the equivalence: for F : D ⥤ SetoidBundle, we construct an
isomorphism F ≅ (setoidDensityPresentation F).toSetoidCopresheaf.

This is the other half of the equivalence, complementing the unit
(setoidComparisonIso) which shows X ≅ setoidDensityPresentation(X.toSetoidCopresheaf)
for presentations X.

The construction proceeds by:
1. Defining raw forward/inverse functions at the carrier level
2. Proving they preserve the relevant equivalence relations
3. Showing round-trip identities
4. Assembling into a natural isomorphism
-/

section SetoidCounit

variable {D : Type u} [Category.{v} D]
variable (F : D ⥤ SetoidBundle.{max u v})

/-! ### Computational Simp Lemmas

These lemmas make the structure of setoidDensityPresentation F accessible
for computation.
-/

@[simp]
theorem setoidDensityPresentation_toSetoidBundleAt_carrier (A : D) :
    ((setoidDensityPresentation F).toSetoidBundleAt A).carrier =
    ccrEval (setoidDensityTgt F) A := rfl

@[simp]
theorem setoidDensityTgt_ccrEval (A : D) :
    ccrEval (setoidDensityTgt F) A = Σ (p : SetoidElements F), (p.obj ⟶ A) := rfl

/-! ### Raw Forward Function

The forward function maps x : (F.obj A).carrier to the canonical element
((A, x), 𝟙 A) in the density presentation.
-/

/--
The forward embedding at the carrier level.
Maps x : (F.obj A).carrier to ((A, x), 𝟙 A).
-/
def setoidCounitForwardRaw (A : D) (x : (F.obj A).carrier) :
    ccrEval (setoidDensityTgt F) A :=
  ⟨⟨A, x⟩, 𝟙 A⟩

@[simp]
theorem setoidCounitForwardRaw_fst (A : D) (x : (F.obj A).carrier) :
    (setoidCounitForwardRaw F A x).fst = ⟨A, x⟩ := rfl

@[simp]
theorem setoidCounitForwardRaw_snd (A : D) (x : (F.obj A).carrier) :
    (setoidCounitForwardRaw F A x).snd = 𝟙 A := rfl

/-! ### Raw Inverse Function

The inverse function maps ((B, y), g : B ⟶ A) to (F.map g).toFun y.
This evaluates the functor F at the morphism g to transport y to A.
-/

/--
The inverse function at the carrier level.
Maps ((B, y), g) to (F.map g).toFun y.
-/
def setoidCounitInverseRaw (A : D) (x : ccrEval (setoidDensityTgt F) A) :
    (F.obj A).carrier :=
  (F.map x.snd).toFun x.fst.elem

@[simp]
theorem setoidCounitInverseRaw_apply (A : D) (B : D) (y : (F.obj B).carrier)
    (g : B ⟶ A) :
    setoidCounitInverseRaw F A ⟨⟨B, y⟩, g⟩ = (F.map g).toFun y := rfl

/-! ### Forward Preserves Relation

The forward function maps F's setoid relation to the coequalizer relation
of the density presentation.
-/

/--
Witness for setoidCounitForward preserving the relation.
Given x ≈ y in F.obj A, we construct a witness that their images are related
in the density coequalizer.

The coequalizer relation requires fst(w) = x and snd(w) = y, so:
- tgtElem = ⟨A, x⟩ (since fst maps to target)
- srcElem = ⟨A, y⟩ (since snd maps to source)
- homData goes from srcElem to tgtElem with compat: (F.map 𝟙)(y) ~ x
-/
def setoidCounitForward_witness (A : D) (x y : (F.obj A).carrier)
    (h : (F.obj A).rel.r x y) :
    ccrEval (setoidDensitySrc F) A :=
  let srcElem : SetoidElements F := ⟨A, y⟩
  let tgtElem : SetoidElements F := ⟨A, x⟩
  have hSym : (F.obj A).rel.r y x := (F.obj A).rel.symm h
  let mapIdCompat : (F.obj A).rel.r ((F.map (𝟙 A)).toFun y) x := by
    have hMapId : F.map (𝟙 A) = 𝟙 (F.obj A) := F.map_id A
    simp only [hMapId]
    exact hSym
  let homData : SetoidElementsHom srcElem tgtElem := ⟨𝟙 A, mapIdCompat⟩
  let mIdx : SetoidMorphismIndex F := ⟨tgtElem, srcElem, homData⟩
  ⟨mIdx, 𝟙 A⟩

set_option backward.isDefEq.respectTransparency false in
/--
The witness maps to the target (x's image) under fst.
-/
theorem setoidCounitForward_witness_fst (A : D) (x y : (F.obj A).carrier)
    (h : (F.obj A).rel.r x y) :
    (ccrToFunctorMap (setoidDensityFst F)).app A (setoidCounitForward_witness F A x y h) =
    setoidCounitForwardRaw F A x := by
  simp only [ccrToFunctorMap_app, ccrToFunctorMapApp, setoidCounitForward_witness,
    setoidDensityFst, ccrHomMk, ccrReindex, ccrFiberMor, ccrEvalMk, ccrEvalIndex, ccrEvalMor,
    SetoidMorphismIndex.tgt, setoidCounitForwardRaw, Category.id_comp]

/--
The witness maps to the source (y's image) under snd.
-/
theorem setoidCounitForward_witness_snd (A : D) (x y : (F.obj A).carrier)
    (h : (F.obj A).rel.r x y) :
    (ccrToFunctorMap (setoidDensitySnd F)).app A (setoidCounitForward_witness F A x y h) =
    setoidCounitForwardRaw F A y := by
  simp only [ccrToFunctorMap_app, ccrToFunctorMapApp, setoidCounitForward_witness,
    setoidDensitySnd, ccrHomMk, ccrReindex, ccrFiberMor, ccrEvalMk, ccrEvalIndex, ccrEvalMor,
    SetoidMorphismIndex.src, SetoidMorphismIndex.homData,
    setoidCounitForwardRaw]
  apply Sigma.ext
  · rfl
  · simp only [heq_eq_eq]
    exact Category.id_comp (𝟙 A)

/--
The forward function preserves the setoid relation.
If x ≈ y in F.obj A, then their images are related in the density coequalizer.
-/
theorem setoidCounitForwardRaw_map_rel (A : D) (x y : (F.obj A).carrier)
    (h : (F.obj A).rel.r x y) :
    (setoidDensityPresentation F).coeqSetoidAt A |>.r
      (setoidCounitForwardRaw F A x) (setoidCounitForwardRaw F A y) := by
  apply Relation.EqvGen.rel
  use setoidCounitForward_witness F A x y h
  constructor
  · exact setoidCounitForward_witness_fst F A x y h
  · exact setoidCounitForward_witness_snd F A x y h

/-! ### Inverse Preserves Relation

The inverse function maps the coequalizer relation of the density presentation
to F's setoid relation.
-/

set_option backward.isDefEq.respectTransparency false in
/--
The inverse function preserves the base coequalizer relation (before EqvGen).
Given a witness w in the source polynomial, the images of fst(w) and snd(w)
under the inverse are related.
-/
theorem setoidCounitInverseRaw_preserves_base (A : D)
    (w : ccrEval (setoidDensitySrc F) A) :
    (F.obj A).rel.r
      (setoidCounitInverseRaw F A ((ccrToFunctorMap (setoidDensityFst F)).app A w))
      (setoidCounitInverseRaw F A ((ccrToFunctorMap (setoidDensitySnd F)).app A w)) := by
  obtain ⟨⟨⟨tgtObj, tgtElem⟩, ⟨srcObj, srcElem⟩, homData⟩, g⟩ := w
  simp only [ccrToFunctorMap_app, ccrToFunctorMapApp, setoidDensityFst, setoidDensitySnd,
    ccrHomMk, ccrReindex, ccrFiberMor, ccrEvalMk, ccrEvalIndex, ccrEvalMor,
    SetoidMorphismIndex.tgt, SetoidMorphismIndex.src, SetoidMorphismIndex.homData,
    SetoidElements.elem, setoidCounitInverseRaw]
  simp only [Category.id_comp]
  have compat := homData.compat
  have h := (F.map g).map_rel _ _ compat
  simp only [SetoidElements.elem, SetoidElements.obj] at h
  have heq : (F.map g).toFun ((F.map homData.hom).toFun srcElem) =
             (F.map (homData.hom ≫ g)).toFun srcElem := by
    have hcomp := F.map_comp homData.hom g
    exact congrFun (congrArg SetoidHom.toFun hcomp.symm) srcElem
  rw [heq] at h
  exact (F.obj A).rel.symm h

set_option backward.isDefEq.respectTransparency false in
/--
The inverse function preserves the full equivalence relation (EqvGen of base).
-/
theorem setoidCounitInverseRaw_map_rel (A : D)
    (x y : ccrEval (setoidDensityTgt F) A)
    (h : (setoidDensityPresentation F).coeqSetoidAt A |>.r x y) :
    (F.obj A).rel.r (setoidCounitInverseRaw F A x) (setoidCounitInverseRaw F A y) := by
  induction h with
  | rel _ _ hbase =>
    obtain ⟨w, hw1, hw2⟩ := hbase
    simp only [setoidDensityPresentation_fst, setoidDensityPresentation_snd] at hw1 hw2
    have hpres := setoidCounitInverseRaw_preserves_base F A w
    simp only [ccrToFunctorMap_app] at hpres
    rw [hw1, hw2] at hpres
    exact hpres
  | refl _ =>
    exact (F.obj A).rel.refl _
  | symm _ _ _ ih =>
    exact (F.obj A).rel.symm ih
  | trans _ _ _ _ _ ih1 ih2 =>
    exact (F.obj A).rel.trans ih1 ih2

/-! ### Round-Trip Identities -/

set_option backward.isDefEq.respectTransparency false in
/--
Round-trip: inverse ∘ forward = id on F.obj A.
-/
theorem setoidCounit_inverse_forward (A : D) (x : (F.obj A).carrier) :
    setoidCounitInverseRaw F A (setoidCounitForwardRaw F A x) = x := by
  simp only [setoidCounitForwardRaw, setoidCounitInverseRaw, SetoidElements.elem]
  have h : F.map (𝟙 A) = 𝟙 (F.obj A) := F.map_id A
  simp only [h]
  rfl

/--
Round-trip: forward ∘ inverse ≈ id on ccrEval (setoidDensityTgt F) A.
The images are related via the coequalizer equivalence relation.
-/
theorem setoidCounit_forward_inverse (A : D)
    (x : ccrEval (setoidDensityTgt F) A) :
    (setoidDensityPresentation F).coeqSetoidAt A |>.r
      (setoidCounitForwardRaw F A (setoidCounitInverseRaw F A x)) x := by
  obtain ⟨⟨B, y⟩, g⟩ := x
  simp only [setoidCounitInverseRaw, setoidCounitForwardRaw, SetoidElements.elem]
  -- Goal: relate ⟨⟨A, (F.map g).toFun y⟩, 𝟙 A⟩ to ⟨⟨B, y⟩, g⟩
  -- Use morphism g : B ⟶ A with compat witnessing F.map g y ≈ F.map g y
  apply Relation.EqvGen.rel
  let srcElem : SetoidElements F := ⟨B, y⟩
  let tgtElem : SetoidElements F := ⟨A, (F.map g).toFun y⟩
  have hcompat : (F.obj tgtElem.obj).rel.r ((F.map g).toFun srcElem.elem) tgtElem.elem := by
    simp only [tgtElem, srcElem, SetoidElements.obj, SetoidElements.elem]
    exact (F.obj A).rel.refl _
  let homData : SetoidElementsHom srcElem tgtElem := ⟨g, hcompat⟩
  let mIdx : SetoidMorphismIndex F := ⟨tgtElem, srcElem, homData⟩
  let witness : ccrEval (setoidDensitySrc F) A := ⟨mIdx, 𝟙 A⟩
  use witness
  constructor
  · simp only [setoidDensityPresentation_fst, ccrToFunctorMapApp, setoidDensityFst,
      ccrHomMk, ccrReindex, ccrFiberMor, ccrEvalMk, ccrEvalIndex, ccrEvalMor,
      SetoidMorphismIndex.tgt, witness, mIdx, tgtElem, setoidDensityTgt,
      ccrObjMk_family, SetoidElements.obj]
    apply Sigma.ext
    · rfl
    · simp only [heq_eq_eq]
      exact Category.id_comp (𝟙 A)
  · simp only [setoidDensityPresentation_snd, ccrToFunctorMapApp, setoidDensitySnd,
      ccrHomMk, ccrReindex, ccrFiberMor, ccrEvalMk, ccrEvalIndex, ccrEvalMor,
      SetoidMorphismIndex.src, SetoidMorphismIndex.homData, witness, mIdx,
      srcElem, homData]
    apply Sigma.ext
    · rfl
    · simp only [heq_eq_eq]
      exact Category.comp_id g

/-! ### Setoid-Level Morphisms

The raw functions preserve equivalence relations and can be assembled into
SetoidHom morphisms. The round-trip properties are:
- inverse ∘ forward = id (exact equality)
- forward ∘ inverse ~ id (equivalent, not equal)

This gives us a "quasi-isomorphism" in SetoidCat: a pair of morphisms where
one round-trip is exact and the other is up to equivalence.
-/

/--
The forward SetoidHom from F.obj A to the setoid density presentation.
-/
def setoidCounitForwardHom (A : D) :
    SetoidHom (F.obj A) ((setoidDensityPresentation F).toSetoidBundleAt A) where
  toFun := setoidCounitForwardRaw F A
  map_rel := fun _ _ h => setoidCounitForwardRaw_map_rel F A _ _ h

/--
The inverse SetoidHom from the setoid density presentation to F.obj A.
-/
def setoidCounitInverseHom (A : D) :
    SetoidHom ((setoidDensityPresentation F).toSetoidBundleAt A) (F.obj A) where
  toFun := setoidCounitInverseRaw F A
  map_rel := fun _ _ h => setoidCounitInverseRaw_map_rel F A _ _ h

/--
The round-trip inverse ∘ forward equals identity (exact).
-/
theorem setoidCounitHom_inv_hom_id (A : D) :
    (setoidCounitInverseHom F A).comp (setoidCounitForwardHom F A) =
    SetoidHom.id (F.obj A) := by
  ext x
  exact setoidCounit_inverse_forward F A x

/--
The round-trip forward ∘ inverse is equivalent to identity.
For all x, forward(inverse(x)) ~ x in the density setoid.
-/
theorem setoidCounitHom_hom_inv_rel (A : D)
    (x : ((setoidDensityPresentation F).toSetoidBundleAt A).carrier) :
    ((setoidDensityPresentation F).toSetoidBundleAt A).rel.r
      ((setoidCounitForwardHom F A).comp (setoidCounitInverseHom F A) x) x :=
  setoidCounit_forward_inverse F A x

/--
Naturality of the forward SetoidHom up to equivalence: for f : A ⟶ B,
setoidCounitForwardHom B (F.map f x) ~ (setoidDensity F).map f (setoidCounitForwardHom A x)
in the density setoid at B.

The two sides represent the same abstract element of the copresheaf at B:
- LHS: (F.map f).toFun x at B, accessed via identity
- RHS: x at A, transported to B via f
-/
theorem setoidCounitForwardHom_natural_rel {A B : D} (f : A ⟶ B)
    (x : (F.obj A).carrier) :
    ((setoidDensityPresentation F).toSetoidBundleAt B).rel.r
      ((setoidCounitForwardHom F B).comp (F.map f) x)
      (((setoidDensityPresentation F).toSetoidCopresheafMap f).comp
        (setoidCounitForwardHom F A) x) := by
  simp only [SetoidHom.comp_apply, setoidCounitForwardHom, setoidCounitForwardRaw,
    PolyPresentation.toSetoidCopresheafMap, PolyPresentation.toSetoidCopresheafMapFun,
    ccrEvalMap]
  apply Relation.EqvGen.rel
  let srcElem : SetoidElements F := ⟨A, x⟩
  let tgtElem : SetoidElements F := ⟨B, (F.map f).toFun x⟩
  have hcompat : (F.obj tgtElem.obj).rel.r
      ((F.map f).toFun srcElem.elem) tgtElem.elem := by
    simp only [tgtElem, srcElem, SetoidElements.obj, SetoidElements.elem]
    exact (F.obj B).rel.refl _
  let homData : SetoidElementsHom srcElem tgtElem := ⟨f, hcompat⟩
  let mIdx : SetoidMorphismIndex F := ⟨tgtElem, srcElem, homData⟩
  let witness : ccrEval (setoidDensitySrc F) B := ⟨mIdx, 𝟙 B⟩
  use witness
  constructor
  · simp only [setoidDensityPresentation_fst, ccrToFunctorMapApp, setoidDensityFst,
      ccrHomMk, ccrReindex, ccrFiberMor, ccrEvalMk, ccrEvalIndex, ccrEvalMor,
      SetoidMorphismIndex.tgt, witness, mIdx, tgtElem, setoidDensityTgt,
      ccrObjMk_family, SetoidElements.obj]
    apply Sigma.ext
    · rfl
    · simp only [heq_eq_eq]
      exact Category.id_comp (𝟙 B)
  · simp only [setoidDensityPresentation_snd, ccrToFunctorMapApp, setoidDensitySnd,
      ccrHomMk, ccrReindex, ccrFiberMor, ccrEvalMk, ccrEvalIndex, ccrEvalMor,
      SetoidMorphismIndex.src, SetoidMorphismIndex.homData, witness, mIdx,
      srcElem, homData]
    apply Sigma.ext
    · rfl
    · simp only [heq_eq_eq]
      calc f ≫ 𝟙 B = f := Category.comp_id f
        _ = 𝟙 A ≫ f := (Category.id_comp f).symm

set_option backward.isDefEq.respectTransparency false in
/--
Naturality of the inverse SetoidHom (exact equality): for f : A ⟶ B,
F.map f ∘ setoidCounitInverseHom A = setoidCounitInverseHom B ∘ (setoidDensity F).map f
-/
theorem setoidCounitInverseHom_natural {A B : D} (f : A ⟶ B) :
    (F.map f).comp (setoidCounitInverseHom F A) =
    (setoidCounitInverseHom F B).comp
      ((setoidDensityPresentation F).toSetoidCopresheafMap f) := by
  ext ⟨⟨C, z⟩, g⟩
  simp only [SetoidHom.comp_apply, setoidCounitInverseHom, setoidCounitInverseRaw,
    PolyPresentation.toSetoidCopresheafMap, PolyPresentation.toSetoidCopresheafMapFun,
    ccrEvalMap, SetoidElements.elem]
  have h : F.map (g ≫ f) = F.map g ≫ F.map f := F.map_comp g f
  simp only [h]
  rfl

/-! ### Quotient-Level Isomorphism

The raw functions are inverses up to the equivalence relation, not pointwise.
To get an isomorphism, we work at the quotient level: the quotient of F.obj A
(which is Quotient (F.obj A).rel) is isomorphic to the coequalizer of the
density presentation at A.
-/

/--
The forward map descends to quotients.
Maps Quotient.mk x to the coequalizer class of ((A, x), 𝟙 A).
-/
def setoidCounitQuotientForward (A : D) :
    Quotient (F.obj A).rel →
    (setoidDensityPresentation F).toCopresheaf.obj A := by
  apply Quotient.lift
    (fun x => (setoidDensityPresentation F).toCopresheafπ.app A
      (setoidCounitForwardRaw F A x))
  intro x y hxy
  apply Quot.eqvGen_sound
  exact setoidCounitForwardRaw_map_rel F A x y hxy

/--
The inverse map descends to quotients.
Maps the coequalizer class of ((B, y), g) to Quotient.mk ((F.map g).toFun y).
-/
def setoidCounitQuotientInverse (A : D) :
    (setoidDensityPresentation F).toCopresheaf.obj A →
    Quotient (F.obj A).rel := by
  apply Quot.lift
    (fun x => Quotient.mk (F.obj A).rel (setoidCounitInverseRaw F A x))
  intro x y hxy
  apply Quotient.sound
  exact setoidCounitInverseRaw_map_rel F A x y (Relation.EqvGen.rel _ _ hxy)

/--
Round-trip: inverse ∘ forward = id at quotient level.
-/
theorem setoidCounitQuotient_inv_hom_id (A : D) :
    setoidCounitQuotientInverse F A ∘ setoidCounitQuotientForward F A = id := by
  funext x
  induction x using Quotient.ind with
  | _ x =>
    simp only [Function.comp_apply, id_eq, setoidCounitQuotientForward,
      setoidCounitQuotientInverse]
    simp only [Quotient.lift_mk, PolyPresentation.toCopresheafπ, functorCoeqπ,
      CoequalizerData.π, typeCoeqπ]
    apply Quotient.sound
    rw [setoidCounit_inverse_forward]

/--
Round-trip: forward ∘ inverse = id at quotient level.
-/
theorem setoidCounitQuotient_hom_inv_id (A : D) :
    setoidCounitQuotientForward F A ∘ setoidCounitQuotientInverse F A = id := by
  funext x
  revert x
  apply Quot.ind
  intro ⟨⟨B, y⟩, g⟩
  simp only [Function.comp_apply, id_eq, setoidCounitQuotientForward,
    setoidCounitQuotientInverse]
  simp only [PolyPresentation.toCopresheafπ, functorCoeqπ,
    CoequalizerData.π, typeCoeqπ, Quotient.lift_mk]
  apply Quot.eqvGen_sound
  exact setoidCounit_forward_inverse F A ⟨⟨B, y⟩, g⟩

/--
The quotient-level isomorphism at each component A.
-/
def setoidCounitQuotientIso (A : D) :
    Quotient (F.obj A).rel ≃ (setoidDensityPresentation F).toCopresheaf.obj A where
  toFun := setoidCounitQuotientForward F A
  invFun := setoidCounitQuotientInverse F A
  left_inv := congrFun (setoidCounitQuotient_inv_hom_id F A)
  right_inv := congrFun (setoidCounitQuotient_hom_inv_id F A)

/-! ### Naturality

The quotient-level maps form a natural transformation.
-/

/--
The forward map is natural: for f : A ⟶ B, the diagram commutes.
-/
theorem setoidCounitQuotientForward_natural {A B : D} (f : A ⟶ B) :
    (SetoidBundle.quotientFunctor.map (F.map f)) ≫
      setoidCounitQuotientForward F B =
    setoidCounitQuotientForward F A ≫
      (setoidDensityPresentation F).toCopresheaf.map f := by
  ext x
  induction x using Quotient.ind with
  | _ x =>
    simp only [types_comp_apply, SetoidBundle.quotientFunctor,
      setoidCounitQuotientForward, Quotient.map'_mk'']
    simp only [Quotient.lift_mk]
    -- LHS: π((B, (F.map f) x), 𝟙 B)
    -- RHS: (density.map f)(π((A, x), 𝟙 A))
    simp only [PolyPresentation.toCopresheaf, CoequalizerData.coeq, functorCoeq,
      PolyPresentation.toCopresheafπ, functorCoeqπ, CoequalizerData.π, typeCoeqπ,
      ccrToFunctorMap_app]
    -- Use Quot.sound via a witness
    apply Quot.sound
    -- Witness: morphism f : A ⟶ B in elements with (F.map f)(x) ≈ (F.map f)(x)
    let srcElem : SetoidElements F := ⟨A, x⟩
    let tgtElem : SetoidElements F := ⟨B, (F.map f).toFun x⟩
    have hcompat : (F.obj B).rel.r ((F.map f).toFun x) ((F.map f).toFun x) :=
      (F.obj B).rel.refl _
    let homData : SetoidElementsHom srcElem tgtElem := ⟨f, hcompat⟩
    let mIdx : SetoidMorphismIndex F := ⟨tgtElem, srcElem, homData⟩
    let witness : ccrEval (setoidDensitySrc F) B := ⟨mIdx, 𝟙 B⟩
    use witness
    constructor
    · simp only [setoidDensityPresentation_fst, ccrToFunctorMapApp, setoidDensityFst,
        ccrHomMk, ccrReindex, ccrFiberMor, ccrEvalMk, ccrEvalIndex, ccrEvalMor,
        SetoidMorphismIndex.tgt, witness, mIdx, tgtElem, setoidCounitForwardRaw,
        setoidDensityTgt, ccrObjMk_family, SetoidElements.obj]
      apply Sigma.ext
      · rfl
      · simp only [heq_eq_eq]
        exact Category.id_comp (𝟙 B)
    · simp only [setoidDensityPresentation_snd, ccrToFunctorMapApp, setoidDensitySnd,
        ccrHomMk, ccrReindex, ccrFiberMor, ccrEvalMk, ccrEvalIndex, ccrEvalMor,
        SetoidMorphismIndex.src, SetoidMorphismIndex.homData,
        witness, mIdx, srcElem, homData, setoidCounitForwardRaw, ccrToFunctor, ccrEvalMap]
      apply Sigma.ext
      · rfl
      · simp only [heq_eq_eq]
        calc f ≫ 𝟙 B = f := Category.comp_id f
          _ = 𝟙 A ≫ f := (Category.id_comp f).symm

set_option backward.isDefEq.respectTransparency false in
/--
The inverse map is natural: for f : A ⟶ B, the diagram commutes.
-/
theorem setoidCounitQuotientInverse_natural {A B : D} (f : A ⟶ B) :
    (setoidDensityPresentation F).toCopresheaf.map f ≫
      setoidCounitQuotientInverse F B =
    setoidCounitQuotientInverse F A ≫
      (SetoidBundle.quotientFunctor.map (F.map f)) := by
  ext x
  revert x
  apply Quot.ind
  intro ⟨⟨C, z⟩, g⟩
  simp only [types_comp_apply, setoidCounitQuotientInverse,
    PolyPresentation.toCopresheaf, CoequalizerData.coeq, functorCoeq,
    ccrToFunctorMap_app]
  simp only [SetoidBundle.quotientFunctor, Quotient.map'_mk'']
  apply Quotient.sound
  simp only [ccrToFunctor, ccrEvalMap, setoidCounitInverseRaw, SetoidElements.elem]
  -- Goal: (F.obj B).rel.r ((F.map (g ≫ f)) z) ((F.map f) ((F.map g) z))
  have hcomp : F.map (g ≫ f) = F.map g ≫ F.map f := F.map_comp g f
  simp only [hcomp]
  exact (F.obj B).rel.refl _

/--
The forward natural transformation from the quotient functor ⋙ F to the
density presentation's coequalizer.
-/
def setoidCounitForwardNatTrans :
    F ⋙ SetoidBundle.quotientFunctor ⟶
    (setoidDensityPresentation F).toCopresheaf where
  app := setoidCounitQuotientForward F
  naturality := fun _ _ f => setoidCounitQuotientForward_natural F f

/--
The inverse natural transformation from the density presentation's coequalizer
to the quotient functor applied to F.
-/
def setoidCounitInverseNatTrans :
    (setoidDensityPresentation F).toCopresheaf ⟶
    F ⋙ SetoidBundle.quotientFunctor where
  app := setoidCounitQuotientInverse F
  naturality := fun _ _ f => setoidCounitQuotientInverse_natural F f

/-! ### The Counit Isomorphism -/

/--
The counit isomorphism: the quotient of F is naturally isomorphic to the
coequalizer of the setoid density presentation.

This completes the counit direction of the equivalence between polynomial
presentations and Setoid-valued copresheaves.
-/
def setoidCounitIso :
    F ⋙ SetoidBundle.quotientFunctor ≅ (setoidDensityPresentation F).toCopresheaf :=
  NatIso.ofComponents
    (fun A => (setoidCounitQuotientIso F A).toIso)
    (fun f => setoidCounitQuotientForward_natural F f)

end SetoidCounit

/-! ## Full Equivalence Assembly

We now assemble the equivalence `PolyPresentationLoc D ≌ (D ⥤ Type)`.

The components are:
- Evaluation functor: polyPresentationLocEvalFunctor
- Density functor: densityPresentationFunctor (already defined above)
- Counit: densityIso provides E ∘ S ≅ Id
- Unit: setoidComparisonIso provides the constructive foundation for S ∘ E ≅ Id

The setoid-based constructions (`setoidComparisonIso`, `setoidCounitIso`)
provide the constructive foundation. The Type-valued equivalence follows
because the evaluation functor is faithful.
-/

section EquivalenceAssembly

variable {D : Type u} [Category.{v} D]

/-! ### Counit Natural Isomorphism

The counit shows that E ∘ S ≅ Id, i.e., for any copresheaf F,
(densityPresentation F).toCopresheaf ≅ F.
-/

set_option backward.isDefEq.respectTransparency false in
/--
The counit isomorphism at each copresheaf F.
This is exactly densityIso F, showing that the density presentation's
coequalizer is naturally isomorphic to the original copresheaf.
-/
def polyPresentationEquivCounitIso :
    densityPresentationFunctor (D := D) ⋙ polyPresentationLocEvalFunctor ≅
    𝟭 (D ⥤ Type (max u w v)) :=
  NatIso.ofComponents
    (fun F => densityIso F)
    (fun {F G} α => by
      ext A x
      revert x
      apply Quot.ind
      intro ⟨p, g⟩
      simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map,
        NatTrans.comp_app, types_comp_apply]
      simp only [polyPresentationLocEvalFunctor, densityPresentationFunctor]
      dsimp only [PolyPresentationLoc.Hom.toInducedMap', PolyPresentationLoc.Hom.mk',
        PolyPresentationQ.Hom.toInducedMap, PolyPresentation.Hom.toQHom,
        PolyPresentation.toCopresheaf, CoequalizerData.desc, CoequalizerData.π,
        functorCoeqDesc, functorCoeq, typeCoeqDesc, typeCoeqπ,
        PolyPresentation.toCopresheafπ, functorCoeqπ,
        densityIso, NatIso.ofComponents]
      simp only [NatTrans.comp_app, ccrToFunctorMap_app, types_comp_apply]
      dsimp only [densityToFunctorApp, ccrToFunctorMapApp, densityPresentationMap,
        densityTgtMap, ccrEvalMk, ccrEvalIndex, ccrEvalMor,
        ccrReindex, ccrFiberMor, ccrHomMk, densityElementsObj]
      rw [show 𝟙 (ccrFamily (densityTgt G) ⟨p.fst, α.app p.fst p.snd⟩) ≫ g = g
            from Category.id_comp g]
      simp only [densityTgt_family]
      exact (congrFun (α.naturality g) p.snd).symm)

/-! ### Unit Natural Isomorphism

For the unit, we need S ∘ E ≅ Id on PolyPresentationLoc. For each presentation X,
we need X ≅ densityPresentation(X.toCopresheaf) in PolyPresentationLoc.

The setoid comparison provides this constructively:
setoidComparisonIso : X ≅ setoidDensityPresentation(X.toSetoidCopresheaf)

Combined with the relationship between setoid and Type density presentations
(through the quotient), this gives the required unit isomorphism.

We work with the universe level `max u v` where the setoid machinery applies.
-/

section UnitIsomorphism

variable (X : PolyPresentation.{u, v, max u v} D)

/-! #### Quotient Morphism from Setoid to Type Density

The quotient map on elements induces a morphism from setoidDensityPresentation
to densityPresentation. This morphism's induced map is an isomorphism since
both presentations have coequalizers isomorphic to X.toCopresheaf.
-/

/--
Map a setoid element to a type element via the quotient.
-/
def setoidToTypeDensityTgtReindex
    (p : SetoidElements X.toSetoidCopresheaf) :
    (X.toCopresheaf).Elements :=
  ⟨p.obj, X.toCopresheafπ.app p.obj p.elem⟩

/--
The target homomorphism from setoid density to type density.
-/
def setoidToTypeDensityTgtHom :
    setoidDensityTgt X.toSetoidCopresheaf ⟶ densityTgt X.toCopresheaf :=
  ccrHomMk
    (setoidToTypeDensityTgtReindex X)
    (fun _ => 𝟙 _)

@[simp]
theorem setoidToTypeDensityTgtHom_reindex
    (p : SetoidElements X.toSetoidCopresheaf) :
    ccrReindex (setoidToTypeDensityTgtHom X) p =
    setoidToTypeDensityTgtReindex X p := rfl

@[simp]
theorem setoidToTypeDensityTgtHom_fiberMor
    (p : SetoidElements X.toSetoidCopresheaf) :
    ccrFiberMor (setoidToTypeDensityTgtHom X) p = 𝟙 _ := rfl

set_option backward.isDefEq.respectTransparency false in
/--
The setoid-to-type morphism respects the coequalization condition.
-/
theorem setoidToTypeDensityTgtHom_respects :
    ccrToFunctorMap (setoidDensityPresentation X.toSetoidCopresheaf).fst ≫
      ccrToFunctorMap (setoidToTypeDensityTgtHom X) ≫
      (densityPresentation X.toCopresheaf).toCopresheafπ =
    ccrToFunctorMap (setoidDensityPresentation X.toSetoidCopresheaf).snd ≫
      ccrToFunctorMap (setoidToTypeDensityTgtHom X) ≫
      (densityPresentation X.toCopresheaf).toCopresheafπ := by
  ext A ⟨mIdx, g⟩
  simp only [NatTrans.comp_app, types_comp_apply, ccrToFunctorMap_app,
    ccrToFunctorMapApp]
  apply densityCoeq_eq_of_toFunctor_eq
  simp only [densityToFunctorApp, ccrEvalMk, ccrEvalIndex, ccrEvalMor,
    setoidDensityPresentation, setoidDensityFst, setoidDensitySnd,
    setoidToTypeDensityTgtHom, ccrHomMk, ccrReindex, ccrFiberMor,
    setoidToTypeDensityTgtReindex, SetoidMorphismIndex.tgt,
    SetoidMorphismIndex.src, SetoidMorphismIndex.homData,
    SetoidElements.obj, SetoidElements.elem, densityTgt_family]
  simp only [Category.id_comp]
  -- p = mIdx.fst (target), q = mIdx.snd.fst (source), homData = mIdx.snd.snd
  -- Goal: F.map g (π(p.obj, p.elem)) = F.map (hom ≫ g) (π(q.obj, q.elem))
  -- By naturality of π:
  --   F.map g (π(p.obj, p.elem)) = π(A, ccrEvalMap g p.elem)
  --   F.map (hom ≫ g) (π(q.obj, q.elem)) = π(A, ccrEvalMap (hom ≫ g) q.elem)
  -- Then show: π(A, ccrEvalMap g p.elem) = π(A, ccrEvalMap (hom ≫ g) q.elem)
  -- By compat: ccrEvalMap hom q.elem ~ p.elem
  -- So ccrEvalMap g (ccrEvalMap hom q.elem) ~ ccrEvalMap g p.elem
  have hnat_lhs := congrFun (X.toCopresheafπ.naturality g) mIdx.fst.snd
  simp only [types_comp_apply, ccrToFunctor, ccrEvalMap] at hnat_lhs
  have hnat_rhs := congrFun (X.toCopresheafπ.naturality
      (mIdx.snd.snd.hom ≫ g)) mIdx.snd.fst.snd
  simp only [types_comp_apply, ccrToFunctor, ccrEvalMap] at hnat_rhs
  -- Normalize goal to match hnat lemmas (definitionally equal but syntactically
  -- different due to unfolding of ccrFamily vs sigma projections)
  change X.toCopresheaf.map g
      (X.toCopresheafπ.app
        (ccrFamily (setoidDensityPresentation X.toSetoidCopresheaf).src mIdx)
        mIdx.fst.snd) =
    X.toCopresheaf.map (mIdx.snd.snd.hom ≫ g)
      (X.toCopresheafπ.app mIdx.snd.fst.obj mIdx.snd.fst.snd)
  rw [hnat_lhs.symm, hnat_rhs.symm]
  simp only [PolyPresentation.toCopresheafπ, functorCoeqπ, CoequalizerData.π, typeCoeqπ]
  apply Quot.eqvGen_sound
  -- The compatibility mIdx.snd.snd.compat states that mapping by hom gives
  -- equivalent elements. Transporting by g preserves this equivalence.
  have compat := mIdx.snd.snd.compat
  simp only [PolyPresentation.toSetoidCopresheaf, PolyPresentation.toSetoidBundleAt,
    PolyPresentation.coeqSetoidAt, PolyPresentation.toSetoidCopresheafMap,
    PolyPresentation.toSetoidCopresheafMapFun, ccrEvalMap] at compat
  have transported := X.coeqSetoidAt_map g compat
  simp only [ccrEvalMap] at transported
  -- Both relations (typeCoeqRel and coeqRelAt) are definitionally equal
  -- The goal terms and transported terms differ only in match expression structure
  change Relation.EqvGen (X.coeqRelAt A) _ _
  -- Destruct the sigma types with equations to propagate to transported
  rcases h_src : mIdx.snd.fst.snd with ⟨i_src, f_src⟩
  rcases h_tgt : mIdx.fst.snd with ⟨i_tgt, f_tgt⟩
  -- Substitute in transported: .elem = .snd, then use equations h_src, h_tgt
  simp only [SetoidElements.elem, h_src, h_tgt, Category.assoc] at transported ⊢
  exact transported.symm

/--
The Q-morphism from setoid density to type density.
-/
def setoidToTypeDensityQ :
    PolyPresentationQ.Hom
      (setoidDensityPresentation X.toSetoidCopresheaf).toQ
      (densityPresentation X.toCopresheaf).toQ where
  tgtHom := setoidToTypeDensityTgtHom X
  respects := setoidToTypeDensityTgtHom_respects X

set_option backward.isDefEq.respectTransparency false in
/--
The induced map of the setoid-to-type morphism equals the composition of
setoidInverseIso.hom with densityIso.inv.
-/
theorem setoidToTypeDensityQ_toInducedMap :
    (setoidToTypeDensityQ X).toInducedMap =
    (setoidInverseIso X).hom ≫ (densityIso X.toCopresheaf).inv := by
  -- The induced map of setoidToTypeDensityQ equals composition of:
  -- 1. setoidInverseIso.hom: setoidDensity.toCopresheaf → X.toCopresheaf
  -- 2. densityIso.inv: X.toCopresheaf → densityPresentation.toCopresheaf
  -- Both go from setoidDensity.toCopresheaf to typeDensity.toCopresheaf
  -- The equality follows by uniqueness of the coequalizer descending map:
  -- both sides factor setoidDensity.π through the same composition with density.π
  symm
  apply CoequalizerData.uniq
  ext A ⟨p, g⟩
  simp only [NatTrans.comp_app, types_comp_apply, PolyPresentation.toCopresheafπ]
  -- Use setoidInverseIso factorization: π ≫ hom = tgtHom ≫ X.π
  have h_fac := PolyPresentationQ.Hom.toInducedMap_fac (setoidInverseQ X)
  simp only [PolyPresentation.toCopresheafπ, PolyPresentationQ.toPres,
    PolyPresentation.toQ] at h_fac
  have h_fac_app := congrFun (congrArg NatTrans.app h_fac) A
  -- Get element-level equality by applying to ⟨p, g⟩
  have h_fac_elem := congrFun h_fac_app ⟨p, g⟩
  simp only [NatTrans.comp_app, types_comp_apply] at h_fac_elem
  rw [show (setoidInverseIso X).hom = (setoidInverseQ X).toInducedMap from rfl]
  rw [h_fac_elem]
  simp only [ccrToFunctorMap_app, ccrToFunctorMapApp, ccrReindex, ccrFiberMor]
  -- Unfold setoidInverseQ and the tgtHom components
  simp only [setoidInverseQ, setoidInverseTgtHom, ccrHomMk, setoidInverseTgtBase,
    setoidInverseTgtFiber, SetoidElements.obj, SetoidElements.elem]
  -- Now apply densityIso.inv definition
  simp only [densityIso, NatIso.ofComponents_inv_app, Function.comp_apply,
    functorToDensityApp, setoidToTypeDensityQ, setoidToTypeDensityTgtHom,
    setoidToTypeDensityTgtReindex]
  -- Simplify setoidToTypeDensityTgtReindex to match setoidDensityPresentation forms
  simp only [SetoidElements.obj]
  -- Both are in the density coequalizer; show they're equal via naturality
  apply densityCoeq_eq_of_toFunctor_eq
  simp only [densityToFunctorApp, ccrEvalMk, ccrEvalIndex, ccrEvalMor, densityTgt_family]
  rw [X.toCopresheaf.map_id]
  simp only [types_id_apply]
  have hnat := congrFun (X.toCopresheafπ.naturality g) ⟨p.elem.fst, p.elem.snd⟩
  simp only [types_comp_apply, PolyPresentation.toCopresheafπ,
    CoequalizerData.π, functorCoeqπ, typeCoeqπ, PolyPresentation.toCopresheaf,
    CoequalizerData.coeq, ccrToFunctor, ccrEvalMap, functorCoeq,
    SetoidElements.elem, ccrFamily, setoidDensityPresentation, setoidDensityTgt,
    ccrObjMk] at hnat ⊢
  conv_rhs => rw [show 𝟙 p.fst ≫ g = g from Category.id_comp g]
  convert hnat using 2

set_option backward.isDefEq.respectTransparency false in
/--
The setoid-to-type morphism's induced map is an isomorphism.
-/
theorem setoidToTypeDensityQ_isIso :
    IsIso (setoidToTypeDensityQ X).toInducedMap := by
  rw [setoidToTypeDensityQ_toInducedMap]
  infer_instance

/--
The localized morphism from setoid density to type density.
-/
def setoidToTypeDensityLoc :
    PolyPresentationLoc.ofPres (setoidDensityPresentation X.toSetoidCopresheaf) ⟶
    PolyPresentationLoc.ofPres (densityPresentation X.toCopresheaf) :=
  PolyPresentationLoc.Hom.mk' (setoidToTypeDensityQ X)

/-! #### The Setoid-to-Type Morphism is an Isomorphism

Since the evaluation functor is faithful and the induced map is an isomorphism,
the morphism setoidToTypeDensityLoc is an isomorphism in PolyPresentationLoc.
-/

/-! #### The Type-Density Comparison Morphism

The composition of setoidComparisonQ with setoidToTypeDensityQ gives a morphism
from X to the type density presentation, whose induced map equals densityIso.inv.
-/

/--
The Q-morphism from X to the type density presentation, obtained by composing
the setoid comparison with the setoid-to-type morphism.
-/
def typeComparisonQ :
    PolyPresentationQ.Hom X.toQ (densityPresentation X.toCopresheaf).toQ :=
  setoidComparisonQ X ≫ setoidToTypeDensityQ X

set_option backward.isDefEq.respectTransparency false in
/--
The induced map of typeComparisonQ equals densityIso.inv.
-/
theorem typeComparisonQ_toInducedMap :
    (typeComparisonQ X).toInducedMap = (densityIso X.toCopresheaf).inv := by
  unfold typeComparisonQ
  rw [PolyPresentationQ.Hom.toInducedMap_comp]
  rw [setoidComparisonQ_toInducedMap, setoidToTypeDensityQ_toInducedMap]
  -- Goal: setoidForwardMap X ≫ (setoidInverseIso X).hom ≫ densityIso.inv = densityIso.inv
  -- Note: (setoidInverseIso X).hom = setoidInverseInducedMap X
  rw [show (setoidInverseIso X).hom = setoidInverseInducedMap X from rfl]
  rw [← Category.assoc, setoidForward_inverse_id]
  exact Category.id_comp _

/--
The typeComparisonQ induced map is an isomorphism.
-/
theorem typeComparisonQ_isIso :
    IsIso (typeComparisonQ X).toInducedMap := by
  rw [typeComparisonQ_toInducedMap]
  infer_instance

/--
The localized morphism from X to the type density presentation.
-/
def typeComparisonLoc :
    PolyPresentationLoc.ofPres X ⟶
    PolyPresentationLoc.ofPres (densityPresentation X.toCopresheaf) :=
  PolyPresentationLoc.Hom.mk' (typeComparisonQ X)

/--
The type comparison equals the composition of setoid comparison and
setoid-to-type in the localized category.
-/
theorem typeComparisonLoc_eq :
    typeComparisonLoc X = setoidComparisonLoc X ≫ setoidToTypeDensityLoc X := by
  unfold typeComparisonLoc setoidComparisonLoc setoidToTypeDensityLoc typeComparisonQ
  unfold PolyPresentationLoc.Hom.mk'
  dsimp only [CategoryStruct.comp,
    PolyPresentationLoc.category]
  apply Quot.sound
  unfold PolyPresentationQ.Hom.equiv
  rfl

/-! #### Constructive Limitations

To complete the equivalence as a full isomorphism in PolyPresentationLoc,
we would need an inverse morphism from densityPresentation back to X.
The inverse induced map is densityIso.hom.

The construction of a Q-morphism with this induced map would require mapping
from quotient elements (in X.toCopresheaf.Elements) back to presentation indices
(in X.tgt.index). This requires choosing representatives from the quotient,
which is non-constructive.

Specifically:
- X.toCopresheaf.obj A = Quotient (coequalizer relation on ccrEval X.tgt A)
- X.toCopresheaf.Elements = Σ A, Quotient (...)
- To define a Q-morphism densityPresentation → X, we need a function
  X.toCopresheaf.Elements → X.tgt.index
- This function must be well-defined on quotients, but extracting an index
  from a quotient class requires choosing a representative.

What we CAN prove constructively:
1. The forward morphism (unitMorphism) exists and has induced map densityIso.inv
2. The induced map is an isomorphism
3. The compositions at the INDUCED MAP level satisfy the triangle identities

What we CANNOT prove constructively:
- The existence of an inverse morphism in PolyPresentationLoc
- Therefore, the full unit isomorphism X ≅ densityPresentation(X.toCopresheaf)
-/

/--
The composition typeComparisonQ.toInducedMap ≫ densityIso.hom = identity.
This is one triangle identity at the induced map level.
-/
theorem typeComparison_densityIso_id :
    (typeComparisonQ X).toInducedMap ≫ (densityIso X.toCopresheaf).hom =
      𝟙 X.toCopresheaf := by
  rw [typeComparisonQ_toInducedMap]
  exact (densityIso X.toCopresheaf).inv_hom_id

/-! #### Quasi-Inverse Structure

Since the full unit isomorphism cannot be constructed constructively
(the inverse direction requires going from quotient back to pre-quotient),
we establish a weaker "quasi-inverse" structure that captures what IS
constructively provable.
-/

/--
The unit morphism at a presentation X: the comparison morphism from X to
its density presentation. This is the constructive part of the unit.
-/
def unitMorphism :
    PolyPresentationLoc.ofPres X ⟶
    PolyPresentationLoc.ofPres (densityPresentation X.toCopresheaf) :=
  typeComparisonLoc X

/--
The unit morphism's induced map equals densityIso.inv.
-/
theorem unitMorphism_toInducedMap :
    PolyPresentationLoc.Hom.toInducedMap' (unitMorphism X) =
    (densityIso X.toCopresheaf).inv := by
  unfold unitMorphism typeComparisonLoc PolyPresentationLoc.Hom.mk'
  unfold PolyPresentationLoc.Hom.toInducedMap'
  exact typeComparisonQ_toInducedMap X

/--
The unit morphism has an isomorphism as its induced map.
This is the constructive content: while we cannot construct the inverse
morphism in PolyPresentationLoc without going from quotient
to representative, the induced map IS an isomorphism.
-/
theorem unitMorphism_inducedMap_isIso :
    IsIso (PolyPresentationLoc.Hom.toInducedMap' (unitMorphism X)) := by
  rw [unitMorphism_toInducedMap]
  infer_instance

end UnitIsomorphism

end EquivalenceAssembly

/-! ## Setoid Equivalence Data

We record the constructive data for the setoid equivalence between
`PolyPresentationLoc D` and `D ⥤ SetoidBundle`.

The full functor `PolyPresentationLoc → (D ⥤ SetoidBundle)` on morphisms is
problematic: different representatives of the same morphism class give different
(though related) natural transformations at the setoid level. The equivalence
relation identifies morphisms with the same induced map on quotients, but the
pre-quotient data (reindex, fiberMor) differs.

What we CAN prove constructively:
1. Object-level correspondences in both directions
2. Counit isomorphism: X ≅ setoidDensityPresentation(X.toSetoidCopresheaf)
   in PolyPresentationLoc
3. Unit setoid natural isomorphism: F ↔ (setoidDensityPresentation F).toSetoidCopresheaf
   with naturality up to setoid equivalence
-/

section SetoidEquivalenceData

variable {D : Type u} [Category.{v} D]

/--
Object-level map from PolyPresentationLoc to setoid copresheaves.
-/
def polyPresentationLocToSetoidCopresheafObj
    (X : PolyPresentationLoc.{u, v, max u v} D) :
    D ⥤ SetoidBundle.{max u v} :=
  X.toPres.toSetoidCopresheaf

/--
Object-level map from setoid copresheaves to PolyPresentationLoc.
-/
def setoidCopresheafToPolyPresentationLocObj
    (F : D ⥤ SetoidBundle.{max u v}) :
    PolyPresentationLoc.{u, v, max u v} D :=
  PolyPresentationLoc.ofPres (setoidDensityPresentation F)

/--
The counit isomorphism: for each X in PolyPresentationLoc, we have
X ≅ setoidDensityPresentation(X.toSetoidCopresheaf).
This is the setoidComparisonIso.
-/
def setoidEquivCounitIsoComponent (X : PolyPresentationLoc.{u, v, max u v} D) :
    setoidCopresheafToPolyPresentationLocObj
      (polyPresentationLocToSetoidCopresheafObj X) ≅ X :=
  (setoidComparisonIso X.toPres).symm

/--
The unit setoid natural isomorphism: for each F : D ⥤ SetoidBundle,
we have a SetoidNatIso between F and the round-trip through PolyPresentationLoc.
-/
def setoidEquivUnitIsoComponent (F : D ⥤ SetoidBundle.{max u v}) :
    SetoidNatIso F
      (polyPresentationLocToSetoidCopresheafObj
        (setoidCopresheafToPolyPresentationLocObj F)) where
  hom := {
    app := fun A => setoidCounitForwardHom F A
    naturality_rel := fun f x => setoidCounitForwardHom_natural_rel F f x
  }
  inv := {
    app := fun A => setoidCounitInverseHom F A
    naturality_rel := fun {A B} f x => by
      have h := setoidCounitInverseHom_natural (F := F) f
      change (F.obj B).rel.r
        ((setoidCounitInverseHom F B).toFun
          (((setoidDensityPresentation F).toSetoidCopresheaf.map f).toFun x))
        ((F.map f).toFun ((setoidCounitInverseHom F A).toFun x))
      have h' : ((F.map f).comp (setoidCounitInverseHom F A)).toFun x =
          ((setoidCounitInverseHom F B).comp
            ((setoidDensityPresentation F).toSetoidCopresheafMap f)).toFun x := by
        rw [h]
      simp only [SetoidHom.comp_apply,
        PolyPresentation.toSetoidCopresheaf] at h' ⊢
      rw [← h']
  }
  inv_hom_id := fun A => setoidCounitHom_inv_hom_id F A
  hom_inv_rel := fun A x => setoidCounitHom_hom_inv_rel F A x

/-!
### Summary of Constructive Content

The setoid equivalence data establishes:

1. **Object bijection**: PolyPresentationLoc objects correspond to setoid
   copresheaves via `polyPresentationLocToSetoidCopresheafObj` and
   `setoidCopresheafToPolyPresentationLocObj`.

2. **Counit**: For each presentation X, we have an isomorphism
   `setoidEquivCounitIsoComponent X : setoidDensity(X.toSetoidCopresheaf) ≅ X`
   in PolyPresentationLoc. This is strict (a true isomorphism in the category).

3. **Unit**: For each setoid copresheaf F, we have a SetoidNatIso
   `setoidEquivUnitIsoComponent F : F ↔ setoidDensity(F).toSetoidCopresheaf`
   where:
   - The inverse direction (evaluating density elements) is exact
   - The forward direction (embedding into density) satisfies naturality up to
     the setoid equivalence relation

This captures the constructive content of the equivalence without requiring
choice principles to go from quotients to representatives.
-/

end SetoidEquivalenceData

end GebLean
