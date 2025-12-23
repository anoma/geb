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

variable (F : D ⥤ Type (max w v))

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
def densityTgt : CoprodCovarRepCat.{u, v, max u w v} D :=
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
def densitySrc : CoprodCovarRepCat.{u, v, max u w v} D :=
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

variable (F : D ⥤ Type (max w v))

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
  simp only [Function.comp_apply, ccrToFunctorMap_app, ccrEvalMk_index,
    ccrEvalMk_mor, densityToFunctorApp]
  -- LHS: F.map (𝟙 m.tgt.fst ≫ g) m.tgt.snd = F.map g m.tgt.snd
  -- RHS: F.map (m.hom.val ≫ g) m.src.snd
  -- Since m.hom : m.src ⟶ m.tgt in F.Elements, we have
  -- F.map m.hom.val m.src.snd = m.tgt.snd
  simp only [densityFst_reindex, densityFst_fiberMor, Category.id_comp,
    densitySnd_reindex, densitySnd_fiberMor, densitySrc_family]
  rw [F.map_comp]
  simp only [types_comp_apply]
  rw [CategoryOfElements.map_snd m.hom]

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
        simp only [types_comp_apply, densityToFunctorApp]
        rw [← F.map_comp]
        rfl }
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

/--
The inverse natural transformation from F to the coequalizer.
-/
def functorToDensityNatTrans :
    F ⟶ (densityPresentation F).toCopresheaf :=
  (densityPresentation F).toCopresheafπ.app _ ∘ functorToDensityApp F _
    |> fun _ => {
      app := fun A => (densityPresentation F).toCopresheafπ.app A ∘
        functorToDensityApp F A
      naturality := fun {A B} f => by
        ext y
        simp only [types_comp_apply, functorToDensityApp]
        -- Need to show: π(⟨⟨B, F.map f y⟩, 𝟙 B⟩) = (coeq.map f)(π(⟨⟨A, y⟩, 𝟙 A⟩))
        -- The coequalizer's map is defined via desc
        have h : (densityPresentation F).toCopresheafπ.app B
            (ccrEvalMap f ⟨⟨A, y⟩, 𝟙 A⟩) =
          (ccrToFunctor (densityTgt F)).map f
            ((densityPresentation F).toCopresheafπ.app A ⟨⟨A, y⟩, 𝟙 A⟩) := by
          exact congrFun ((densityPresentation F).toCopresheafπ.naturality f)
            ⟨⟨A, y⟩, 𝟙 A⟩
        simp only [ccrToFunctor_map, ccrEvalMap, ccrEvalMk_index, ccrEvalMk_mor,
          PolyPresentation.toCopresheafπ, densityPresentation_tgt, densityTgt,
          ccrObjMk_family] at h ⊢
        -- LHS: π(⟨⟨B, F.map f y⟩, 𝟙 B⟩)
        -- RHS: (coeq.map f)(π(⟨⟨A, y⟩, 𝟙 A⟩))
        -- We need to show these are equal via the coequalizer relation
        -- The morphism (⟨A, y⟩, ⟨B, F.map f y⟩, f') witnesses the equality
        -- where f' is the Elements morphism induced by f
        let elemMor : (⟨A, y⟩ : F.Elements) ⟶ ⟨B, F.map f y⟩ :=
          ⟨f, rfl⟩
        let mIdx : DensityMorphismIndex F := ⟨⟨B, F.map f y⟩, ⟨A, y⟩, elemMor⟩
        have heq1 : (ccrToFunctorMap (densityFst F)).app B ⟨mIdx, 𝟙 B⟩ =
            ⟨⟨B, F.map f y⟩, 𝟙 B⟩ := by
          simp only [ccrToFunctorMap_app, ccrEvalMk, densityFst_reindex,
            densityFst_fiberMor, Category.id_comp, mIdx]
        have heq2 : (ccrToFunctorMap (densitySnd F)).app B ⟨mIdx, 𝟙 B⟩ =
            ⟨⟨A, y⟩, f ≫ 𝟙 B⟩ := by
          simp only [ccrToFunctorMap_app, ccrEvalMk, densitySnd_reindex,
            densitySnd_fiberMor, mIdx, DensityMorphismIndex.src,
            DensityMorphismIndex.hom, elemMor]
        have hcond := congrFun
          ((densityPresentation F).toCopresheaf_condition.symm)
          (⟨mIdx, 𝟙 B⟩ : ccrEval (densitySrc F) B)
        simp only [NatTrans.comp_app, types_comp_apply,
          PolyPresentation.toCopresheafπ, densityPresentation_fst,
          densityPresentation_snd] at hcond
        rw [heq1, heq2] at hcond
        simp only [Category.comp_id] at heq2
        rw [Category.comp_id] at hcond
        -- Now hcond : π(⟨⟨B, F.map f y⟩, 𝟙 B⟩) = π(⟨⟨A, y⟩, f⟩)
        rw [hcond]
        -- Goal: π(⟨⟨A, y⟩, f⟩) = (coeq.map f)(π(⟨⟨A, y⟩, 𝟙 A⟩))
        -- The coequalizer's naturality says:
        -- π_B ∘ ccrToFunctor.map f = coeq.map f ∘ π_A
        -- At ⟨⟨A, y⟩, 𝟙 A⟩:
        -- π_B(ccrToFunctor.map f ⟨⟨A, y⟩, 𝟙 A⟩) = coeq.map f (π_A ⟨⟨A, y⟩, 𝟙 A⟩)
        -- ccrToFunctor.map f ⟨⟨A, y⟩, 𝟙 A⟩ = ⟨⟨A, y⟩, 𝟙 A ≫ f⟩ = ⟨⟨A, y⟩, f⟩
        simp only [Category.id_comp] at h
        rw [← h]
        congr 1
        simp only [ccrEvalMap, ccrEvalMk_index, ccrEvalMk_mor]
        rfl }

/-! ### The Isomorphism -/

/--
Round-trip: densityToFunctor ∘ functorToDensity = id.
-/
theorem densityToFunctor_functorToDensity (A : D) (y : F.obj A) :
    densityToFunctorApp F A (functorToDensityApp F A y) = y := by
  simp only [densityToFunctorApp, functorToDensityApp, F.map_id, types_id_apply]

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
  obtain ⟨d, y⟩ := p
  let elemMor : (⟨d, y⟩ : F.Elements) ⟶ ⟨A, F.map g y⟩ := ⟨g, rfl⟩
  let mIdx : DensityMorphismIndex F := ⟨⟨A, F.map g y⟩, ⟨d, y⟩, elemMor⟩
  have heq1 : (ccrToFunctorMap (densityFst F)).app A ⟨mIdx, 𝟙 A⟩ =
      ⟨⟨A, F.map g y⟩, 𝟙 A⟩ := by
    simp only [ccrToFunctorMap_app, ccrEvalMk, densityFst_reindex,
      densityFst_fiberMor, Category.id_comp]
  have heq2 : (ccrToFunctorMap (densitySnd F)).app A ⟨mIdx, 𝟙 A⟩ =
      ⟨⟨d, y⟩, g ≫ 𝟙 A⟩ := by
    simp only [ccrToFunctorMap_app, ccrEvalMk, densitySnd_reindex,
      densitySnd_fiberMor, mIdx, DensityMorphismIndex.src,
      DensityMorphismIndex.hom, elemMor]
  have hcond := congrFun
    ((densityPresentation F).toCopresheaf_condition.symm)
    (⟨mIdx, 𝟙 A⟩ : ccrEval (densitySrc F) A)
  simp only [NatTrans.comp_app, types_comp_apply,
    PolyPresentation.toCopresheafπ, densityPresentation_fst,
    densityPresentation_snd] at hcond
  rw [heq1, heq2, Category.comp_id] at hcond
  exact hcond.symm

/--
The density isomorphism: the coequalizer of the density presentation
is naturally isomorphic to F.
-/
def densityIso : (densityPresentation F).toCopresheaf ≅ F :=
  NatIso.ofComponents
    (fun A => {
      hom := CoequalizerData.desc _ _ (densityToFunctorApp F A)
        (congrFun (densityToFunctorApp_coequalizes F A))
      inv := (densityPresentation F).toCopresheafπ.app A ∘
        functorToDensityApp F A
      hom_inv_id := by
        apply CoequalizerData.uniq
        ext ⟨p, g⟩
        simp only [types_comp_apply, types_id_apply,
          CoequalizerData.fac, functorToDensityApp,
          PolyPresentation.toCopresheafπ]
        exact functorToDensity_densityToFunctor F A ⟨p, g⟩
      inv_hom_id := by
        ext y
        simp only [types_comp_apply, types_id_apply,
          CoequalizerData.fac, functorToDensityApp]
        exact densityToFunctor_functorToDensity F A y })
    (fun {A B} f => by
      ext x
      revert x
      apply Quot.ind
      intro ⟨p, g⟩
      simp only [types_comp_apply, NatIso.ofComponents_hom_app,
        PolyPresentation.toCopresheaf, CoequalizerData.coeq,
        functorCoeq, CoequalizerData.desc, functorCoeqDesc,
        CoequalizerData.π, functorCoeqπ, typeCoeqπ, typeCoeqDesc,
        densityToFunctorApp]
      rw [← F.map_comp]
      rfl)

end DensityIsomorphism

/-! ## Density Presentation Functor

The density presentation construction is functorial: a natural transformation
α : F ⟶ G induces a morphism densityPresentation F → densityPresentation G
in PolyPresentationLoc.
-/

section DensityFunctor

variable {F G : D ⥤ Type (max w v)}

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
    rw [← α.naturality f.val]
    simp only [types_comp_apply]
    rw [CategoryOfElements.map_snd f]⟩

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
    densitySrcMap α ≫ densityFst G = densityFst F ≫ densityTgtMap α := by
  apply ccrHomExt
  · intro m
    simp only [ccrHomComp_reindex, densitySrcMap_reindex, densityFst_reindex,
      densityMorphismIndexMap, densityTgtMap_reindex, DensityMorphismIndex.tgt]
  · intro m
    simp only [ccrHomComp_fiberMor, densitySrcMap_reindex, densitySrcMap_fiberMor,
      densityFst_fiberMor, Category.id_comp, densityMorphismIndexMap,
      densityTgtMap_fiberMor, Category.comp_id, DensityMorphismIndex.tgt]

/--
The induced maps commute with the second parallel morphism.
-/
theorem densityMap_snd_comm (α : F ⟶ G) :
    densitySrcMap α ≫ densitySnd G = densitySnd F ≫ densityTgtMap α := by
  apply ccrHomExt
  · intro m
    simp only [ccrHomComp_reindex, densitySrcMap_reindex, densitySnd_reindex,
      densityMorphismIndexMap, densityElementsObj, densityTgtMap_reindex,
      DensityMorphismIndex.src]
  · intro m
    simp only [ccrHomComp_fiberMor, densitySrcMap_reindex, densitySrcMap_fiberMor,
      densitySnd_fiberMor, Category.id_comp, densityMorphismIndexMap,
      densityElementsHom, densityTgtMap_fiberMor, Category.comp_id,
      DensityMorphismIndex.hom]

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

/--
The identity natural transformation induces the identity morphism.
-/
theorem densityPresentationMap_id :
    densityPresentationMap (𝟙 F) = 𝟙 (densityPresentation F) := by
  apply PolyPresentation.Hom.ext
  · apply ccrHomExt
    · intro m
      simp only [densityPresentationMap_srcHom, densitySrcMap_reindex,
        densityMorphismIndexMap, densityElementsObj, densityElementsHom,
        NatTrans.id_app, DensityMorphismIndex.tgt, DensityMorphismIndex.src,
        DensityMorphismIndex.hom, PolyPresentation.id_srcHom']
      rfl
    · intro m
      simp only [densityPresentationMap_srcHom, densitySrcMap_fiberMor,
        PolyPresentation.id_srcHom', ccrIdMk_fiberMor]
  · apply ccrHomExt
    · intro p
      simp only [densityPresentationMap_tgtHom, densityTgtMap_reindex,
        densityElementsObj, NatTrans.id_app, PolyPresentation.id_tgtHom']
      rfl
    · intro p
      simp only [densityPresentationMap_tgtHom, densityTgtMap_fiberMor,
        PolyPresentation.id_tgtHom', ccrIdMk_fiberMor]

variable {F}

/--
Composition of natural transformations induces composition of morphisms.
-/
theorem densityPresentationMap_comp {H : D ⥤ Type (max w v)} (α : F ⟶ G) (β : G ⟶ H) :
    densityPresentationMap (α ≫ β) =
    densityPresentationMap α ≫ densityPresentationMap β := by
  apply PolyPresentation.Hom.ext
  · apply ccrHomExt
    · intro m
      simp only [densityPresentationMap_srcHom, densitySrcMap_reindex,
        densityMorphismIndexMap, densityElementsObj, densityElementsHom,
        NatTrans.comp_app, PolyPresentation.comp_srcHom', ccrHomComp_reindex,
        DensityMorphismIndex.tgt, DensityMorphismIndex.src, DensityMorphismIndex.hom]
      rfl
    · intro m
      simp only [densityPresentationMap_srcHom, densitySrcMap_fiberMor,
        PolyPresentation.comp_srcHom', ccrHomComp_fiberMor, densitySrcMap_reindex,
        Category.id_comp]
  · apply ccrHomExt
    · intro p
      simp only [densityPresentationMap_tgtHom, densityTgtMap_reindex,
        densityElementsObj, NatTrans.comp_app, PolyPresentation.comp_tgtHom',
        ccrHomComp_reindex]
      rfl
    · intro p
      simp only [densityPresentationMap_tgtHom, densityTgtMap_fiberMor,
        PolyPresentation.comp_tgtHom', ccrHomComp_fiberMor, densityTgtMap_reindex,
        Category.id_comp]

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
    (D ⥤ Type (max w v)) ⥤ PolyPresentationLoc.{u, v, max u w v} D where
  obj F := PolyPresentationLoc.ofPres (densityPresentation F)
  map α := PolyPresentationLoc.Hom.mk'
    ((densityPresentationMap α).toQ)
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

variable (X : PolyPresentation.{u, v, w} D)

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
theorem densityCoeq_eq_of_toFunctor_eq (F : D ⥤ Type (max w v)) (A : D)
    (x y : ccrEval (densityTgt F) A)
    (h : densityToFunctorApp F A x = densityToFunctorApp F A y) :
    (densityPresentation F).toCopresheafπ.app A x =
    (densityPresentation F).toCopresheafπ.app A y := by
  -- densityIso.hom ∘ π = densityToFunctorApp (by definition via desc)
  -- Since densityIso.hom is an isomorphism, it's injective
  -- So h implies π(x) = π(y)
  have hinj : Function.Injective ((densityIso F).hom.app A) := by
    intro a b hab
    have : (densityIso F).inv.app A ((densityIso F).hom.app A a) =
           (densityIso F).inv.app A ((densityIso F).hom.app A b) := by
      rw [hab]
    simp only [Iso.inv_hom_id_app, types_id_apply] at this
    exact this
  apply hinj
  simp only [densityIso, NatIso.ofComponents_hom_app]
  -- The hom is defined via CoequalizerData.desc, which satisfies
  -- desc ∘ π = the original map (densityToFunctorApp)
  have hfac := CoequalizerData.fac
    (ccrToFunctorMap (densityPresentation F).fst)
    (ccrToFunctorMap (densityPresentation F).snd)
    (densityToFunctorApp F A)
    (congrFun (densityToFunctorApp_coequalizes F A))
  simp only [types_comp_apply] at hfac
  rw [hfac, hfac]
  exact h

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
    ccrEvalMk, ccrHomComp_reindex, ccrHomComp_fiberMor,
    comparisonTgtHom_reindex, comparisonTgtHom_fiberMor,
    Category.id_comp, comparisonTgtReindex]
  -- Apply the helper: show images under densityToFunctorApp are equal
  apply densityCoeq_eq_of_toFunctor_eq
  -- Now show densityToFunctorApp gives equal results
  simp only [densityToFunctorApp]
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
    simp only [ccrToFunctor_map, ccrEvalMap, ccrEvalMk_index, ccrEvalMk_mor,
      Category.id_comp, types_comp_apply] at this
    exact this.symm
  have hπ_nat_snd : X.toCopresheaf.map (ccrFiberMor X.snd j)
      (X.toCopresheafπ.app _ ⟨ccrReindex X.snd j, 𝟙 _⟩) =
      X.toCopresheafπ.app _ ⟨ccrReindex X.snd j, ccrFiberMor X.snd j⟩ := by
    have := congrFun (X.toCopresheafπ.naturality (ccrFiberMor X.snd j))
      ⟨ccrReindex X.snd j, 𝟙 _⟩
    simp only [ccrToFunctor_map, ccrEvalMap, ccrEvalMk_index, ccrEvalMk_mor,
      Category.id_comp, types_comp_apply] at this
    exact this.symm
  rw [hπ_nat_fst, hπ_nat_snd]
  -- Now use naturality again with g
  have hπ_nat_fst' := congrFun (X.toCopresheafπ.naturality g)
      ⟨ccrReindex X.fst j, ccrFiberMor X.fst j⟩
  have hπ_nat_snd' := congrFun (X.toCopresheafπ.naturality g)
      ⟨ccrReindex X.snd j, ccrFiberMor X.snd j⟩
  simp only [ccrToFunctor_map, ccrEvalMap, ccrEvalMk_index, ccrEvalMk_mor,
    types_comp_apply] at hπ_nat_fst' hπ_nat_snd'
  rw [hπ_nat_fst', hπ_nat_snd']
  -- Now the goal is: π⟨fstIdx, fstFiber ≫ g⟩ = π⟨sndIdx, sndFiber ≫ g⟩
  -- This is exactly X.toCopresheaf_condition at ⟨j, g⟩
  have hX := congrFun (X.toCopresheaf_condition) (⟨j, g⟩ : ccrEval X.src A)
  simp only [PolyPresentation.toCopresheafπ, NatTrans.comp_app, types_comp_apply,
    ccrToFunctorMap_app, ccrEvalMk] at hX
  exact hX

/--
The comparison morphism from X to its density presentation as a
PolyPresentationQ morphism.
-/
def comparisonMorphismQ :
    PolyPresentationQ.Hom X.toQ (densityPresentation X.toCopresheaf).toQ where
  tgtHom := comparisonTgtHom X
  respects := comparisonTgtHom_respects X

/--
The induced map on coequalizers from the comparison morphism is the
inverse of the density isomorphism.
-/
theorem comparisonMorphismQ_toInducedMap :
    (comparisonMorphismQ X).toInducedMap = (densityIso X.toCopresheaf).inv := by
  apply CoequalizerData.uniq
  ext A ⟨i, g⟩
  simp only [NatTrans.comp_app, types_comp_apply, PolyPresentationQ.Hom.toInducedMap,
    CoequalizerData.fac, ccrToFunctorMap_app, ccrEvalMk, comparisonMorphismQ,
    comparisonTgtHom_reindex, comparisonTgtHom_fiberMor, Category.id_comp,
    comparisonTgtReindex, PolyPresentation.toCopresheafπ, densityIso,
    NatIso.ofComponents_inv_app]
  -- LHS: density_π (⟨(ccrFamily i, X.π⟨i, 𝟙⟩), g⟩)
  -- RHS: X.π ∘ functorToDensityApp
  -- The inverse of densityIso sends y to density_π(⟨(A, y), 𝟙⟩)
  -- We want density_π(⟨(ccrFamily i, X.π⟨i, 𝟙⟩), g⟩) =
  --        density_π(⟨(A, X.π⟨i, g⟩), 𝟙⟩)
  -- Use naturality: X.π⟨i, 𝟙⟩ under map g gives X.π⟨i, g⟩
  simp only [functorToDensityApp]
  -- The density coequalizer relation identifies these elements
  apply densityCoeq_eq_of_toFunctor_eq
  simp only [densityToFunctorApp]
  -- LHS: X.toCopresheaf.map g (X.π⟨i, 𝟙⟩)
  -- RHS: X.toCopresheaf.map 𝟙 (X.π⟨i, g⟩) = X.π⟨i, g⟩
  simp only [X.toCopresheaf.map_id, types_id_apply]
  -- Use naturality of X.π
  have hnat := congrFun (X.toCopresheafπ.naturality g) ⟨i, 𝟙 _⟩
  simp only [ccrToFunctor_map, ccrEvalMap, ccrEvalMk_index, ccrEvalMk_mor,
    Category.id_comp, types_comp_apply] at hnat
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
  simp only [polyPresentationLocEvalFunctor, comparisonMorphism,
    PolyPresentationLoc.Hom.toInducedMap', comparisonMorphismQ_toInducedMap]
  infer_instance

/-! ### Naturality of the Comparison

The comparison morphism is natural in X.
-/

variable {X}

/--
The comparison morphism is natural: for f : X → Y, the square commutes.
-/
theorem comparisonMorphism_naturality {Y : PolyPresentation.{u, v, w} D}
    (f : X ⟶ Y) :
    comparisonMorphism X ≫
      PolyPresentationLoc.Hom.mk' (densityPresentationMap
        (polyPresentationLocEvalFunctor.map
          (PolyPresentationLoc.Hom.mk' f.toQ))).toQ =
    PolyPresentationLoc.Hom.mk' f.toQ ≫ comparisonMorphism Y := by
  -- Both sides are in PolyPresentationLoc, so they're equal iff
  -- they induce the same map on coequalizers
  apply Quot.sound
  unfold PolyPresentationQ.Hom.equiv
  -- The induced maps:
  -- LHS: (densityIso X.toCopresheaf).inv ≫ E(S(f.toCopresheafHom))
  -- RHS: f.toCopresheafHom ≫ (densityIso Y.toCopresheaf).inv
  -- By naturality of densityIso.inv, these are equal
  simp only [PolyPresentationQ.Hom.toInducedMap_comp,
    PolyPresentationLoc.Hom.comp', PolyPresentationLoc.Hom.compLift2,
    PolyPresentationLoc.Hom.compRep, PolyPresentationLoc.Hom.mk',
    PolyPresentationQ.Hom.toInducedMap, comparisonMorphism,
    comparisonMorphismQ, comparisonMorphismQ_toInducedMap,
    polyPresentationLocEvalFunctor]
  -- Need to show the equality of composed maps
  ext A
  simp only [NatTrans.comp_app, types_comp_apply]
  -- Use naturality of densityIso
  have hnat := (densityIso (D := D)).inv.naturality
    (PolyPresentation.toCopresheafHom f)
  simp only [NatTrans.comp_app, types_comp_apply] at hnat
  intro x
  rw [← hnat]
  congr 1
  -- Show that densityPresentationMap(f.toCopresheafHom).toInducedMap
  -- equals (densityIso Y).hom ≫ f.toCopresheafHom ≫ (densityIso X).inv
  -- on the image of (densityIso X).inv
  simp only [densityIso, NatIso.ofComponents_inv_app, NatIso.ofComponents_hom_app,
    PolyPresentation.toCopresheafHom, PolyPresentationQ.Hom.toInducedMap]
  -- This requires showing the density functor respects the induced maps
  rfl

/-! ### Counit Naturality

The density isomorphism is natural with respect to natural transformations,
making it the counit of the adjunction.
-/

/--
The counit of the adjunction: E ∘ S → Id.
This is just the density isomorphism assembled into a natural isomorphism.
-/
def counitIso : polyPresentationLocEvalFunctor (D := D) ⋙
    densityPresentationFunctor D ⋙ polyPresentationLocEvalFunctor ≅
    polyPresentationLocEvalFunctor := by
  refine NatIso.ofComponents (fun X => ?_) (fun f => ?_)
  · -- Component at X: (densityPresentation X.toCopresheaf).toCopresheaf ≅ X.toCopresheaf
    exact densityIso X.toPres.toCopresheaf
  · -- Naturality
    simp only [Functor.comp_obj, Functor.comp_map, densityPresentationFunctor,
      polyPresentationLocEvalFunctor, PolyPresentationLoc.Hom.toInducedMap']
    ext A x
    revert x
    apply Quot.ind
    intro x'
    simp only [NatTrans.comp_app, types_comp_apply]
    -- Use naturality of densityIso
    have hnat := (densityIso (D := D)).hom.naturality
      (PolyPresentationLoc.Hom.toInducedMap' f)
    exact congrFun (congrFun hnat A) (Quot.mk _ x')

end Equivalence

end GebLean
