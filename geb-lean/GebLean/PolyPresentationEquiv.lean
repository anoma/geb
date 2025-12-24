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
    dsimp only [Functor.comp_map, familyFunctor, familyMap, Cat.opFunctor',
      Functor.op', functorOp'Obj, ccrFamily, DensityMorphismIndex.hom,
      densityMorphismIndexMap, densityTgt, densitySrc, densityElementsObj,
      DensityMorphismIndex.src, ccrObjMk, DensityMorphismIndex.tgt]
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
      dsimp only [Functor.comp_map, familyFunctor, familyMap, Cat.opFunctor',
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
      dsimp only [Functor.comp_map, familyFunctor, familyMap, Cat.opFunctor',
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
  simp only [PolyPresentation.toCopresheafπ, functorCoequalizerData, functorCoeqπ]
  -- Now the goal has CoequalizerData.π (fst.app A) (snd.app A) applied to x and y
  have hfac := CoequalizerData.fac
    ((ccrToFunctorMap (densityPresentation F).fst).app A)
    ((ccrToFunctorMap (densityPresentation F).snd).app A)
    (densityToFunctorApp F A)
    (densityToFunctorApp_coequalizes F A)
  -- hfac : π ≫ desc = densityToFunctorApp F A
  -- Apply pointwise: desc (π x) = densityToFunctorApp F A x
  have h1 := congrFun hfac x
  have h2 := congrFun hfac y
  simp only [types_comp_apply] at h1 h2
  rw [h1, h2]
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

end GebLean
