import GebLean.Utilities.Category

/-!
# Equivalences Between Over-Based and Dependent Category Structures

This module proves equivalences between the Over/Arrow-based category structures
(which have proof-irrelevant constraints) and the dependently-typed structures
in `Category.lean`. This enables interaction with mathlib's `Category` using
Over/Arrow categories instead of dealing with casts, `eqToHom`, and
heterogeneous equality.

## Main results

### Quiver-level equivalences
* `HomSet.toOverQuiver`: Bundle morphisms from a HomSet into an OverQuiver
* `OverQuiver.toHomSet`: Extract fibers from an OverQuiver as a HomSet
* `HomSet.fiber_equiv`: Round-trip equivalence for HomSet → OverQuiver → HomSet
* `OverQuiver.sigma_equiv`: Round-trip equivalence for OverQuiver → HomSet →
  OverQuiver

### Category-level equivalences
* `CategoryData.toOverCategoryData`: Convert CategoryData to OverCategoryData
* `OverCategoryData.toCategoryData`: Convert OverCategoryData to CategoryData

### Functor-level equivalences
* `FunctorData.toOverFunctorData`: Convert FunctorData to OverFunctorData
* `OverFunctorData.toFunctorData`: Convert OverFunctorData to FunctorData

### Natural transformation equivalences
* `NatTransData.toOverNatTransData`: Convert NatTransData to OverNatTransData
* `OverNatTransData.toNatTransData`: Convert OverNatTransData to NatTransData
-/

namespace GebLean

open CategoryTheory

universe u

/-! ## Phase 1: Quiver-level equivalences

We work in a single universe `u` for simplicity. The object type and morphism
types are all in `Type u`. -/

section QuiverEquiv

variable {U : Type u} (hs : HomSet.{u + 1, u} U)

/-! ### From HomSet to OverQuiver -/

/-- The sigma type bundling all morphisms from a HomSet into a single type.
    This is the total space of the morphism family. -/
abbrev HomSet.SigmaMor : Type u := Σ (a b : U), hs a b

/-- The endpoint projection from the sigma type to pairs of objects. -/
def HomSet.sigmaEndpoints : hs.SigmaMor → U × U :=
  fun ⟨a, b, _⟩ => (a, b)

/-- Bundle morphisms from a HomSet into an OverQuiver.
    The morphism type is the sigma of all hom-sets, with projection to
    source-target pairs. -/
def HomSet.toOverQuiver : OverQuiver.{u} where
  Obj := U
  Mor := Over.mk hs.sigmaEndpoints

/-- The morphism type of the bundled OverQuiver is the sigma type. -/
theorem HomSet.toOverQuiver_MorType : hs.toOverQuiver.MorType = hs.SigmaMor := rfl

/-- The source of a morphism in the bundled OverQuiver. -/
theorem HomSet.toOverQuiver_src (m : hs.SigmaMor) :
    hs.toOverQuiver.src m = m.1 := rfl

/-- The target of a morphism in the bundled OverQuiver. -/
theorem HomSet.toOverQuiver_tgt (m : hs.SigmaMor) :
    hs.toOverQuiver.tgt m = m.2.1 := rfl

/-! ### From OverQuiver to HomSet -/

variable (Q : OverQuiver.{u})

/-- Extract fibers from an OverQuiver as a HomSet.
    The hom-set from `a` to `b` is the fiber of the endpoint map over `(a, b)`. -/
def OverQuiver.toHomSet : HomSet.{u + 1, u} Q.Obj :=
  fun a b => { f : Q.MorType // Q.src f = a ∧ Q.tgt f = b }

/-- A morphism in the fiber with its source proof. -/
theorem OverQuiver.toHomSet_src {a b : Q.Obj} (f : Q.toHomSet a b) :
    Q.src f.val = a := f.property.1

/-- A morphism in the fiber with its target proof. -/
theorem OverQuiver.toHomSet_tgt {a b : Q.Obj} (f : Q.toHomSet a b) :
    Q.tgt f.val = b := f.property.2

/-! ### Round-trip equivalences -/

/-- The fiber of the bundled OverQuiver over `(a, b)` is equivalent to `hs a b`.
    This is the round-trip HomSet → OverQuiver → HomSet. -/
def HomSet.fiber_equiv (a b : U) :
    hs.toOverQuiver.toHomSet a b ≃ hs a b where
  toFun := fun ⟨⟨a', b', f⟩, ⟨ha, hb⟩⟩ => ha ▸ hb ▸ f
  invFun := fun f => ⟨⟨a, b, f⟩, ⟨rfl, rfl⟩⟩
  left_inv := fun ⟨⟨a', b', f⟩, ⟨ha, hb⟩⟩ => by
    subst ha hb
    rfl
  right_inv := fun _ => rfl

/-- The sigma of fibers is equivalent to the original morphism type.
    This is the round-trip OverQuiver → HomSet → OverQuiver. -/
def OverQuiver.sigma_equiv :
    Q.MorType ≃ (Σ (a b : Q.Obj), Q.toHomSet a b) where
  toFun := fun f => ⟨Q.src f, Q.tgt f, f, rfl, rfl⟩
  invFun := fun ⟨_, _, fib⟩ => fib.val
  left_inv := fun _ => rfl
  right_inv := fun ⟨a, b, ⟨f, ha, hb⟩⟩ => by
    subst ha hb
    rfl

end QuiverEquiv

/-! ## Phase 2: Category-level equivalences -/

section CategoryEquiv

variable {U : Type u} {hs : HomSet.{u + 1, u} U}

/-! ### From CategoryData to OverCategoryData -/

/-- The diagonal embedding for the bundled OverQuiver. -/
def HomSet.toOverQuiver_diag_hom (hs : HomSet.{u + 1, u} U)
    (data : CategoryData U hs) : U → hs.SigmaMor :=
  fun a => ⟨a, a, data.id a⟩

/-- The diagonal embedding respects endpoints. -/
theorem HomSet.toOverQuiver_diag_comm (hs : HomSet.{u + 1, u} U)
    (data : CategoryData U hs) :
    hs.sigmaEndpoints ∘ hs.toOverQuiver_diag_hom data =
      fun a => (a, a) := rfl

/-- The identity as an Over morphism for the bundled OverQuiver. -/
def HomSet.toOverQuiver_id (hs : HomSet.{u + 1, u} U)
    (data : CategoryData U hs) : hs.toOverQuiver.diag ⟶ hs.toOverQuiver.Mor :=
  Over.homMk (hs.toOverQuiver_diag_hom data) (hs.toOverQuiver_diag_comm data)

/-- The identity function extracted from the Over morphism. -/
theorem HomSet.toOverQuiver_idFn (hs : HomSet.{u + 1, u} U)
    (data : CategoryData U hs) (a : U) :
    (hs.toOverQuiver_id data).left a = ⟨a, a, data.id a⟩ := rfl

/-- Helper: extract the composability equation in explicit form. -/
theorem HomSet.compPair_mid_eq (hs : HomSet.{u + 1, u} U)
    (p : hs.toOverQuiver.ComposablePairsType) :
    p.val.1.2.1 = p.val.2.1 := p.property

/-- Composition function for composable pairs in the bundled OverQuiver. -/
def HomSet.toOverQuiver_comp_hom (hs : HomSet.{u + 1, u} U)
    (data : CategoryData U hs) :
    hs.toOverQuiver.ComposablePairsType → hs.SigmaMor :=
  fun p =>
    let a := p.val.1.1
    let b := p.val.1.2.1
    let c := p.val.2.2.1
    let f : hs a b := p.val.1.2.2
    let b' := p.val.2.1
    let g : hs b' c := p.val.2.2.2
    let hmid : b = b' := hs.compPair_mid_eq p
    ⟨a, c, data.comp f (hmid.symm ▸ g)⟩

/-- Composition respects endpoints. -/
theorem HomSet.toOverQuiver_comp_comm (hs : HomSet.{u + 1, u} U)
    (data : CategoryData U hs) :
    hs.sigmaEndpoints ∘ hs.toOverQuiver_comp_hom data =
      hs.toOverQuiver.ComposablePairs.hom := by
  funext p
  simp only [Function.comp_apply, sigmaEndpoints, toOverQuiver_comp_hom,
    OverQuiver.ComposablePairs, Over.coe_hom]
  rfl

/-- Composition as an Over morphism for the bundled OverQuiver. -/
def HomSet.toOverQuiver_comp (hs : HomSet.{u + 1, u} U)
    (data : CategoryData U hs) :
    hs.toOverQuiver.ComposablePairs ⟶ hs.toOverQuiver.Mor :=
  Over.homMk (hs.toOverQuiver_comp_hom data) (hs.toOverQuiver_comp_comm data)

/-- The composition function extracted from the Over morphism. -/
theorem HomSet.toOverQuiver_compFn (hs : HomSet.{u + 1, u} U)
    (data : CategoryData U hs)
    (p : hs.toOverQuiver.ComposablePairsType) :
    (hs.toOverQuiver_comp data).left p =
      ⟨p.val.1.1, p.val.2.2.1,
        data.comp p.val.1.2.2 ((hs.compPair_mid_eq p).symm ▸ p.val.2.2.2)⟩ := rfl

/-- Convert CategoryData to OverCategoryOps for the bundled OverQuiver. -/
def CategoryData.toOverCategoryOps (data : CategoryData U hs) :
    OverCategoryOps hs.toOverQuiver where
  id := hs.toOverQuiver_id data
  comp := hs.toOverQuiver_comp data

/-- Helper lemma for sigma equality. -/
theorem HomSet.sigma_eq {U : Type u} {hs : HomSet.{u + 1, u} U}
    {a₁ a₂ b₁ b₂ : U} {f₁ : hs a₁ b₁} {f₂ : hs a₂ b₂}
    (ha : a₁ = a₂) (hb : b₁ = b₂) (hf : ha ▸ hb ▸ f₁ = f₂) :
    (⟨a₁, b₁, f₁⟩ : hs.SigmaMor) = ⟨a₂, b₂, f₂⟩ := by
  cases ha
  cases hb
  cases hf
  rfl

/-- Convert CategoryData to OverCategoryData for the bundled OverQuiver. -/
def CategoryData.toOverCategoryData (data : CategoryData U hs) :
    OverCategoryData hs.toOverQuiver where
  toOverCategoryOps := data.toOverCategoryOps
  id_comp := fun f => by
    unfold toOverCategoryOps OverCategoryOps.idFn OverCategoryOps.compFn
    simp only [HomSet.toOverQuiver_idFn, HomSet.toOverQuiver_compFn,
      HomSet.toOverQuiver_src]
    exact HomSet.sigma_eq rfl rfl (data.laws.id_laws.id_comp f.2.2)
  comp_id := fun f => by
    unfold toOverCategoryOps OverCategoryOps.idFn OverCategoryOps.compFn
    simp only [HomSet.toOverQuiver_idFn, HomSet.toOverQuiver_compFn,
      HomSet.toOverQuiver_tgt]
    exact HomSet.sigma_eq rfl rfl (data.laws.id_laws.comp_id f.2.2)
  assoc := fun ⟨⟨⟨a, ⟨b, f⟩⟩, ⟨⟨b', ⟨c, g⟩⟩, ⟨c', ⟨d, h⟩⟩⟩⟩, ⟨h1, h2⟩⟩ => by
    unfold toOverCategoryOps OverCategoryOps.compFn
    simp only [HomSet.toOverQuiver_compFn] at *
    cases h1
    cases h2
    exact HomSet.sigma_eq rfl rfl (data.assoc f g h)

/-! ### From OverCategoryData to CategoryData -/

/-- Extract identity morphism from an OverCategoryData. -/
def OverCategoryData.extractId {Q : OverQuiver.{u}}
    (data : OverCategoryData Q) (a : Q.Obj) : Q.toHomSet a a :=
  ⟨data.idFn a, data.id_src a, data.id_tgt a⟩

/-- Extract composition from an OverCategoryData.
    Given morphisms f : a → b and g : b → c in the fiber HomSet,
    produce their composite f ≫ g : a → c. -/
def OverCategoryData.extractComp {Q : OverQuiver.{u}}
    (data : OverCategoryData Q) {a b c : Q.Obj}
    (f : Q.toHomSet a b) (g : Q.toHomSet b c) : Q.toHomSet a c :=
  let fval := f.val
  let gval := g.val
  let composable : Q.Composable fval gval := f.property.2.trans g.property.1.symm
  ⟨data.compFn ⟨(fval, gval), composable⟩,
   (data.comp_src ⟨(fval, gval), composable⟩).trans f.property.1,
   (data.comp_tgt ⟨(fval, gval), composable⟩).trans g.property.2⟩

/-- Convert OverCategoryData to CategoryOps on the fiber HomSet. -/
def OverCategoryData.toCategoryOps {Q : OverQuiver.{u}}
    (data : OverCategoryData Q) : CategoryOps Q.toHomSet where
  comp := fun f g => data.extractComp f g
  id := fun a => data.extractId a

/-- Convert OverCategoryData to CategoryData on the fiber HomSet. -/
def OverCategoryData.toCategoryData {Q : OverQuiver.{u}}
    (data : OverCategoryData Q) : CategoryData Q.Obj Q.toHomSet where
  toCategoryOps := data.toCategoryOps
  laws := {
    assoc := fun f g h => by
      apply Subtype.ext
      have hassoc := data.assoc
        ⟨(f.val, g.val, h.val),
         ⟨f.property.2.trans g.property.1.symm,
          g.property.2.trans h.property.1.symm⟩⟩
      simp only [OverCategoryOps.compFn] at hassoc
      exact hassoc
    id_laws := {
      id_comp := fun ⟨fval, hsrc, htgt⟩ => by
        apply Subtype.ext
        simp only [toCategoryOps, extractComp, extractId]
        have hid := data.id_comp fval
        simp only [OverCategoryOps.idFn, OverCategoryOps.compFn] at hid
        cases hsrc
        exact hid
      comp_id := fun ⟨fval, hsrc, htgt⟩ => by
        apply Subtype.ext
        simp only [toCategoryOps, extractComp, extractId]
        have hid := data.comp_id fval
        simp only [OverCategoryOps.idFn, OverCategoryOps.compFn] at hid
        cases htgt
        exact hid
    }
  }

end CategoryEquiv

/-! ## Phase 3: Functor-level equivalences -/

section FunctorEquiv

variable {U : Type u} {V : Type u}
variable {hsC : HomSet.{u + 1, u} U} {hsD : HomSet.{u + 1, u} V}
variable {dataC : CategoryData U hsC} {dataD : CategoryData V hsD}

/-! ### From FunctorData to OverFunctorData -/

/-- The Arrow morphism for a functor between bundled OverQuivers. -/
def FunctorOps.toArrowHom (fops : FunctorOps hsC hsD) :
    hsC.toOverQuiver.toArrow ⟶ hsD.toOverQuiver.toArrow where
  left := fun ⟨a, b, f⟩ => ⟨fops.obj a, fops.obj b, fops.map f⟩
  right := Prod.map fops.obj fops.obj
  w := rfl

/-- Convert FunctorOps to an OverQuiverMorphism. -/
def FunctorOps.toOverQuiverMorphism (fops : FunctorOps hsC hsD) :
    OverQuiverMorphism hsC.toOverQuiver hsD.toOverQuiver where
  objFn := fops.obj
  arrowHom := fops.toArrowHom
  right_eq := rfl

/-- The morphism function from the converted OverQuiverMorphism. -/
theorem FunctorOps.toOverQuiverMorphism_morFn (fops : FunctorOps hsC hsD)
    (m : hsC.SigmaMor) :
    fops.toOverQuiverMorphism.morFn m =
      ⟨fops.obj m.1, fops.obj m.2.1, fops.map m.2.2⟩ := rfl

/-- Convert FunctorData to OverFunctorData for bundled OverQuivers. -/
def FunctorData.toOverFunctorData (fd : FunctorData dataC dataD) :
    OverFunctorData dataC.toOverCategoryData dataD.toOverCategoryData where
  toOverQuiverMorphism := fd.toFunctorOps.toOverQuiverMorphism
  map_id := fun a => by
    simp only [FunctorOps.toOverQuiverMorphism_morFn]
    exact HomSet.sigma_eq rfl rfl (fd.map_id a)
  map_comp := fun ⟨⟨⟨a, b, f⟩, ⟨b', c, g⟩⟩, hmid⟩ => by
    simp only [OverQuiverMorphism.morFn, FunctorOps.toOverQuiverMorphism,
      FunctorOps.toArrowHom, CategoryData.toOverCategoryData,
      CategoryData.toOverCategoryOps, OverCategoryOps.compFn,
      HomSet.toOverQuiver_comp]
    cases hmid
    exact HomSet.sigma_eq rfl rfl (fd.map_comp f g)

/-! ### From OverFunctorData to FunctorData -/

/-- Extract the object map from an OverFunctorData. -/
def OverFunctorData.extractObj {Q₁ Q₂ : OverQuiver.{u}}
    {C₁ : OverCategoryData Q₁} {C₂ : OverCategoryData Q₂}
    (F : OverFunctorData C₁ C₂) : Q₁.Obj → Q₂.Obj :=
  F.objFn

/-- Extract the morphism map from an OverFunctorData to fiber HomSets. -/
def OverFunctorData.extractMap {Q₁ Q₂ : OverQuiver.{u}}
    {C₁ : OverCategoryData Q₁} {C₂ : OverCategoryData Q₂}
    (F : OverFunctorData C₁ C₂) {a b : Q₁.Obj}
    (f : Q₁.toHomSet a b) : Q₂.toHomSet (F.objFn a) (F.objFn b) :=
  ⟨F.morFn f.val,
   (F.src_comm f.val).trans (congrArg F.objFn f.property.1),
   (F.tgt_comm f.val).trans (congrArg F.objFn f.property.2)⟩

/-- Convert OverFunctorData to FunctorOps on fiber HomSets. -/
def OverFunctorData.toFunctorOps {Q₁ Q₂ : OverQuiver.{u}}
    {C₁ : OverCategoryData Q₁} {C₂ : OverCategoryData Q₂}
    (F : OverFunctorData C₁ C₂) : FunctorOps Q₁.toHomSet Q₂.toHomSet where
  obj := F.extractObj
  map := fun f => F.extractMap f

/-- Convert OverFunctorData to FunctorData on fiber HomSets. -/
def OverFunctorData.toFunctorData {Q₁ Q₂ : OverQuiver.{u}}
    {C₁ : OverCategoryData Q₁} {C₂ : OverCategoryData Q₂}
    (F : OverFunctorData C₁ C₂) :
    FunctorData C₁.toCategoryData C₂.toCategoryData where
  toFunctorOps := F.toFunctorOps
  laws := {
    map_id := fun a => by
      apply Subtype.ext
      simp only [toFunctorOps, extractMap]
      exact F.map_id a
    map_comp := fun {a b c} f g => by
      apply Subtype.ext
      simp only [toFunctorOps, extractMap]
      have hcomp := F.map_comp ⟨(f.val, g.val),
        f.property.2.trans g.property.1.symm⟩
      exact hcomp
  }

end FunctorEquiv

/-! ## Phase 4: Natural transformation equivalences -/

section NatTransEquiv

variable {U : Type u} {V : Type u}
variable {hsC : HomSet.{u + 1, u} U} {hsD : HomSet.{u + 1, u} V}
variable {dataC : CategoryData U hsC} {dataD : CategoryData V hsD}
variable {F G : FunctorData dataC dataD}

/-! ### From NatTransData to OverNatTransData -/

/-- The componentOver type for bundled functors. -/
def FunctorData.bundled_componentOver :
    Over (V × V) :=
  Over.mk (fun a : U => (F.obj a, G.obj a))

/-- The component function for converting NatTransData to OverNatTransData. -/
def NatTransData.toComponentHom_fn (α : NatTransData F G) (a : U) :
    hsD.SigmaMor :=
  ⟨F.obj a, G.obj a, α.app a⟩

/-- The component map respects the Over structure. -/
theorem NatTransData.toComponentHom_comm (α : NatTransData F G) :
    hsD.sigmaEndpoints ∘ α.toComponentHom_fn =
      (fun a : U => (F.obj a, G.obj a)) := rfl

/-- The component as an Over morphism for converting NatTransData. -/
def NatTransData.toComponentHom (α : NatTransData F G) :
    FunctorData.bundled_componentOver (F := F) (G := G) ⟶ hsD.toOverQuiver.Mor :=
  Over.homMk α.toComponentHom_fn α.toComponentHom_comm

/-- Convert NatTransData to OverNatTransData for bundled OverQuivers. -/
def NatTransData.toOverNatTransData (α : NatTransData F G) :
    OverNatTransData F.toOverFunctorData G.toOverFunctorData where
  componentHom := α.toComponentHom
  naturality := fun ⟨a, b, f⟩ => by
    simp only [FunctorData.toOverFunctorData, FunctorOps.toOverQuiverMorphism,
      FunctorOps.toArrowHom, OverQuiverMorphism.morFn,
      CategoryData.toOverCategoryData, CategoryData.toOverCategoryOps,
      OverCategoryOps.compFn, HomSet.toOverQuiver_comp, toComponentHom]
    exact HomSet.sigma_eq rfl rfl (α.naturality f).symm

/-! ### From OverNatTransData to NatTransData -/

/-- Extract the component from an OverNatTransData to fiber HomSets. -/
def OverNatTransData.extractApp {Q₁ Q₂ : OverQuiver.{u}}
    {C₁ : OverCategoryData Q₁} {C₂ : OverCategoryData Q₂}
    {F G : OverFunctorData C₁ C₂}
    (η : OverNatTransData F G) (a : Q₁.Obj) :
    Q₂.toHomSet (F.objFn a) (G.objFn a) :=
  ⟨η.component a, η.comp_src a, η.comp_tgt a⟩

/-- Convert OverNatTransData to NatTransData on fiber HomSets. -/
def OverNatTransData.toNatTransData {Q₁ Q₂ : OverQuiver.{u}}
    {C₁ : OverCategoryData Q₁} {C₂ : OverCategoryData Q₂}
    {F G : OverFunctorData C₁ C₂}
    (η : OverNatTransData F G) :
    NatTransData F.toFunctorData G.toFunctorData where
  app := fun a => η.extractApp a
  laws := {
    naturality := fun {a b} ⟨f, hsrc, htgt⟩ => by
      apply Subtype.ext
      simp only [OverFunctorData.toFunctorData, OverFunctorData.toFunctorOps,
        OverFunctorData.extractMap, OverCategoryData.toCategoryData,
        OverCategoryData.toCategoryOps, OverCategoryData.extractComp,
        extractApp]
      have hnat := η.naturality f
      cases hsrc
      cases htgt
      exact hnat.symm
  }

end NatTransEquiv

end GebLean
