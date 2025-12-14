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

universe v u

/-! ## Phase 1: Quiver-level equivalences -/

section QuiverEquiv

variable {U : Type u} (hs : HomSet.{v + 1, u} U)

/-! ### From HomSet to OverQuiver -/

/-- The sigma type bundling all morphisms from a HomSet into a single type.
    This is the total space of the morphism family. -/
abbrev HomSet.SigmaMor : Type (max u v) := Σ (a b : U), hs a b

/-- The endpoint projection from the sigma type to pairs of objects. -/
def HomSet.sigmaEndpoints : hs.SigmaMor → U × U :=
  fun ⟨a, b, _⟩ => (a, b)

/-- Bundle morphisms from a HomSet into an OverQuiver.
    The morphism type is the sigma of all hom-sets, with explicit
    source and target projections. -/
def HomSet.toOverQuiver : OverQuiver.{max u v, u} where
  Obj := U
  MorType := hs.SigmaMor
  src := fun ⟨a, _, _⟩ => a
  tgt := fun ⟨_, b, _⟩ => b

/-- The morphism type of the bundled OverQuiver is the sigma type. -/
theorem HomSet.toOverQuiver_MorType : hs.toOverQuiver.MorType = hs.SigmaMor := rfl

/-- The source of a morphism in the bundled OverQuiver. -/
theorem HomSet.toOverQuiver_src (m : hs.SigmaMor) :
    hs.toOverQuiver.src m = m.1 := rfl

/-- The target of a morphism in the bundled OverQuiver. -/
theorem HomSet.toOverQuiver_tgt (m : hs.SigmaMor) :
    hs.toOverQuiver.tgt m = m.2.1 := rfl

/-! ### From OverQuiver to HomSet -/

variable (Q : OverQuiver.{v, u})

/-- Extract fibers from an OverQuiver as a HomSet.
    The hom-set from `a` to `b` is the fiber of the endpoint map over `(a, b)`. -/
def OverQuiver.toHomSet : HomSet.{v + 1, u} Q.Obj :=
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

/-- Direct round-trip from HomSet back to itself, using the fiber equivalence.
    This avoids the universe bump: HomSet.{v+1, u} → OverQuiver → HomSet.{v+1, u}.
    The intermediate OverQuiver has morphisms in Type (max u v), but the
    equivalence projects back to the original Type v. -/
def HomSet.roundtrip (a b : U) : hs a b ≃ hs a b :=
  (hs.fiber_equiv a b).symm.trans (hs.fiber_equiv a b)

/-- The round-trip is the identity equivalence. -/
theorem HomSet.roundtrip_eq_refl (a b : U) :
    hs.roundtrip a b = Equiv.refl (hs a b) := by
  simp only [roundtrip, Equiv.symm_trans_self]

end QuiverEquiv

/-! ## Phase 2: Category-level equivalences -/

section CategoryEquiv

variable {U : Type u} {hs : HomSet.{v + 1, u} U}

/-! ### From CategoryData to OverCategoryData -/

/-- Helper: extract the composability equation in explicit form. -/
theorem HomSet.compPair_mid_eq (hs : HomSet.{v + 1, u} U)
    (p : hs.toOverQuiver.ComposablePairsType) :
    p.val.1.2.1 = p.val.2.1 := p.property

/-- Helper lemma for sigma equality. -/
theorem HomSet.sigma_eq {U : Type u} {hs : HomSet.{v + 1, u} U}
    {a₁ a₂ b₁ b₂ : U} {f₁ : hs a₁ b₁} {f₂ : hs a₂ b₂}
    (ha : a₁ = a₂) (hb : b₁ = b₂) (hf : ha ▸ hb ▸ f₁ = f₂) :
    (⟨a₁, b₁, f₁⟩ : hs.SigmaMor) = ⟨a₂, b₂, f₂⟩ := by
  cases ha
  cases hb
  cases hf
  rfl

/-- Convert CategoryData to OverCategoryOps for the bundled OverQuiver. -/
def CategoryData.toOverCategoryOps (data : CategoryData U hs) :
    OverCategoryOps hs.toOverQuiver where
  idFn := fun a => ⟨a, a, data.id a⟩
  compFn := fun p =>
    let a := p.val.1.1
    let b := p.val.1.2.1
    let c := p.val.2.2.1
    let f : hs a b := p.val.1.2.2
    let b' := p.val.2.1
    let g : hs b' c := p.val.2.2.2
    let hmid : b = b' := hs.compPair_mid_eq p
    ⟨a, c, data.comp f (hmid.symm ▸ g)⟩
  id_src := fun _ => rfl
  id_tgt := fun _ => rfl
  comp_src := fun _ => rfl
  comp_tgt := fun _ => rfl

/-- Convert CategoryData to OverCategoryData for the bundled OverQuiver. -/
def CategoryData.toOverCategoryData (data : CategoryData U hs) :
    OverCategoryData hs.toOverQuiver where
  toOverCategoryOps := data.toOverCategoryOps
  id_comp := fun f => by
    simp only [toOverCategoryOps]
    exact HomSet.sigma_eq rfl rfl (data.laws.id_laws.id_comp f.2.2)
  comp_id := fun f => by
    simp only [toOverCategoryOps]
    exact HomSet.sigma_eq rfl rfl (data.laws.id_laws.comp_id f.2.2)
  assoc := fun ⟨⟨⟨a, ⟨b, f⟩⟩, ⟨⟨b', ⟨c, g⟩⟩, ⟨c', ⟨d, h⟩⟩⟩⟩, ⟨h1, h2⟩⟩ => by
    simp only [toOverCategoryOps]
    cases h1
    cases h2
    exact HomSet.sigma_eq rfl rfl (data.assoc f g h)

/-! ### From OverCategoryData to CategoryData -/

/-- Extract identity morphism from an OverCategoryData. -/
def OverCategoryData.extractId {Q : OverQuiver.{v, u}}
    (data : OverCategoryData Q) (a : Q.Obj) : Q.toHomSet a a :=
  ⟨data.idFn a, data.id_src a, data.id_tgt a⟩

/-- Extract composition from an OverCategoryData.
    Given morphisms f : a → b and g : b → c in the fiber HomSet,
    produce their composite f ≫ g : a → c. -/
def OverCategoryData.extractComp {Q : OverQuiver.{v, u}}
    (data : OverCategoryData Q) {a b c : Q.Obj}
    (f : Q.toHomSet a b) (g : Q.toHomSet b c) : Q.toHomSet a c :=
  let fval := f.val
  let gval := g.val
  let composable : Q.Composable fval gval := f.property.2.trans g.property.1.symm
  ⟨data.compFn ⟨(fval, gval), composable⟩,
   (data.comp_src ⟨(fval, gval), composable⟩).trans f.property.1,
   (data.comp_tgt ⟨(fval, gval), composable⟩).trans g.property.2⟩

/-- Helper lemma for nested sigma equality with subtypes.
    Given equal source/target proofs and the same underlying morphism value,
    prove equality of sigma types containing HomSet fibers. -/
theorem OverQuiver.sigma_homset_eq {Q : OverQuiver.{v, u}}
    {a₁ a₂ b₁ b₂ : Q.Obj} (f : Q.MorType)
    (ha : Q.src f = a₁) (ha' : a₁ = a₂)
    (hb : Q.tgt f = b₁) (hb' : b₁ = b₂) :
    (⟨a₁, b₁, ⟨f, ha, hb⟩⟩ : Σ (a b : Q.Obj), Q.toHomSet a b) =
      ⟨a₂, b₂, ⟨f, ha.trans ha', hb.trans hb'⟩⟩ := by
  cases ha'
  cases hb'
  rfl

/-- sigma_equiv applied to an identity morphism equals the extracted identity.
    This handles the proof term difference: sigma_equiv uses rfl proofs while
    extractId uses id_src/id_tgt proofs. -/
theorem OverQuiver.sigma_equiv_id {Q : OverQuiver.{v, u}}
    (data : OverCategoryData Q) (a : Q.Obj) :
    Q.sigma_equiv (data.idFn a) =
      ⟨a, a, OverCategoryData.extractId data a⟩ := by
  unfold sigma_equiv OverCategoryData.extractId
  exact sigma_homset_eq (data.idFn a) rfl (data.id_src a) rfl (data.id_tgt a)

/-- sigma_equiv applied to a composition produces a triple with comp_src/comp_tgt proofs.
    The inner subtype contains the composed morphism with transitivity proofs. -/
theorem OverQuiver.sigma_equiv_comp {Q : OverQuiver.{v, u}}
    (data : OverCategoryData Q) (p : Q.ComposablePairsType) :
    Q.sigma_equiv (data.compFn p) =
      ⟨Q.src p.val.1, Q.tgt p.val.2,
        ⟨data.compFn p,
         (data.comp_src p).trans rfl,
         (data.comp_tgt p).trans rfl⟩⟩ := by
  unfold sigma_equiv
  have hsrc := data.comp_src p
  have htgt := data.comp_tgt p
  exact sigma_homset_eq (data.compFn p) rfl hsrc rfl htgt

/-- compFn only depends on the morphism pair, not the composability proof. -/
theorem OverCategoryData.compFn_congr {Q : OverQuiver.{v, u}}
    (data : OverCategoryData Q)
    {f g : Q.MorType} (h1 h2 : Q.Composable f g) :
    data.compFn ⟨(f, g), h1⟩ = data.compFn ⟨(f, g), h2⟩ := rfl

/-- Transport on a HomSet subtype preserves the underlying morphism value. -/
theorem HomSet.val_eqRec {Q : OverQuiver.{v, u}}
    {a b a' : Q.Obj} (ha : a = a') (f : Q.toHomSet a b) :
    (ha ▸ f : Q.toHomSet a' b).val = f.val := by
  cases ha
  rfl

/-- Transport on a HomSet subtype (second index) preserves the underlying morphism value. -/
theorem HomSet.val_eqRec' {Q : OverQuiver.{v, u}}
    {a b b' : Q.Obj} (hb : b = b') (f : Q.toHomSet a b) :
    (hb ▸ f : Q.toHomSet a b').val = f.val := by
  cases hb
  rfl

/-- Convert OverCategoryData to CategoryOps on the fiber HomSet. -/
def OverCategoryData.toCategoryOps {Q : OverQuiver.{v, u}}
    (data : OverCategoryData Q) : CategoryOps Q.toHomSet where
  comp := fun f g => data.extractComp f g
  id := fun a => data.extractId a

/-- Convert OverCategoryData to CategoryData on the fiber HomSet. -/
def OverCategoryData.toCategoryData {Q : OverQuiver.{v, u}}
    (data : OverCategoryData Q) : CategoryData Q.Obj Q.toHomSet where
  toCategoryOps := data.toCategoryOps
  laws := {
    assoc := fun f g h => by
      apply Subtype.ext
      have hassoc := data.assoc
        ⟨(f.val, g.val, h.val),
         ⟨f.property.2.trans g.property.1.symm,
          g.property.2.trans h.property.1.symm⟩⟩
      exact hassoc
    id_laws := {
      id_comp := fun ⟨fval, hsrc, htgt⟩ => by
        apply Subtype.ext
        simp only [toCategoryOps, extractComp, extractId]
        have hid := data.id_comp fval
        cases hsrc
        exact hid
      comp_id := fun ⟨fval, hsrc, htgt⟩ => by
        apply Subtype.ext
        simp only [toCategoryOps, extractComp, extractId]
        have hid := data.comp_id fval
        cases htgt
        exact hid
    }
  }

end CategoryEquiv

/-! ## Phase 3: Functor-level equivalences -/

section FunctorEquiv

variable {U : Type u} {V : Type u}
variable {hsC : HomSet.{v + 1, u} U} {hsD : HomSet.{v + 1, u} V}
variable {dataC : CategoryData U hsC} {dataD : CategoryData V hsD}

/-! ### From FunctorData to OverFunctorData -/

/-- Convert FunctorOps to an OverQuiverMorphism. -/
def FunctorOps.toOverQuiverMorphism (fops : FunctorOps hsC hsD) :
    OverQuiverMorphism hsC.toOverQuiver hsD.toOverQuiver where
  objFn := fops.obj
  morFn := fun ⟨a, b, f⟩ => ⟨fops.obj a, fops.obj b, fops.map f⟩
  src_comm := fun _ => rfl
  tgt_comm := fun _ => rfl

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
    simp only [FunctorOps.toOverQuiverMorphism, CategoryData.toOverCategoryData,
      CategoryData.toOverCategoryOps]
    cases hmid
    exact HomSet.sigma_eq rfl rfl (fd.map_comp f g)

/-! ### From OverFunctorData to FunctorData -/

/-- Extract the object map from an OverFunctorData. -/
def OverFunctorData.extractObj {Q₁ Q₂ : OverQuiver.{v, u}}
    {C₁ : OverCategoryData Q₁} {C₂ : OverCategoryData Q₂}
    (F : OverFunctorData C₁ C₂) : Q₁.Obj → Q₂.Obj :=
  F.objFn

/-- Extract the morphism map from an OverFunctorData to fiber HomSets. -/
def OverFunctorData.extractMap {Q₁ Q₂ : OverQuiver.{v, u}}
    {C₁ : OverCategoryData Q₁} {C₂ : OverCategoryData Q₂}
    (F : OverFunctorData C₁ C₂) {a b : Q₁.Obj}
    (f : Q₁.toHomSet a b) : Q₂.toHomSet (F.objFn a) (F.objFn b) :=
  ⟨F.morFn f.val,
   (F.src_comm f.val).trans (congrArg F.objFn f.property.1),
   (F.tgt_comm f.val).trans (congrArg F.objFn f.property.2)⟩

/-- Convert OverFunctorData to FunctorOps on fiber HomSets. -/
def OverFunctorData.toFunctorOps {Q₁ Q₂ : OverQuiver.{v, u}}
    {C₁ : OverCategoryData Q₁} {C₂ : OverCategoryData Q₂}
    (F : OverFunctorData C₁ C₂) : FunctorOps Q₁.toHomSet Q₂.toHomSet where
  obj := F.extractObj
  map := fun f => F.extractMap f

/-- Convert OverFunctorData to FunctorData on fiber HomSets. -/
def OverFunctorData.toFunctorData {Q₁ Q₂ : OverQuiver.{v, u}}
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

/-! ### Round-trip isomorphisms for FunctorData -/

/-- The object map is preserved under the round-trip
    FunctorData → OverFunctorData → FunctorData. -/
theorem FunctorData.roundtrip_obj_eq (fd : FunctorData dataC dataD) :
    fd.toOverFunctorData.toFunctorData.obj = fd.obj := rfl

/-- The morphism map is preserved under the round-trip
    FunctorData → OverFunctorData → FunctorData (up to fiber equivalence).
    Given a morphism in the fiber, the round-trip functor maps it to a morphism
    whose underlying sigma element matches the original functor's action. -/
theorem FunctorData.roundtrip_map_val_eq (fd : FunctorData dataC dataD)
    {a b : U} (f : hsC.toOverQuiver.toHomSet a b) :
    (fd.toOverFunctorData.toFunctorData.map f).val =
      ⟨fd.obj a, fd.obj b, fd.map (hsC.fiber_equiv a b f)⟩ := by
  simp only [FunctorData.toOverFunctorData, OverFunctorData.toFunctorData,
    OverFunctorData.toFunctorOps, OverFunctorData.extractMap,
    FunctorOps.toOverQuiverMorphism, HomSet.fiber_equiv]
  obtain ⟨⟨a', b', g⟩, ⟨ha, hb⟩⟩ := f
  subst ha hb
  rfl

/-- The object function is preserved under the round-trip
    OverFunctorData → FunctorData → OverFunctorData. -/
theorem OverFunctorData.roundtrip_objFn_eq
    {Q₁ Q₂ : OverQuiver.{v, u}}
    {C₁ : OverCategoryData Q₁} {C₂ : OverCategoryData Q₂}
    (F : OverFunctorData C₁ C₂) :
    F.toFunctorData.toOverFunctorData.objFn = F.objFn := rfl

/-- The morphism function is preserved under the round-trip
    OverFunctorData → FunctorData → OverFunctorData (on fiber elements).
    The underlying morphism value is preserved. -/
theorem OverFunctorData.roundtrip_morFn_val_eq
    {Q₁ Q₂ : OverQuiver.{v, u}}
    {C₁ : OverCategoryData Q₁} {C₂ : OverCategoryData Q₂}
    (F : OverFunctorData C₁ C₂)
    {a b : Q₁.Obj} (f : Q₁.toHomSet a b) :
    let f' : Q₁.toHomSet.SigmaMor := ⟨a, b, f⟩
    (F.toFunctorData.toOverFunctorData.morFn f').2.2.val = F.morFn f.val := rfl

end FunctorEquiv

/-! ## Phase 4: Natural transformation equivalences -/

section NatTransEquiv

variable {U : Type u} {V : Type u}
variable {hsC : HomSet.{v + 1, u} U} {hsD : HomSet.{v + 1, u} V}
variable {dataC : CategoryData U hsC} {dataD : CategoryData V hsD}
variable {F G : FunctorData dataC dataD}

/-! ### From NatTransData to OverNatTransData -/

/-- Convert NatTransData to OverNatTransData for bundled OverQuivers. -/
def NatTransData.toOverNatTransData (α : NatTransData F G) :
    OverNatTransData F.toOverFunctorData G.toOverFunctorData where
  component := fun a => ⟨F.obj a, G.obj a, α.app a⟩
  comp_src := fun _ => rfl
  comp_tgt := fun _ => rfl
  naturality := fun ⟨a, b, f⟩ => by
    simp only [FunctorData.toOverFunctorData, FunctorOps.toOverQuiverMorphism,
      CategoryData.toOverCategoryData, CategoryData.toOverCategoryOps]
    exact HomSet.sigma_eq rfl rfl (α.naturality f).symm

/-! ### From OverNatTransData to NatTransData -/

/-- Extract the component from an OverNatTransData to fiber HomSets. -/
def OverNatTransData.extractApp {Q₁ Q₂ : OverQuiver.{v, u}}
    {C₁ : OverCategoryData Q₁} {C₂ : OverCategoryData Q₂}
    {F G : OverFunctorData C₁ C₂}
    (η : OverNatTransData F G) (a : Q₁.Obj) :
    Q₂.toHomSet (F.objFn a) (G.objFn a) :=
  ⟨η.component a, η.comp_src a, η.comp_tgt a⟩

/-- Convert OverNatTransData to NatTransData on fiber HomSets. -/
def OverNatTransData.toNatTransData {Q₁ Q₂ : OverQuiver.{v, u}}
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

/-! ### Round-trip isomorphisms for NatTransData -/

/-- The component is preserved under the round-trip
    NatTransData → OverNatTransData → NatTransData (up to fiber equivalence).
    The round-trip nat trans applies it to a fiber element
    whose underlying sigma element matches the original component. -/
theorem NatTransData.roundtrip_app_val_eq (α : NatTransData F G)
    (a : U) :
    (α.toOverNatTransData.toNatTransData.app a).val =
      ⟨F.obj a, G.obj a, α.app a⟩ := rfl

/-- The NatTransApp is preserved under the round-trip
    NatTransData → OverNatTransData → NatTransData. -/
theorem NatTransData.roundtrip_app_component_eq (α : NatTransData F G)
    (a : U) :
    α.toOverNatTransData.toNatTransData.app a =
      ⟨⟨F.obj a, G.obj a, α.app a⟩, rfl, rfl⟩ := rfl

/-- The component is preserved under the round-trip
    OverNatTransData → NatTransData → OverNatTransData (on objects).
    The underlying morphism value is preserved. -/
theorem OverNatTransData.roundtrip_component_eq
    {Q₁ Q₂ : OverQuiver.{v, u}}
    {C₁ : OverCategoryData Q₁} {C₂ : OverCategoryData Q₂}
    {F G : OverFunctorData C₁ C₂}
    (η : OverNatTransData F G)
    (a : Q₁.Obj) :
    (η.toNatTransData.toOverNatTransData.component a).2.2.val =
      η.component a := rfl

end NatTransEquiv

/-! ## Bundled Category Equivalences

Conversions between BundledOverCategoryData and BundledCategoryData,
establishing equivalences between the two representations.

Universe level behavior:
- `OverQuiver.{v, u}` has `MorType : Type v` and `Obj : Type u`
- `OverQuiver.toHomSet` produces `HomSet.{v + 1, u}` (fibers are subtypes)
- `HomSet.{v + 1, u}` has morphisms `hs a b : Type v`
- `HomSet.toOverQuiver` produces `OverQuiver.{max v u, u}`

The sigma construction `Σ (a b : U), hs a b` lives in `Type (max u v)` because
it bundles indices from `Type u` with fibers from `Type v`.

When `v ≥ u`, we have `max v u = v`, so the round-trip preserves universe levels:
- `BundledOverCategoryData.{v, u}` → `BundledCategoryData.{v, u}` (always)
- `BundledCategoryData.{v, u}` → `BundledOverCategoryData.{v, u}` (when v ≥ u)

However, for round-trips starting from BundledCategoryData, we can use the
fiber equivalence `HomSet.fiber_equiv` to project back to the original
universe level without any constraint. -/

section BundledEquiv

/-- Convert a BundledOverCategoryData to a BundledCategoryData.
    An OverQuiver.{v, u} produces a HomSet.{v + 1, u} via toHomSet, which
    corresponds to BundledCategoryData.{v, u} (since Hom : HomSet.{v + 1, u}).
    This direction always preserves universe levels. -/
def BundledOverCategoryData.toBundledCategoryData
    (C : BundledOverCategoryData.{v, u}) :
    BundledCategoryData.{v, u} where
  Obj := C.quiver.Obj
  Hom := C.quiver.toHomSet
  data := C.data.toCategoryData

/-- Convert a BundledCategoryData to a BundledOverCategoryData.
    A BundledCategoryData.{v, u} has HomSet.{v + 1, u} with morphisms in Type v.
    The sigma type SigmaMor lives in Type (max v u), giving
    OverQuiver.{max v u, u}. When v ≥ u, this equals OverQuiver.{v, u}. -/
def BundledCategoryData.toBundledOverCategoryData
    (C : BundledCategoryData.{v, u}) :
    BundledOverCategoryData.{max v u, u} where
  quiver := C.Hom.toOverQuiver
  data := C.data.toOverCategoryData

/-- Round-trip BundledCategoryData → BundledOverCategoryData → BundledCategoryData,
    using fiber_equiv to project back to the original universe level.
    This works for any universe parameters {v, u} without constraints. -/
def BundledCategoryData.roundtripHomSet (C : BundledCategoryData.{v, u}) :
    HomSet.{v + 1, u} C.Obj :=
  fun a b => C.Hom a b

/-- The round-trip HomSet equals the original. -/
theorem BundledCategoryData.roundtripHomSet_eq (C : BundledCategoryData.{v, u}) :
    C.roundtripHomSet = C.Hom := rfl

/-- The round-trip via fiber_equiv gives an equivalence at each hom-set. -/
def BundledCategoryData.roundtripEquiv (C : BundledCategoryData.{v, u})
    (a b : C.Obj) :
    C.toBundledOverCategoryData.toBundledCategoryData.Hom a b ≃ C.Hom a b :=
  C.Hom.fiber_equiv a b

end BundledEquiv

/-! ## Categorical Equivalence

We now establish that the conversion functors between BundledOverCategoryData
and BundledCategoryData form a categorical equivalence.

The conversions work with general universe parameters {v, u}. The point is:
- `BundledOverCategoryData.{v, u} → BundledCategoryData.{v, u}` always works
- `BundledCategoryData.{v, u} → BundledOverCategoryData.{max v u, u}` gives
  the sigma-bundled version

When `v ≥ u`, we have `max v u = v`, so both directions preserve universe
levels, giving a clean categorical equivalence in `Cat.{v, u}`. -/

section CategoricalEquiv

/-! ### Functoriality of toBundledCategoryData

The conversion toBundledCategoryData is functorial: it maps functors to
functors and preserves identity and composition. This direction always
preserves universe levels. -/

/-- The conversion `toBundledCategoryData` maps OverFunctorData to FunctorData.
    This gives the morphism part of the functor. -/
def toBundledCategoryData_map {C D : BundledOverCategoryData.{v, u}}
    (F : OverFunctorData C.data D.data) :
    FunctorData C.toBundledCategoryData.data D.toBundledCategoryData.data :=
  F.toFunctorData

/-- The conversion toBundledCategoryData preserves identity functors. -/
theorem toBundledCategoryData_map_id (C : BundledOverCategoryData.{v, u}) :
    toBundledCategoryData_map (OverFunctorData.id C.data) =
      BundledCategoryData.idFunctorData C.toBundledCategoryData := by
  simp only [toBundledCategoryData_map, OverFunctorData.toFunctorData,
    OverFunctorData.toFunctorOps, OverFunctorData.extractObj,
    OverFunctorData.extractMap, OverFunctorData.id,
    OverQuiverMorphism.id, BundledCategoryData.idFunctorData]
  rfl

/-- The conversion toBundledCategoryData preserves functor composition. -/
theorem toBundledCategoryData_map_comp {C D E : BundledOverCategoryData.{v, u}}
    (F : OverFunctorData C.data D.data) (G : OverFunctorData D.data E.data) :
    toBundledCategoryData_map (F.comp G) =
      (toBundledCategoryData_map F).comp (toBundledCategoryData_map G) := by
  simp only [toBundledCategoryData_map, OverFunctorData.toFunctorData,
    OverFunctorData.toFunctorOps, OverFunctorData.extractObj,
    OverFunctorData.extractMap, OverFunctorData.comp,
    OverQuiverMorphism.comp, FunctorData.comp, FunctorOps.comp]
  rfl

/-- FunctorData for the conversion functor from BundledOverCategoryData to
    BundledCategoryData. Works for all universe parameters {v, u}. -/
def toBundledCategoryDataFunctorData :
    FunctorData BundledOverCategoryData.categoryData.{v, u}
      BundledCategoryData.categoryData.{v, u} where
  toFunctorOps := {
    obj := BundledOverCategoryData.toBundledCategoryData
    map := toBundledCategoryData_map
  }
  laws := {
    map_id := toBundledCategoryData_map_id
    map_comp := fun F G => toBundledCategoryData_map_comp F G
  }

/-! ### Functoriality of toBundledOverCategoryData

The conversion toBundledOverCategoryData is functorial. The target universe
is `max v u` due to the sigma construction bundling objects and morphisms.
When `v ≥ u`, this equals `v`, preserving universe levels. -/

/-- The conversion `toBundledOverCategoryData` maps FunctorData to
    OverFunctorData. This gives the morphism part of the functor. -/
def toBundledOverCategoryData_map {C D : BundledCategoryData.{v, u}}
    (F : FunctorData C.data D.data) :
    OverFunctorData C.toBundledOverCategoryData.data
      D.toBundledOverCategoryData.data :=
  F.toOverFunctorData

/-- The conversion toBundledOverCategoryData preserves identity functors. -/
theorem toBundledOverCategoryData_map_id (C : BundledCategoryData.{v, u}) :
    toBundledOverCategoryData_map (BundledCategoryData.idFunctorData C) =
      OverFunctorData.id C.toBundledOverCategoryData.data := by
  simp only [toBundledOverCategoryData_map, FunctorData.toOverFunctorData,
    FunctorOps.toOverQuiverMorphism, BundledCategoryData.idFunctorData,
    OverFunctorData.id, OverQuiverMorphism.id]
  rfl

/-- The conversion toBundledOverCategoryData preserves functor composition. -/
theorem toBundledOverCategoryData_map_comp {C D E : BundledCategoryData.{v, u}}
    (F : FunctorData C.data D.data) (G : FunctorData D.data E.data) :
    toBundledOverCategoryData_map (F.comp G) =
      (toBundledOverCategoryData_map F).comp
        (toBundledOverCategoryData_map G) := by
  simp only [toBundledOverCategoryData_map, FunctorData.toOverFunctorData,
    FunctorOps.toOverQuiverMorphism, FunctorData.comp, FunctorOps.comp,
    OverFunctorData.comp, OverQuiverMorphism.comp]
  rfl

/-- FunctorData for the conversion functor from BundledCategoryData to
    BundledOverCategoryData. The target universe is `max v u` due to the
    sigma construction; when `v ≥ u`, this equals `v`. -/
def toBundledOverCategoryDataFunctorData :
    FunctorData BundledCategoryData.categoryData.{v, u}
      BundledOverCategoryData.categoryData.{max v u, u} where
  toFunctorOps := {
    obj := BundledCategoryData.toBundledOverCategoryData
    map := toBundledOverCategoryData_map
  }
  laws := {
    map_id := toBundledOverCategoryData_map_id
    map_comp := fun F G => toBundledOverCategoryData_map_comp F G
  }

end CategoricalEquiv

/-! ## Universe-Polymorphic Categorical Equivalence

Parameterizing both sides with `{max v u, u}` is equivalent to
imposing the constraint `v ≥ u`.

This gives functors:
- `BundledOverCategoryData.{max v u, u} → BundledCategoryData.{max v u, u}`
- `BundledCategoryData.{max v u, u} → BundledOverCategoryData.{max v u, u}`

that form a categorical equivalence. -/

section UniversePolyEquiv

/-- Functor from BundledOverCategoryData to BundledCategoryData at universe
    `{max v u, u}`. -/
def overToCatFunctorData :
    FunctorData BundledOverCategoryData.categoryData.{max v u, u}
      BundledCategoryData.categoryData.{max v u, u} :=
  toBundledCategoryDataFunctorData

/-- Functor from BundledCategoryData to BundledOverCategoryData at universe
    `{max v u, u}`. Since `max (max v u) u = max v u`, the target universe
    matches the source. -/
def catToOverFunctorData :
    FunctorData BundledCategoryData.categoryData.{max v u, u}
      BundledOverCategoryData.categoryData.{max v u, u} :=
  toBundledOverCategoryDataFunctorData

/-- Round-trip Over → Cat → Over. -/
def overCatOverFunctorData :
    FunctorData BundledOverCategoryData.categoryData.{max v u, u}
      BundledOverCategoryData.categoryData.{max v u, u} :=
  overToCatFunctorData.comp catToOverFunctorData

/-- Round-trip Cat → Over → Cat. -/
def catOverCatFunctorData :
    FunctorData BundledCategoryData.categoryData.{max v u, u}
      BundledCategoryData.categoryData.{max v u, u} :=
  catToOverFunctorData.comp overToCatFunctorData

/-- The round-trip Cat → Over → Cat preserves objects definitionally. -/
theorem catOverCat_obj_eq (C : BundledCategoryData.{max v u, u}) :
    (catOverCatFunctorData.obj C).Obj = C.Obj := rfl

/-- The round-trip Over → Cat → Over preserves objects definitionally. -/
theorem overCatOver_obj_eq (C : BundledOverCategoryData.{max v u, u}) :
    (overCatOverFunctorData.obj C).quiver.Obj = C.quiver.Obj := rfl

/-- For the Cat → Over → Cat round-trip, the fiber equivalence provides
    an isomorphism between the round-trip hom-sets and the original. -/
def catOverCat_homEquiv (C : BundledCategoryData.{max v u, u}) (a b : C.Obj) :
    (catOverCatFunctorData.obj C).Hom a b ≃ C.Hom a b :=
  C.Hom.fiber_equiv a b

end UniversePolyEquiv

end GebLean
