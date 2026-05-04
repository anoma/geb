import GebLean.PshInternalCat

open CategoryTheory Limits

namespace GebLean

universe u v w

variable {C : Type u} [Category.{v} C]
variable (X : PshInternalCat.{u, v, w} C)
variable (c : Cᵒᵖ)

/-- The type of objects of the fiber category
at stage `c`. -/
abbrev fiberObj :=
  X.objPresheaf.obj c

/-- The type of all morphisms of the fiber
category at stage `c`. -/
abbrev fiberMor :=
  X.morPresheaf.obj c

/-- The source function of the fiber category
at stage `c`. -/
abbrev fiberSrc :
    fiberMor X c → fiberObj X c :=
  X.src.app c

/-- The target function of the fiber category
at stage `c`. -/
abbrev fiberTgt :
    fiberMor X c → fiberObj X c :=
  X.tgt.app c

/-- The identity assignment of the fiber category
at stage `c`. -/
abbrev fiberId :
    fiberObj X c → fiberMor X c :=
  X.idMap.app c

/-- The type of composable pairs in the fiber
category at stage `c`: the presheaf of composable
pairs evaluated at `c`. -/
abbrev fiberCompPairs :=
  (pshProdOverComp X.morSpan X.morSpan).left.obj c

/-- The composition function of the fiber category
at stage `c`. -/
abbrev fiberComp :
    fiberCompPairs X c → fiberMor X c :=
  X.compMap.app c

/-- The hom-type of the fiber category at stage
`c`: morphisms with specified source and target. -/
def fiberHom
    (a b : fiberObj X c) : Type w :=
  { m : fiberMor X c //
    fiberSrc X c m = a ∧ fiberTgt X c m = b }

/-- Composing the identity assignment with the
source map yields the identity. -/
@[simp]
theorem fiberIdMap_src :
    X.idMap ≫ X.src = 𝟙 X.objPresheaf := by
  change (MonObj.one (X := X.cat.X)).left ≫
    X.morSpan.hom ≫ pshProdFst _ _ = 𝟙 _
  rw [← Category.assoc,
    Over.w (MonObj.one (X := X.cat.X))]
  change pshProdLift (𝟙 X.objPresheaf)
    (𝟙 X.objPresheaf) ≫ pshProdFst _ _ =
    𝟙 X.objPresheaf
  simp [pshProdLift]

/-- Composing the identity assignment with the
target map yields the identity. -/
@[simp]
theorem fiberIdMap_tgt :
    X.idMap ≫ X.tgt = 𝟙 X.objPresheaf := by
  change (MonObj.one (X := X.cat.X)).left ≫
    X.morSpan.hom ≫ pshProdSnd _ _ = 𝟙 _
  rw [← Category.assoc,
    Over.w (MonObj.one (X := X.cat.X))]
  change pshProdLift (𝟙 X.objPresheaf)
    (𝟙 X.objPresheaf) ≫ pshProdSnd _ _ =
    𝟙 X.objPresheaf
  simp [pshProdLift]

/-- The source of the identity morphism at `a`
is `a`. -/
@[simp]
theorem fiberSrc_id
    (a : fiberObj X c) :
    fiberSrc X c (fiberId X c a) = a :=
  congr_fun (NatTrans.congr_app
    (fiberIdMap_src X) c) a

/-- The target of the identity morphism at `a`
is `a`. -/
@[simp]
theorem fiberTgt_id
    (a : fiberObj X c) :
    fiberTgt X c (fiberId X c a) = a :=
  congr_fun (NatTrans.congr_app
    (fiberIdMap_tgt X) c) a

/-- The identity element of `fiberHom`. -/
def fiberIdHom
    (a : fiberObj X c) : fiberHom X c a a :=
  ⟨fiberId X c a,
    ⟨fiberSrc_id X c a, fiberTgt_id X c a⟩⟩

/-- Extensionality for `fiberHom`: two morphisms
are equal when their underlying elements are. -/
@[ext]
theorem fiberHom_ext
    {a b : fiberObj X c}
    {f g : fiberHom X c a b}
    (h : f.val = g.val) : f = g :=
  Subtype.ext h

/-- Given composable morphisms `f : a ⟶ b` and
`g : b ⟶ c`, construct the composable pair as
an element of the pullback presheaf. -/
def fiberMkCompPair
    {a b d : fiberObj X c}
    (f : fiberHom X c a b)
    (g : fiberHom X c b d) :
    fiberCompPairs X c :=
  ⟨⟨f.val, g.val⟩, f.2.2.trans g.2.1.symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- The source of a composite equals the source
of the first morphism. -/
@[simp]
theorem fiberCompMap_src :
    X.compMap ≫ X.src =
      presheafPullbackFst X.tgt X.src ≫
        X.src := by
  change (MonObj.mul (X := X.cat.X)).left ≫
    X.morSpan.hom ≫ pshProdFst _ _ =
    presheafPullbackFst X.tgt X.src ≫
      X.morSpan.hom ≫ pshProdFst _ _
  rw [← Category.assoc,
    Over.w (MonObj.mul (X := X.cat.X))]
  change pshProdLift
    (presheafPullbackFst X.tgt X.src ≫ X.src)
    (presheafPullbackSnd X.tgt X.src ≫ X.tgt)
      ≫ pshProdFst _ _ =
    presheafPullbackFst X.tgt X.src ≫
      X.morSpan.hom ≫ pshProdFst _ _
  simp [pshProdLift]

set_option backward.isDefEq.respectTransparency false in
/-- The target of a composite equals the target
of the second morphism. -/
@[simp]
theorem fiberCompMap_tgt :
    X.compMap ≫ X.tgt =
      presheafPullbackSnd X.tgt X.src ≫
        X.tgt := by
  change (MonObj.mul (X := X.cat.X)).left ≫
    X.morSpan.hom ≫ pshProdSnd _ _ =
    presheafPullbackSnd X.tgt X.src ≫
      X.morSpan.hom ≫ pshProdSnd _ _
  rw [← Category.assoc,
    Over.w (MonObj.mul (X := X.cat.X))]
  change pshProdLift
    (presheafPullbackFst X.tgt X.src ≫ X.src)
    (presheafPullbackSnd X.tgt X.src ≫ X.tgt)
      ≫ pshProdSnd _ _ =
    presheafPullbackSnd X.tgt X.src ≫
      X.morSpan.hom ≫ pshProdSnd _ _
  simp [pshProdLift]

/-- Pointwise: the source of a composite equals
the source of the first morphism. -/
@[simp]
theorem fiberSrc_comp
    (p : fiberCompPairs X c) :
    fiberSrc X c (fiberComp X c p) =
      fiberSrc X c p.val.1 :=
  congr_fun (NatTrans.congr_app
    (fiberCompMap_src X) c) p

/-- Pointwise: the target of a composite equals
the target of the second morphism. -/
@[simp]
theorem fiberTgt_comp
    (p : fiberCompPairs X c) :
    fiberTgt X c (fiberComp X c p) =
      fiberTgt X c p.val.2 :=
  congr_fun (NatTrans.congr_app
    (fiberCompMap_tgt X) c) p

/-- Composition of morphisms in the fiber
category. -/
def fiberCompHom
    {a b d : fiberObj X c}
    (f : fiberHom X c a b)
    (g : fiberHom X c b d) :
    fiberHom X c a d :=
  let p := fiberMkCompPair X c f g
  ⟨fiberComp X c p,
    ⟨(fiberSrc_comp X c p).trans f.2.1,
     (fiberTgt_comp X c p).trans g.2.2⟩⟩

/-- Left identity: `id ≫ f = f`. -/
theorem fiberComp_id_left
    {a b : fiberObj X c}
    (f : fiberHom X c a b) :
    fiberCompHom X c (fiberIdHom X c a) f =
      f := by
  apply fiberHom_ext
  let q : (pshProdOverComp
      (pshProdOverId X.objPresheaf)
      X.morSpan).left.obj c :=
    ⟨(a, f.val), f.2.1.symm⟩
  have h := congr_fun (NatTrans.congr_app
    (congrArg (·.left)
      (MonObj.one_mul (X := X.cat.X)))
    c) q
  dsimp only [] at h
  convert h using 1

/-- Right identity: `f ≫ id = f`. -/
theorem fiberComp_id_right
    {a b : fiberObj X c}
    (f : fiberHom X c a b) :
    fiberCompHom X c f (fiberIdHom X c b) =
      f := by
  apply fiberHom_ext
  let q : (pshProdOverComp
      X.morSpan
      (pshProdOverId X.objPresheaf)).left.obj c :=
    ⟨(f.val, b), f.2.2⟩
  have h := congr_fun (NatTrans.congr_app
    (congrArg (·.left)
      (MonObj.mul_one (X := X.cat.X)))
    c) q
  dsimp only [] at h
  convert h using 1

/-- Associativity:
`(f ≫ g) ≫ h = f ≫ (g ≫ h)`. -/
theorem fiberComp_assoc
    {a b d e : fiberObj X c}
    (f : fiberHom X c a b)
    (g : fiberHom X c b d)
    (h : fiberHom X c d e) :
    fiberCompHom X c
      (fiberCompHom X c f g) h =
      fiberCompHom X c f
        (fiberCompHom X c g h) := by
  apply fiberHom_ext
  let pair_fg : (pshProdOverComp
      X.morSpan X.morSpan).left.obj c :=
    fiberMkCompPair X c f g
  let q : (pshProdOverComp
      (pshProdOverComp X.morSpan X.morSpan)
      X.morSpan).left.obj c :=
    ⟨(pair_fg, h.val),
      g.2.2.trans h.2.1.symm⟩
  have hax := congr_fun (NatTrans.congr_app
    (congrArg (·.left)
      (MonObj.mul_assoc (X := X.cat.X)))
    c) q
  dsimp only [] at hax
  convert hax using 1

/-- The category structure on the fiber of an
internal category at stage `c`. -/
instance fiberCategory :
    Category (fiberObj X c) where
  Hom := fiberHom X c
  id := fiberIdHom X c
  comp f g := fiberCompHom X c f g
  id_comp := fiberComp_id_left X c
  comp_id := fiberComp_id_right X c
  assoc f g h := fiberComp_assoc X c f g h

variable {c}

/-- The restriction functor along a morphism
`f : c ⟶ c'` in `Cᵒᵖ`.  Sends each object and
morphism of the fiber at `c` to the fiber at `c'`
by applying the presheaf actions. -/
def fiberRestrict
    {c c' : Cᵒᵖ} (f : c ⟶ c') :
    fiberObj X c ⥤ fiberObj X c' where
  obj a := X.objPresheaf.map f a
  map {a b} m := ⟨X.morPresheaf.map f m.val, by
    constructor
    · change (X.morPresheaf.map f ≫
        X.src.app c') m.val =
        X.objPresheaf.map f a
      rw [X.src.naturality f]
      exact congrArg _ m.2.1
    · change (X.morPresheaf.map f ≫
        X.tgt.app c') m.val =
        X.objPresheaf.map f b
      rw [X.tgt.naturality f]
      exact congrArg _ m.2.2⟩
  map_id a := by
    apply fiberHom_ext
    have h := congr_fun
      (X.idMap.naturality f) a
    dsimp at h
    exact h.symm
  map_comp {a b d} m n := by
    apply fiberHom_ext
    have h := congr_fun
      (X.compMap.naturality f)
      (fiberMkCompPair X c m n)
    dsimp at h
    exact h.symm

/-- Composing `eqToHom` on the left preserves the
underlying morphism value. -/
theorem fiberHom_val_eqToHom_comp
    {a b d : fiberObj X c}
    (h : a = b) (f : b ⟶ d) :
    (eqToHom h ≫ f).val = f.val := by
  subst h
  exact congrArg Subtype.val (Category.id_comp f)

/-- Composing `eqToHom` on the right preserves the
underlying morphism value. -/
theorem fiberHom_val_comp_eqToHom
    {a b d : fiberObj X c}
    (f : a ⟶ b) (h : b = d) :
    (f ≫ eqToHom h).val = f.val := by
  subst h
  exact congrArg Subtype.val (Category.comp_id f)

/-- Restriction along the identity morphism is
the identity functor. -/
theorem fiberRestrict_id
    (c : Cᵒᵖ) :
    fiberRestrict X (𝟙 c) = 𝟭 _ := by
  refine CategoryTheory.Functor.ext
    (fun a ↦ congr_fun
      (X.objPresheaf.map_id c) a)
    (fun {a b} f ↦ ?_)
  apply Subtype.ext
  simp only [fiberRestrict,
    fiberHom_val_eqToHom_comp,
    fiberHom_val_comp_eqToHom,
    Functor.id_map]
  exact congr_fun
    (X.morPresheaf.map_id c) f.val

/-- Restriction along a composite morphism equals
the composition of the individual restrictions. -/
theorem fiberRestrict_comp
    {c c' c'' : Cᵒᵖ}
    (f : c ⟶ c') (g : c' ⟶ c'') :
    fiberRestrict X (f ≫ g) =
      fiberRestrict X f ⋙ fiberRestrict X g := by
  refine CategoryTheory.Functor.ext
    (fun a ↦ congr_fun
      (X.objPresheaf.map_comp f g) a)
    (fun {a b} m ↦ ?_)
  apply Subtype.ext
  simp only [fiberRestrict,
    fiberHom_val_eqToHom_comp,
    fiberHom_val_comp_eqToHom,
    Functor.comp_map]
  exact congr_fun
    (X.morPresheaf.map_comp f g) m.val

/-- The externalization of an internal category:
a functor from `Cᵒᵖ` to `Cat` sending each stage
to its fiber category and each morphism to the
restriction functor. -/
def externalize :
    Cᵒᵖ ⥤ Cat.{w, w} where
  obj c := Cat.of (fiberObj X c)
  map f := Cat.Hom.ofFunctor (fiberRestrict X f)
  map_id c := Cat.Hom.ext (fiberRestrict_id X c)
  map_comp f g :=
    Cat.Hom.ext (fiberRestrict_comp X f g)

variable {X}

set_option backward.isDefEq.respectTransparency false in
/-- An internal functor preserves source:
`morMap ≫ Y.src = X.src ≫ objMap`. -/
theorem PshInternalFunctor.morMap_src
    {Y : PshInternalCat.{u, v, w} C}
    (F : PshInternalFunctor X Y) :
    F.morMap ≫ Y.src = X.src ≫ F.objMap := by
  calc F.morMap ≫ Y.src
      = F.morMap ≫ Y.morSpan.hom ≫
          pshProdFst _ _ := by
        rfl
    _ = (X.morSpan.hom ≫
          pshProdMap F.objMap F.objMap) ≫
          pshProdFst _ _ := by
        rw [← Category.assoc, F.compat]
    _ = X.morSpan.hom ≫
          pshProdMap F.objMap F.objMap ≫
          pshProdFst _ _ := by
        rw [Category.assoc]
    _ = X.src ≫ F.objMap := by
        simp

set_option backward.isDefEq.respectTransparency false in
/-- An internal functor preserves target:
`morMap ≫ Y.tgt = X.tgt ≫ objMap`. -/
theorem PshInternalFunctor.morMap_tgt
    {Y : PshInternalCat.{u, v, w} C}
    (F : PshInternalFunctor X Y) :
    F.morMap ≫ Y.tgt = X.tgt ≫ F.objMap := by
  calc F.morMap ≫ Y.tgt
      = F.morMap ≫ Y.morSpan.hom ≫
          pshProdSnd _ _ := by
        rfl
    _ = (X.morSpan.hom ≫
          pshProdMap F.objMap F.objMap) ≫
          pshProdSnd _ _ := by
        rw [← Category.assoc, F.compat]
    _ = X.morSpan.hom ≫
          pshProdMap F.objMap F.objMap ≫
          pshProdSnd _ _ := by
        rw [Category.assoc]
    _ = X.tgt ≫ F.objMap := by
        simp

/-- The fiber functor induced by an internal
functor at stage `c`. -/
def pshIntFiberFunctor
    {Y : PshInternalCat.{u, v, w} C}
    (F : PshInternalFunctor X Y)
    (c : Cᵒᵖ) :
    fiberObj X c ⥤ fiberObj Y c where
  obj a := F.objMap.app c a
  map {a b} m :=
    ⟨F.morMap.app c m.val, by
      constructor
      · exact congr_fun (NatTrans.congr_app
          F.morMap_src c) m.val
          |>.trans (congrArg _ m.2.1)
      · exact congr_fun (NatTrans.congr_app
          F.morMap_tgt c) m.val
          |>.trans (congrArg _ m.2.2)⟩
  map_id a := by
    apply fiberHom_ext
    exact congr_fun (NatTrans.congr_app
      F.id_pres c) a
  map_comp {a b d} m n := by
    apply fiberHom_ext
    dsimp only [fiberCompHom, fiberMkCompPair,
      fiberComp]
    exact congr_fun (NatTrans.congr_app
      F.comp_pres c)
      (fiberMkCompPair X c m n)

set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation between externalized
categories induced by an internal functor. -/
def externalizeNatTrans
    {Y : PshInternalCat.{u, v, w} C}
    (F : PshInternalFunctor X Y) :
    externalize X ⟶ externalize Y where
  app c :=
    Cat.Hom.ofFunctor (pshIntFiberFunctor F c)
  naturality c c' f := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext
      (fun a ↦ congr_fun
        (F.objMap.naturality f) a)
      (fun {a b} m ↦ ?_)
    apply Subtype.ext
    rw [fiberHom_val_eqToHom_comp,
      fiberHom_val_comp_eqToHom]
    exact congr_fun
      (F.morMap.naturality f) m.val

/-- The fiber functor of the identity internal
functor is the identity functor. -/
theorem pshIntFiberFunctor_id
    (c : Cᵒᵖ) :
    pshIntFiberFunctor (PshInternalFunctor.id X) c =
      𝟭 _ := by
  refine CategoryTheory.Functor.ext
    (fun a ↦ rfl)
    (fun {a b} m ↦ ?_)
  apply Subtype.ext
  rw [fiberHom_val_eqToHom_comp,
    fiberHom_val_comp_eqToHom]
  rfl

/-- `externalizeNatTrans` sends the identity
internal functor to the identity natural
transformation. -/
theorem externalizeNatTrans_id :
    externalizeNatTrans
      (PshInternalFunctor.id X) =
      𝟙 (externalize X) := by
  apply NatTrans.ext
  funext c
  exact Cat.Hom.ext (pshIntFiberFunctor_id (X := X) c)

/-- The fiber functor of a composite internal
functor is the composite of the fiber functors. -/
theorem pshIntFiberFunctor_comp
    {Y Z : PshInternalCat.{u, v, w} C}
    (F : PshInternalFunctor X Y)
    (G : PshInternalFunctor Y Z)
    (c : Cᵒᵖ) :
    pshIntFiberFunctor (PshInternalFunctor.comp F G) c =
      pshIntFiberFunctor F c ⋙ pshIntFiberFunctor G c := by
  refine CategoryTheory.Functor.ext
    (fun a ↦ rfl)
    (fun {a b} m ↦ ?_)
  apply Subtype.ext
  rw [fiberHom_val_eqToHom_comp,
    fiberHom_val_comp_eqToHom]
  rfl

/-- `externalizeNatTrans` preserves composition
of internal functors. -/
theorem externalizeNatTrans_comp
    {Y Z : PshInternalCat.{u, v, w} C}
    (F : PshInternalFunctor X Y)
    (G : PshInternalFunctor Y Z) :
    externalizeNatTrans
      (PshInternalFunctor.comp F G) =
      externalizeNatTrans F ≫
        externalizeNatTrans G := by
  apply NatTrans.ext
  funext c
  exact Cat.Hom.ext (pshIntFiberFunctor_comp F G c)

section DiscreteUnitCompat

universe w'

variable
    (Y : PshInternalCat.{0, 0, w'}
      (Discrete Unit))

/-- The object type of `externalize Y` at the
unique stage equals the object type of the
`DiscreteUnitEquiv` construction. -/
theorem fiberObj_eq_icObj :
    fiberObj Y (Opposite.op ⟨⟨⟩⟩) = icObj Y :=
  rfl

/-- The hom-type of `fiberCategory` at the unique
stage equals the hom-type of `icCategory`. -/
theorem fiberHom_eq_icHom
    (a b : fiberObj Y (Opposite.op ⟨⟨⟩⟩)) :
    fiberHom Y (Opposite.op ⟨⟨⟩⟩) a b =
      icHom Y a b :=
  rfl

/-- The identity morphism of `fiberCategory` at
the unique stage equals the identity morphism of
`icCategory`. -/
theorem fiberIdHom_eq_icId
    (a : fiberObj Y (Opposite.op ⟨⟨⟩⟩)) :
    fiberIdHom Y (Opposite.op ⟨⟨⟩⟩) a =
      icId Y a :=
  rfl

/-- Composition in `fiberCategory` at the unique
stage equals composition in `icCategory`. -/
theorem fiberCompHom_eq_icComp
    {a b d : fiberObj Y (Opposite.op ⟨⟨⟩⟩)}
    (f : fiberHom Y (Opposite.op ⟨⟨⟩⟩) a b)
    (g : fiberHom Y (Opposite.op ⟨⟨⟩⟩) b d) :
    fiberCompHom Y (Opposite.op ⟨⟨⟩⟩) f g =
      icComp Y f g :=
  rfl

/-- The `fiberCategory` instance at the unique
stage equals the `icCategory` instance. -/
theorem fiberCategory_eq_icCategory :
    (fiberCategory Y (Opposite.op ⟨⟨⟩⟩)) =
      icCategory Y :=
  rfl

/-- The `Cat` object produced by `externalize` at
the unique stage equals `pshInternalCatToCat`. -/
theorem externalize_unit_obj_eq :
    (externalize Y).obj (Opposite.op ⟨⟨⟩⟩) =
      pshInternalCatToCat Y :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The fiber functor at the unique stage equals
`pshInternalFunctorToFunctor`: the externalization's
action on internal functors agrees with the
`DiscreteUnitEquiv` construction. -/
theorem pshIntFiberFunctor_eq_pshInternalFunctorToFunctor
    {Z : PshInternalCat.{0, 0, w'}
      (Discrete Unit)}
    (F : PshInternalFunctor Y Z) :
    pshIntFiberFunctor F (Opposite.op ⟨⟨⟩⟩) =
      pshInternalFunctorToFunctor F := by
  refine CategoryTheory.Functor.ext
    (fun a ↦ rfl) (fun {a b} f ↦ ?_)
  simp only [eqToHom_refl, Category.id_comp,
    Category.comp_id]
  apply Subtype.ext
  rfl

/-- The `Cat` morphism produced by
`externalizeNatTrans` at the unique stage
equals the one produced by
`pshInternalCatToCatFunctor`. -/
theorem externalizeNatTrans_unit_eq
    {Z : PshInternalCat.{0, 0, w'}
      (Discrete Unit)}
    (F : PshInternalFunctor Y Z) :
    (externalizeNatTrans F).app
      (Opposite.op ⟨⟨⟩⟩) =
      pshInternalCatToCatFunctor.map F := by
  apply Cat.Hom.ext
  exact
    pshIntFiberFunctor_eq_pshInternalFunctorToFunctor
      Y F

end DiscreteUnitCompat

end GebLean
