/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Model
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Tactic.CategoryTheory.Reassoc

set_option doc.verso true in
/-!
# The category of a model of the theory of an elementary topos

A model of the theory is a category: its objects are the model's objects, and a morphism from
one object to another is an arrow with that domain and codomain; identities and composition are
the model's, and the laws of a category are the category block's axioms. Each further block of
axioms gives the category a universal morphism and its universal property: the finite limits and
colimits, the exponential, the subobject classifier, the natural numbers object,
the list object of each object, and the rose-tree object, initial among algebras of the
functor {lit}`x ↦ nat × list x`.

## Main definitions

* {lit}`ToposModel.Cat` — the objects of a model, carrying its category.
* {lit}`ToposModel.prodLift`, {lit}`ToposModel.equalizerLift`, {lit}`ToposModel.coprodDesc`,
  {lit}`ToposModel.coequalizerDesc`, {lit}`ToposModel.curry` — the universal morphisms of the
  finite limits and colimits and of the exponential.
* {lit}`ToposModel.chiHom`, {lit}`ToposModel.chiLift` — the characteristic map of a
  monomorphism and the factorization through it of a morphism along which that map is truth.
* {lit}`ToposModel.natRec`, {lit}`ToposModel.listRec`, {lit}`ToposModel.roseRec` — recursion
  from the natural numbers object, from a list object and from the rose-tree object.

## Main statements

* {lit}`ToposModel.chiHom_uniq` — the characteristic map is the unique morphism along which the
  monomorphism is a pullback of truth.
* {lit}`ToposModel.natRec_uniq`, {lit}`ToposModel.listRec_uniq`, {lit}`ToposModel.roseRec_uniq` —
  a morphism satisfying the recursion equations is the recursion.

## Tags

elementary topos, model, category
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

open CategoryTheory

universe v

namespace ToposModel

variable (T : ToposModel.{v})

/-- The objects of a model, carrying the model's category. -/
abbrev Cat : Type v := T.Obj

instance : Category T.Cat where
  Hom a b := {f : T.Ar // T.domOf f = a ∧ T.codOf f = b}
  id a := ⟨T.idOf a, T.domOf_idOf a, T.codOf_idOf a⟩
  comp f g := ⟨T.compOf g.1 f.1 (f.2.2.trans g.2.1.symm),
    (T.domOf_compOf _).trans f.2.1, (T.codOf_compOf _).trans g.2.2⟩
  id_comp f := by
    obtain ⟨f, rfl, rfl⟩ := f
    exact Subtype.ext (T.compOf_idOf f)
  comp_id f := by
    obtain ⟨f, rfl, rfl⟩ := f
    exact Subtype.ext (T.idOf_compOf f)
  assoc f g h := by
    obtain ⟨f, rfl, rfl⟩ := f
    obtain ⟨g, hg, rfl⟩ := g
    obtain ⟨h, hh, rfl⟩ := h
    exact Subtype.ext (T.compOf_assoc hg.symm hh.symm)

variable {T}

/-- Two morphisms of the model's category are equal when their arrows are. -/
theorem hom_ext {a b : T.Cat} {f g : a ⟶ b} (h : f.1 = g.1) : f = g := Subtype.ext h

/-- The arrow of a composite is the composite of the arrows. -/
theorem comp_val {a b c : T.Cat} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).1 = T.compOf g.1 f.1 (f.2.2.trans g.2.1.symm) := rfl

/-- The arrow of an identity is the identity of the object. -/
theorem id_val (a : T.Cat) : (𝟙 a : a ⟶ a).1 = T.idOf a := rfl

variable (T)

/-- The terminal object, as an object of the category. -/
abbrev one : T.Cat := T.oneOf

/-- The morphism from an object to the terminal object. -/
def toOne (a : T.Cat) : a ⟶ T.one := ⟨T.bangOf a, T.domOf_bangOf a, T.codOf_bangOf a⟩

/-- A morphism to the terminal object is the morphism from its domain. -/
theorem toOne_uniq {a : T.Cat} (f : a ⟶ T.one) : f = T.toOne a := by
  obtain ⟨f, rfl, hf⟩ := f
  exact Subtype.ext (T.eq_bangOf hf)

/-- The product of two objects, as an object of the category. -/
abbrev prod (a b : T.Cat) : T.Cat := T.prodOf a b

/-- The first projection of a product. -/
def prodFst (a b : T.Cat) : T.prod a b ⟶ a := ⟨T.fstOf a b, T.domOf_fstOf a b, T.codOf_fstOf a b⟩

/-- The second projection of a product. -/
def prodSnd (a b : T.Cat) : T.prod a b ⟶ b := ⟨T.sndOf a b, T.domOf_sndOf a b, T.codOf_sndOf a b⟩

variable {T}

/-- The pairing of two morphisms of one domain. -/
def prodLift {a b c : T.Cat} (f : c ⟶ a) (g : c ⟶ b) : c ⟶ T.prod a b :=
  ⟨T.pairOf f.1 g.1 (f.2.1.trans g.2.1.symm), (T.domOf_pairOf _).trans f.2.1,
    (T.codOf_pairOf _).trans (by rw [f.2.2, g.2.2])⟩

/-- A pairing after the first projection is its first component. -/
@[reassoc]
theorem prodLift_fst {a b c : T.Cat} (f : c ⟶ a) (g : c ⟶ b) :
    prodLift f g ≫ T.prodFst a b = f := by
  obtain ⟨f, rfl, rfl⟩ := f
  obtain ⟨g, hg, rfl⟩ := g
  exact Subtype.ext (T.fstOf_pairOf hg.symm)

/-- A pairing after the second projection is its second component. -/
@[reassoc]
theorem prodLift_snd {a b c : T.Cat} (f : c ⟶ a) (g : c ⟶ b) :
    prodLift f g ≫ T.prodSnd a b = g := by
  obtain ⟨f, rfl, rfl⟩ := f
  obtain ⟨g, hg, rfl⟩ := g
  exact Subtype.ext (T.sndOf_pairOf hg.symm)

/-- A morphism into a product is the pairing of its composites with the projections. -/
theorem prodLift_uniq {a b c : T.Cat} (m : c ⟶ T.prod a b) :
    m = prodLift (m ≫ T.prodFst a b) (m ≫ T.prodSnd a b) := by
  obtain ⟨m, rfl, hm⟩ := m
  exact Subtype.ext (T.pairOf_eta hm).symm

/-- Two parallel morphisms of the category have parallel arrows. -/
theorem par_of_hom {a b : T.Cat} (f g : a ⟶ b) : T.Par f.1 g.1 :=
  ⟨f.2.1.trans g.2.1.symm, f.2.2.trans g.2.2.symm⟩

/-- The equalizer of two parallel morphisms, as an object of the category. -/
abbrev equalizer {a b : T.Cat} (f g : a ⟶ b) : T.Cat := T.eqzOf f.1 g.1 (par_of_hom f g)

/-- The inclusion of an equalizer. -/
def equalizerι {a b : T.Cat} (f g : a ⟶ b) : equalizer f g ⟶ a :=
  ⟨T.eqInclOf f.1 g.1 (par_of_hom f g), T.domOf_eqInclOf (par_of_hom f g),
    (T.codOf_eqInclOf (par_of_hom f g)).trans f.2.1⟩

/-- An equalizer's inclusion equalizes the morphisms. -/
@[reassoc]
theorem equalizerι_condition {a b : T.Cat} (f g : a ⟶ b) :
    equalizerι f g ≫ f = equalizerι f g ≫ g :=
  Subtype.ext (T.compOf_eqInclOf (par_of_hom f g))

/-- The factorization through an equalizer of a morphism that equalizes the pair. -/
def equalizerLift {a b c : T.Cat} {f g : a ⟶ b} (k : c ⟶ a) (w : k ≫ f = k ≫ g) :
    c ⟶ equalizer f g :=
  ⟨T.eqLiftOf f.1 g.1 k.1 (par_of_hom f g) (k.2.2.trans f.2.1.symm) (congrArg Subtype.val w),
    (T.domOf_eqLiftOf (par_of_hom f g) (k.2.2.trans f.2.1.symm) (congrArg Subtype.val w)).trans
      k.2.1,
    T.codOf_eqLiftOf (par_of_hom f g) (k.2.2.trans f.2.1.symm) (congrArg Subtype.val w)⟩

/-- A factorization through an equalizer after the inclusion is the factored morphism. -/
@[reassoc]
theorem equalizerLift_ι {a b c : T.Cat} {f g : a ⟶ b} (k : c ⟶ a) (w : k ≫ f = k ≫ g) :
    equalizerLift k w ≫ equalizerι f g = k :=
  Subtype.ext (T.eqInclOf_eqLiftOf (par_of_hom f g) (k.2.2.trans f.2.1.symm)
    (congrArg Subtype.val w))

/-- A morphism into an equalizer is the factorization of its composite with the inclusion. -/
theorem equalizerLift_uniq {a b c : T.Cat} {f g : a ⟶ b} (m : c ⟶ equalizer f g) :
    m = equalizerLift (m ≫ equalizerι f g)
      (by rw [Category.assoc, equalizerι_condition, ← Category.assoc]) := by
  obtain ⟨m, rfl, hm⟩ := m
  exact Subtype.ext (T.eqLiftOf_eta (par_of_hom f g) hm).symm

variable (T)

/-- The initial object, as an object of the category. -/
abbrev zero : T.Cat := T.zeroOf

/-- The morphism from the initial object to an object. -/
def fromZero (a : T.Cat) : T.zero ⟶ a := ⟨T.absurdOf a, T.domOf_absurdOf a, T.codOf_absurdOf a⟩

/-- A morphism from the initial object is the morphism to its codomain. -/
theorem fromZero_uniq {a : T.Cat} (f : T.zero ⟶ a) : f = T.fromZero a := by
  obtain ⟨f, hf, rfl⟩ := f
  exact Subtype.ext (T.eq_absurdOf hf)

/-- The coproduct of two objects, as an object of the category. -/
abbrev coprod (a b : T.Cat) : T.Cat := T.coprodOf a b

/-- The first injection into a coproduct. -/
def coprodInl (a b : T.Cat) : a ⟶ T.coprod a b :=
  ⟨T.inlOf a b, T.domOf_inlOf a b, T.codOf_inlOf a b⟩

/-- The second injection into a coproduct. -/
def coprodInr (a b : T.Cat) : b ⟶ T.coprod a b :=
  ⟨T.inrOf a b, T.domOf_inrOf a b, T.codOf_inrOf a b⟩

variable {T}

/-- The copairing of two morphisms of one codomain. -/
def coprodDesc {a b c : T.Cat} (f : a ⟶ c) (g : b ⟶ c) : T.coprod a b ⟶ c :=
  ⟨T.copairOf f.1 g.1 (f.2.2.trans g.2.2.symm), (T.domOf_copairOf _).trans (by rw [f.2.1, g.2.1]),
    (T.codOf_copairOf _).trans f.2.2⟩

/-- The first injection after a copairing is its first component. -/
@[reassoc]
theorem coprodInl_desc {a b c : T.Cat} (f : a ⟶ c) (g : b ⟶ c) :
    T.coprodInl a b ≫ coprodDesc f g = f := by
  obtain ⟨f, rfl, rfl⟩ := f
  obtain ⟨g, rfl, hg⟩ := g
  exact Subtype.ext (T.copairOf_inlOf hg.symm)

/-- The second injection after a copairing is its second component. -/
@[reassoc]
theorem coprodInr_desc {a b c : T.Cat} (f : a ⟶ c) (g : b ⟶ c) :
    T.coprodInr a b ≫ coprodDesc f g = g := by
  obtain ⟨f, rfl, rfl⟩ := f
  obtain ⟨g, rfl, hg⟩ := g
  exact Subtype.ext (T.copairOf_inrOf hg.symm)

/-- A morphism from a coproduct is the copairing of its composites with the injections. -/
theorem coprodDesc_uniq {a b c : T.Cat} (m : T.coprod a b ⟶ c) :
    m = coprodDesc (T.coprodInl a b ≫ m) (T.coprodInr a b ≫ m) := by
  obtain ⟨m, hm, rfl⟩ := m
  exact Subtype.ext (T.copairOf_eta hm).symm

/-- The coequalizer of two parallel morphisms, as an object of the category. -/
abbrev coequalizer {a b : T.Cat} (f g : a ⟶ b) : T.Cat := T.coeqzOf f.1 g.1 (par_of_hom f g)

/-- The projection onto a coequalizer. -/
def coequalizerπ {a b : T.Cat} (f g : a ⟶ b) : b ⟶ coequalizer f g :=
  ⟨T.coeqProjOf f.1 g.1 (par_of_hom f g), (T.domOf_coeqProjOf (par_of_hom f g)).trans f.2.2,
    T.codOf_coeqProjOf (par_of_hom f g)⟩

/-- A coequalizer's projection coequalizes the morphisms. -/
@[reassoc]
theorem coequalizerπ_condition {a b : T.Cat} (f g : a ⟶ b) :
    f ≫ coequalizerπ f g = g ≫ coequalizerπ f g :=
  Subtype.ext (T.compOf_coeqProjOf (par_of_hom f g))

/-- The descent through a coequalizer of a morphism that coequalizes the pair. -/
def coequalizerDesc {a b c : T.Cat} {f g : a ⟶ b} (k : b ⟶ c) (w : f ≫ k = g ≫ k) :
    coequalizer f g ⟶ c :=
  ⟨T.coeqDescOf f.1 g.1 k.1 (par_of_hom f g) (f.2.2.trans k.2.1.symm) (congrArg Subtype.val w),
    T.domOf_coeqDescOf (par_of_hom f g) (f.2.2.trans k.2.1.symm) (congrArg Subtype.val w),
    (T.codOf_coeqDescOf (par_of_hom f g) (f.2.2.trans k.2.1.symm)
      (congrArg Subtype.val w)).trans k.2.2⟩

/-- The projection after a descent through a coequalizer is the descended morphism. -/
@[reassoc]
theorem coequalizerπ_desc {a b c : T.Cat} {f g : a ⟶ b} (k : b ⟶ c) (w : f ≫ k = g ≫ k) :
    coequalizerπ f g ≫ coequalizerDesc k w = k :=
  Subtype.ext (T.coeqDescOf_coeqProjOf (par_of_hom f g) (f.2.2.trans k.2.1.symm)
    (congrArg Subtype.val w))

/-- A morphism from a coequalizer is the descent of its composite with the projection. -/
theorem coequalizerDesc_uniq {a b c : T.Cat} {f g : a ⟶ b} (m : coequalizer f g ⟶ c) :
    m = coequalizerDesc (coequalizerπ f g ≫ m)
      (by rw [← Category.assoc, coequalizerπ_condition, Category.assoc]) := by
  obtain ⟨m, hm, rfl⟩ := m
  exact Subtype.ext (T.coeqDescOf_eta (par_of_hom f g) hm).symm

/-- A pairing followed by a morphism is the pairing of the composites. -/
theorem comp_prodLift {a b c d : T.Cat} (h : d ⟶ c) (f : c ⟶ a) (g : c ⟶ b) :
    h ≫ prodLift f g = prodLift (h ≫ f) (h ≫ g) := by
  rw [prodLift_uniq (h ≫ prodLift f g), Category.assoc, Category.assoc, prodLift_fst, prodLift_snd]

/-- Two morphisms into a product are equal when their composites with the projections are. -/
theorem prod_hom_ext {a b c : T.Cat} {m n : c ⟶ T.prod a b}
    (hf : m ≫ T.prodFst a b = n ≫ T.prodFst a b) (hs : m ≫ T.prodSnd a b = n ≫ T.prodSnd a b) :
    m = n := by
  rw [prodLift_uniq m, prodLift_uniq n, hf, hs]

/-- The morphism {lit}`k × id`, from the product of {lit}`k`'s domain and {lit}`a` to the
product of its codomain and {lit}`a`. -/
def prodMap {c d : T.Cat} (k : c ⟶ d) (a : T.Cat) : T.prod c a ⟶ T.prod d a :=
  prodLift (T.prodFst c a ≫ k) (T.prodSnd c a)

/-- The product with the identity preserves composition. -/
theorem prodMap_comp {c d e : T.Cat} (k : c ⟶ d) (l : d ⟶ e) (a : T.Cat) :
    prodMap (k ≫ l) a = prodMap k a ≫ prodMap l a :=
  prod_hom_ext (by simp only [prodMap, Category.assoc, prodLift_fst, prodLift_fst_assoc])
    (by simp only [prodMap, Category.assoc, prodLift_snd])

/-- The arrow of {lit}`k × id` is the model's product of {lit}`k`'s arrow with the
identity. -/
theorem prodMap_val {c d : T.Cat} (k : c ⟶ d) (a : T.Cat) :
    (prodMap k a).1 = T.prodMapLeftOf k.1 a := by
  obtain ⟨k, rfl, rfl⟩ := k
  rfl

variable (T)

/-- The exponential, as an object of the category. -/
abbrev exp (a b : T.Cat) : T.Cat := T.expOf a b

/-- The evaluation morphism. -/
def ev (a b : T.Cat) : T.prod (T.exp a b) a ⟶ b := ⟨T.evOf a b, T.domOf_evOf a b, T.codOf_evOf a b⟩

variable {T}

/-- The currying of a morphism from a product. -/
def curry {c a b : T.Cat} (f : T.prod c a ⟶ b) : c ⟶ T.exp a b :=
  ⟨T.curryOf c a f.1 f.2.1, T.domOf_curryOf f.2.1,
    (T.codOf_curryOf f.2.1).trans (congrArg (T.expOf a) f.2.2)⟩

/-- Evaluation after the product of a currying with the identity is the curried morphism. -/
@[reassoc]
theorem prodMap_curry_ev {c a b : T.Cat} (f : T.prod c a ⟶ b) :
    prodMap (curry f) a ≫ T.ev a b = f := by
  obtain ⟨f, hf, rfl⟩ := f
  refine Subtype.ext ?_
  calc (prodMap (curry ⟨f, hf, rfl⟩) a ≫ T.ev a (T.codOf f)).1
      = T.compOf (T.evOf a (T.codOf f)) (T.prodMapLeftOf (T.curryOf c a f hf) a)
          (T.codOf_prodMapLeftOf_curryOf hf) :=
        (comp_val _ _).trans (T.compOf_congr rfl (prodMap_val _ _) _ _)
    _ = f := T.evOf_curryOf hf

/-- A morphism into an exponential is the currying of evaluation after its product with the
identity. -/
theorem curry_uniq {c a b : T.Cat} (k : c ⟶ T.exp a b) :
    curry (prodMap k a ≫ T.ev a b) = k := by
  obtain ⟨k, hd, hk⟩ := k
  have hc : T.codOf (T.prodMapLeftOf k a) = T.domOf (T.evOf a b) := by
    rw [codOf_prodMapLeftOf, domOf_evOf, hk]
  refine Subtype.ext ?_
  calc (curry (prodMap ⟨k, hd, hk⟩ a ≫ T.ev a b)).1
      = T.curryOf c a (T.compOf (T.evOf a b) (T.prodMapLeftOf k a) hc)
          (T.domOf_evOf_prodMapLeftOf hd hc) :=
        T.curryOf_congr (h := (prodMap ⟨k, hd, hk⟩ a ≫ T.ev a b).2.1)
          ((comp_val _ _).trans (T.compOf_congr rfl (prodMap_val _ _) _ _))
    _ = k := T.curryOf_eta hd hk

/-- Currying is natural in its domain. -/
theorem comp_curry {c c' a b : T.Cat} (h : c' ⟶ c) (f : T.prod c a ⟶ b) :
    h ≫ curry f = curry (prodMap h a ≫ f) := by
  rw [← curry_uniq (h ≫ curry f), prodMap_comp, Category.assoc, prodMap_curry_ev]

variable (T)

/-- The symmetry of a product. -/
def swap (a b : T.Cat) : T.prod a b ⟶ T.prod b a := prodLift (T.prodSnd a b) (T.prodFst a b)

/-- The symmetry of a product is its own inverse. -/
@[reassoc]
theorem swap_swap (a b : T.Cat) : T.swap a b ≫ T.swap b a = 𝟙 (T.prod a b) :=
  prod_hom_ext (by simp only [swap, Category.assoc, prodLift_fst, prodLift_snd, Category.id_comp])
    (by simp only [swap, Category.assoc, prodLift_snd, prodLift_fst, Category.id_comp])

/-- The subobject classifier, as an object of the category. -/
abbrev omega : T.Cat := T.omegaOf

/-- Truth, from the terminal object to the subobject classifier. -/
def truth : T.one ⟶ T.omega := ⟨T.truOf, T.domOf_truOf, T.codOf_truOf⟩

variable {T}

/-- Two morphisms into an equalizer are equal when their composites with the inclusion are. -/
theorem equalizer_hom_ext {a b c : T.Cat} {f g : a ⟶ b} {m n : c ⟶ equalizer f g}
    (h : m ≫ equalizerι f g = n ≫ equalizerι f g) : m = n := by
  rw [equalizerLift_uniq m, equalizerLift_uniq n]
  congr 1

/-- A monomorphism of the category is a monomorphism of the model: its kernel pair's
projections are equal. -/
theorem isMono_of_mono {u x : T.Cat} (m : u ⟶ x) [Mono m] : T.IsMono m.1 := by
  obtain ⟨m, rfl, rfl⟩ := m
  let k : equalizer (T.prodFst (T.domOf m) (T.domOf m) ≫ ⟨m, rfl, rfl⟩)
      (T.prodSnd (T.domOf m) (T.domOf m) ≫ ⟨m, rfl, rfl⟩) ⟶ T.prod (T.domOf m) (T.domOf m) :=
    equalizerι _ _
  have hk : (k ≫ T.prodFst _ _) ≫ (⟨m, rfl, rfl⟩ : T.domOf m ⟶ T.codOf m) =
      (k ≫ T.prodSnd _ _) ≫ ⟨m, rfl, rfl⟩ := by
    simp only [Category.assoc, k]
    exact equalizerι_condition _ _
  exact congrArg Subtype.val (cancel_mono _ |>.mp hk)

/-- The characteristic map of a monomorphism of the model, as a morphism. -/
def chiHom {u x : T.Cat} (m : u ⟶ x) (hm : T.IsMono m.1) : x ⟶ T.omega :=
  ⟨T.chiOf m.1 hm, (T.domOf_chiOf hm).trans m.2.2, T.codOf_chiOf hm⟩

/-- A characteristic map's square commutes. -/
theorem chiHom_square {u x : T.Cat} (m : u ⟶ x) (hm : T.IsMono m.1) :
    m ≫ chiHom m hm = T.toOne u ≫ T.truth := by
  obtain ⟨m, rfl, rfl⟩ := m
  exact Subtype.ext (T.chiOf_square hm)

/-- A monomorphism equalizes its characteristic map and truth after the morphism to the
terminal object. -/
theorem chiHom_equalizes {u x : T.Cat} (m : u ⟶ x) (hm : T.IsMono m.1) :
    m ≫ chiHom m hm = m ≫ (T.toOne x ≫ T.truth) := by
  rw [chiHom_square, ← Category.assoc, T.toOne_uniq (m ≫ T.toOne x)]

/-- The pullback of truth along a characteristic map: the equalizer of the map and truth after
the morphism to the terminal object. -/
abbrev truthEqz {u x : T.Cat} (m : u ⟶ x) (hm : T.IsMono m.1) : T.Cat :=
  equalizer (chiHom m hm) (T.toOne x ≫ T.truth)

/-- Truth after the morphism to the terminal object from a characteristic map's domain, at the
arrows. -/
theorem truth_val {u x : T.Cat} (m : u ⟶ x) (hm : T.IsMono m.1) :
    (T.toOne x ≫ T.truth).1 = T.compOf T.truOf (T.bangOf (T.domOf (T.chiOf m.1 hm)))
      (T.codOf_bangOf_eq_domOf_truOf _) :=
  T.compOf_congr rfl (congrArg T.bangOf ((T.domOf_chiOf hm).trans m.2.2).symm)
    ((T.toOne x).2.2.trans T.truth.2.1.symm) _

/-- The pullback of truth along a characteristic map is the model's. -/
theorem truthEqz_eq {u x : T.Cat} (m : u ⟶ x) (hm : T.IsMono m.1) :
    truthEqz m hm = T.truthEqOf (T.chiOf m.1 hm) (T.codOf_chiOf hm) :=
  T.eqzOf_congr (truth_val m hm) _ _

/-- The inverse of a monomorphism's comparison with the pullback of truth, as a morphism. -/
def chiInvHom {u x : T.Cat} (m : u ⟶ x) (hm : T.IsMono m.1) : truthEqz m hm ⟶ u :=
  ⟨T.chiInvOf m.1 hm, (T.domOf_chiInvOf hm).trans (truthEqz_eq m hm).symm,
    (T.codOf_chiInvOf hm).trans m.2.1⟩

/-- The comparison of a monomorphism with the pullback of truth. -/
def chiLiftHom {u x : T.Cat} (m : u ⟶ x) (hm : T.IsMono m.1) : u ⟶ truthEqz m hm :=
  equalizerLift m (chiHom_equalizes m hm)

/-- The comparison's arrow is the model's. -/
theorem chiLiftHom_val {u x : T.Cat} (m : u ⟶ x) (hm : T.IsMono m.1) :
    (chiLiftHom m hm).1 = T.truthLiftOf m.1 hm :=
  T.eqLiftOf_congr (truth_val m hm) (par_of_hom (chiHom m hm) (T.toOne x ≫ T.truth))
    (T.par_truth (T.codOf_chiOf hm)) (m.2.2.trans (chiHom m hm).2.1.symm)
    (congrArg Subtype.val (chiHom_equalizes m hm)) (T.chiOf_equalizes hm)

/-- The comparison after its inverse is the identity of the pullback. -/
theorem chiInvHom_chiLiftHom {u x : T.Cat} (m : u ⟶ x) (hm : T.IsMono m.1) :
    chiInvHom m hm ≫ chiLiftHom m hm = 𝟙 (truthEqz m hm) := by
  refine Subtype.ext ?_
  calc (chiInvHom m hm ≫ chiLiftHom m hm).1
      = T.compOf (T.truthLiftOf m.1 hm) (T.chiInvOf m.1 hm)
          ((T.codOf_chiInvOf hm).trans (T.domOf_truthLiftOf hm).symm) :=
        T.compOf_congr (chiLiftHom_val m hm) rfl
          ((chiInvHom m hm).2.2.trans (chiLiftHom m hm).2.1.symm) _
    _ = T.idOf (T.truthEqOf (T.chiOf m.1 hm) (T.codOf_chiOf hm)) := T.truthLiftOf_chiInvOf hm
    _ = (𝟙 (truthEqz m hm) : truthEqz m hm ⟶ truthEqz m hm).1 :=
        congrArg T.idOf (truthEqz_eq m hm).symm

/-- The inverse after the comparison is the identity of the monomorphism's domain. -/
theorem chiLiftHom_chiInvHom {u x : T.Cat} (m : u ⟶ x) (hm : T.IsMono m.1) :
    chiLiftHom m hm ≫ chiInvHom m hm = 𝟙 u := by
  refine Subtype.ext ?_
  calc (chiLiftHom m hm ≫ chiInvHom m hm).1
      = T.compOf (T.chiInvOf m.1 hm) (T.truthLiftOf m.1 hm)
          ((T.codOf_truthLiftOf hm).trans (T.domOf_chiInvOf hm).symm) :=
        T.compOf_congr rfl (chiLiftHom_val m hm)
          ((chiLiftHom m hm).2.2.trans (chiInvHom m hm).2.1.symm) _
    _ = T.idOf (T.domOf m.1) := T.chiInvOf_truthLiftOf hm
    _ = (𝟙 u : u ⟶ u).1 := congrArg T.idOf m.2.1

/-- The inverse after the monomorphism is the pullback's inclusion. -/
theorem chiInvHom_comp {u x : T.Cat} (m : u ⟶ x) (hm : T.IsMono m.1) :
    chiInvHom m hm ≫ m = equalizerι _ _ := by
  have h : chiLiftHom m hm ≫ equalizerι _ _ = m := equalizerLift_ι _ _
  refine (congrArg (chiInvHom m hm ≫ ·) h.symm).trans ?_
  rw [← Category.assoc, chiInvHom_chiLiftHom, Category.id_comp]

/-- The factorization through a monomorphism of a morphism along which the characteristic map is
truth: the pullback's lift. -/
def chiLift {u x w : T.Cat} (m : u ⟶ x) (hm : T.IsMono m.1) (s : w ⟶ x)
    (hs : s ≫ chiHom m hm = T.toOne w ≫ T.truth) : w ⟶ u :=
  equalizerLift s (by rw [hs, ← Category.assoc, T.toOne_uniq (s ≫ T.toOne x)]) ≫ chiInvHom m hm

/-- The pullback's lift after the monomorphism is the lifted morphism. -/
theorem chiLift_fac {u x w : T.Cat} (m : u ⟶ x) (hm : T.IsMono m.1) (s : w ⟶ x)
    (hs : s ≫ chiHom m hm = T.toOne w ≫ T.truth) : chiLift m hm s hs ≫ m = s := by
  rw [chiLift, Category.assoc, chiInvHom_comp, equalizerLift_ι]

/-- A morphism into the classifier along which a monomorphism is a pullback of truth, through
a morphism from the pullback that factors the inclusion, is the monomorphism's characteristic
map. -/
theorem chiHom_uniq {u x : T.Cat} (m : u ⟶ x) [Mono m] (hm : T.IsMono m.1) (φ : x ⟶ T.omega)
    (hmφ : m ≫ φ = T.toOne u ≫ T.truth)
    (j : equalizer φ (T.toOne x ≫ T.truth) ⟶ u)
    (hj : j ≫ m = equalizerι φ (T.toOne x ≫ T.truth)) : φ = chiHom m hm := by
  have hw : m ≫ φ = m ≫ (T.toOne x ≫ T.truth) := by
    rw [hmφ, ← Category.assoc, T.toOne_uniq (m ≫ T.toOne x)]
  let i : u ⟶ equalizer φ (T.toOne x ≫ T.truth) := equalizerLift m hw
  have hi : i ≫ equalizerι φ (T.toOne x ≫ T.truth) = m := equalizerLift_ι _ _
  have hji : j ≫ i = 𝟙 _ :=
    equalizer_hom_ext (by rw [Category.assoc, hi, hj, Category.id_comp])
  have hij : i ≫ j = 𝟙 u :=
    (cancel_mono m).mp (by rw [Category.assoc, hj, hi, Category.id_comp])
  obtain ⟨φ, hφd, hφc⟩ := φ
  obtain ⟨m', hmd, hmc⟩ := m
  subst hmd hφd
  refine Subtype.ext (T.eq_chiOf hm hmc.symm hφc (i := i.1) (j := j.1)
    (i.2.2.trans (T.domOf_eqInclOf _).symm) ?_ (j.2.2.trans i.2.1.symm) ?_
    (i.2.2.trans j.2.1.symm) ?_)
  · exact congrArg Subtype.val hi
  · exact congrArg Subtype.val hji
  · exact congrArg Subtype.val hij

variable (T)

/-- The natural numbers object, as an object of the category. -/
abbrev nat : T.Cat := T.natOf

/-- Zero. -/
def zeroN : T.one ⟶ T.nat := ⟨T.zeroNOf, T.domOf_zeroNOf, T.codOf_zeroNOf⟩

/-- The successor. -/
def succ : T.nat ⟶ T.nat := ⟨T.succOf, T.domOf_succOf, T.codOf_succOf⟩

variable {T}

/-- The morphism from the natural numbers object that recursion with a start and a step
defines. -/
def natRec {a : T.Cat} (z : T.one ⟶ a) (s : a ⟶ a) : T.nat ⟶ a :=
  ⟨T.natRecOf z.1 s.1 z.2.1 (z.2.2.trans s.2.1.symm) (s.2.1.trans s.2.2.symm),
    T.domOf_natRecOf _ _ _, (T.codOf_natRecOf _ _ _).trans z.2.2⟩

/-- A recursion after zero is its start. -/
@[reassoc]
theorem zeroN_natRec {a : T.Cat} (z : T.one ⟶ a) (s : a ⟶ a) : T.zeroN ≫ natRec z s = z :=
  Subtype.ext (T.natRecOf_zeroNOf z.2.1 (z.2.2.trans s.2.1.symm) (s.2.1.trans s.2.2.symm))

/-- A recursion after the successor is the step after the recursion. -/
@[reassoc]
theorem succ_natRec {a : T.Cat} (z : T.one ⟶ a) (s : a ⟶ a) :
    T.succ ≫ natRec z s = natRec z s ≫ s :=
  Subtype.ext (T.natRecOf_succOf z.2.1 (z.2.2.trans s.2.1.symm) (s.2.1.trans s.2.2.symm))

/-- A morphism from the natural numbers object satisfying the recursion equations is the
recursion. -/
theorem natRec_uniq {a : T.Cat} (z : T.one ⟶ a) (s : a ⟶ a) (u : T.nat ⟶ a)
    (h0 : T.zeroN ≫ u = z) (h1 : T.succ ≫ u = u ≫ s) : u = natRec z s := by
  obtain ⟨u, hu, huc⟩ := u
  exact Subtype.ext (T.eq_natRecOf z.2.1 (z.2.2.trans s.2.1.symm) (s.2.1.trans s.2.2.symm) hu
    (congrArg Subtype.val h0) (huc.trans s.2.1.symm) (congrArg Subtype.val h1))

/-- The morphism {lit}`id × k`, from the product of {lit}`a` and {lit}`k`'s domain to the
product of {lit}`a` and its codomain. -/
def prodMapRight (a : T.Cat) {c d : T.Cat} (k : c ⟶ d) : T.prod a c ⟶ T.prod a d :=
  prodLift (T.prodFst a c) (T.prodSnd a c ≫ k)

/-- The arrow of {lit}`id × k` is the model's product of the identity with {lit}`k`'s arrow. -/
theorem prodMapRight_val (a : T.Cat) {c d : T.Cat} (k : c ⟶ d) :
    (prodMapRight a k).1 = T.prodMapRightOf a k.1 := by
  obtain ⟨k, rfl, rfl⟩ := k
  rfl

variable (T)

/-- The list object of an object, as an object of the category. -/
abbrev list (a : T.Cat) : T.Cat := T.listOf a

/-- The empty list. -/
def nil (a : T.Cat) : T.one ⟶ T.list a := ⟨T.nilOf a, T.domOf_nilOf a, T.codOf_nilOf a⟩

/-- The construction of a list from an element and a list. -/
def cons (a : T.Cat) : T.prod a (T.list a) ⟶ T.list a :=
  ⟨T.consOf a, T.domOf_consOf a, T.codOf_consOf a⟩

variable {T}

/-- The morphism from the list object of {lit}`a` that recursion with a start and a step
defines. -/
def listRec {a b : T.Cat} (z : T.one ⟶ b) (s : T.prod a b ⟶ b) : T.list a ⟶ b :=
  ⟨T.listRecOf a z.1 s.1 z.2.1 (z.2.2.trans s.2.2.symm)
      (s.2.1.trans (congrArg (T.prodOf a) s.2.2.symm)),
    T.domOf_listRecOf _ _ _, (T.codOf_listRecOf _ _ _).trans z.2.2⟩

/-- A recursion on lists after the empty list is its start. -/
@[reassoc]
theorem nil_listRec {a b : T.Cat} (z : T.one ⟶ b) (s : T.prod a b ⟶ b) :
    T.nil a ≫ listRec z s = z :=
  Subtype.ext (T.listRecOf_nilOf z.2.1 (z.2.2.trans s.2.2.symm)
    (s.2.1.trans (congrArg (T.prodOf a) s.2.2.symm)))

/-- A recursion on lists after the construction of a list is the step after the product of
the identity with the recursion. -/
@[reassoc]
theorem cons_listRec {a b : T.Cat} (z : T.one ⟶ b) (s : T.prod a b ⟶ b) :
    T.cons a ≫ listRec z s = prodMapRight a (listRec z s) ≫ s :=
  Subtype.ext <| (T.listRecOf_consOf z.2.1 (z.2.2.trans s.2.2.symm)
    (s.2.1.trans (congrArg (T.prodOf a) s.2.2.symm))).trans
    ((T.compOf_congr rfl (prodMapRight_val a (listRec z s)).symm _ _).trans (comp_val _ _).symm)

/-- A morphism from a list object satisfying the recursion equations is the recursion. -/
theorem listRec_uniq {a b : T.Cat} (z : T.one ⟶ b) (s : T.prod a b ⟶ b) (u : T.list a ⟶ b)
    (h0 : T.nil a ≫ u = z) (h1 : T.cons a ≫ u = prodMapRight a u ≫ s) : u = listRec z s := by
  have hus : T.codOf (T.prodMapRightOf a u.1) = T.domOf s.1 :=
    (T.codOf_prodMapRightOf a u.1).trans ((congrArg (T.prodOf a) u.2.2).trans s.2.1.symm)
  have k1 := congrArg Subtype.val h1
  rw [comp_val, comp_val] at k1
  simp only [prodMapRight_val] at k1
  refine Subtype.ext (T.eq_listRecOf z.2.1 (z.2.2.trans s.2.2.symm)
    (s.2.1.trans (congrArg (T.prodOf a) s.2.2.symm)) u.2.1 (congrArg Subtype.val h0) hus k1)

/-- The action of the list object on a morphism: recursion with the empty list and the
construction of a list after the morphism. -/
def listMap {a b : T.Cat} (f : a ⟶ b) : T.list a ⟶ T.list b :=
  listRec (T.nil b) (prodMap f (T.list b) ≫ T.cons b)

/-- The arrow of the list object's action is the model's. -/
theorem listMap_val {a b : T.Cat} (f : a ⟶ b) : (listMap f).1 = T.listMapOf f.1 := by
  obtain ⟨f, rfl, rfl⟩ := f
  rfl

variable (T)

/-- The rose-tree object, as an object of the category. -/
abbrev rose : T.Cat := T.roseOf

/-- The construction of a rose tree from a label and a list of children. -/
def node : T.prod T.nat (T.list T.rose) ⟶ T.rose := ⟨T.nodeOf, T.domOf_nodeOf, T.codOf_nodeOf⟩

variable {T}

/-- The fold of the rose-tree object into an algebra of the functor
{lit}`x ↦ nat × list x`. -/
def roseRec {b : T.Cat} (f : T.prod T.nat (T.list b) ⟶ b) : T.rose ⟶ b :=
  ⟨T.roseRecOf f.1 (f.2.1.trans (congrArg (fun c ↦ T.prodOf T.natOf (T.listOf c)) f.2.2.symm)),
    T.domOf_roseRecOf _, (T.codOf_roseRecOf _).trans f.2.2⟩

/-- A fold after the construction of a rose tree is the algebra after the fold of the
children. -/
@[reassoc]
theorem node_roseRec {b : T.Cat} (f : T.prod T.nat (T.list b) ⟶ b) :
    T.node ≫ roseRec f = prodMapRight T.nat (listMap (roseRec f)) ≫ f :=
  Subtype.ext <| (T.roseRecOf_nodeOf
    (f.2.1.trans (congrArg (fun c ↦ T.prodOf T.natOf (T.listOf c)) f.2.2.symm))).trans
    ((T.compOf_congr rfl ((prodMapRight_val _ _).trans (congrArg (T.prodMapRightOf T.natOf)
      (listMap_val (roseRec f)))).symm _ _).trans (comp_val _ _).symm)

/-- A morphism from the rose-tree object satisfying the fold's equation is the fold. -/
theorem roseRec_uniq {b : T.Cat} (f : T.prod T.nat (T.list b) ⟶ b) (u : T.rose ⟶ b)
    (h : T.node ≫ u = prodMapRight T.nat (listMap u) ≫ f) : u = roseRec f := by
  have hf := f.2.1.trans (congrArg (fun c ↦ T.prodOf T.natOf (T.listOf c)) f.2.2.symm)
  have huc := u.2.2.trans f.2.2.symm
  have k := congrArg Subtype.val h
  rw [comp_val, comp_val] at k
  simp only [prodMapRight_val, listMap_val] at k
  exact Subtype.ext (T.eq_roseRecOf hf u.2.1 huc k)

end ToposModel

end Geb.FreeTopos

end
