/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinCat.Category
public import Mathlib.CategoryTheory.Functor.Basic

/-!
# Functor specifications

A functor between two finite-category specifications is specified by a
map on object indices, a map on client morphisms, and a `Bool` equation
asserting preservation of composition. The client morphism map lands in
the target's full hom type, a functor being free to send a non-identity
morphism to an identity. Preservation of identities is not checked: the
extension of the morphism map to the full hom types sends the reserved
identity to the reserved identity by construction.

Functor specifications compose, and the identity and composition
satisfy the unit and associativity laws as equalities of
specifications, not merely up to isomorphism.

## Main definitions

* `CategoryTheory.FinCat.Hom.mapTotalOf`,
  `CategoryTheory.FinCat.Hom.mapTotal` — the extension of the morphism
  map to the full hom types.
* `CategoryTheory.FinCat.Hom.compCheckOf`,
  `CategoryTheory.FinCat.Hom.compCheck` — the decidable
  preservation-of-composition check on pairs of client morphisms.
* `CategoryTheory.FinCat.Hom` — the functor specification type.
* `CategoryTheory.FinCat.Hom.id`, `CategoryTheory.FinCat.Hom.comp` —
  the identity specification and composition of specifications.
* `CategoryTheory.FinCat.Hom.toFunctor` — the mathlib functor a
  specification generates.

## Main statements

* `FinCat.Hom.compCheck_eq_true_iff` — the check reflects preservation
  of composition on pairs of client morphisms.
* `FinCat.Hom.mapTotal_emb`, `FinCat.Hom.mapTotal_id` — the total map on
  a client morphism and on the reserved identity.
* `FinCat.Hom.mapTotal_compTotal` — preservation of composition, on all
  pairs of morphisms.
* `FinCat.Hom.id_mapTotalOf`, `FinCat.Hom.comp_mapTotalOf`,
  `FinCat.Hom.id_mapTotal`, `FinCat.Hom.comp_mapTotal` — the total map
  of the identity and of a composite.
* `FinCat.Hom.id_comp`, `FinCat.Hom.comp_id`, `FinCat.Hom.assoc` — the
  unit and associativity laws, as equalities.

## Implementation notes

`mapTotalOf` and `compCheckOf` precede the structure because the
`compValid` field's type mentions them. The enclosing `namespace FinCat`
stays open throughout; the inner `namespace Hom` block closes before
`structure Hom`, which cannot be declared inside a namespace of its own
name, and reopens after.

The check is stated over the total composition and the total morphism
map rather than over the client data alone: a composite of two client
morphisms may land on the reserved identity index, on which the client's
morphism map is undefined.

`mapTotal_compTotal` extends the check off the client range. The
extension, rather than the check itself, is what the composite of two
functor specifications needs: its validity field is the outer
specification's preservation of composition at two morphisms of the form
`mapTotal (emb _)`, which need not be embedded client morphisms of the
middle specification.

`id_mapTotalOf` and `comp_mapTotalOf` are stated about `mapTotalOf`
applied to given data rather than about a specification, because
`FinCat.Hom.id` and `FinCat.Hom.comp` consume them to discharge their
own validity fields. `id_mapTotal` and `comp_mapTotal` are the
corresponding statements about the specifications those two build.

The unit and associativity laws go through the heterogeneous `ext`
lemma: the `objMap` components agree definitionally, so the `HEq` of
the `map` components is an equality, and the `compValid` components are
proof-irrelevant.

## References

* [JohnsonYau2021] § 1.1 — the notion of functor, of which this module's
  specification type is a presentation.

## Tags

category, functor, finite category, decidable, constructive, choice-free
-/

@[expose] public section

namespace CategoryTheory

namespace FinCat

namespace Hom

/-- The extension of a functor specification's morphism map to the full
hom types, sending the reserved identity to the reserved identity. The
identity branch's bound needs `i = j`, which `eq_of_nonIdCount_le`
supplies; the value component crosses with no `Eq.rec`. -/
def mapTotalOf {S T : FinCat} (objMap : Fin S.objCount → Fin T.objCount)
    (map : (i j : Fin S.objCount) → Fin (S.nonIdCount i j) → T.Mor (objMap i) (objMap j))
    {i j : Fin S.objCount} (x : S.Mor i j) : T.Mor (objMap i) (objMap j) :=
  if hx : x.val < S.nonIdCount i j then map i j ⟨x.val, hx⟩
  else ⟨(T.id (objMap i)).val, by
    have hij := S.eq_of_nonIdCount_le x (Nat.not_lt.mp hx)
    subst hij
    exact (T.id (objMap i)).isLt⟩

/-- Preservation of composition, as a `Bool`, on pairs of client
morphisms. Stated over the total composition and the total morphism
map: a client composite may land on the reserved index, on which the
partial map is undefined. -/
def compCheckOf (S T : FinCat) (objMap : Fin S.objCount → Fin T.objCount)
    (map : (i j : Fin S.objCount) → Fin (S.nonIdCount i j) → T.Mor (objMap i) (objMap j)) :
    Bool :=
  decide <| ∀ (i j k : Fin S.objCount) (f : Fin (S.nonIdCount i j))
    (g : Fin (S.nonIdCount j k)),
      mapTotalOf objMap map (S.compTotal (S.emb f) (S.emb g))
        = T.compTotal (mapTotalOf objMap map (S.emb f)) (mapTotalOf objMap map (S.emb g))

end Hom

/-- A functor specification between two finite-category
specifications. `FinCat.Hom` is named for its position — the 1-cells of
a 2-category — not for its shape: unlike `CategoryTheory.Cat.Hom` it is
not a one-field bundling. -/
@[ext] structure Hom (S T : FinCat) where
  /-- The map on object indices. -/
  objMap : Fin S.objCount → Fin T.objCount
  /-- The map on client morphisms. It lands in the target's full hom
  type, since a functor may send a non-identity morphism to an
  identity; every functor into the terminal category does. -/
  map : (i j : Fin S.objCount) →
    Fin (S.nonIdCount i j) → T.Mor (objMap i) (objMap j)
  /-- Preservation of composition. -/
  compValid : Hom.compCheckOf S T objMap map = true

namespace Hom

variable {S T : FinCat}

/-- The composition check reflects preservation of composition on pairs
of client morphisms. -/
theorem compCheck_eq_true_iff (S T : FinCat) (objMap : Fin S.objCount → Fin T.objCount)
    (map : (i j : Fin S.objCount) → Fin (S.nonIdCount i j) → T.Mor (objMap i) (objMap j)) :
    compCheckOf S T objMap map = true ↔
      ∀ (i j k : Fin S.objCount) (f : Fin (S.nonIdCount i j)) (g : Fin (S.nonIdCount j k)),
        mapTotalOf objMap map (S.compTotal (S.emb f) (S.emb g))
          = T.compTotal (mapTotalOf objMap map (S.emb f)) (mapTotalOf objMap map (S.emb g)) :=
  decide_eq_true_iff

/-- `F` on the full hom types. -/
def mapTotal (F : Hom S T) {i j : Fin S.objCount} (x : S.Mor i j) :
    T.Mor (F.objMap i) (F.objMap j) := mapTotalOf F.objMap F.map x

/-- `F`'s composition check. -/
def compCheck (F : Hom S T) : Bool := compCheckOf S T F.objMap F.map

/-- On an embedded client morphism the total map is the client map. -/
theorem mapTotal_emb (F : Hom S T) {i j : Fin S.objCount}
    (f : Fin (S.nonIdCount i j)) : F.mapTotal (S.emb f) = F.map i j f := by
  have hlt : (S.emb f).val < S.nonIdCount i j := f.isLt
  unfold Hom.mapTotal mapTotalOf
  rw [dif_pos hlt]
  rfl

/-- The total map preserves the reserved identity. -/
theorem mapTotal_id (F : Hom S T) (i : Fin S.objCount) :
    F.mapTotal (S.id i) = T.id (F.objMap i) := by
  have hlt : ¬ ((S.id i).val < S.nonIdCount i i) := Nat.lt_irrefl _
  unfold Hom.mapTotal mapTotalOf
  rw [dif_neg hlt]

/-- The total map preserves the total composition, on all pairs of
morphisms. -/
theorem mapTotal_compTotal (F : Hom S T) {i j k : Fin S.objCount}
    (x : S.Mor i j) (y : S.Mor j k) :
    F.mapTotal (S.compTotal x y) = T.compTotal (F.mapTotal x) (F.mapTotal y) := by
  by_cases hx : x.val < S.nonIdCount i j
  · by_cases hy : y.val < S.nonIdCount j k
    · exact (compCheck_eq_true_iff S T F.objMap F.map).mp F.compValid i j k
        ⟨x.val, hx⟩ ⟨y.val, hy⟩
    · have hjk := S.eq_of_nonIdCount_le y (Nat.not_lt.mp hy)
      subst hjk
      rw [show y = S.id _ from Fin.ext (S.val_eq_of_nonIdCount_le y (Nat.not_lt.mp hy)),
        S.comp_id, mapTotal_id, T.comp_id]
  · have hij := S.eq_of_nonIdCount_le x (Nat.not_lt.mp hx)
    subst hij
    rw [show x = S.id _ from Fin.ext (S.val_eq_of_nonIdCount_le x (Nat.not_lt.mp hx)),
      S.id_comp, mapTotal_id, T.id_comp]

/-- `mapTotalOf` at the identity 1-cell's data is the identity. -/
theorem id_mapTotalOf (S : FinCat) {i j : Fin S.objCount} (x : S.Mor i j) :
    mapTotalOf (fun i ↦ i) (fun _ _ f ↦ S.emb f) x = x := by
  unfold mapTotalOf
  by_cases hx : x.val < S.nonIdCount i j
  · rw [dif_pos hx]
    rfl
  · rw [dif_neg hx]
    have hij := S.eq_of_nonIdCount_le x (Nat.not_lt.mp hx)
    subst hij
    exact Fin.ext (S.val_eq_of_nonIdCount_le x (Nat.not_lt.mp hx)).symm

/-- `mapTotalOf` at a composite's data factors as the outer 1-cell
applied to the inner. -/
theorem comp_mapTotalOf {S T U : FinCat} (F : Hom S T) (G : Hom T U)
    {i j : Fin S.objCount} (x : S.Mor i j) :
    mapTotalOf (fun i ↦ G.objMap (F.objMap i)) (fun i j f ↦ G.mapTotal (F.map i j f)) x
      = G.mapTotal (F.mapTotal x) := by
  by_cases hx : x.val < S.nonIdCount i j
  · have h1 : mapTotalOf (fun i ↦ G.objMap (F.objMap i))
        (fun i j f ↦ G.mapTotal (F.map i j f)) x = G.mapTotal (F.map i j ⟨x.val, hx⟩) :=
      dif_pos hx
    have h2 : F.mapTotal x = F.map i j ⟨x.val, hx⟩ := dif_pos hx
    rw [h1, h2]
  · have hij := S.eq_of_nonIdCount_le x (Nat.not_lt.mp hx)
    subst hij
    rw [show x = S.id i from Fin.ext (S.val_eq_of_nonIdCount_le x (Nat.not_lt.mp hx)),
      F.mapTotal_id, G.mapTotal_id]
    exact dif_neg (Nat.lt_irrefl _)

/-- The identity 1-cell. -/
protected def id (S : FinCat) : Hom S S where
  objMap := fun i ↦ i
  map := fun _ _ f ↦ S.emb f
  compValid := by
    refine (compCheck_eq_true_iff S S (fun i ↦ i) (fun _ _ f ↦ S.emb f)).mpr ?_
    intro i j k f g
    rw [id_mapTotalOf, id_mapTotalOf, id_mapTotalOf]

/-- Composition of 1-cells. -/
def comp {S T U : FinCat} (F : Hom S T) (G : Hom T U) : Hom S U where
  objMap := fun i ↦ G.objMap (F.objMap i)
  map := fun i j f ↦ G.mapTotal (F.map i j f)
  compValid := by
    refine (compCheck_eq_true_iff S U _ _).mpr ?_
    intro i j k f g
    rw [comp_mapTotalOf, comp_mapTotalOf, comp_mapTotalOf, F.mapTotal_compTotal,
      G.mapTotal_compTotal]

/-- The identity 1-cell acts as the identity on total morphisms. -/
theorem id_mapTotal (S : FinCat) {i j : Fin S.objCount} (x : S.Mor i j) :
    (Hom.id S).mapTotal x = x := id_mapTotalOf S x

/-- A composite 1-cell's total map factors. -/
theorem comp_mapTotal {S T U : FinCat} (F : Hom S T) (G : Hom T U)
    {i j : Fin S.objCount} (x : S.Mor i j) :
    (F.comp G).mapTotal x = G.mapTotal (F.mapTotal x) := comp_mapTotalOf F G x

/-- The identity 1-cell is a left identity, on the nose. -/
theorem id_comp {S T : FinCat} (F : Hom S T) : (Hom.id S).comp F = F :=
  Hom.ext rfl (heq_of_eq (funext fun _ ↦ funext fun _ ↦ funext fun f ↦
    F.mapTotal_emb f))

/-- The identity 1-cell is a right identity, on the nose. -/
theorem comp_id {S T : FinCat} (F : Hom S T) : F.comp (Hom.id T) = F :=
  Hom.ext rfl (heq_of_eq (funext fun i ↦ funext fun j ↦ funext fun f ↦
    id_mapTotal T (F.map i j f)))

/-- 1-cell composition is associative, on the nose. -/
theorem assoc {S T U V : FinCat} (F : Hom S T) (G : Hom T U)
    (H : Hom U V) : (F.comp G).comp H = F.comp (G.comp H) :=
  Hom.ext rfl (heq_of_eq (funext fun i ↦ funext fun j ↦ funext fun f ↦
    (comp_mapTotal G H (F.map i j f)).symm))

/-- The mathlib functor a functor specification generates. The type is
written with explicit instance arguments rather than through `⥤`, so
that `v` appears in it and is not left to be inferred from a hidden
instance argument. -/
def toFunctor.{v, u} {S T : FinCat} (F : Hom S T) :
    @Functor (Obj.{u} S) (Obj.category.{v, u} S) (Obj.{u} T) (Obj.category.{v, u} T) where
  obj X := ⟨ULift.up (F.objMap X.idx.down)⟩
  map f := ULift.up (F.mapTotal f.down)
  map_id _ := congrArg ULift.up (F.mapTotal_id _)
  map_comp _ _ := congrArg ULift.up (F.mapTotal_compTotal _ _)

end Hom

end FinCat

end CategoryTheory
