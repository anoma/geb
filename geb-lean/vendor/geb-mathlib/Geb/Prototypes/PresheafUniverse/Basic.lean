/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.Finite.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Fin.Basic

/-!
# Prototype: the dependent-type universe as a presheaf polynomial functor on the walking arrow

Throwaway exploration, not upstream-eligible content. Every declaration here is
`Classical.choice`-free.

The universe of [GhaniNordvallForsbergMalatesta2015] (Examples 2.5 and 2.6),
whose inductive-recursive presentation is
`Geb/Mathlib/Data/PFunctor/IndRec/Universes.lean`, presented instead as a
presheaf polynomial endofunctor on presheaves over the walking arrow. A presheaf
`Z` on the walking arrow is a map `Z 1 → Z 0`, read as the typing map from terms
to codes; the inductive-recursive decoding `IRdecode u` is replaced by the fiber
of that map over `u`, so the decoding is no longer a function into a universe of
types and the functor is an endofunctor on a genuine presheaf category rather
than on a slice of `Type` over itself.

The base category is the preorder on `Fin 2`: the object `0` indexes the codes,
the object `1` the terms, and the unique morphism `0 ⟶ 1` induces the typing map
`Z 1 → Z 0`. Shapes and directions are both finite, so the functor is a
`FinitePresheafPFunctor` and membership in the fibers of its W-type is decided by
`FinitePresheafPFunctor.memWBool`.

## What the finite arities do and do not capture

A shape's arity is a presheaf on the base fixed independently of `Z`, so a code
node has a fixed finite number of subcode and subterm slots. The
inductive-recursive `sigma` code carries a whole family `IRdecode u → Code`
indexed by the decoding of its first argument; no arity independent of `Z`
indexes that family. What the finite arities do capture is the family evaluated
at a term: the `pair` shape has two term directions and two code directions, and
the naturality of a direction assignment (`PresheafDomPFunctorData.IsNatural`)
forces the code direction to receive the code of the term direction. Hereditary
naturality of a W-tree is therefore exactly the statement that the tree is
well-typed, and the presheaf restriction of a term tree is its type. The `sigma`
and `pi` shapes accordingly denote the non-dependent product and function space,
and `pi` has no introduction shape, a lambda being an infinitary constructor in
the same way.

## Main definitions

* `Shp` — the shapes: the base code, the two binder codes, the base-type terms,
  and the pair term.
* `PairDir` / `Dir` — the direction types: the two components of a pair term and
  their two codes, and the direction type of each shape.
* `rDir` / `qShp` — the direction-input and shape-output maps.
* `codeDir` / `codeShp` / `reindexDir` — the code direction of a direction, the
  code shape of a shape, and the inclusion of a code shape's directions into the
  directions of the shapes restricting to it.
* `dirTo` / `restrShp` / `reindexTo` — the direction restriction, shape
  restriction, and arity reindexing, as bare functions of the target index.
* `universeData` / `universeFunctor` / `finiteUniverse` — the operations, the
  functor with its seven functor laws, and the functor bundled with its
  finiteness evidence.

## References

* [GhaniNordvallForsbergMalatesta2015]
* [HancockMcBrideGhaniMalatestaAltenkirch2013]
* [Weber2007]

## Tags

prototype, inductive-recursive, inductive-inductive, presheaf, universe,
walking arrow, parametric right adjoint
-/

@[expose] public section

open CategoryTheory

namespace GebProto.PresheafUniverse

/-! ## Choice-free `FinEnum` evidence -/

/-- A choice-free `FinEnum (Fin 2)` for the base category's objects, from the
identity equivalence rather than `FinEnum.fin` (which routes through
`Classical.choice`). -/
instance finEnumFin2 : FinEnum (Fin 2) where
  card := 2
  equiv := Equiv.refl (Fin 2)
  decEq := inferInstance

/-- A choice-free `FinEnum (PLift p)` for a decidable proposition `p`: one
element when `p` holds, none otherwise. -/
instance finEnumPLift {p : Prop} [Decidable p] : FinEnum (PLift p) :=
  if h : p then
    { card := 1
      equiv :=
        { toFun := fun _ ↦ 0
          invFun := fun _ ↦ ⟨h⟩
          left_inv := fun x ↦ by cases x; rfl
          right_inv := fun i ↦ Fin.cases rfl (fun j ↦ j.elim0) i }
      decEq := fun a b ↦ isTrue (by cases a; cases b; rfl) }
  else
    { card := 0
      equiv :=
        { toFun := fun x ↦ absurd x.down h
          invFun := fun i ↦ i.elim0
          left_inv := fun x ↦ absurd x.down h
          right_inv := fun i ↦ i.elim0 }
      decEq := fun a _ ↦ absurd a.down h }

/-- A choice-free `FinEnum` of a hom-set of the base category, stated at the `⟶`
head and delegating to the `ULift`/`PLift` enumeration. -/
instance finEnumHom (i i' : Fin 2) : FinEnum (i' ⟶ i) :=
  inferInstanceAs (FinEnum (ULift (PLift (i' ≤ i))))

/-- A choice-free `FinEnum Empty`, supplying the direction enumeration of the
leaf shapes. -/
instance finEnumEmpty : FinEnum Empty where
  card := 0
  equiv :=
    { toFun := fun x ↦ x.elim
      invFun := fun i ↦ i.elim0
      left_inv := fun x ↦ x.elim
      right_inv := fun i ↦ i.elim0 }
  decEq := fun x ↦ x.elim

/-- A choice-free `FinEnum Bool`, supplying the direction enumeration of the
binder shapes. -/
instance finEnumBool : FinEnum Bool where
  card := 2
  equiv :=
    { toFun := fun b ↦ if b then 1 else 0
      invFun := fun i ↦ i = 1
      left_inv := fun b ↦ by cases b <;> rfl
      right_inv := fun i ↦ Fin.cases rfl (Fin.cases rfl fun j ↦ j.elim0) i }
  decEq := inferInstance

/-! ## Shapes and directions -/

/-- The shapes: the base-type code `base`, the two binder codes `sigma` and
`pi`, one term shape `lit b` per element of the base type, and the pair term
`pair`. -/
inductive Shp where
  /-- The code of the base type. -/
  | base
  /-- The dependent-sum former, degenerating to the product; see the module
  docstring. -/
  | sigma
  /-- The dependent-product former, degenerating to the function space. -/
  | pi
  /-- The term of the base type at `b`. -/
  | lit (b : Bool)
  /-- The introduction form of `sigma`. -/
  | pair
  deriving DecidableEq

/-- The directions of the `pair` shape: the two component terms and their two
codes. -/
inductive PairDir where
  /-- The `i`-th component term. -/
  | tm (i : Bool)
  /-- The code of the `i`-th component term. -/
  | ty (i : Bool)
  deriving DecidableEq

/-- A choice-free `FinEnum Shp`: the six shapes mapped to `Fin 6`. -/
instance finEnumShp : FinEnum Shp where
  card := 6
  equiv :=
    { toFun := fun s ↦ match s with
        | .base => 0
        | .sigma => 1
        | .pi => 2
        | .lit false => 3
        | .lit true => 4
        | .pair => 5
      invFun := fun i ↦ match i with
        | 0 => .base
        | 1 => .sigma
        | 2 => .pi
        | 3 => .lit false
        | 4 => .lit true
        | 5 => .pair
      left_inv := fun s ↦ by
        cases s with
        | lit b => cases b <;> rfl
        | _ => rfl
      right_inv := fun i ↦
        Fin.cases rfl
          (Fin.cases rfl
            (Fin.cases rfl
              (Fin.cases rfl
                (Fin.cases rfl
                  (Fin.cases rfl fun j ↦ j.elim0))))) i }
  decEq := inferInstance

/-- A choice-free `FinEnum PairDir`: the four directions of `pair` mapped to
`Fin 4`. -/
instance finEnumPairDir : FinEnum PairDir where
  card := 4
  equiv :=
    { toFun := fun d ↦ match d with
        | .tm false => 0
        | .tm true => 1
        | .ty false => 2
        | .ty true => 3
      invFun := fun i ↦ match i with
        | 0 => .tm false
        | 1 => .tm true
        | 2 => .ty false
        | 3 => .ty true
      left_inv := fun d ↦ by
        cases d with
        | tm b => cases b <;> rfl
        | ty b => cases b <;> rfl
      right_inv := fun i ↦
        Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl fun j ↦ j.elim0))) i }
  decEq := inferInstance

/-- The direction type of each shape: the binder codes have their two subcodes,
the pair term has its two components and their codes, and the remaining shapes
are leaves. -/
@[reducible] def Dir : Shp → Type
  | .base => Empty
  | .sigma => Bool
  | .pi => Bool
  | .lit _ => Empty
  | .pair => PairDir

/-- The direction-input map: a subcode direction lies over the code object `0`,
a component-term direction over the term object `1`. -/
def rDir : (a : Shp) → Dir a → Fin 2
  | .base, d => d.elim
  | .sigma, _ => 0
  | .pi, _ => 0
  | .lit _, d => d.elim
  | .pair, .tm _ => 1
  | .pair, .ty _ => 0

/-- The shape-output map: the code shapes lie over the code object `0`, the term
shapes over the term object `1`. -/
def qShp : Shp → Fin 2
  | .base => 0
  | .sigma => 0
  | .pi => 0
  | .lit _ => 1
  | .pair => 1

/-! ## The restriction data -/

/-- The code direction of a direction: the direction over the code object that a
direction restricts to. The identity on directions already over the code
object. -/
def codeDir : (a : Shp) → Dir a → Dir a
  | .base, d => d.elim
  | .sigma, d => d
  | .pi, d => d
  | .lit _, d => d.elim
  | .pair, .tm i => .ty i
  | .pair, .ty i => .ty i

/-- The code shape of a shape: the shape over the code object that a shape
restricts to, that is, the type of a term shape. The identity on code shapes. -/
def codeShp : Shp → Shp
  | .base => .base
  | .sigma => .sigma
  | .pi => .pi
  | .lit _ => .base
  | .pair => .sigma

/-- The inclusion of a code shape's directions into the directions of the shapes
restricting to it: the subcodes of a `sigma` are the codes of a `pair`'s
components. -/
def reindexDir : (a : Shp) → Dir (codeShp a) → Dir a
  | .base, d => d
  | .sigma, d => d
  | .pi, d => d
  | .lit _, d => d.elim
  | .pair, i => .ty i

/-- The direction restriction to a target index: the identity at the term
object, `codeDir` at the code object. -/
def dirTo : Fin 2 → (a : Shp) → Dir a → Dir a
  | 0, a, d => codeDir a d
  | 1, _, d => d

/-- The shape restriction to a target index: the identity at the term object,
`codeShp` at the code object. -/
def restrShp : Fin 2 → Shp → Shp
  | 0, a => codeShp a
  | 1, a => a

/-- The arity reindexing along a restriction to a target index: the identity at
the term object, `reindexDir` at the code object. -/
def reindexTo : (j : Fin 2) → (a : Shp) → Dir (restrShp j a) → Dir a
  | 0, a, d => reindexDir a d
  | 1, _, d => d

/-! ## The laws of the restriction data -/

/-- A code direction lies over the code object. -/
theorem rDir_codeDir : ∀ (a : Shp) (d : Dir a), rDir a (codeDir a d) = 0
  | .base, d => d.elim
  | .sigma, _ => rfl
  | .pi, _ => rfl
  | .lit _, d => d.elim
  | .pair, .tm _ => rfl
  | .pair, .ty _ => rfl

/-- A direction already over the code object is its own code direction. -/
theorem codeDir_self : ∀ (a : Shp) (d : Dir a), rDir a d = 0 → codeDir a d = d
  | .base, d, _ => d.elim
  | .sigma, _, _ => rfl
  | .pi, _, _ => rfl
  | .lit _, d, _ => d.elim
  | .pair, .tm _, h => absurd h (by decide +revert)
  | .pair, .ty _, _ => rfl

/-- The direction restriction lands over its target index. -/
theorem rDir_dirTo (a : Shp) (i i' : Fin 2) (d : Dir a) (hd : rDir a d = i) (h : i' ≤ i) :
    rDir a (dirTo i' a d) = i' := by
  match i' with
  | 0 => exact rDir_codeDir a d
  | 1 => have : i = 1 := by omega
         exact hd.trans this

/-- The direction restriction to a direction's own index is the identity. -/
theorem dirTo_self (a : Shp) (i : Fin 2) (d : Dir a) (hd : rDir a d = i) :
    dirTo i a d = d := by
  match i with
  | 0 => exact codeDir_self a d hd
  | 1 => rfl

/-- The direction restriction is functorial in the target index. -/
theorem dirTo_dirTo (a : Shp) (i' i'' : Fin 2) (h : i'' ≤ i') (d : Dir a) :
    dirTo i'' a (dirTo i' a d) = dirTo i'' a d := by
  match i', i'' with
  | 0, 0 => exact codeDir_self a (codeDir a d) (rDir_codeDir a d)
  | 1, 0 => rfl
  | 1, 1 => rfl
  | 0, 1 => exact absurd h (by decide +revert)

/-- A code shape lies over the code object. -/
theorem qShp_codeShp : ∀ a : Shp, qShp (codeShp a) = 0
  | .base => rfl
  | .sigma => rfl
  | .pi => rfl
  | .lit _ => rfl
  | .pair => rfl

/-- A shape already over the code object is its own code shape. -/
theorem codeShp_self : ∀ a : Shp, qShp a = 0 → codeShp a = a
  | .base, _ => rfl
  | .sigma, _ => rfl
  | .pi, _ => rfl
  | .lit _, h => absurd h (by decide +revert)
  | .pair, h => absurd h (by decide +revert)

/-- The shape restriction lands over its target index. -/
theorem qShp_restrShp (a : Shp) (j' : Fin 2) (h : j' ≤ qShp a) :
    qShp (restrShp j' a) = j' := by
  match j' with
  | 0 => exact qShp_codeShp a
  | 1 => have : qShp a = 1 := by omega
         exact this

/-- The shape restriction to a shape's own index is the identity. -/
theorem restrShp_self (a : Shp) (j : Fin 2) (h : qShp a = j) : restrShp j a = a := by
  match j with
  | 0 => exact codeShp_self a h
  | 1 => rfl

/-- The shape restriction is functorial in the target index. -/
theorem restrShp_restrShp (a : Shp) (j' j'' : Fin 2) (h : j'' ≤ j') :
    restrShp j'' (restrShp j' a) = restrShp j'' a := by
  match j', j'' with
  | 0, 0 => exact codeShp_self (codeShp a) (qShp_codeShp a)
  | 1, 0 => rfl
  | 1, 1 => rfl
  | 0, 1 => exact absurd h (by decide +revert)

/-- The arity reindexing preserves the input index. -/
theorem rDir_reindexDir : ∀ (a : Shp) (d : Dir (codeShp a)),
    rDir a (reindexDir a d) = rDir (codeShp a) d
  | .base, d => d.elim
  | .sigma, _ => rfl
  | .pi, _ => rfl
  | .lit _, d => d.elim
  | .pair, _ => rfl

/-- The arity reindexing to a target index preserves the input index. -/
theorem rDir_reindexTo (j' : Fin 2) (a : Shp) (d : Dir (restrShp j' a)) :
    rDir a (reindexTo j' a d) = rDir (restrShp j' a) d := by
  match j' with
  | 0 => exact rDir_reindexDir a d
  | 1 => rfl

/-- The arity reindexing commutes with the direction restriction: it is a
morphism of arity presheaves. -/
theorem dirTo_reindexTo (j' i' : Fin 2) (a : Shp) (d : Dir (restrShp j' a)) :
    dirTo i' a (reindexTo j' a d) = reindexTo j' a (dirTo i' (restrShp j' a) d) := by
  match j', i' with
  | 1, _ => rfl
  | 0, 1 => rfl
  | 0, 0 => cases a <;> rfl

/-- The arity reindexing along a shape's own index is the identity. -/
theorem reindexTo_self (j : Fin 2) (a : Shp) (h : qShp a = j) (d : Dir (restrShp j a)) :
    reindexTo j a d ≍ d := by
  match j with
  | 0 => cases a
         · rfl
         · rfl
         · rfl
         · exact absurd h (by decide +revert)
         · exact absurd h (by decide +revert)
  | 1 => rfl

/-- The arity reindexing is functorial in the target index. -/
theorem reindexTo_reindexTo (j' j'' : Fin 2) (h : j'' ≤ j') (a : Shp)
    (d : Dir (restrShp j'' a)) (e : Dir (restrShp j'' (restrShp j' a))) (hde : e ≍ d) :
    reindexTo j' a (reindexTo j'' (restrShp j' a) e) ≍ reindexTo j'' a d := by
  match j', j'' with
  | 1, _ => cases eq_of_heq hde; rfl
  | 0, 0 => cases a <;> (cases eq_of_heq hde; rfl)
  | 0, 1 => exact absurd h (by decide +revert)

/-! ## The functor -/

/-- The operations of the universe endofunctor on presheaves over the walking
arrow. Reducible so its shape and direction types unfold, which is what lets the
`decide` tests reduce. -/
@[reducible] def universeData : PresheafPFunctorData (Fin 2) (Fin 2) where
  A := Shp
  B := Dir
  r := fun x ↦ rDir x.1 x.2
  q := qShp
  directionRestr := fun a _i i' g d ↦
    ⟨dirTo i' a d.val, rDir_dirTo a _i i' d.val d.property (leOfHom g)⟩
  shapeRestr := fun _j j' g s ↦
    ⟨restrShp j' s.val, qShp_restrShp s.val j' (le_of_le_of_eq (leOfHom g) s.property.symm)⟩
  reindex := fun _j j' _g a _i d ↦
    ⟨reindexTo j' a.val d.val, (rDir_reindexTo j' a.val d.val).trans d.property⟩

/-- The underlying value of a direction cast along an equality of shapes is the
original underlying value. -/
theorem cast_direction_val {j : Fin 2} {s s' : universeData.Shape j} (h : s = s') {i : Fin 2}
    (p : universeData.Direction s.val i) :
    (cast (congrArg (fun t : universeData.Shape j ↦ universeData.Direction t.val i) h) p).val
      ≍ p.val := by
  cases h
  rfl

/-- The universe endofunctor: the operations with the seven functor laws. -/
@[reducible] def universeFunctor : PresheafPFunctor (Fin 2) (Fin 2) where
  toPresheafPFunctorData := universeData
  isFunctorial :=
    { directionRestr_id := fun a i ↦ funext fun d ↦
        Subtype.ext (dirTo_self a i d.val d.property)
      directionRestr_comp := fun a _i _i' _i'' _f g ↦ funext fun d ↦
        Subtype.ext (dirTo_dirTo a _i' _i'' (leOfHom g) d.val).symm
      shapeRestr_id := fun j ↦ funext fun s ↦ Subtype.ext (restrShp_self s.val j s.property)
      shapeRestr_comp := fun _j _j' _j'' _g h ↦ funext fun s ↦
        Subtype.ext (restrShp_restrShp s.val _j' _j'' (leOfHom h)).symm
      reindex_naturality := fun _j j' _g a _i i' f ↦ funext fun d ↦
        Subtype.ext (dirTo_reindexTo j' i' a.val d.val)
      reindex_id := fun j a i b ↦ by
        apply Subtype.ext
        apply eq_of_heq
        refine HEq.trans (reindexTo_self j a.val a.property b.val) ?_
        exact (cast_direction_val
          (show universeData.shapeRestr (𝟙 j) a = id a from
            Subtype.ext (restrShp_self a.val j a.property)) b).symm
      reindex_comp := fun _j j' j'' g h a _i b ↦ by
        apply Subtype.ext
        apply eq_of_heq
        refine (reindexTo_reindexTo j' j'' (leOfHom h) a.val b.val _ ?_).symm
        exact cast_direction_val
          (show universeData.shapeRestr (h ≫ g) a
              = universeData.shapeRestr h (universeData.shapeRestr g a) from
            Subtype.ext (restrShp_restrShp a.val j' j'' (leOfHom h)).symm) b }

set_option warn.classDefReducibility false in
/-- Each shape has finitely many directions. -/
def finitaryDir : ∀ a : Shp, FinEnum (Dir a)
  | .base => finEnumEmpty
  | .sigma => finEnumBool
  | .pi => finEnumBool
  | .lit _ => finEnumEmpty
  | .pair => finEnumPairDir

set_option warn.classDefReducibility false in
/-- The universe endofunctor is finitary. -/
def finitaryUniverse : universeFunctor.toPFunctor.Finitary := finitaryDir

/-- The universe endofunctor bundled with its finiteness evidence. Reducible so
instance resolution can unfold it and `decide` reduces through the forwarding
instances. -/
@[reducible] def finiteUniverse : FinitePresheafPFunctor (Fin 2) (Fin 2) where
  toPresheafPFunctor := universeFunctor
  finEnumI := finEnumFin2
  finEnumHomI := finEnumHom
  finEnumJ := finEnumFin2
  finEnumA := finEnumShp
  finitary := finitaryUniverse

end GebProto.PresheafUniverse
