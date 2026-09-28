/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.PartialHorn.Basic

set_option doc.verso true in
/-!
# The partial Horn theory of an elementary topos with data objects

The theory whose models are the elementary toposes with chosen structure and the natural
numbers, list and rose-tree objects. Its sorts are the objects and the arrows. Its operations
are the domain, the codomain, identities and composition, as in the theory of categories of
Example 4 of \[PalmgrenVickers2007\]; the terminal and initial objects, binary products and
coproducts, equalizers and coequalizers, exponentials and a subobject classifier, the structure
of an elementary topos as Section 4.3 of \[Goldblatt1984\] defines it, each with its
universal morphisms; and the natural numbers object, the list object of an object, the
rose-tree object and the rose-tree object over an object of labels, each an initial algebra with
its structure maps and its fold.

Each partial operation is defined exactly where its domain's equations hold, by a pair of
sequents; each universal property is stated by its computation equations and its uniqueness,
the uniqueness of a factorization as the equation between a morphism and the factorization of
its composite, and the uniqueness of a fold and of a characteristic map as an equation with
premises. Composition {lit}`comp g f` is {lit}`g` after {lit}`f`, defined when the codomain of
{lit}`f` is the domain of {lit}`g`. A monomorphism is a morphism whose kernel pair's
projections are equal, the kernel pair being the equalizer of its composites with the product
projections. The subobject classifier's axioms state that a monomorphism's factorization
through the equalizer of its characteristic map and truth is an isomorphism, whose inverse is an
operation, and that a morphism into the classifier along which a monomorphism is such an
equalizer is the monomorphism's characteristic map.

## Main definitions

* {lit}`Sorts.obj`, {lit}`Sorts.arr` — the sorts.
* {lit}`sig` — the signature.
* {lit}`axioms` — the axioms, by block.
* {lit}`theory` — the theory.

## References

* \[PalmgrenVickers2007\], Example 4, for the theory of categories.
* \[Goldblatt1984\], Section 4.3, for the definition of an elementary topos.

## Tags

elementary topos, essentially algebraic theory, partial Horn logic, natural numbers object,
initial algebra
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

open PartialHorn

namespace Sorts

/-- The sort of objects. -/
@[match_pattern] abbrev obj : ℕ := 0

/-- The sort of arrows. -/
@[match_pattern] abbrev arr : ℕ := 1

end Sorts

open Sorts

/-- The signature: the operations' argument and result sorts, by index. -/
def sig : Sig := [
  -- the category: domain, codomain, identity, composition
  ([arr], obj), ([arr], obj), ([obj], arr), ([arr, arr], arr),
  -- the terminal object and the morphism to it
  ([], obj), ([obj], arr),
  -- binary products, projections and pairing
  ([obj, obj], obj), ([obj, obj], arr), ([obj, obj], arr), ([arr, arr], arr),
  -- equalizers, their inclusions and factorizations
  ([arr, arr], obj), ([arr, arr], arr), ([arr, arr, arr], arr),
  -- the initial object and the morphism from it
  ([], obj), ([obj], arr),
  -- binary coproducts, injections and copairing
  ([obj, obj], obj), ([obj, obj], arr), ([obj, obj], arr), ([arr, arr], arr),
  -- coequalizers, their projections and descents
  ([arr, arr], obj), ([arr, arr], arr), ([arr, arr, arr], arr),
  -- exponentials, evaluation and currying
  ([obj, obj], obj), ([obj, obj], arr), ([obj, obj, arr], arr),
  -- the subobject classifier, truth, characteristic maps and their pullbacks' inverses
  ([], obj), ([], arr), ([arr], arr), ([arr], arr),
  -- the natural numbers object, zero, successor and recursion
  ([], obj), ([], arr), ([], arr), ([arr, arr], arr),
  -- list objects, the empty list, cons and recursion
  ([obj], obj), ([obj], arr), ([obj], arr), ([obj, arr, arr], arr),
  -- the rose-tree object, its structure map and recursion
  ([], obj), ([], arr), ([arr], arr),
  -- rose-tree objects over objects of labels, their structure maps and recursion
  ([obj], obj), ([obj], arr), ([obj, arr], arr)]

/-- The variable of an index. -/
abbrev x (i : ℕ) : Tree := var i

/-- The domain of an arrow. -/
def dom (f : Tree) : Tree := op 0 [f]

/-- The codomain of an arrow. -/
def cod (f : Tree) : Tree := op 1 [f]

/-- The identity of an object. -/
def idt (a : Tree) : Tree := op 2 [a]

/-- The composite of {lit}`g` after {lit}`f`. -/
def comp (g f : Tree) : Tree := op 3 [g, f]

/-- The terminal object. -/
def one : Tree := op 4 []

/-- The morphism from an object to the terminal object. -/
def bang (a : Tree) : Tree := op 5 [a]

/-- The product of two objects. -/
def prod (a b : Tree) : Tree := op 6 [a, b]

/-- The first projection of a product. -/
def fst (a b : Tree) : Tree := op 7 [a, b]

/-- The second projection of a product. -/
def snd (a b : Tree) : Tree := op 8 [a, b]

/-- The pairing of two morphisms of one domain. -/
def pair (f g : Tree) : Tree := op 9 [f, g]

/-- The equalizer of two parallel morphisms. -/
def eqz (f g : Tree) : Tree := op 10 [f, g]

/-- The inclusion of the equalizer of two parallel morphisms. -/
def eqIncl (f g : Tree) : Tree := op 11 [f, g]

/-- The factorization through the equalizer of {lit}`f` and {lit}`g` of a morphism that
equalizes them. -/
def eqLift (f g h : Tree) : Tree := op 12 [f, g, h]

/-- The initial object. -/
def zero : Tree := op 13 []

/-- The morphism from the initial object to an object. -/
def absurd (a : Tree) : Tree := op 14 [a]

/-- The coproduct of two objects. -/
def coprod (a b : Tree) : Tree := op 15 [a, b]

/-- The first injection into a coproduct. -/
def inl (a b : Tree) : Tree := op 16 [a, b]

/-- The second injection into a coproduct. -/
def inr (a b : Tree) : Tree := op 17 [a, b]

/-- The copairing of two morphisms of one codomain. -/
def copair (f g : Tree) : Tree := op 18 [f, g]

/-- The coequalizer of two parallel morphisms. -/
def coeqz (f g : Tree) : Tree := op 19 [f, g]

/-- The projection onto the coequalizer of two parallel morphisms. -/
def coeqProj (f g : Tree) : Tree := op 20 [f, g]

/-- The descent through the coequalizer of {lit}`f` and {lit}`g` of a morphism that
coequalizes them. -/
def coeqDesc (f g h : Tree) : Tree := op 21 [f, g, h]

/-- The exponential {lit}`exp a b`, the object of morphisms from {lit}`a` to {lit}`b`. -/
def exp (a b : Tree) : Tree := op 22 [a, b]

/-- The evaluation morphism, from the product of {lit}`exp a b` and {lit}`a` to {lit}`b`. -/
def ev (a b : Tree) : Tree := op 23 [a, b]

/-- The currying of a morphism from the product of {lit}`c` and {lit}`a`. -/
def curry (c a f : Tree) : Tree := op 24 [c, a, f]

/-- The subobject classifier. -/
def omega : Tree := op 25 []

/-- Truth, from the terminal object to the subobject classifier. -/
def tru : Tree := op 26 []

/-- The characteristic map of a monomorphism. -/
def chi (m : Tree) : Tree := op 27 [m]

/-- The inverse of a monomorphism's factorization through the equalizer of its characteristic
map and truth. -/
def chiInv (m : Tree) : Tree := op 28 [m]

/-- The natural numbers object. -/
def nat : Tree := op 29 []

/-- Zero, from the terminal object to the natural numbers object. -/
def zeroN : Tree := op 30 []

/-- The successor. -/
def succ : Tree := op 31 []

/-- The morphism from the natural numbers object that recursion with a start and a step
defines. -/
def natRec (z s : Tree) : Tree := op 32 [z, s]

/-- The list object of an object. -/
def list (a : Tree) : Tree := op 33 [a]

/-- The empty list, from the terminal object. -/
def nil (a : Tree) : Tree := op 34 [a]

/-- The construction of a list from an element and a list. -/
def cons (a : Tree) : Tree := op 35 [a]

/-- The morphism from the list object of {lit}`a` that recursion with a start and a step
defines. -/
def listRec (a z s : Tree) : Tree := op 36 [a, z, s]

/-- The rose-tree object. -/
def rose : Tree := op 37 []

/-- The rose-tree object's structure map, from the product of the natural numbers object and
the list object of the rose-tree object. -/
def node : Tree := op 38 []

/-- The fold of the rose-tree object into an algebra. -/
def roseRec (f : Tree) : Tree := op 39 [f]

/-- The rose-tree object over an object of labels. -/
def lrose (a : Tree) : Tree := op 40 [a]

/-- The structure map of the rose-tree object over the object of labels {lit}`a`, from the
product of {lit}`a` and the list object of the rose-tree object. -/
def lnode (a : Tree) : Tree := op 41 [a]

/-- The fold of the rose-tree object over the object of labels {lit}`a` into an algebra. -/
def lroseRec (a f : Tree) : Tree := op 42 [a, f]

/-- The equation stating that a term is defined. -/
def dfd (t : Tree) : Eqn := ⟨t, t⟩

/-- The morphism {lit}`f × id`, from the product of the domain of {lit}`f` and {lit}`a` to
the product of its codomain and {lit}`a`. -/
def prodMapLeft (f a : Tree) : Tree :=
  pair (comp f (fst (dom f) a)) (snd (dom f) a)

/-- The morphism {lit}`id × f`, from the product of {lit}`a` and the domain of {lit}`f` to the
product of {lit}`a` and its codomain. -/
def prodMapRight (a f : Tree) : Tree :=
  pair (fst a (dom f)) (comp f (snd a (dom f)))

/-- The action of the list object on a morphism, by recursion. -/
def listMap (f : Tree) : Tree :=
  listRec (dom f) (nil (cod f)) (comp (cons (cod f)) (prodMapLeft f (list (cod f))))

/-- The diagonal of an object, the pairing of its identity with itself. -/
def diag (a : Tree) : Tree := pair (idt a) (idt a)

/-- The condition that an arrow is a monomorphism: the projections of its kernel pair, the
equalizer of its composites with the product projections, are equal. -/
def monoCond (m : Tree) : Eqn :=
  let a := dom m
  let k := eqIncl (comp m (fst a a)) (comp m (snd a a))
  ⟨comp (fst a a) k, comp (snd a a) k⟩

/-- The equalizer of a morphism into the classifier and truth after the morphism to the
terminal object: the pullback of truth along it. -/
def truthEq (φ : Tree) : Tree := eqz φ (comp tru (bang (dom φ)))

/-- The inclusion of {lit}`truthEq`. -/
def truthIncl (φ : Tree) : Tree := eqIncl φ (comp tru (bang (dom φ)))

/-- The factorization of a morphism through {lit}`truthEq`. -/
def truthLift (φ m : Tree) : Tree := eqLift φ (comp tru (bang (dom φ))) m

/-- The axioms of a category (Example 4 of the theory of categories). -/
def categoryAxioms : List Seq := [
  ⟨[arr], [], dfd (dom (x 0))⟩,
  ⟨[arr], [], dfd (cod (x 0))⟩,
  ⟨[obj], [], dfd (idt (x 0))⟩,
  ⟨[arr, arr], [dfd (comp (x 0) (x 1))], ⟨cod (x 1), dom (x 0)⟩⟩,
  ⟨[arr, arr], [⟨cod (x 1), dom (x 0)⟩], dfd (comp (x 0) (x 1))⟩,
  ⟨[arr, arr], [dfd (comp (x 0) (x 1))], ⟨dom (comp (x 0) (x 1)), dom (x 1)⟩⟩,
  ⟨[arr, arr], [dfd (comp (x 0) (x 1))], ⟨cod (comp (x 0) (x 1)), cod (x 0)⟩⟩,
  ⟨[arr, arr, arr], [dfd (comp (x 0) (comp (x 1) (x 2)))],
    ⟨comp (x 0) (comp (x 1) (x 2)), comp (comp (x 0) (x 1)) (x 2)⟩⟩,
  ⟨[obj], [], ⟨dom (idt (x 0)), x 0⟩⟩,
  ⟨[obj], [], ⟨cod (idt (x 0)), x 0⟩⟩,
  ⟨[arr], [], ⟨comp (x 0) (idt (dom (x 0))), x 0⟩⟩,
  ⟨[arr], [], ⟨comp (idt (cod (x 0))) (x 0), x 0⟩⟩]

/-- The axioms of the terminal object. -/
def terminalAxioms : List Seq := [
  ⟨[], [], dfd one⟩,
  ⟨[obj], [], ⟨dom (bang (x 0)), x 0⟩⟩,
  ⟨[obj], [], ⟨cod (bang (x 0)), one⟩⟩,
  ⟨[arr], [⟨cod (x 0), one⟩], ⟨x 0, bang (dom (x 0))⟩⟩]

/-- The axioms of binary products. -/
def productAxioms : List Seq := [
  ⟨[obj, obj], [], dfd (prod (x 0) (x 1))⟩,
  ⟨[obj, obj], [], ⟨dom (fst (x 0) (x 1)), prod (x 0) (x 1)⟩⟩,
  ⟨[obj, obj], [], ⟨cod (fst (x 0) (x 1)), x 0⟩⟩,
  ⟨[obj, obj], [], ⟨dom (snd (x 0) (x 1)), prod (x 0) (x 1)⟩⟩,
  ⟨[obj, obj], [], ⟨cod (snd (x 0) (x 1)), x 1⟩⟩,
  ⟨[arr, arr], [dfd (pair (x 0) (x 1))], ⟨dom (x 0), dom (x 1)⟩⟩,
  ⟨[arr, arr], [⟨dom (x 0), dom (x 1)⟩], dfd (pair (x 0) (x 1))⟩,
  ⟨[arr, arr], [dfd (pair (x 0) (x 1))], ⟨dom (pair (x 0) (x 1)), dom (x 0)⟩⟩,
  ⟨[arr, arr], [dfd (pair (x 0) (x 1))],
    ⟨cod (pair (x 0) (x 1)), prod (cod (x 0)) (cod (x 1))⟩⟩,
  ⟨[arr, arr], [dfd (pair (x 0) (x 1))],
    ⟨comp (fst (cod (x 0)) (cod (x 1))) (pair (x 0) (x 1)), x 0⟩⟩,
  ⟨[arr, arr], [dfd (pair (x 0) (x 1))],
    ⟨comp (snd (cod (x 0)) (cod (x 1))) (pair (x 0) (x 1)), x 1⟩⟩,
  ⟨[arr, obj, obj], [⟨cod (x 0), prod (x 1) (x 2)⟩],
    ⟨pair (comp (fst (x 1) (x 2)) (x 0)) (comp (snd (x 1) (x 2)) (x 0)), x 0⟩⟩]

/-- The axioms of equalizers. -/
def equalizerAxioms : List Seq := [
  ⟨[arr, arr], [dfd (eqz (x 0) (x 1))], ⟨dom (x 0), dom (x 1)⟩⟩,
  ⟨[arr, arr], [dfd (eqz (x 0) (x 1))], ⟨cod (x 0), cod (x 1)⟩⟩,
  ⟨[arr, arr], [⟨dom (x 0), dom (x 1)⟩, ⟨cod (x 0), cod (x 1)⟩], dfd (eqz (x 0) (x 1))⟩,
  ⟨[arr, arr], [dfd (eqIncl (x 0) (x 1))], dfd (eqz (x 0) (x 1))⟩,
  ⟨[arr, arr], [dfd (eqz (x 0) (x 1))], dfd (eqIncl (x 0) (x 1))⟩,
  ⟨[arr, arr], [dfd (eqz (x 0) (x 1))], ⟨dom (eqIncl (x 0) (x 1)), eqz (x 0) (x 1)⟩⟩,
  ⟨[arr, arr], [dfd (eqz (x 0) (x 1))], ⟨cod (eqIncl (x 0) (x 1)), dom (x 0)⟩⟩,
  ⟨[arr, arr], [dfd (eqz (x 0) (x 1))],
    ⟨comp (x 0) (eqIncl (x 0) (x 1)), comp (x 1) (eqIncl (x 0) (x 1))⟩⟩,
  ⟨[arr, arr, arr], [dfd (eqLift (x 0) (x 1) (x 2))], dfd (eqz (x 0) (x 1))⟩,
  ⟨[arr, arr, arr], [dfd (eqLift (x 0) (x 1) (x 2))], ⟨comp (x 0) (x 2), comp (x 1) (x 2)⟩⟩,
  ⟨[arr, arr, arr], [dfd (eqz (x 0) (x 1)), ⟨comp (x 0) (x 2), comp (x 1) (x 2)⟩],
    dfd (eqLift (x 0) (x 1) (x 2))⟩,
  ⟨[arr, arr, arr], [dfd (eqLift (x 0) (x 1) (x 2))],
    ⟨dom (eqLift (x 0) (x 1) (x 2)), dom (x 2)⟩⟩,
  ⟨[arr, arr, arr], [dfd (eqLift (x 0) (x 1) (x 2))],
    ⟨cod (eqLift (x 0) (x 1) (x 2)), eqz (x 0) (x 1)⟩⟩,
  ⟨[arr, arr, arr], [dfd (eqLift (x 0) (x 1) (x 2))],
    ⟨comp (eqIncl (x 0) (x 1)) (eqLift (x 0) (x 1) (x 2)), x 2⟩⟩,
  ⟨[arr, arr, arr], [dfd (eqz (x 0) (x 1)), ⟨cod (x 2), eqz (x 0) (x 1)⟩],
    ⟨eqLift (x 0) (x 1) (comp (eqIncl (x 0) (x 1)) (x 2)), x 2⟩⟩]

/-- The axioms of the initial object. -/
def initialAxioms : List Seq := [
  ⟨[], [], dfd zero⟩,
  ⟨[obj], [], ⟨dom (absurd (x 0)), zero⟩⟩,
  ⟨[obj], [], ⟨cod (absurd (x 0)), x 0⟩⟩,
  ⟨[arr], [⟨dom (x 0), zero⟩], ⟨x 0, absurd (cod (x 0))⟩⟩]

/-- The axioms of binary coproducts. -/
def coproductAxioms : List Seq := [
  ⟨[obj, obj], [], dfd (coprod (x 0) (x 1))⟩,
  ⟨[obj, obj], [], ⟨dom (inl (x 0) (x 1)), x 0⟩⟩,
  ⟨[obj, obj], [], ⟨cod (inl (x 0) (x 1)), coprod (x 0) (x 1)⟩⟩,
  ⟨[obj, obj], [], ⟨dom (inr (x 0) (x 1)), x 1⟩⟩,
  ⟨[obj, obj], [], ⟨cod (inr (x 0) (x 1)), coprod (x 0) (x 1)⟩⟩,
  ⟨[arr, arr], [dfd (copair (x 0) (x 1))], ⟨cod (x 0), cod (x 1)⟩⟩,
  ⟨[arr, arr], [⟨cod (x 0), cod (x 1)⟩], dfd (copair (x 0) (x 1))⟩,
  ⟨[arr, arr], [dfd (copair (x 0) (x 1))],
    ⟨dom (copair (x 0) (x 1)), coprod (dom (x 0)) (dom (x 1))⟩⟩,
  ⟨[arr, arr], [dfd (copair (x 0) (x 1))], ⟨cod (copair (x 0) (x 1)), cod (x 0)⟩⟩,
  ⟨[arr, arr], [dfd (copair (x 0) (x 1))],
    ⟨comp (copair (x 0) (x 1)) (inl (dom (x 0)) (dom (x 1))), x 0⟩⟩,
  ⟨[arr, arr], [dfd (copair (x 0) (x 1))],
    ⟨comp (copair (x 0) (x 1)) (inr (dom (x 0)) (dom (x 1))), x 1⟩⟩,
  ⟨[arr, obj, obj], [⟨dom (x 0), coprod (x 1) (x 2)⟩],
    ⟨copair (comp (x 0) (inl (x 1) (x 2))) (comp (x 0) (inr (x 1) (x 2))), x 0⟩⟩]

/-- The axioms of coequalizers. -/
def coequalizerAxioms : List Seq := [
  ⟨[arr, arr], [dfd (coeqz (x 0) (x 1))], ⟨dom (x 0), dom (x 1)⟩⟩,
  ⟨[arr, arr], [dfd (coeqz (x 0) (x 1))], ⟨cod (x 0), cod (x 1)⟩⟩,
  ⟨[arr, arr], [⟨dom (x 0), dom (x 1)⟩, ⟨cod (x 0), cod (x 1)⟩], dfd (coeqz (x 0) (x 1))⟩,
  ⟨[arr, arr], [dfd (coeqProj (x 0) (x 1))], dfd (coeqz (x 0) (x 1))⟩,
  ⟨[arr, arr], [dfd (coeqz (x 0) (x 1))], dfd (coeqProj (x 0) (x 1))⟩,
  ⟨[arr, arr], [dfd (coeqz (x 0) (x 1))], ⟨dom (coeqProj (x 0) (x 1)), cod (x 0)⟩⟩,
  ⟨[arr, arr], [dfd (coeqz (x 0) (x 1))], ⟨cod (coeqProj (x 0) (x 1)), coeqz (x 0) (x 1)⟩⟩,
  ⟨[arr, arr], [dfd (coeqz (x 0) (x 1))],
    ⟨comp (coeqProj (x 0) (x 1)) (x 0), comp (coeqProj (x 0) (x 1)) (x 1)⟩⟩,
  ⟨[arr, arr, arr], [dfd (coeqDesc (x 0) (x 1) (x 2))], dfd (coeqz (x 0) (x 1))⟩,
  ⟨[arr, arr, arr], [dfd (coeqDesc (x 0) (x 1) (x 2))],
    ⟨comp (x 2) (x 0), comp (x 2) (x 1)⟩⟩,
  ⟨[arr, arr, arr], [dfd (coeqz (x 0) (x 1)), ⟨comp (x 2) (x 0), comp (x 2) (x 1)⟩],
    dfd (coeqDesc (x 0) (x 1) (x 2))⟩,
  ⟨[arr, arr, arr], [dfd (coeqDesc (x 0) (x 1) (x 2))],
    ⟨dom (coeqDesc (x 0) (x 1) (x 2)), coeqz (x 0) (x 1)⟩⟩,
  ⟨[arr, arr, arr], [dfd (coeqDesc (x 0) (x 1) (x 2))],
    ⟨cod (coeqDesc (x 0) (x 1) (x 2)), cod (x 2)⟩⟩,
  ⟨[arr, arr, arr], [dfd (coeqDesc (x 0) (x 1) (x 2))],
    ⟨comp (coeqDesc (x 0) (x 1) (x 2)) (coeqProj (x 0) (x 1)), x 2⟩⟩,
  ⟨[arr, arr, arr], [dfd (coeqz (x 0) (x 1)), ⟨dom (x 2), coeqz (x 0) (x 1)⟩],
    ⟨coeqDesc (x 0) (x 1) (comp (x 2) (coeqProj (x 0) (x 1))), x 2⟩⟩]

/-- The axioms of exponentials: currying's computation rule through evaluation, and its
uniqueness. -/
def exponentialAxioms : List Seq := [
  ⟨[obj, obj], [], dfd (exp (x 0) (x 1))⟩,
  ⟨[obj, obj], [], ⟨dom (ev (x 0) (x 1)), prod (exp (x 0) (x 1)) (x 0)⟩⟩,
  ⟨[obj, obj], [], ⟨cod (ev (x 0) (x 1)), x 1⟩⟩,
  ⟨[obj, obj, arr], [dfd (curry (x 0) (x 1) (x 2))], ⟨dom (x 2), prod (x 0) (x 1)⟩⟩,
  ⟨[obj, obj, arr], [⟨dom (x 2), prod (x 0) (x 1)⟩], dfd (curry (x 0) (x 1) (x 2))⟩,
  ⟨[obj, obj, arr], [dfd (curry (x 0) (x 1) (x 2))], ⟨dom (curry (x 0) (x 1) (x 2)), x 0⟩⟩,
  ⟨[obj, obj, arr], [dfd (curry (x 0) (x 1) (x 2))],
    ⟨cod (curry (x 0) (x 1) (x 2)), exp (x 1) (cod (x 2))⟩⟩,
  ⟨[obj, obj, arr], [dfd (curry (x 0) (x 1) (x 2))],
    ⟨comp (ev (x 1) (cod (x 2))) (prodMapLeft (curry (x 0) (x 1) (x 2)) (x 1)), x 2⟩⟩,
  ⟨[obj, obj, obj, arr], [⟨dom (x 3), x 0⟩, ⟨cod (x 3), exp (x 1) (x 2)⟩],
    ⟨curry (x 0) (x 1) (comp (ev (x 1) (x 2)) (prodMapLeft (x 3) (x 1))), x 3⟩⟩]

/-- The axioms of the subobject classifier: a monomorphism is the pullback of truth along its
characteristic map, whose comparison with the equalizer of the characteristic map and truth has
an inverse, and a morphism along which a monomorphism is so a pullback is its characteristic
map. -/
def classifierAxioms : List Seq := [
  ⟨[], [], dfd omega⟩,
  ⟨[], [], ⟨dom tru, one⟩⟩,
  ⟨[], [], ⟨cod tru, omega⟩⟩,
  ⟨[arr], [dfd (chi (x 0))], monoCond (x 0)⟩,
  ⟨[arr], [monoCond (x 0)], dfd (chi (x 0))⟩,
  ⟨[arr], [dfd (chi (x 0))], ⟨dom (chi (x 0)), cod (x 0)⟩⟩,
  ⟨[arr], [dfd (chi (x 0))], ⟨cod (chi (x 0)), omega⟩⟩,
  ⟨[arr], [dfd (chi (x 0))], ⟨comp (chi (x 0)) (x 0), comp tru (bang (dom (x 0)))⟩⟩,
  ⟨[arr], [dfd (chiInv (x 0))], dfd (chi (x 0))⟩,
  ⟨[arr], [dfd (chi (x 0))], dfd (chiInv (x 0))⟩,
  ⟨[arr], [dfd (chi (x 0))], ⟨dom (chiInv (x 0)), truthEq (chi (x 0))⟩⟩,
  ⟨[arr], [dfd (chi (x 0))], ⟨cod (chiInv (x 0)), dom (x 0)⟩⟩,
  ⟨[arr], [dfd (chi (x 0))],
    ⟨comp (truthLift (chi (x 0)) (x 0)) (chiInv (x 0)), idt (truthEq (chi (x 0)))⟩⟩,
  ⟨[arr], [dfd (chi (x 0))],
    ⟨comp (chiInv (x 0)) (truthLift (chi (x 0)) (x 0)), idt (dom (x 0))⟩⟩,
  ⟨[arr, arr, arr, arr],
    [dfd (chi (x 0)), ⟨dom (x 1), cod (x 0)⟩, ⟨cod (x 1), omega⟩,
      ⟨comp (truthIncl (x 1)) (x 2), x 0⟩, ⟨comp (x 2) (x 3), idt (truthEq (x 1))⟩,
      ⟨comp (x 3) (x 2), idt (dom (x 0))⟩],
    ⟨x 1, chi (x 0)⟩⟩]

/-- The axioms of the natural numbers object, the initial algebra of the functor taking an
object to its sum with the terminal object, stated by its start and its step. -/
def natAxioms : List Seq := [
  ⟨[], [], ⟨dom zeroN, one⟩⟩,
  ⟨[], [], ⟨cod zeroN, nat⟩⟩,
  ⟨[], [], ⟨dom succ, nat⟩⟩,
  ⟨[], [], ⟨cod succ, nat⟩⟩,
  ⟨[arr, arr], [dfd (natRec (x 0) (x 1))], ⟨dom (x 0), one⟩⟩,
  ⟨[arr, arr], [dfd (natRec (x 0) (x 1))], ⟨cod (x 0), dom (x 1)⟩⟩,
  ⟨[arr, arr], [dfd (natRec (x 0) (x 1))], ⟨dom (x 1), cod (x 1)⟩⟩,
  ⟨[arr, arr], [⟨dom (x 0), one⟩, ⟨cod (x 0), dom (x 1)⟩, ⟨dom (x 1), cod (x 1)⟩],
    dfd (natRec (x 0) (x 1))⟩,
  ⟨[arr, arr], [dfd (natRec (x 0) (x 1))], ⟨dom (natRec (x 0) (x 1)), nat⟩⟩,
  ⟨[arr, arr], [dfd (natRec (x 0) (x 1))], ⟨cod (natRec (x 0) (x 1)), cod (x 0)⟩⟩,
  ⟨[arr, arr], [dfd (natRec (x 0) (x 1))], ⟨comp (natRec (x 0) (x 1)) zeroN, x 0⟩⟩,
  ⟨[arr, arr], [dfd (natRec (x 0) (x 1))],
    ⟨comp (natRec (x 0) (x 1)) succ, comp (x 1) (natRec (x 0) (x 1))⟩⟩,
  ⟨[arr, arr, arr],
    [dfd (natRec (x 0) (x 1)), ⟨dom (x 2), nat⟩, ⟨comp (x 2) zeroN, x 0⟩,
      ⟨comp (x 2) succ, comp (x 1) (x 2)⟩],
    ⟨x 2, natRec (x 0) (x 1)⟩⟩]

/-- The axioms of list objects, each the initial algebra of the functor taking an object to its
sum with the terminal object and the product with the list's element object, stated by its start
and its step. -/
def listAxioms : List Seq := [
  ⟨[obj], [], dfd (list (x 0))⟩,
  ⟨[obj], [], ⟨dom (nil (x 0)), one⟩⟩,
  ⟨[obj], [], ⟨cod (nil (x 0)), list (x 0)⟩⟩,
  ⟨[obj], [], ⟨dom (cons (x 0)), prod (x 0) (list (x 0))⟩⟩,
  ⟨[obj], [], ⟨cod (cons (x 0)), list (x 0)⟩⟩,
  ⟨[obj, arr, arr], [dfd (listRec (x 0) (x 1) (x 2))], ⟨dom (x 1), one⟩⟩,
  ⟨[obj, arr, arr], [dfd (listRec (x 0) (x 1) (x 2))], ⟨cod (x 1), cod (x 2)⟩⟩,
  ⟨[obj, arr, arr], [dfd (listRec (x 0) (x 1) (x 2))],
    ⟨dom (x 2), prod (x 0) (cod (x 2))⟩⟩,
  ⟨[obj, arr, arr], [⟨dom (x 1), one⟩, ⟨cod (x 1), cod (x 2)⟩,
      ⟨dom (x 2), prod (x 0) (cod (x 2))⟩],
    dfd (listRec (x 0) (x 1) (x 2))⟩,
  ⟨[obj, arr, arr], [dfd (listRec (x 0) (x 1) (x 2))],
    ⟨dom (listRec (x 0) (x 1) (x 2)), list (x 0)⟩⟩,
  ⟨[obj, arr, arr], [dfd (listRec (x 0) (x 1) (x 2))],
    ⟨cod (listRec (x 0) (x 1) (x 2)), cod (x 1)⟩⟩,
  ⟨[obj, arr, arr], [dfd (listRec (x 0) (x 1) (x 2))],
    ⟨comp (listRec (x 0) (x 1) (x 2)) (nil (x 0)), x 1⟩⟩,
  ⟨[obj, arr, arr], [dfd (listRec (x 0) (x 1) (x 2))],
    ⟨comp (listRec (x 0) (x 1) (x 2)) (cons (x 0)),
      comp (x 2) (prodMapRight (x 0) (listRec (x 0) (x 1) (x 2)))⟩⟩,
  ⟨[obj, arr, arr, arr],
    [dfd (listRec (x 0) (x 1) (x 2)), ⟨dom (x 3), list (x 0)⟩, ⟨comp (x 3) (nil (x 0)), x 1⟩,
      ⟨comp (x 3) (cons (x 0)), comp (x 2) (prodMapRight (x 0) (x 3))⟩],
    ⟨x 3, listRec (x 0) (x 1) (x 2)⟩⟩]

/-- The axioms of the rose-tree object, the initial algebra of the functor taking an object to
the product of the natural numbers object and the object's list object. -/
def roseAxioms : List Seq := [
  ⟨[], [], ⟨dom node, prod nat (list rose)⟩⟩,
  ⟨[], [], ⟨cod node, rose⟩⟩,
  ⟨[arr], [dfd (roseRec (x 0))], ⟨dom (x 0), prod nat (list (cod (x 0)))⟩⟩,
  ⟨[arr], [⟨dom (x 0), prod nat (list (cod (x 0)))⟩], dfd (roseRec (x 0))⟩,
  ⟨[arr], [dfd (roseRec (x 0))], ⟨dom (roseRec (x 0)), rose⟩⟩,
  ⟨[arr], [dfd (roseRec (x 0))], ⟨cod (roseRec (x 0)), cod (x 0)⟩⟩,
  ⟨[arr], [dfd (roseRec (x 0))],
    ⟨comp (roseRec (x 0)) node, comp (x 0) (prodMapRight nat (listMap (roseRec (x 0))))⟩⟩,
  ⟨[arr, arr],
    [dfd (roseRec (x 0)), ⟨dom (x 1), rose⟩,
      ⟨comp (x 1) node, comp (x 0) (prodMapRight nat (listMap (x 1)))⟩],
    ⟨x 1, roseRec (x 0)⟩⟩]

/-- The axioms of the rose-tree object over an object of labels, the initial algebra of the
functor taking an object to the product of the object of labels and the object's list object. -/
def lroseAxioms : List Seq := [
  ⟨[obj], [], dfd (lrose (x 0))⟩,
  ⟨[obj], [], ⟨dom (lnode (x 0)), prod (x 0) (list (lrose (x 0)))⟩⟩,
  ⟨[obj], [], ⟨cod (lnode (x 0)), lrose (x 0)⟩⟩,
  ⟨[obj, arr], [dfd (lroseRec (x 0) (x 1))], ⟨dom (x 1), prod (x 0) (list (cod (x 1)))⟩⟩,
  ⟨[obj, arr], [⟨dom (x 1), prod (x 0) (list (cod (x 1)))⟩], dfd (lroseRec (x 0) (x 1))⟩,
  ⟨[obj, arr], [dfd (lroseRec (x 0) (x 1))], ⟨dom (lroseRec (x 0) (x 1)), lrose (x 0)⟩⟩,
  ⟨[obj, arr], [dfd (lroseRec (x 0) (x 1))], ⟨cod (lroseRec (x 0) (x 1)), cod (x 1)⟩⟩,
  ⟨[obj, arr], [dfd (lroseRec (x 0) (x 1))],
    ⟨comp (lroseRec (x 0) (x 1)) (lnode (x 0)),
      comp (x 1) (prodMapRight (x 0) (listMap (lroseRec (x 0) (x 1))))⟩⟩,
  ⟨[obj, arr, arr],
    [dfd (lroseRec (x 0) (x 1)), ⟨dom (x 2), lrose (x 0)⟩,
      ⟨comp (x 2) (lnode (x 0)), comp (x 1) (prodMapRight (x 0) (listMap (x 2)))⟩],
    ⟨x 2, lroseRec (x 0) (x 1)⟩⟩]

/-- The axioms, block by block; a certificate cites an axiom by its index here, so the list is
only extended. -/
def axioms : List Seq :=
  categoryAxioms ++ terminalAxioms ++ productAxioms ++ equalizerAxioms ++ initialAxioms ++
    coproductAxioms ++ coequalizerAxioms ++ exponentialAxioms ++ classifierAxioms ++
    natAxioms ++ listAxioms ++ roseAxioms ++ lroseAxioms

/-- The partial Horn theory of an elementary topos with the natural numbers, list and
rose-tree objects. -/
def theory : Theory := ⟨sig, axioms⟩

end Geb.FreeTopos

end
