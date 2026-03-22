import GebLean.PolyAlg
import GebLean.Utilities.Slice

/-!
# Polynomial Combinators

Generic combinators for constructing polynomial
endofunctors on slice categories, with support for
multi-sorted (non-trivial base) polynomials.
-/

namespace GebLean

open CategoryTheory

universe u

/--
The empty polynomial: no positions at any fiber.
-/
def polyEmpty (X : Type u) : PolyEndo X :=
  fun _ => ccrObjMk
    (fun (e : PEmpty.{u + 1}) => PEmpty.elim e)

/--
Reindex a polynomial endofunctor along a map `f : X → Y`.

At fiber `y : Y`, positions are triples
`(x : X, _ : f x = y, i : polyBetweenIndex P x)`.
Directions at such a position are those of `P` at
`x` and position `i`, with the fiber map composed
with `f`.
-/
def polyFiberReindex {X : Type u} {Y : Type u}
    (f : X → Y) (P : PolyEndo X) : PolyEndo Y :=
  fun y => ccrObjMk
    (fun (p : (x : X) ×
        PLift (f x = y) ×
        polyBetweenIndex X X P x) =>
      let dirObj := polyBetweenFamily X X P
        p.1 p.2.2
      Over.mk (f ∘ dirObj.hom))

/--
Embed a polynomial from a smaller base into a
larger base along `f : X → Y`. At fibers `y` not
in the image of `f`, the polynomial has no positions.
-/
abbrev polyFiberEmbed {X : Type u} {Y : Type u}
    (f : X → Y) (P : PolyEndo X) : PolyEndo Y :=
  polyFiberReindex f P

/--
Pointwise coproduct of two polynomial endofunctors.
At each fiber, the position type is the sum of the
two position types, and directions are inherited from
the corresponding summand.
-/
def polyFiberCoprod {X : Type u}
    (P Q : PolyEndo X) : PolyEndo X :=
  fun x => ccrObjMk
    (fun (p : polyBetweenIndex X X P x ⊕
              polyBetweenIndex X X Q x) =>
      match p with
      | Sum.inl i =>
        polyBetweenFamily X X P x i
      | Sum.inr j =>
        polyBetweenFamily X X Q x j)

/--
A polynomial on `Fin n` with one constructor at
fiber `j` whose `k` directions each map to fiber `i`.
At fibers other than `j`, the polynomial is empty.
-/
def polyCrossSortCtor {n : Nat}
    (j i : Fin n) (k : Nat) :
    PolyEndo (Fin n) :=
  fun x =>
    if _ : x = j then
      ccrObjMk
        (fun _ : PUnit.{1} =>
          Over.mk (fun _ : Fin k => i))
    else
      ccrObjMk
        (fun (e : PEmpty.{1}) =>
          PEmpty.elim e)

/--
A polynomial at one fiber with `Nat`-indexed
positions. At fiber `x`, position `n` has `Fin n`
directions, each mapping to `target`. At all other
fibers, the polynomial is empty.
-/
def polyNatIndexed {X : Type u} [DecidableEq X]
    (x : X) (target : X) : PolyEndo X :=
  fun y =>
    if _ : y = x then
      ccrObjMk
        (fun (n : ULift.{u} Nat) =>
          Over.mk
            (fun (_ : ULift.{u} (Fin n.down)) =>
              target))
    else
      ccrObjMk
        (fun (e : PEmpty.{u + 1}) =>
          PEmpty.elim e)

end GebLean
