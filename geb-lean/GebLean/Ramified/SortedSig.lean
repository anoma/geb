import GebLean.Ramified.AlgSig

/-!
# Multi-sorted signatures and the constructor summand

Finitary presentation data for multi-sorted algebraic signatures. A
`SortedSig` over a sort type `S` names its operations together with each
operation's sorted arity and result sort. `SortedSig.sum` assembles two
signatures over the same sorts by disjoint union of their operations,
the data-types-a-la-carte pattern of pluggable summands. `constructorSig`
derives, from a free-algebra signature `AlgSig`, the sorted signature
whose operations are the algebra's constructors replicated at each object
sort: shapes become operations and arity positions become sorted arities.

These definitions are novel packaging: they present the free-algebra
conventions of Leivant III section 2.1 and the data-system layer adopted
in the spec from Danner and Royer through multi-sorted signatures over an
explicit sort type. No recursion is involved; the structures are
finitary presentation data.

## Main definitions

* `SortedSig` — a multi-sorted algebraic signature: operations with
  sorted arities and result sorts.
* `SortedSig.sum` — the disjoint union of two signatures over the same
  sorts (data-types-a-la-carte assembly).
* `constructorSig` — the constructor summand derived from a free-algebra
  signature, one operation per object sort and constructor label.

## References

The multi-sorted-signature presentation follows the free-algebra
conventions of D. Leivant, "Ramified recurrence and computational
complexity III: Higher type recurrence and elementary complexity",
Annals of Pure and Applied Logic 96 (1999) 209-229, DOI
`10.1016/S0168-0072(98)00040-2`, section 2.1. The constructor-summand
derivation adopts the data-system layer of N. Danner, J. S. Royer,
"Ramified structural recursion and corecursion", 2012, arXiv `1201.4567`.

## Tags

ramified recurrence, multi-sorted signature, algebraic signature,
data types a la carte, constructor
-/

namespace GebLean.Ramified

variable {S : Type}

/-- A multi-sorted algebraic signature: a type of operations, each with a
sorted arity (the list of sorts of its arguments) and a result sort.
Novel packaging of the free-algebra conventions of Leivant III section
2.1 over an explicit sort type `S`. -/
structure SortedSig (S : Type) where
  /-- The type of operations. -/
  Op : Type
  /-- The sorted arity of each operation: the sorts of its arguments. -/
  arity : Op → List S
  /-- The result sort of each operation. -/
  result : Op → S

/-- The sum of two signatures over the same sorts: operations are the
disjoint union of the summands' operations, with arities and result sorts
inherited by cases. The data-types-a-la-carte assembly of pluggable
summands (novel packaging). -/
def SortedSig.sum (F G : SortedSig S) : SortedSig S where
  Op := F.Op ⊕ G.Op
  arity := Sum.elim F.arity G.arity
  result := Sum.elim F.result G.result

/-- The constructor summand derived from a free-algebra signature `A`
(shapes = operations, positions = arities), one copy per object sort: for
each object sort `s` (a sort satisfying `IsObj`) and constructor label
`b`, an operation of arity `List.replicate (A.ar b) s` and result `s`.
Novel packaging adopting the data-system layer of Danner and Royer (arXiv
`1201.4567`); every object sort denotes a copy of the algebra's carrier
(Leivant III section 2.7). -/
def constructorSig (A : AlgSig) (IsObj : S → Prop) : SortedSig S where
  Op := { s : S // IsObj s } × A.B
  arity op := List.replicate (A.ar op.2) op.1.val
  result op := op.1.val

end GebLean.Ramified
