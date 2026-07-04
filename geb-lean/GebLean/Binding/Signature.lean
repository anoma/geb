import GebLean.PolyAlg

/-!
# Binding signatures

The signature layer of an indexed binder-substitution kit: a context (a list
of sorts), a de Bruijn variable position into a context, and a signature of
operations with binding presented as a `Ctx Ty × Ty`-indexed polynomial
endofunctor (decision 8). An operation's argument `(Ξ, t)` is a subterm of
sort `t` in the ambient context extended by the bound sorts `Ξ`
(append-at-end convention), following the context-shifting-direction pattern
of `GebLean.Ramified.HigherOrder.identEndo`.

## Main definitions

* `Ctx` — a context: a finite list of sorts.
* `Var` — a de Bruijn variable position into a context, indexed by sort.
* `BinderSig` — a signature of operations with binding.
* `BinderSig.polyEndo` — the context-and-sort-indexed signature endofunctor
  of a `BinderSig`.

## Main statements

* `BinderSig.polyEndo_index` — the positions of `S.polyEndo` at `(Γ, s)` are
  the operations with result sort `s`.
* `BinderSig.polyEndo_target` — the direction at argument `j = (Ξ, t)` of an
  operation targets the extended index `(Γ ++ Ξ, t)`.

## Implementation notes

`BinderSig.polyEndo`'s direction type at a position is `ULift.{u} (Fin n)`
rather than `Fin n`: `Ty : Type u` is universe-polymorphic, and the
signature endofunctor lives in `Over (Ctx Ty × Ty) : Type u`, so its
directions must be lifted into `Type u` to match, following the same
`ULift` device as `GebLean.polyNatDirs`.

## References

The binder-signature and context-extension conventions follow G. Allais,
R. Atkey, J. Chapman, C. McBride, and J. McKinna, "A type and scope safe
universe of syntaxes with binding: their semantics and proofs", Proceedings
of the ACM on Programming Languages 2 (ICFP), 2018,
DOI `10.1145/3236785`.
-/

namespace GebLean.Binding

open CategoryTheory

universe u

variable {Ty : Type u}

/-- A context: a finite list of sorts, read as a family of typed positions. -/
abbrev Ctx (Ty : Type u) : Type u := List Ty

/-- A variable: a `Type`-valued de Bruijn position into the context `Γ` whose
sort is `s`. Not the `Prop` membership `s ∈ Γ`, which is proof-irrelevant and
would collapse distinct occurrences of the same sort into a single witness.
First-order data, exempt from decision 8. -/
def Var (Γ : Ctx Ty) (s : Ty) : Type := { i : Fin Γ.length // Γ.get i = s }

/-- A signature of operations with binding: each operation has a result sort
and a list of arguments; an argument `(Ξ, t)` is a subterm of sort `t` in the
ambient context extended by the bound sorts `Ξ` (append-at-end convention). -/
structure BinderSig (Ty : Type u) where
  /-- The operations of the signature. -/
  Op : Type u
  /-- The result sort of an operation. -/
  result : Op → Ty
  /-- The arguments of an operation, each a pair of bound sorts and a
  result sort for the corresponding subterm. -/
  args : Op → List (Ctx Ty × Ty)

/-- The context-and-sort-indexed signature endofunctor of a `BinderSig`
(decision 8; follows the context-shifting-direction pattern of
`GebLean.Ramified.HigherOrder.identEndo`, with the append-at-end context
extension its own). At output index `(Γ, s)`, the positions are the
operations with result `s`; the direction at argument `j = (Ξ, t)` targets
the extended index `(Γ ++ Ξ, t)`. -/
def BinderSig.polyEndo (S : BinderSig Ty) : PolyEndo (Ctx Ty × Ty) :=
  fun idx => ccrObjMk fun o : { o : S.Op // S.result o = idx.2 } =>
    Over.mk fun j : ULift.{u} (Fin (S.args o.val).length) =>
      (idx.1 ++ ((S.args o.val).get j.down).1, ((S.args o.val).get j.down).2)

/-- The positions of `S.polyEndo` at index `(Γ, s)` are the operations of `S`
with result sort `s`. -/
@[simp] theorem BinderSig.polyEndo_index (S : BinderSig Ty) (Γ : Ctx Ty) (s : Ty) :
    ccrIndex (S.polyEndo (Γ, s)) = { o : S.Op // S.result o = s } := rfl

/-- The direction at argument `j` of a position `o` of `S.polyEndo` at
index `(Γ, s)` targets the extended index `(Γ ++ Ξ_j, t_j)`, where
`(Ξ_j, t_j) = (S.args o.val).get j.down`. Directions are `ULift`-lifted
`Fin`-values so that the direction type lives in the same universe as the
sort type `Ty`, matching `GebLean.polyNatDirs`. -/
@[simp] theorem BinderSig.polyEndo_target (S : BinderSig Ty) (Γ : Ctx Ty) (s : Ty)
    (o : { o : S.Op // S.result o = s }) (j : ULift.{u} (Fin (S.args o.val).length)) :
    (ccrFamily (S.polyEndo (Γ, s)) o).hom j =
      (Γ ++ ((S.args o.val).get j.down).1, ((S.args o.val).get j.down).2) := rfl

end GebLean.Binding
