import GebLean.Binding.Substitution

/-!
# The simply-typed lambda calculus, as an acceptance test

The end-to-end instantiation of the indexed binder-substitution kit
(decision 8) at the simply-typed lambda calculus: a base type and function
types (`StlcTy`), the binder signature `stlcSig` of application and
abstraction, and the identity term `λx. x` (`stlcId`), built from the
generic `Tm`, `ren`, `sub`, and the environment helpers of Tasks 1-8. The
worked `example`s in `GebLeanTests.Binding.Stlc` exercise `var`, `ren`,
`sub`, `instantiate₁`, and each law of the substitution-lemma suite
(`sub_var`, `sub_id`, `ren_sub`, `sub_ren`, `sub_sub`) on `stlcId` and its
body. This is the kit's acceptance test, not a consumer API (design spec
section 3.8).

## Main definitions

* `StlcTy` — the simple types: a base type and the function-type former.
* `StlcOp` — the two operation families of `stlcSig`: application `app` and
  abstraction `lam`.
* `stlcSig` — the binder signature of the simply-typed lambda calculus.
* `stlcBody` — the bound variable, the body of `stlcId`.
* `stlcId` — the identity term `λx. x`.

## References

The binder signature, the append-at-end context-extension convention, and
the simply-typed lambda calculus as the running example follow G. Allais,
R. Atkey, J. Chapman, C. McBride, and J. McKinna, "A type and scope safe
universe of syntaxes with binding: their semantics and proofs", Proceedings
of the ACM on Programming Languages 2 (ICFP), 2018, DOI `10.1145/3236785`.
-/

namespace GebLean.Binding

/-- The simple types of the simply-typed lambda calculus: a single base
type and the function-type former. -/
inductive StlcTy : Type where
  /-- The base type. -/
  | base : StlcTy
  /-- The function type `a ⇒ b`. -/
  | arrow (a b : StlcTy) : StlcTy
  deriving DecidableEq, Repr

/-- The operations of `stlcSig`: application `app a b` (a function of sort
`a ⇒ b` and an argument of sort `a`, both non-binding) and abstraction
`lam a b` (a body of sort `b` binding a fresh variable of sort `a`). -/
inductive StlcOp : Type where
  /-- Application of a function of sort `a ⇒ b` to an argument of sort `a`. -/
  | app (a b : StlcTy) : StlcOp
  /-- Abstraction over a fresh variable of sort `a`, of a body of sort `b`. -/
  | lam (a b : StlcTy) : StlcOp
  deriving DecidableEq

/-- The binder signature of the simply-typed lambda calculus: application
`app a b`, with two non-binding arguments (the function, of sort `a ⇒ b`,
and the argument, of sort `a`) and result `b`; abstraction `lam a b`, with
one argument (the body, of sort `b`, binding a fresh `a`) and result
`a ⇒ b`. -/
def stlcSig : BinderSig StlcTy where
  Op := StlcOp
  result
    | .app _ b => b
    | .lam a b => StlcTy.arrow a b
  args
    | .app a b => [([], StlcTy.arrow a b), ([], a)]
    | .lam a b => [([a], b)]

/-- The bound variable: the sole argument of an abstraction `lam a a` is a
term of sort `a` in the context extended by the bound sort `a`; at the
empty ambient context this extended context is the singleton `[a]`, whose
unique position is the bound variable itself. -/
def stlcBody (a : StlcTy) : Tm stlcSig [a] a := Tm.var ⟨0, rfl⟩

/-- The identity term `λx. x`, at type `a ⇒ a`: an abstraction over `a`
whose sole argument is the bound variable `stlcBody`, in the extended
context `[] ++ [a] = [a]`. The single argument is read off by `Fin.cases`
on its index in the singleton argument list of `lam a a`, as in
`instantiate₁`'s recovery of the sort equality at a singleton suffix. -/
def stlcId (a : StlcTy) : Tm stlcSig [] (StlcTy.arrow a a) :=
  Tm.op (S := stlcSig) (Γ := []) (o := StlcOp.lam a a) (fun j => by
    cases j using Fin.cases with
    | zero => exact stlcBody a
    | succ i => exact i.elim0)

end GebLean.Binding
