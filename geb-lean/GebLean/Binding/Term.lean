import GebLean.Binding.Signature

/-!
# The term type of a binder-substitution kit

The term layer of an indexed binder-substitution kit (decision 8): terms with
binders over a `BinderSig`, at a context and sort, realized as the free monad
of the signature's endofunctor over a diagonal variable family. Unlike the
existing per-context `Tm` idiom (`GebLean/Ramified/Term.lean:107,:113`),
where the context is a parameter and the leaf object is the per-context
`varOver Γ`, here the context is part of the index, so the leaf object must
be a single `Ctx Ty × Ty`-indexed family, taken over the total space of all
contexts and their positions, whose fiber over `(Γ, s)` is `Var Γ s`: a
per-context leaf object would place an operation's binder arguments — at the
extended index `(Γ ++ Ξ, t)` — in a different free monad and break the
single-`PolyFix` structure (research note section 4).

## Main definitions

* `varOver` — the diagonal variable family: total space `Σ Γ, Fin Γ.length`,
  fibered over `Ctx Ty × Ty` by pairing a context with the sort at its
  indicated position.
* `Tm` — terms with binders over `S` at context `Γ` and sort `s`: the free
  monad of `S.polyEndo` at `varOver`.
* `Tm.var` — a variable term (the free monad's unit at a variable's leaf).
* `Tm.op` — an operation applied to a tuple of argument terms, each in the
  ambient context extended by that argument's bound sorts.

## References

The binder-signature and context-extension conventions follow G. Allais,
R. Atkey, J. Chapman, C. McBride, and J. McKinna, "A type and scope safe
universe of syntaxes with binding: their semantics and proofs", Proceedings
of the ACM on Programming Languages 2 (ICFP), 2018,
DOI `10.1145/3236785`. Background and the diagonal-leaf rationale are
detailed in the research note,
`docs/superpowers/notes/2026-07-04-binder-substitution-research.md`, section
4.
-/

namespace GebLean.Binding

open CategoryTheory

universe u

variable {Ty : Type u}

/-- The diagonal variable family: total space `Σ Γ, Fin Γ.length`, with fiber
over `(Γ, s)` equal to `Var Γ s`. The context is part of the index (binders
shift it), so the leaf object cannot depend on a fixed `Γ`. -/
def varOver : Over (Ctx Ty × Ty) :=
  Over.mk (fun p : (Σ Γ : Ctx Ty, Fin Γ.length) => (p.1, p.1.get p.2))

/-- Terms with binders over `S` at context `Γ` and sort `s`: the free monad of
`S.polyEndo` over the diagonal variable family, a single `PolyFix` over
`Ctx Ty × Ty` (decision 8). -/
def Tm (S : BinderSig Ty) (Γ : Ctx Ty) (s : Ty) : Type u :=
  PolyFreeM varOver S.polyEndo (Γ, s)

/-- A variable term (the free monad's unit at the variable's leaf). -/
def Tm.var {S : BinderSig Ty} {Γ : Ctx Ty} {s : Ty} (x : Var Γ s) : Tm S Γ s :=
  polyFreeMPure varOver S.polyEndo ⟨⟨Γ, x.1⟩, congrArg (Prod.mk Γ) x.2⟩

/-- An operation applied to a tuple of argument terms, each in the ambient
context extended by that argument's bound sorts. The direction type of
`S.polyEndo` is `ULift`-lifted (`BinderSig.polyEndo`), so the argument tuple's
bare `Fin` index is bridged to it via `ULift.down`. -/
def Tm.op {S : BinderSig Ty} {Γ : Ctx Ty} (o : S.Op)
    (args : ∀ j : Fin (S.args o).length,
      Tm S (Γ ++ ((S.args o).get j).1) ((S.args o).get j).2) :
    Tm S Γ (S.result o) :=
  PolyFix.mk (Γ, S.result o) (Sum.inr ⟨o, rfl⟩) (fun e => args e.down)

end GebLean.Binding
