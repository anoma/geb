import GebLean
import GebLean.Ramified.Polynomial.HigherOrderEquiv
import GebLeanTests.Ramified.Polynomial.Ident

/-!
# Tests for the primed-to-legacy higher-order category equivalence

Executable checks over the `1 + X` word algebra `natAlgSig`
(`GebLeanTests.Ramified.Polynomial.IdentTest.A`). The object map of
`rmRecCatSliceEquiv` is checked on the one-sort primed context `[o]`, and its
morphism map on `identHom'` of the constant-zero identifier `idZero'` and of the
variable identifier `idVar' : RIdent' A [o] o`
(`GebLeanTests/Ramified/Polynomial/Ident.lean`), which it carries to the legacy
`identHom` of the bridge image of each. The two identifiers differ in their
context: `idZero'` degenerates the domain-side `unmapEnv` reindexing, `idVar'`
exercises it.
-/

namespace GebLeanTests.Ramified.Polynomial.HigherOrderEquivTest

open GebLean.Ramified GebLean.Ramified.Polynomial CategoryTheory
open GebLeanTests.Ramified.Polynomial.IdentTest (A idZero' idVar')

-- The object map carries the primed one-sort context `[o]` to the legacy `[o]`.
example : (rmRecCatSliceEquiv A).functor.obj [RType'.o] = [RType.o] := by
  change List.map rTypeSliceEquiv [RType'.o] = [RType.o]
  rw [List.map_cons, List.map_nil, rTypeSliceEquiv_o]

/-- The morphism map carries a primed identifier morphism to the legacy
identifier morphism of the identifier's bridge image, at any context. -/
private theorem map_identHom' {Γ' : List RType'} {τ' : RType'} (f : RIdent' A Γ' τ') :
    (rmRecCatSliceEquiv A).functor.map (identHom' f)
      = identHom (identSliceEquiv f) := by
  refine Hom.ext_eval (fun ρ => funext fun i => ?_)
  refine Fin.cases ?_ (fun k => k.elim0) i
  refine Eq.trans (congrFun ((higherOrderPresEquiv A).mapHom_eval
    ((synCatSliceEquiv (higherOrder' A)).functor.map (identHom' f)) ρ) _) ?_
  have hsyn : Hom.eval ((synCatSliceEquiv (higherOrder' A)).functor.map (identHom' f))
        ((higherOrderPresEquiv A).unmapEnv ρ)
      = Hom'.eval (identHom' f) ((higherOrderPresEquiv A).unmapEnv ρ) :=
    funext fun _ => tmSliceEquiv_eval _ _ _
  refine Eq.trans (congrFun (congrArg (higherOrderPresEquiv A).mapEnv hsyn) _) ?_
  refine Eq.trans ?_ (identHom_eval (identSliceEquiv f) ρ).symm
  have hE : (higherOrderPresEquiv A).mapEnv ((higherOrderPresEquiv A).unmapEnv ρ) = ρ :=
    (higherOrderPresEquiv A).mapEnv_unmapEnv ρ
  conv_rhs => rw [← hE]
  exact Eq.trans (cast_eq _ _)
    (identSliceEquiv_interp f ((higherOrderPresEquiv A).unmapEnv ρ)).symm

-- The morphism map at the constant-zero identifier `idZero'`, whose context is
-- empty.
example :
    (rmRecCatSliceEquiv A).functor.map (identHom' idZero')
      = identHom (identSliceEquiv idZero') :=
  map_identHom' idZero'

-- The morphism map at the variable identifier `idVar' : RIdent' A [o] o`, whose
-- nonempty context exercises the domain-side `unmapEnv` reindexing that
-- degenerates at `idZero'`.
example :
    (rmRecCatSliceEquiv A).functor.map (identHom' idVar')
      = identHom (identSliceEquiv idVar') :=
  map_identHom' idVar'

end GebLeanTests.Ramified.Polynomial.HigherOrderEquivTest
