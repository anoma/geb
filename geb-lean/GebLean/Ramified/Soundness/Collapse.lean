import GebLean.Ramified.Definability.Top
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Ramified recurrence: the collapse packaging

The first-order syntactic category `SynCatFO` and its standard-model denotation
`collapseDenotation`, packaging the Phase 5 definability data
(`GebLean/Ramified/Definability/Top.lean`) as functorial input for the
soundness functor `collapseFunctor : SynCatFO ⥤ LawvereERCat`.

`SynCatFO` is the full subcategory of `RMRecCat natAlgSig` on the contexts all
of whose sorts are object sorts (`isObjCtx`). `SynCatFO.toObjCtx` bridges such an
object to the length-indexed object-sort context `ObjCtx` of Phase 5, and
`objLen` reads its length. `collapseDenotation` reads a full-subcategory morphism
through that bridge into `ramifiedDenotation`, the numeric denotation of a
morphism between object-sort contexts. The functoriality laws
`collapseDenotation_id` and `collapseDenotation_comp` — the identity and
composition laws of standard-model evaluation — are the `map_id` / `map_comp`
inputs consumed by the soundness functor.

## Main definitions

* `isObjCtx` — the object property selecting the contexts of `RMRecCat natAlgSig`
  all of whose sorts are object sorts.
* `SynCatFO` — the full subcategory of `RMRecCat natAlgSig` on `isObjCtx`.
* `SynCatFO.toObjCtx` — the bridge from a `SynCatFO` object to the Phase 5
  `ObjCtx`.
* `objLen` — the length of a `SynCatFO` object.
* `collapseDenotation` — the numeric denotation of a `SynCatFO` morphism, read
  through `ramifiedDenotation`.

## Main statements

* `collapseDenotation_id` — the collapse denotation of an identity is the
  identity.
* `collapseDenotation_comp` — the collapse denotation of a composite is the
  composition of the collapse denotations.

## Implementation notes

Novel packaging of the section 6.1 soundness statement. The bridge from a
full-subcategory object (a context with an object-sort proof) to `ObjCtx`
threads the per-position object-sort proof; the underlying context of the bridge
equals the original object (`SynCatFO.toObjCtx_toCtx`), the equality along which
`collapseDenotation` transports the full-subcategory morphism into
`ramifiedDenotation`'s domain.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`. The soundness direction is
Theorem 14 (1) ⇒ (4), section 6.1.

## Tags

ramified recurrence, elementary recurrence, soundness, Lawvere theory, object
sort, syntactic category, full subcategory
-/

namespace GebLean.Ramified

open CategoryTheory
open GebLean.Ramified.Definability

/-- The object property selecting the contexts of `RMRecCat natAlgSig` all of
whose sorts are object sorts. -/
def isObjCtx : ObjectProperty (RMRecCat natAlgSig) :=
  fun Γ => ∀ i : Fin Γ.length, (Γ.get i).IsObj

/-- The full subcategory of `RMRecCat natAlgSig` on the object-sort contexts. -/
abbrev SynCatFO : Type := isObjCtx.FullSubcategory

/-- The bridge from a `SynCatFO` object to the Phase 5 object-sort context: the
length-indexed family of object sorts read off the underlying context, each
tagged by its object-sort proof. -/
def SynCatFO.toObjCtx (Γ : SynCatFO) : Σ n, ObjCtx n :=
  ⟨Γ.obj.length, fun i => ⟨Γ.obj.get i, Γ.property i⟩⟩

/-- The length of a `SynCatFO` object. -/
def objLen (Γ : SynCatFO) : ℕ := Γ.toObjCtx.1

/-- The underlying context of the bridge equals the original object. -/
theorem SynCatFO.toObjCtx_toCtx (Γ : SynCatFO) : (Γ.toObjCtx.2).toCtx = Γ.obj := by
  simp only [SynCatFO.toObjCtx, ObjCtx.toCtx]
  exact List.ofFn_get Γ.obj

/-- The bridge transport of a `SynCatFO` morphism into a morphism between the
underlying contexts of the bridged object-sort contexts. -/
def collapseHom {Γ Δ : SynCatFO} (g : Γ ⟶ Δ) :
    Hom (higherOrder natAlgSig) (interpQuotRel (higherOrder natAlgSig))
      (Γ.toObjCtx.2).toCtx (Δ.toObjCtx.2).toCtx :=
  cast (by rw [Γ.toObjCtx_toCtx, Δ.toObjCtx_toCtx]; rfl) g.hom

/-- The numeric denotation of a `SynCatFO` morphism: the Phase 5
`ramifiedDenotation` read through the bridge `SynCatFO.toObjCtx`. -/
def collapseDenotation {Γ Δ : SynCatFO} (g : Γ ⟶ Δ) :
    (Fin (objLen Γ) → ℕ) → (Fin (objLen Δ) → ℕ) :=
  ramifiedDenotation (collapseHom g)

end GebLean.Ramified
