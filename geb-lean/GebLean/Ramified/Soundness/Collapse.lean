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

/-- The carrier-copy transport round trip: reading an object-sort value as a
natural and transporting it back recovers the value. -/
theorem objFromNat_objToNat {s : RType} (hs : s.IsObj)
    (x : RType.interp (FreeAlg natAlgSig) s) : objFromNat hs (objToNat hs x) = x := by
  unfold objFromNat objToNat
  rw [natToFreeAlg_freeAlgToNat, cast_cast, cast_eq]

/-- Evaluation of an identity morphism is the identity on environments. -/
theorem Hom.eval_id {P : Presentation} {Γ : Ctx P.S}
    (ρ : (standardModel P).Env Γ) :
    (Hom.id P (interpQuotRel P) Γ).eval ρ = ρ := by
  funext i
  simp only [Hom.id, Hom.eval_mk, HomTuple.eval, HomTuple.id, Tm.eval_var]

/-- The numeric denotation at a value and codomain position. -/
theorem ramifiedDenotation_apply {n m : ℕ} {Γ : ObjCtx n} {Δ : ObjCtx m}
    (g : Hom (higherOrder natAlgSig) (interpQuotRel (higherOrder natAlgSig))
      Γ.toCtx Δ.toCtx) (v : Fin n → ℕ) (j : Fin m) :
    ramifiedDenotation g v j
      = objToNat (Δ.toCtx_get_isObj (Fin.cast (Δ.toCtx_length).symm j))
          (g.eval (ramifiedEnv Γ v) (Fin.cast (Δ.toCtx_length).symm j)) :=
  rfl

/-- The numeric denotation of an identity morphism is the identity. -/
theorem ramifiedDenotation_id {n : ℕ} (Γ : ObjCtx n) :
    ramifiedDenotation
      (Hom.id (higherOrder natAlgSig) (interpQuotRel (higherOrder natAlgSig)) Γ.toCtx)
      = id := by
  funext v j
  rw [ramifiedDenotation_apply, Hom.eval_id]
  exact objToNat_objFromNat _ _

/-- The numeric denotation of a composite is the composition of the numeric
denotations (the composition law of standard-model evaluation). -/
theorem ramifiedDenotation_comp {n m k : ℕ}
    {Γ : ObjCtx n} {Δ : ObjCtx m} {Θ : ObjCtx k}
    (g : Hom (higherOrder natAlgSig) (interpQuotRel (higherOrder natAlgSig))
      Γ.toCtx Δ.toCtx)
    (h : Hom (higherOrder natAlgSig) (interpQuotRel (higherOrder natAlgSig))
      Δ.toCtx Θ.toCtx) :
    ramifiedDenotation (g.comp h) = ramifiedDenotation h ∘ ramifiedDenotation g := by
  funext v j
  have hmid : ramifiedEnv Δ (ramifiedDenotation g v) = g.eval (ramifiedEnv Γ v) := by
    funext i
    change objFromNat (Δ.toCtx_get_isObj i)
        (objToNat (Δ.toCtx_get_isObj i) (g.eval (ramifiedEnv Γ v) i))
        = g.eval (ramifiedEnv Γ v) i
    exact objFromNat_objToNat _ _
  change ramifiedDenotation (g.comp h) v j = ramifiedDenotation h (ramifiedDenotation g v) j
  rw [ramifiedDenotation_apply, ramifiedDenotation_apply, Hom.eval_comp, hmid]

/-- The bridge transport of an identity morphism is the identity morphism. -/
theorem cast_hom_id {P : Presentation} {r : QuotRel P.sig} {A B : Ctx P.S}
    (hAB : A = B) (h : Hom P r A A = Hom P r B B) :
    cast h (Hom.id P r A) = Hom.id P r B := by
  subst hAB
  simp only [cast_eq]

/-- The bridge transport of a composite is the composite of the bridge
transports. -/
theorem cast_hom_comp {P : Presentation} {r : QuotRel P.sig}
    {A A' B B' C C' : Ctx P.S} (hA : A = A') (hB : B = B') (hC : C = C')
    (f : Hom P r A B) (g : Hom P r B C)
    (hac : Hom P r A C = Hom P r A' C') (hab : Hom P r A B = Hom P r A' B')
    (hbc : Hom P r B C = Hom P r B' C') :
    cast hac (Hom.comp f g) = Hom.comp (cast hab f) (cast hbc g) := by
  subst hA
  subst hB
  subst hC
  simp only [cast_eq]

/-- The bridge transport of an identity `SynCatFO` morphism is the identity. -/
theorem collapseHom_id (Γ : SynCatFO) :
    collapseHom (𝟙 Γ)
      = Hom.id (higherOrder natAlgSig) (interpQuotRel (higherOrder natAlgSig))
          (Γ.toObjCtx.2).toCtx := by
  unfold collapseHom
  rw [CategoryTheory.ObjectProperty.FullSubcategory.id_hom]
  exact cast_hom_id Γ.toObjCtx_toCtx.symm _

/-- The bridge transport of a composite `SynCatFO` morphism is the composite. -/
theorem collapseHom_comp {Γ Δ Θ : SynCatFO} (g : Γ ⟶ Δ) (h : Δ ⟶ Θ) :
    collapseHom (g ≫ h) = (collapseHom g).comp (collapseHom h) := by
  unfold collapseHom
  rw [CategoryTheory.ObjectProperty.FullSubcategory.comp_hom]
  exact cast_hom_comp Γ.toObjCtx_toCtx.symm Δ.toObjCtx_toCtx.symm Θ.toObjCtx_toCtx.symm
    g.hom h.hom _ _ _

/-- The collapse denotation of an identity morphism is the identity. -/
theorem collapseDenotation_id (Γ : SynCatFO) : collapseDenotation (𝟙 Γ) = id := by
  unfold collapseDenotation
  rw [collapseHom_id]
  exact ramifiedDenotation_id Γ.toObjCtx.2

/-- The collapse denotation of a composite is the composition of the collapse
denotations. -/
theorem collapseDenotation_comp {Γ Δ Θ : SynCatFO} (g : Γ ⟶ Δ) (h : Δ ⟶ Θ) :
    collapseDenotation (g ≫ h) = collapseDenotation h ∘ collapseDenotation g := by
  unfold collapseDenotation
  rw [collapseHom_comp]
  exact ramifiedDenotation_comp (collapseHom g) (collapseHom h)

end GebLean.Ramified
