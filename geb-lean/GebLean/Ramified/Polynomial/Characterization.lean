import GebLean.Ramified.Polynomial.Collapse

/-!
# The elementary characterization on the primed stack

The primed mirror of `GebLean/Ramified/Characterization.lean`: the denotational
form of Leivant III's Theorem 14, items (1)-(2) (section 6.1, p. 227), stated
over the first-order syntactic category `SynCatFO'` of the higher-type ramified
system built on the vendored `SlicePFunctor` stack.

Both arms transfer across the restriction equivalence
`synCatFOSliceEquiv : SynCatFO' ≌ SynCatFO`
(`GebLean/Ramified/Polynomial/Collapse.lean`), so neither the elementary
definability argument nor the soundness argument is redone: the primed
soundness functor `collapseFunctor'` is the composite of that equivalence's
functor with the legacy `collapseFunctor`, faithful as a composite of faithful
functors, and `ramified_definability'` reads the legacy witnesses back through
the equivalence's fully faithful preimage.

The object identifications are `ObjCtx.toObjCtx'`, the objectwise preimage of
an object-sort context under the sort bridge `rTypeSliceEquiv`: its underlying
context maps onto the original (`ObjCtx.toObjCtx'_map`), so the image of its
lift under the equivalence is the legacy lift
(`synCatFOSliceEquiv_obj_toSynCatFO'`), and it carries the base-sort context to
the primed base-sort context (`oCtx_toObjCtx'`). The arity bookkeeping is
`arityCongr` throughout, with `arityCongr_trans`
(`GebLean/Ramified/Characterization.lean`) collapsing stacked congruences.

## Main definitions

* `ObjCtx.toObjCtx'` — the objectwise preimage of an object-sort context under
  the sort bridge.
* `collapseFunctor'` — the primed soundness functor
  `SynCatFO' ⥤ LawvereERCat`.
* `collapseKFunctor'` — the primed K-valued soundness functor
  `SynCatFO' ⥤ LawvereKSimDCat 2`.

## Main statements

* `ObjCtx.toObjCtx'_map`, `synCatFOSliceEquiv_obj_toSynCatFO'`,
  `oCtx_toObjCtx'`, `synCatFOSliceEquiv_obj_oCtx'` — the object
  identifications across the restriction equivalence.
* `collapseFunctor'.Faithful`, `collapseKFunctor'.Faithful` — the two primed
  soundness functors are faithful.
* `ramified_definability'` — every morphism of `LawvereERCat` has a primed
  object-sort context and a `SynCatFO'` morphism whose primed collapse
  denotation is the morphism's interpretation.
* `ramified_definability_kSim'` — the same over `LawvereKSimDCat 2`, with the
  `K^sim` interpretation.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`. The characterization is
Theorem 14, section 6.1; the definability direction is item (1) ⇒ (2).

Tourlakis 2018, *Topics in PR Complexity*, Corollary 0.1.0.44 at `n = 2`: the
inclusion supplying the equivalence `erKSimEquiv` along which the K-valued arm
is stated.

## Tags

ramified recurrence, elementary recurrence, characterization, Lawvere theory,
object sort, syntactic category, definability, slice category, W-type
-/

namespace GebLean.Ramified.Polynomial

open CategoryTheory GebLean.Ramified GebLean.Ramified.Definability

/-- The objectwise preimage of an object-sort context under the sort bridge:
each sort is read back by `rTypeSliceEquiv.symm`, its object-sort property
transported by `rTypeSliceEquiv_isObj`. -/
def _root_.GebLean.Ramified.Definability.ObjCtx.toObjCtx' {n : ℕ} (Γ : ObjCtx n) :
    ObjCtx' n :=
  fun i => ⟨rTypeSliceEquiv.symm (Γ i).val, by
    rw [rTypeSliceEquiv_isObj, Equiv.apply_symm_apply]
    exact (Γ i).2⟩

/-- The underlying context of the objectwise preimage maps onto the original
underlying context. -/
theorem _root_.GebLean.Ramified.Definability.ObjCtx.toObjCtx'_map {n : ℕ} (Γ : ObjCtx n) :
    Γ.toObjCtx'.toCtx.map rTypeSliceEquiv = Γ.toCtx := by
  simp only [ObjCtx'.toCtx, ObjCtx.toCtx, ObjCtx.toObjCtx', List.map_ofFn]
  exact congrArg List.ofFn (funext fun i => rTypeSliceEquiv.apply_symm_apply _)

/-- The image of the lift of the objectwise preimage is the legacy lift. -/
theorem synCatFOSliceEquiv_obj_toSynCatFO' {n : ℕ} (Γ : ObjCtx n) :
    synCatFOSliceEquiv.functor.obj Γ.toObjCtx'.toSynCatFO' = Γ.toSynCatFO :=
  ObjectProperty.FullSubcategory.ext Γ.toObjCtx'_map

/-- The objectwise preimage of the base-sort context is the primed base-sort
context, by `rTypeSliceEquiv_o` read backward. -/
theorem oCtx_toObjCtx' (m : ℕ) : (oCtx m).toObjCtx' = oCtx' m := by
  funext i
  exact Subtype.ext ((Equiv.symm_apply_eq rTypeSliceEquiv).mpr rTypeSliceEquiv_o.symm)

/-- The image of the lift of the primed base-sort context is the legacy lift of
the base-sort context. -/
theorem synCatFOSliceEquiv_obj_oCtx' (m : ℕ) :
    synCatFOSliceEquiv.functor.obj (oCtx' m).toSynCatFO' = (oCtx m).toSynCatFO := by
  rw [← oCtx_toObjCtx']
  exact synCatFOSliceEquiv_obj_toSynCatFO' (oCtx m)

/-- The primed soundness functor (Leivant III Theorem 14, the arm (1) ⇒ (4),
section 6.1): the restriction equivalence `synCatFOSliceEquiv` followed by the
legacy soundness functor `collapseFunctor`. -/
def collapseFunctor' : SynCatFO' ⥤ LawvereERCat :=
  synCatFOSliceEquiv.functor ⋙ collapseFunctor

/-- The primed soundness functor is faithful: a composite of the functor of an
equivalence with the faithful `collapseFunctor`. -/
instance : collapseFunctor'.Faithful :=
  inferInstanceAs (synCatFOSliceEquiv.functor ⋙ collapseFunctor).Faithful

/-- The primed K-valued soundness functor: the primed soundness functor
followed by the encoding `erToKFunctor` of the equivalence
`erKSimEquiv : LawvereERCat ≌ LawvereKSimDCat 2`. -/
def collapseKFunctor' : SynCatFO' ⥤ LawvereKSimDCat 2 :=
  collapseFunctor' ⋙ erToKFunctor

/-- The primed K-valued soundness functor is faithful: a composite of the
faithful `collapseFunctor'` with `erToKFunctor`, faithful as the functor of the
equivalence `erKSimEquiv`. -/
instance : collapseKFunctor'.Faithful :=
  inferInstanceAs (collapseFunctor' ⋙ erToKFunctor).Faithful

/-- The primed collapse denotation of the fully faithful preimage of a legacy
morphism conjugated by object identifications is the legacy collapse
denotation, read across the induced arity identifications. The preimage of
`synCatFOSliceEquiv.functor` is the conjugation of the inverse functor's action
by the equivalence's unit, so this is `collapseDenotation_sliceEquiv` read
backward. -/
theorem collapseDenotation'_preimage {Γ' Δ' : SynCatFO'} {Γ Δ : SynCatFO}
    (hΓ : synCatFOSliceEquiv.functor.obj Γ' = Γ)
    (hΔ : synCatFOSliceEquiv.functor.obj Δ' = Δ) (g : Γ ⟶ Δ) :
    collapseDenotation' (synCatFOSliceEquiv.fullyFaithfulFunctor.preimage
        (eqToHom hΓ ≫ g ≫ eqToHom hΔ.symm))
      = arityCongr ((objLen_functor_obj Γ').trans (congrArg objLen hΓ)).symm
          ((objLen_functor_obj Δ').trans (congrArg objLen hΔ)).symm
          (collapseDenotation g) := by
  subst hΓ
  subst hΔ
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  funext v j
  have h := congrFun (congrFun (collapseDenotation_sliceEquiv
      (synCatFOSliceEquiv.fullyFaithfulFunctor.preimage g))
      (fun i => v (Fin.cast (objLen_functor_obj Γ').symm i)))
      (Fin.cast (objLen_functor_obj Δ') j)
  rw [Functor.FullyFaithful.map_preimage] at h
  exact h.symm

/-- Definability on the primed stack, quantified over primed object-sort input
contexts (Leivant III Theorem 14 (1) ⇒ (2), section 6.1, DOI
`10.1016/S0168-0072(98)00040-2`): every morphism of `LawvereERCat` has a primed
object-sort context and a `SynCatFO'` morphism whose primed collapse
denotation, read along the arity identifications `objLen'_toSynCatFO'`, is the
morphism's interpretation. As on the legacy stack, the quantification ranges
over all object-sort contexts, beyond the tower sorts, and the statement is an
existential, not fullness of `collapseFunctor'`. The witnesses are those of the
legacy `ramified_definability`, read back through the fully faithful preimage
of the restriction equivalence at the object identifications
`synCatFOSliceEquiv_obj_toSynCatFO'` and `synCatFOSliceEquiv_obj_oCtx'`. -/
theorem ramified_definability' {n m : LawvereERCat} (f : n ⟶ m) :
    ∃ (Γ' : ObjCtx' n) (g' : Γ'.toSynCatFO' ⟶ (oCtx' m).toSynCatFO'),
      collapseDenotation' g'
        = arityCongr (objLen'_toSynCatFO' Γ').symm (objLen'_toSynCatFO' (oCtx' m)).symm
            f.interp := by
  obtain ⟨Γ, g, hg⟩ := ramified_definability f
  refine ⟨Γ.toObjCtx', synCatFOSliceEquiv.fullyFaithfulFunctor.preimage
    (eqToHom (synCatFOSliceEquiv_obj_toSynCatFO' Γ) ≫ g
      ≫ eqToHom (synCatFOSliceEquiv_obj_oCtx' m).symm), ?_⟩
  rw [collapseDenotation'_preimage (hΔ := synCatFOSliceEquiv_obj_oCtx' m), hg,
    arityCongr_trans]

/-- Definability on the primed stack transferred to the depth-2 `K^sim`
Lawvere theory across `erKSimEquiv` (Leivant III Theorem 14 (1) ⇒ (2), section
6.1, DOI `10.1016/S0168-0072(98)00040-2`, with Tourlakis 2018 Corollary
0.1.0.44 at `n = 2` supplying the equivalence): every morphism of
`LawvereKSimDCat 2` has a primed object-sort context and a `SynCatFO'` morphism
whose primed collapse denotation, read along the arity identifications
`objLen'_toSynCatFO'`, is the morphism's `K^sim` interpretation. As on the ER
side, the statement is an existential, not fullness of `collapseKFunctor'`. The
witnesses are those of `ramified_definability'` at `kToERFunctor.map f`, whose
ER interpretation is the `K^sim` interpretation of `f` by
`kToERFunctor_map_interp`. -/
theorem ramified_definability_kSim' {n m : LawvereKSimDCat 2} (f : n ⟶ m) :
    ∃ (Γ' : ObjCtx' n) (g' : Γ'.toSynCatFO' ⟶ (oCtx' m).toSynCatFO'),
      collapseDenotation' g'
        = arityCongr (objLen'_toSynCatFO' Γ').symm (objLen'_toSynCatFO' (oCtx' m)).symm
            f.hom.interp := by
  obtain ⟨Γ', g', hg⟩ := ramified_definability' (kToERFunctor.map f)
  exact ⟨Γ', g', hg.trans (congrArg (arityCongr _ _) (kToERFunctor_map_interp f))⟩

end GebLean.Ramified.Polynomial
