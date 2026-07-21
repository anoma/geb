import GebLean.Ramified.Polynomial.SynCat

/-!
# The term-layer syntactic-category equivalence

An equivalence of categories between the primed syntactic category
`SynCat' P (interpQuotRel' P)` (`GebLean/Ramified/Polynomial/SynCat.lean`), built
on the slice free monad's term layer `Tm'`, and the legacy syntactic category
`SynCat P (interpQuotRel P)` (`GebLean/Ramified/SynCat.lean`), built on the
legacy term layer `Tm`. Both are quotiented by interpretative equality at the
standard model. The equivalence is the identity on objects (both carriers are
`Ctx P.S`) and, on morphisms, the componentwise application of the bridge
equivalence `tmSliceEquiv` (`GebLean/Ramified/Polynomial/Term.lean`); its inverse
applies `(tmSliceEquiv Γ s).symm` componentwise. Well-definedness on the
quotient is `tmSliceEquiv_rel`: `tmSliceEquiv` intertwines the two interpretative
setoids, a consequence of the evaluation-agreement lemma `tmSliceEquiv_eval`.

## Main definitions

* `synCatSliceFunctor` — the functor from the primed to the legacy syntactic
  category: identity on objects, componentwise `tmSliceEquiv` on morphisms.
* `synCatSliceInverse` — the inverse functor: componentwise
  `(tmSliceEquiv Γ s).symm` on morphisms.
* `synCatSliceEquiv` — the equivalence of categories, with unit and counit the
  identity isomorphisms.

## Main statements

* `tmSliceEquiv_rel` — the bridge equivalence intertwines the primed and legacy
  interpretative setoids.

## Implementation notes

`synCatSliceFunctor` and `synCatSliceInverse` lift `tmSliceEquiv` and its inverse
along the hom quotients by `Quotient.lift`; well-definedness is `tmSliceEquiv_rel`
in the two directions. The functor laws reduce componentwise: `map_id` by the
variable-naturality `tmSliceEquiv_var`, `map_comp` by the substitution-naturality
`tmSliceEquiv_subst`, each via `congrArg (Quotient.mk _)` on a `funext`. The
inverse's laws re-orient the same naturality lemmas through `Equiv.symm_apply_eq`
and the `Equiv` round trips. The unit and counit isomorphisms are `Iso.refl` at
every object (the functors fix objects); their naturality squares reduce to the
`Equiv` round trips `Equiv.symm_apply_apply` and `Equiv.apply_symm_apply` after
the identity morphisms cancel by `Tm'.var_subst` / `Tm'.subst_id` (respectively
`Tm.var_subst` / `Tm.subst_id`).

## References

The free multi-sorted Lawvere theory / term-clone conventions of the two
syntactic categories follow D. Leivant, "Ramified recurrence and computational
complexity III: Higher type recurrence and elementary complexity", Annals of
Pure and Applied Logic 96 (1999) 209-229, DOI
`10.1016/S0168-0072(98)00040-2`, section 2.1.

## Tags

ramified recurrence, syntactic category, equivalence of categories, term clone,
quotient category, free monad, slice category
-/

namespace GebLean.Ramified.Polynomial

open CategoryTheory GebLean.Ramified

/-- The bridge equivalence `tmSliceEquiv` intertwines the primed interpretative
setoid `interpSetoid'` with the legacy `interpSetoid`: two primed terms evaluate
equally at the standard model exactly when their `tmSliceEquiv` images do. Both
directions follow from the evaluation-agreement lemma `tmSliceEquiv_eval`. -/
theorem tmSliceEquiv_rel (P : Presentation) {Γ : Ctx P.S} {s : P.S}
    (t u : Tm' P.sig Γ s) :
    (interpSetoid' P Γ s) t u ↔
      (interpSetoid P Γ s) (tmSliceEquiv Γ s t) (tmSliceEquiv Γ s u) := by
  constructor
  · intro h ρ
    rw [tmSliceEquiv_eval, tmSliceEquiv_eval]
    exact h ρ
  · intro h ρ
    have hρ := h ρ
    rw [tmSliceEquiv_eval, tmSliceEquiv_eval] at hρ
    exact hρ

/-- The image of a primed hom under the equivalence's functor: componentwise
`tmSliceEquiv`, lifted along the hom quotient. Well-defined by the forward
direction of `tmSliceEquiv_rel`. Mirrors `foHomMap`
(`GebLean/Ramified/Polynomial/FirstOrder.lean`). -/
def synHomMap (P : Presentation) (Γ Δ : Ctx P.S)
    (f : Hom' P (interpQuotRel' P) Γ Δ) : Hom P (interpQuotRel P) Γ Δ :=
  Quotient.liftOn f (fun f' => Quotient.mk _ (fun i => tmSliceEquiv Γ (Δ.get i) (f' i)))
    (fun _ _ h => Quotient.sound (fun i => (tmSliceEquiv_rel P _ _).mp (h i)))

/-- The image of a legacy hom under the equivalence's inverse functor:
componentwise `(tmSliceEquiv Γ s).symm`, lifted along the hom quotient.
Well-defined by the backward direction of `tmSliceEquiv_rel` read at the inverse
images (the `Equiv` round trip cancels). -/
def synHomMapInv (P : Presentation) (Γ Δ : Ctx P.S)
    (f : Hom P (interpQuotRel P) Γ Δ) : Hom' P (interpQuotRel' P) Γ Δ :=
  Quotient.liftOn f (fun f' => Quotient.mk _ (fun i => (tmSliceEquiv Γ (Δ.get i)).symm (f' i)))
    (fun _ _ h => Quotient.sound (fun i => (tmSliceEquiv_rel P _ _).mpr (by
      simp only [Equiv.apply_symm_apply]
      exact h i)))

/-- The functor from the primed to the legacy syntactic category: the identity
on objects (contexts) and `synHomMap` on morphisms. The identity law reduces by
`tmSliceEquiv_var` (the identity tuple is the variable tuple) and the composition
law by `tmSliceEquiv_subst`, componentwise. -/
def synCatSliceFunctor (P : Presentation) :
    SynCat' P (interpQuotRel' P) ⥤ SynCat P (interpQuotRel P) where
  obj Γ := Γ
  map {Γ Δ} f := synHomMap P Γ Δ f
  map_id Γ := congrArg (Quotient.mk _) (funext fun i => tmSliceEquiv_var i)
  map_comp {Γ Δ E} f g := by
    induction f using Quotient.ind with
    | _ f' =>
    induction g using Quotient.ind with
    | _ g' => exact congrArg (Quotient.mk _) (funext fun i => tmSliceEquiv_subst (g' i) f')

/-- The inverse functor from the legacy to the primed syntactic category: the
identity on objects and `synHomMapInv` on morphisms. Its functor laws re-orient
the forward naturality of `tmSliceEquiv` through `Equiv.symm_apply_eq`. -/
def synCatSliceInverse (P : Presentation) :
    SynCat P (interpQuotRel P) ⥤ SynCat' P (interpQuotRel' P) where
  obj Γ := Γ
  map {Γ Δ} f := synHomMapInv P Γ Δ f
  map_id Γ := congrArg (Quotient.mk _)
    (funext fun i => (tmSliceEquiv Γ (Γ.get i)).symm_apply_eq.mpr (tmSliceEquiv_var i).symm)
  map_comp {Γ Δ E} f g := by
    induction f using Quotient.ind with
    | _ f' =>
    induction g using Quotient.ind with
    | _ g' =>
      refine congrArg (Quotient.mk _) (funext fun i => ?_)
      refine (tmSliceEquiv Γ (E.get i)).symm_apply_eq.mpr ?_
      simp only [HomTuple.comp, HomTuple'.comp]
      rw [tmSliceEquiv_subst]
      simp only [Equiv.apply_symm_apply]

/-- The equivalence of categories between the primed and legacy syntactic
categories: `synCatSliceFunctor` and `synCatSliceInverse`, with unit and counit
the identity isomorphisms at every object (the functors fix objects). The
naturality squares reduce, after the identity morphisms cancel, to the `Equiv`
round trips of `tmSliceEquiv`. -/
def synCatSliceEquiv (P : Presentation) :
    SynCat' P (interpQuotRel' P) ≌ SynCat P (interpQuotRel P) where
  functor := synCatSliceFunctor P
  inverse := synCatSliceInverse P
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro Γ Δ f
    induction f using Quotient.ind with
    | _ f' =>
      refine congrArg (Quotient.mk _) (funext fun i => ?_)
      change (Tm'.var i).subst f' =
        ((tmSliceEquiv Γ (Δ.get i)).symm (tmSliceEquiv Γ (Δ.get i) (f' i))).subst Tm'.var
      rw [Tm'.var_subst, Tm'.subst_id, Equiv.symm_apply_apply])
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro Γ Δ f
    induction f using Quotient.ind with
    | _ f' =>
      refine congrArg (Quotient.mk _) (funext fun i => ?_)
      change ((Tm.var i).subst
          (fun j => tmSliceEquiv Γ (Δ.get j) ((tmSliceEquiv Γ (Δ.get j)).symm (f' j))))
        = (f' i).subst Tm.var
      rw [Tm.var_subst, Tm.subst_id, Equiv.apply_symm_apply])
  functor_unitIso_comp X :=
    (Category.comp_id _).trans ((synCatSliceFunctor P).map_id X)

end GebLean.Ramified.Polynomial
