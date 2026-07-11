import GebLean.Ramified.Soundness.Collapse

/-!
# Ramified recurrence: the elementary characterization

The denotational form of Leivant III's Theorem 14, items (1)-(2), relative to
`LawvereERCat` (section 6.1, p. 227), as the pair

* the soundness functor `collapseFunctor : SynCatFO ⥤ LawvereERCat` is
  well-defined and faithful — the Phase 6 packaging
  (`GebLean.Ramified.collapseFunctor` and its `Functor.Faithful` instance in
  `GebLean/Ramified/Soundness/Collapse.lean`);
* every morphism of `LawvereERCat` is ramified-definable
  (`ramified_definability`): it has an object-sort context and a `SynCatFO`
  morphism whose collapse denotation is the morphism's interpretation.

The arity bookkeeping: an object-sort context `ObjCtx n` is indexed by its
arity, while a `SynCatFO` object carries a context list whose length equals
that arity only propositionally (`objLen_toSynCatFO`). `ObjCtx.toSynCatFO`
lifts an object-sort context to `SynCatFO`, `synCatFOHom` lifts a hom between
the underlying contexts, and `arityCongr` — `finCongr` at each arity,
transported through `Equiv.arrowCongr` — reads a numeric function across the
arity identifications. `collapseDenotation_synCatFOHom` anchors the collapse
denotation of a lifted hom at the arity congruence of its numeric denotation.

The categorical packaging of the characterization is not asserted: no
equivalence of categories between `SynCatFO` and `LawvereERCat` (nor fullness
of `collapseFunctor`) is claimed.

## Main definitions

* `ObjCtx.toSynCatFO` — the lift of an object-sort context to `SynCatFO`.
* `synCatFOHom` — the lift of a hom between underlying contexts to `SynCatFO`.
* `arityCongr` — the congruence of numeric function spaces along arity
  equalities.

## Main statements

* `ramified_definability` — every morphism of `LawvereERCat` has an
  object-sort context and a `SynCatFO` morphism whose collapse denotation is
  the morphism's interpretation.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`. The characterization is
Theorem 14, section 6.1; the definability direction is item (1) ⇒ (2).

## Tags

ramified recurrence, elementary recurrence, characterization, Lawvere theory,
object sort, syntactic category, definability
-/

namespace GebLean.Ramified

open CategoryTheory
open GebLean.Ramified.Definability

/-- The lift of an object-sort context to the first-order syntactic category:
the underlying context, all of whose sorts are object sorts by
`ObjCtx.toCtx_get_isObj`. -/
def Definability.ObjCtx.toSynCatFO {n : ℕ} (Γ : ObjCtx n) : SynCatFO :=
  ⟨Γ.toCtx, Γ.toCtx_get_isObj⟩

/-- The length of a lifted object-sort context is its arity. -/
@[simp] theorem Definability.ObjCtx.objLen_toSynCatFO {n : ℕ} (Γ : ObjCtx n) :
    objLen Γ.toSynCatFO = n :=
  Γ.toCtx_length

/-- The lift of a hom between the underlying contexts of two object-sort
contexts to a morphism of `SynCatFO` between the lifted objects. -/
def synCatFOHom {n m : ℕ} {Γ : ObjCtx n} {Δ : ObjCtx m}
    (g : Hom (higherOrder natAlgSig) (interpQuotRel (higherOrder natAlgSig))
      Γ.toCtx Δ.toCtx) :
    Γ.toSynCatFO ⟶ Δ.toSynCatFO :=
  ⟨g⟩

/-- The congruence of numeric function spaces along arity equalities:
`finCongr` at each arity, transported through `Equiv.arrowCongr`. -/
def arityCongr {n n' m m' : ℕ} (hn : n = n') (hm : m = m') :
    ((Fin n → ℕ) → (Fin m → ℕ)) ≃ ((Fin n' → ℕ) → (Fin m' → ℕ)) :=
  Equiv.arrowCongr ((finCongr hn).arrowCongr (Equiv.refl ℕ))
    ((finCongr hm).arrowCongr (Equiv.refl ℕ))

/-- The arity congruence at a function, an input tuple, and an output
position. -/
@[simp] theorem arityCongr_apply {n n' m m' : ℕ} (hn : n = n') (hm : m = m')
    (F : (Fin n → ℕ) → (Fin m → ℕ)) (v : Fin n' → ℕ) (j : Fin m') :
    arityCongr hn hm F v j = F (fun i => v (Fin.cast hn i)) (Fin.cast hm.symm j) :=
  rfl

/-- The lift inverts the Phase 6 bridge, heterogeneously across the arity
equality: the object-sort context read back from the lift by
`SynCatFO.toObjCtx` is the original. -/
theorem Definability.ObjCtx.heq_toSynCatFO_toObjCtx {n : ℕ} (Γ : ObjCtx n) :
    HEq Γ Γ.toSynCatFO.toObjCtx.2 := by
  refine Function.hfunext (congrArg Fin Γ.toCtx_length.symm) fun i i' hii => ?_
  refine heq_of_eq (Subtype.ext ?_)
  have hval : i.val = i'.val := (Fin.heq_ext_iff Γ.toCtx_length.symm).mp hii
  refine Eq.trans
    (congrArg (fun k => (Γ k).val)
      (Fin.ext (b := Fin.cast Γ.toCtx_length i') hval)) ?_
  exact (Γ.toCtx_get i').symm

/-- The numeric denotation transported along heterogeneously equal object-sort
contexts is the arity congruence of the untransported denotation. -/
theorem ramifiedDenotation_cast {n n' m m' : ℕ} {Γ : ObjCtx n} {Γ' : ObjCtx n'}
    {Δ : ObjCtx m} {Δ' : ObjCtx m'} (hn : n = n') (hm : m = m')
    (hΓ : HEq Γ Γ') (hΔ : HEq Δ Δ')
    (h : Hom (higherOrder natAlgSig) (interpQuotRel (higherOrder natAlgSig))
          Γ.toCtx Δ.toCtx
        = Hom (higherOrder natAlgSig) (interpQuotRel (higherOrder natAlgSig))
          Γ'.toCtx Δ'.toCtx)
    (g : Hom (higherOrder natAlgSig) (interpQuotRel (higherOrder natAlgSig))
      Γ.toCtx Δ.toCtx) :
    ramifiedDenotation (cast h g) = arityCongr hn hm (ramifiedDenotation g) := by
  subst hn
  subst hm
  obtain rfl := eq_of_heq hΓ
  obtain rfl := eq_of_heq hΔ
  rw [cast_eq]
  rfl

/-- The collapse denotation of a lifted hom is the arity congruence of its
numeric denotation. -/
theorem collapseDenotation_synCatFOHom {n m : ℕ} {Γ : ObjCtx n} {Δ : ObjCtx m}
    (g : Hom (higherOrder natAlgSig) (interpQuotRel (higherOrder natAlgSig))
      Γ.toCtx Δ.toCtx) :
    collapseDenotation (synCatFOHom g)
      = arityCongr Γ.toCtx_length.symm Δ.toCtx_length.symm (ramifiedDenotation g) :=
  ramifiedDenotation_cast Γ.toCtx_length.symm Δ.toCtx_length.symm
    Γ.heq_toSynCatFO_toObjCtx Δ.heq_toSynCatFO_toObjCtx _ g

/-- Definability, quantified over object-sort input contexts (Leivant III
Theorem 14 (1) ⇒ (2), section 6.1, DOI `10.1016/S0168-0072(98)00040-2`): every
morphism of `LawvereERCat` has an object-sort context and a `SynCatFO`
morphism whose collapse denotation, read along the arity identifications
`objLen_toSynCatFO`, is the morphism's interpretation. The quantification
ranges over all object-sort contexts, beyond the tower sorts, and the
statement is an existential, not fullness of `collapseFunctor`: sort-uniform
hom-sets are strictly smaller than elementary. The witnesses come from the
Phase 5 family `erMorN_ramified_definable` on a representative of the hom
class, lifted through `synCatFOHom`. -/
theorem ramified_definability {n m : LawvereERCat} (f : n ⟶ m) :
    ∃ (Γ : ObjCtx n) (g : Γ.toSynCatFO ⟶ (oCtx m).toSynCatFO),
      collapseDenotation g
        = arityCongr Γ.objLen_toSynCatFO.symm ((oCtx m).objLen_toSynCatFO).symm
            f.interp := by
  obtain ⟨e, rfl⟩ := Quotient.exists_rep (s := erMorNSetoid n m) f
  obtain ⟨Γ, g, hg⟩ := erMorN_ramified_definable e
  refine ⟨Γ, synCatFOHom g, ?_⟩
  rw [collapseDenotation_synCatFOHom, hg, ERMorNQuo.interp_mk]
  rfl

end GebLean.Ramified
