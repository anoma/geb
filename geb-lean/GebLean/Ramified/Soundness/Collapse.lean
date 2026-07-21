import GebLean.Ramified.Definability.Top
import GebLean.Ramified.Soundness.NormStepER
import GebLean.LawvereERQuot
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Ramified recurrence: the collapse packaging

The first-order syntactic category `SynCatFO`, its standard-model denotation
`collapseDenotation`, and the soundness functor
`collapseFunctor : SynCatFO ⥤ LawvereERCat` with its `Faithful` instance,
packaging the Phase 5 definability data
(`GebLean/Ramified/Definability/Top.lean`) and the sub-phase 6.4 landing
normalizer (`GebLean/Ramified/Soundness/NormStepER.lean`).

`SynCatFO` is the full subcategory of `RMRecCat natAlgSig` on the contexts all
of whose sorts are object sorts (`isObjCtx`). `SynCatFO.toObjCtx` bridges such an
object to the length-indexed object-sort context `ObjCtx` of Phase 5, and
`objLen` reads its length. `collapseDenotation` reads a full-subcategory morphism
through that bridge into `ramifiedDenotation`, the numeric denotation of a
morphism between object-sort contexts. The functoriality laws
`collapseDenotation_id` and `collapseDenotation_comp` — the identity and
composition laws of standard-model evaluation — are the `map_id` / `map_comp`
inputs consumed by the soundness functor.

The functor's morphism map lands each hom class on the class of its collapse
tuple `collapseTupleER`: per codomain position, the applicative translation
`hoTmTranslate` of the tuple component is fed through the kappa-hat input
coercions and the delta output coercion (`GebLean/Ramified/OmegaShift.lean`),
λ-abstracted into a closed curried term (`collapseComponentTm`), and landed by
the atomic collapse morphism `collapseERN`. The tupling lemma
`collapseTupleER_interp` anchors the landed tuple's interpretation at
`ramifiedDenotation`; well-definedness on the hom-quotient, functoriality, and
faithfulness all read off this anchor.

## Main definitions

* `isObjCtx` — the object property selecting the contexts of `RMRecCat natAlgSig`
  all of whose sorts are object sorts.
* `SynCatFO` — the full subcategory of `RMRecCat natAlgSig` on `isObjCtx`.
* `SynCatFO.toObjCtx` — the bridge from a `SynCatFO` object to the Phase 5
  `ObjCtx`.
* `objLen` — the length of a `SynCatFO` object.
* `collapseDenotation` — the numeric denotation of a `SynCatFO` morphism, read
  through `ramifiedDenotation`.
* `hoTermModel`, `hoTmTranslate` — the applicative translation of higher-order
  terms, the term-level extension of `prop7Translate`.
* `collapseInput`, `collapseInputs`, `collapseBodyTm`, `collapseComponentTm` —
  the coerced component source terms of the collapse.
* `collapseTupleER` — the landed morphism tuple of a raw hom-tuple.
* `collapseHomER` — the morphism map on hom classes, a `Quotient.lift`.
* `collapseFunctor` — the soundness functor `SynCatFO ⥤ LawvereERCat`.

## Main statements

* `homEval_heq_cast` — evaluation of a context-transported morphism agrees,
  heterogeneously, with evaluation of the untransported morphism.
* `collapseDenotation_apply` — the transport-free reading of the collapse
  denotation.
* `collapseDenotation_id` — the collapse denotation of an identity is the
  identity.
* `collapseDenotation_comp` — the collapse denotation of a composite is the
  composition of the collapse denotations.
* `hoTmTranslate_interp` — the applicative translation preserves the denoted
  value.
* `collapseTupleER_interp` — the tupling lemma: the landed tuple's
  interpretation is the numeric denotation of the hom class.
* `ramifiedDenotation_injective` — the numeric denotation determines the
  morphism.
* `collapseFunctor.Faithful` — the soundness functor is faithful.

## Implementation notes

Novel packaging of the section 6.1 soundness statement. The bridge from a
full-subcategory object (a context with an object-sort proof) to `ObjCtx`
threads the per-position object-sort proof; the underlying context of the bridge
equals the original object (`SynCatFO.toObjCtx_toCtx`), the equality along which
`collapseDenotation` transports the full-subcategory morphism into
`ramifiedDenotation`'s domain.

The component source terms fix the sort shape `collapseERN` expects — every
input at an `Ω`-shifted sort, the output at the base sort `o` — by feeding the
coercions of Leivant III section 2.4(1): `kappaHatIdent` reads an input
`Ω σᵢ → σᵢ` and `deltaIdent` lowers the output `θ → o`, each extensionally the
identity on the carrier copies, so the denotational anchor survives the
reshaping.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`. The soundness direction is
Theorem 14 (1) ⇒ (4), section 6.1; the coercions are section 2.4(1); the
per-component landing is Proposition 13, section 5.

## Tags

ramified recurrence, elementary recurrence, soundness, Lawvere theory, object
sort, syntactic category, full subcategory, faithful functor
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

/-- Evaluation of a context-transported morphism agrees, heterogeneously, with
evaluation of the untransported morphism at the corresponding environment and
codomain position. -/
theorem homEval_heq_cast {P : Presentation} {A A' B B' : Ctx P.S}
    (hA : A = A') (hB : B = B')
    (h : Hom P (interpQuotRel P) A B = Hom P (interpQuotRel P) A' B')
    (f : Hom P (interpQuotRel P) A B)
    (ρ : (standardModel P).Env A) (ρ' : (standardModel P).Env A') (hρ : ρ ≍ ρ')
    (i : Fin B.length) (i' : Fin B'.length) (hi : i ≍ i') :
    (cast h f).eval ρ' i' ≍ f.eval ρ i := by
  subst hA
  subst hB
  obtain rfl := eq_of_heq hρ
  obtain rfl := eq_of_heq hi
  rw [cast_eq]

/-- The transport-free reading of the collapse denotation: the numeric reading
of the underlying hom's evaluation at the numeric environment over the
underlying context. -/
theorem collapseDenotation_apply {Γ Δ : SynCatFO} (g : Γ ⟶ Δ)
    (v : Fin (objLen Γ) → ℕ) (j : Fin (objLen Δ)) :
    collapseDenotation g v j
      = objToNat (Δ.property j)
          (Hom.eval g.hom (fun i => objFromNat (Γ.property i) (v i)) j) := by
  refine Eq.trans (ramifiedDenotation_apply (collapseHom g) v j) ?_
  refine objToNat_heq _ _ ?_
  refine homEval_heq_cast Γ.toObjCtx_toCtx.symm Δ.toObjCtx_toCtx.symm _ g.hom
    (fun i => objFromNat (Γ.property i) (v i)) (ramifiedEnv Γ.toObjCtx.2 v) ?_ j _ ?_
  · refine Function.hfunext (congrArg Fin (congrArg List.length Γ.toObjCtx_toCtx.symm)) ?_
    intro a a' haa
    have hval : a.val = a'.val :=
      (Fin.heq_ext_iff (congrArg List.length Γ.toObjCtx_toCtx.symm)).mp haa
    have hv : v a = v (Fin.cast (Γ.toObjCtx.2).toCtx_length a') := congrArg v (Fin.ext hval)
    rw [hv]
    exact objFromNat_heq _ _ _
  · exact (Fin.heq_ext_iff (congrArg List.length Δ.toObjCtx_toCtx.symm)).mpr rfl

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

/-- The applicative-term model of the higher-order presentation (the term-level
extension of the direct Proposition 7 translation, Leivant III section 4.1): the
signature of `higherOrder natAlgSig` interpreted into `RλMR_o^ω` terms in an
ambient context `Γ`. Mirrors `higherOrderModel` but valued in applicative terms,
following `defnModelTerm`: a constructor becomes a `con`-headed application
spine (`appSpine`), application becomes `app'`, a saturated identifier
substitutes its translation `prop7Translate` along the argument terms
(`Binding.sub`), and an identifier constant abstracts its translation into a
combinator value (`lamSpine` after weakening by `suffixThinning`). Novel
packaging. -/
def hoTermModel {Γ : Binding.Ctx RType} :
    SortedModel (higherOrder natAlgSig).sig where
  carrier := fun σ => Binding.Tm (rlmrOSig natAlgSig) Γ σ
  interpOp op args :=
    match op with
    | Sum.inl (Sum.inl (Sum.inl cop)) =>
      appSpine (List.replicate (natAlgSig.ar cop.2) cop.1.val)
        (Binding.Tm.op (S := rlmrOSig natAlgSig)
          (RlmrOOp.con cop.1.val cop.1.2 cop.2) (fun k => k.elim0)) args
    | Sum.inl (Sum.inl (Sum.inr _aop)) =>
      app' (args ⟨0, Nat.zero_lt_two⟩) (args ⟨1, Nat.one_lt_two⟩)
    | Sum.inl (Sum.inr iop) =>
      Binding.sub (fun _s x => x.2 ▸ args x.1) (prop7Translate iop.2.2)
    | Sum.inr icop =>
      lamSpine icop.1 (Binding.ren (suffixThinning Γ) (prop7Translate icop.2.2))

/-- The direct applicative translation of a higher-order term (Leivant III
section 4.1, the term-level extension of Proposition 7): fold the term against
the applicative-term model `hoTermModel` over the identity variable
environment. The component-wise translation of the syntactic category's
morphism tuples consumed by the collapse functor. Novel packaging. -/
def hoTmTranslate {Γ : Ctx RType} {σ : RType}
    (t : Tm (higherOrder natAlgSig).sig Γ σ) :
    Binding.Tm (rlmrOSig natAlgSig) Γ σ :=
  t.eval hoTermModel (fun i => Binding.Tm.var ⟨i, rfl⟩)

/-- The applicative translation of a higher-order term preserves the denoted
value (Leivant III section 4.1): `appEval` of `hoTmTranslate t` agrees with the
standard-model evaluation of `t` at every environment. The fold is transported
by the model morphism `Tm.eval_model_morphism` along `appEval (·, ρ)`, the
per-operation commutations discharged as in `prop7DefnStep_interp`, with
`prop7Translate_interp` supplying the identifier agreements. -/
theorem hoTmTranslate_interp {Γ : Ctx RType} {σ : RType}
    (t : Tm (higherOrder natAlgSig).sig Γ σ)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    appEval (hoTmTranslate t) ρ
      = t.eval (standardModel (higherOrder natAlgSig)) ρ := by
  refine Tm.eval_model_morphism hoTermModel (standardModel (higherOrder natAlgSig))
    (fun {_σ} u => appEval u ρ) ?_
    (fun i => Binding.Tm.var ⟨i, rfl⟩) ρ (fun i => appEval_var ⟨i, rfl⟩ ρ) t
  intro o args
  rcases o with ((cop | _aop) | iop) | icop
  · simp only [hoTermModel, higherOrder, higherOrderModel, SortedSig.sum, constructorSig,
      Sum.elim_inl, appEval_appSpine]
    exact appChain_curryInterp natAlgSig (List.replicate (natAlgSig.ar cop.2) cop.1.val)
      cop.1.val (stdConstructorInterp natAlgSig cop) (fun i => appEval (args i) ρ)
  · dsimp only [hoTermModel, higherOrder, higherOrderModel]
    rw [appEval_app']
    rfl
  · dsimp only [hoTermModel, higherOrder, higherOrderModel]
    refine (appEval_sub (prop7Translate iop.2.2) _ ρ).trans ?_
    exact prop7Translate_interp iop.2.2 _
  · dsimp only [hoTermModel, higherOrder, higherOrderModel]
    refine (appEval_lamSpine Γ icop.1
      (Binding.ren (suffixThinning Γ) (prop7Translate icop.2.2)) ρ).trans ?_
    refine congrArg (curryInterp natAlgSig icop.1 icop.2.1) ?_
    funext cv
    refine (appEval_ren (prop7Translate icop.2.2) (suffixThinning Γ)
      (joinEnv ρ cv)).trans ?_
    rw [renEnvSem_suffixThinning_joinEnv]
    exact prop7Translate_interp icop.2.2 cv

/-- Every position of a singleton context carries its sole sort. -/
theorem singleton_get {θ : RType} (k : Fin ([θ] : Ctx RType).length) :
    ([θ] : Ctx RType).get k = θ :=
  match k with
  | ⟨0, _⟩ => rfl
  | ⟨_ + 1, h⟩ => absurd h (by simp)

/-- The substitution from a singleton context sending its sole variable to a
term `S`. The substitution shape through which the collapse feeds the kappa-hat
and delta coercions, whose translated bodies live over singleton contexts. -/
def singletonEnv {Ξ : Binding.Ctx RType} (θ : RType)
    (S : Binding.Tm (rlmrOSig natAlgSig) Ξ θ) :
    Binding.Env (Binding.Tm (rlmrOSig natAlgSig)) [θ] Ξ :=
  fun _s x => ((singleton_get x.1).symm.trans x.2) ▸ S

/-- The evaluation of the singleton substitution reads the substituted term,
heterogeneously, at every position. -/
theorem subEnvSem_singletonEnv {Ξ : Binding.Ctx RType} (θ : RType)
    (S : Binding.Tm (rlmrOSig natAlgSig) Ξ θ)
    (ρ : ∀ k : Fin Ξ.length, RType.interp (FreeAlg natAlgSig) (Ξ.get k))
    (i : Fin ([θ] : Ctx RType).length) :
    subEnvSem (singletonEnv θ S) ρ i ≍ appEval S ρ := by
  refine HEq.trans
    (heq_of_eq (appEval_eqRec ((singleton_get i).symm.trans rfl) S ρ)) ?_
  exact eqRec_heq _ _

/-- The shifted input context of an object-sort context: one `Ω`-shifted copy
of each input sort, the domain shape of the atomic collapse morphism
`collapseERN`. -/
abbrev omegaCtx {n : ℕ} (Γo : ObjCtx n) : Binding.Ctx RType :=
  List.ofFn fun i => RType.omega ((Γo i).val)

/-- The coerced input at position `i`: the applicative translation of the
kappa-hat coercion `Ω σᵢ → σᵢ` (`kappaHatIdent`), substituted at the `i`-th
variable of the shifted input context. Denotes the carrier-copy identity on
that variable (`appEval_collapseInput`). -/
def collapseInput {n : ℕ} (Γo : ObjCtx n) (i : Fin n) :
    Binding.Tm (rlmrOSig natAlgSig) (omegaCtx Γo) ((Γo i).val) :=
  Binding.sub
    (singletonEnv (RType.omega ((Γo i).val))
      (Binding.Tm.var ⟨Fin.cast List.length_ofFn.symm i,
        (List.get_ofFn _ _).trans
          (congrArg (fun k => RType.omega ((Γo k).val)) (Fin.ext rfl))⟩))
    (prop7Translate (kappaHatIdent natAlgSig (Γo i).val (Γo i).2))

/-- The coerced input denotes the environment's entry at its position,
heterogeneously across the carrier-copy identifications: the kappa-hat
coercion is extensionally the identity (`kappaHatIdent_interp`). -/
theorem appEval_collapseInput {n : ℕ} (Γo : ObjCtx n) (i : Fin n)
    (ρ : ∀ k : Fin (omegaCtx Γo).length,
      RType.interp (FreeAlg natAlgSig) ((omegaCtx Γo).get k)) :
    appEval (collapseInput Γo i) ρ ≍ ρ (Fin.cast List.length_ofFn.symm i) := by
  refine HEq.trans (heq_of_eq (Eq.trans (appEval_sub
      (prop7Translate (kappaHatIdent natAlgSig (Γo i).val (Γo i).2))
      (singletonEnv _ _) ρ)
    (Eq.trans (prop7Translate_interp (kappaHatIdent natAlgSig (Γo i).val (Γo i).2) _)
      (kappaHatIdent_interp natAlgSig (Γo i).val (Γo i).2 _)))) ?_
  refine (cast_heq _ _).trans ?_
  refine (subEnvSem_singletonEnv _ _ ρ 0).trans ?_
  refine HEq.trans (heq_of_eq (appEval_var _ ρ)) ?_
  exact eqRec_heq _ _

/-- The coerced-input substitution: each position of the underlying context of
`Γo` reads its coerced input `collapseInput` from the shifted input context. -/
def collapseInputs {n : ℕ} (Γo : ObjCtx n) :
    Binding.Env (Binding.Tm (rlmrOSig natAlgSig)) Γo.toCtx (omegaCtx Γo) :=
  fun _s x => (((Γo.toCtx_get x.1).symm.trans x.2) ▸
    collapseInput Γo (Fin.cast Γo.toCtx_length x.1))

/-- The `j`-th component body of the collapse, open over the shifted input
context: the applicative translation `hoTmTranslate` of the tuple component,
its inputs fed through the kappa-hat coercions (`collapseInputs`) and its
output lowered to the base sort through the delta coercion (`deltaIdent`).
Novel packaging; the coercions are Leivant III section 2.4(1). -/
def collapseBodyTm {n m : ℕ} (Γo : ObjCtx n) (Δo : ObjCtx m)
    (f : HomTuple (higherOrder natAlgSig) Γo.toCtx Δo.toCtx) (j : Fin m) :
    Binding.Tm (rlmrOSig natAlgSig) (omegaCtx Γo) RType.o :=
  Binding.sub
    (singletonEnv (Δo.toCtx.get (Fin.cast (Δo.toCtx_length).symm j))
      (Binding.sub (collapseInputs Γo)
        (hoTmTranslate (f (Fin.cast (Δo.toCtx_length).symm j)))))
    (prop7Translate (deltaIdent natAlgSig false rfl
      (Δo.toCtx.get (Fin.cast (Δo.toCtx_length).symm j))
      (Δo.toCtx_get_isObj (Fin.cast (Δo.toCtx_length).symm j))))

/-- The `j`-th component source term of the collapse: the component body
`collapseBodyTm`, λ-abstracted over the shifted input context. The closed head
the atomic collapse morphism `collapseERN` lands. -/
def collapseComponentTm {n m : ℕ} (Γo : ObjCtx n) (Δo : ObjCtx m)
    (f : HomTuple (higherOrder natAlgSig) Γo.toCtx Δo.toCtx) (j : Fin m) :
    Binding.Tm (rlmrOSig natAlgSig) []
      (RType.curried (List.ofFn fun i => RType.omega ((Γo i).val)) RType.o) :=
  lamSpine (Γ := []) (omegaCtx Γo) (collapseBodyTm Γo Δo f j)

/-- The landed morphism tuple of a raw hom-tuple: one atomic collapse morphism
`collapseERN` per codomain position, at that position's component source term
`collapseComponentTm`. The tupling into `ERMorN` is definitional (6.4 spec
section 6.4). -/
def collapseTupleER {n m : ℕ} (Γo : ObjCtx n) (Δo : ObjCtx m)
    (f : HomTuple (higherOrder natAlgSig) Γo.toCtx Δo.toCtx) : ERMorN n m :=
  fun j => OneLambda.collapseERN (τs := fun i => (Γo i).val)
    (collapseComponentTm Γo Δo f j) 0

/-- Joining the empty environment with a suffix environment is the suffix
environment. The empty-prefix instance of `joinEnv`, closing the
λ-abstraction of the component source term over the whole shifted input
context. -/
theorem joinEnv_nil {Ξ : Binding.Ctx RType}
    (cv : ∀ k : Fin Ξ.length, RType.interp (FreeAlg natAlgSig) (Ξ.get k)) :
    joinEnv (Γ := []) finZeroElim cv = cv := by
  funext k
  apply eq_of_heq
  have h : ¬ k.val < ([] : Binding.Ctx RType).length := by simp
  have hb : k.val - ([] : Binding.Ctx RType).length < Ξ.length := by
    simp
  refine (joinEnv_heq_right finZeroElim cv k h hb).trans ?_
  exact congr_arg_heq cv (Fin.ext (by simp))

/-- The evaluation of the coerced-input substitution at the constructor-word
environment of a numeric input tuple is the numeric environment `ramifiedEnv`:
position by position, the kappa-hat coercion reads the word's value back on
the input sort's carrier copy. -/
theorem subEnvSem_collapseInputs {n : ℕ} (Γo : ObjCtx n) (v : Fin n → ℕ) :
    subEnvSem (collapseInputs Γo)
        (OneLambda.ofFnOmegaEnv (fun i => (Γo i).val) fun i => natToFreeAlg (v i))
      = ramifiedEnv Γo v := by
  funext k
  apply eq_of_heq
  refine HEq.trans ?_ (cast_heq _ _).symm
  refine HEq.trans (heq_of_eq (appEval_eqRec ((Γo.toCtx_get k).symm.trans rfl)
    (collapseInput Γo (Fin.cast Γo.toCtx_length k)) _)) ?_
  refine (eqRec_heq _ _).trans ?_
  refine (appEval_collapseInput Γo (Fin.cast Γo.toCtx_length k) _).trans ?_
  refine (cast_heq _ _).trans ?_
  exact congr_arg_heq (fun idx => natToFreeAlg (v idx)) (Fin.ext rfl)

/-- The numeric reading of the component body's denotation is the numeric
reading of the tuple component's standard-model evaluation at the coerced
environment: the delta coercion is extensionally the identity
(`deltaIdent_interp`), and the applicative translation preserves the denoted
value (`hoTmTranslate_interp`). -/
theorem appEval_collapseBodyTm {n m : ℕ} (Γo : ObjCtx n) (Δo : ObjCtx m)
    (f : HomTuple (higherOrder natAlgSig) Γo.toCtx Δo.toCtx) (j : Fin m)
    (ρ : ∀ k : Fin (omegaCtx Γo).length,
      RType.interp (FreeAlg natAlgSig) ((omegaCtx Γo).get k)) :
    freeAlgToNat (appEval (collapseBodyTm Γo Δo f j) ρ)
      = objToNat (Δo.toCtx_get_isObj (Fin.cast (Δo.toCtx_length).symm j))
          ((f (Fin.cast (Δo.toCtx_length).symm j)).eval
            (standardModel (higherOrder natAlgSig))
            (subEnvSem (collapseInputs Γo) ρ)) := by
  refine Eq.trans (congrArg freeAlgToNat (Eq.trans (appEval_sub
      (prop7Translate (deltaIdent natAlgSig false rfl _ _)) (singletonEnv _ _) ρ)
    (Eq.trans (prop7Translate_interp _ _)
      (deltaIdent_interp natAlgSig false rfl _
        (Δo.toCtx_get_isObj (Fin.cast (Δo.toCtx_length).symm j)) _)))) ?_
  refine congrArg freeAlgToNat (eq_of_heq ?_)
  refine (cast_heq _ _).trans ?_
  refine HEq.trans ?_ (cast_heq _ _).symm
  refine (subEnvSem_singletonEnv _ _ _ 0).trans ?_
  refine heq_of_eq ?_
  refine Eq.trans (appEval_sub
    (hoTmTranslate (f (Fin.cast (Δo.toCtx_length).symm j))) (collapseInputs Γo) ρ) ?_
  exact hoTmTranslate_interp (f (Fin.cast (Δo.toCtx_length).symm j)) _

/-- The tupling lemma (6.4 spec section 6.4): the interpretation of the landed
morphism tuple is the numeric denotation `ramifiedDenotation` of the raw
hom-tuple's class. Lifts the per-component adequacy `collapseERN_interp` to
the whole morphism, through the evaluation lemma `appEval_sourceApps`, the
λ-spine and application-chain cancellation
(`appEval_lamSpine`/`appChain_curryInterp`), and the coercion identities. -/
theorem collapseTupleER_interp {n m : ℕ} (Γo : ObjCtx n) (Δo : ObjCtx m)
    (f : HomTuple (higherOrder natAlgSig) Γo.toCtx Δo.toCtx) (v : Fin n → ℕ) :
    (collapseTupleER Γo Δo f).interp v
      = ramifiedDenotation (Quotient.mk
          (homSetoid (higherOrder natAlgSig) (interpQuotRel (higherOrder natAlgSig))
            Γo.toCtx Δo.toCtx) f) v := by
  funext j
  have h1 : (collapseTupleER Γo Δo f).interp v j
      = freeAlgToNat (appEval (OneLambda.sourceApps (collapseComponentTm Γo Δo f j)
          fun i => sourceWord (natToFreeAlg (v i)) ((Γo i).val)) finZeroElim) :=
    congrFun (OneLambda.collapseERN_interp (collapseComponentTm Γo Δo f j) v) 0
  rw [h1, OneLambda.appEval_sourceApps]
  simp only [appEval_sourceWord]
  unfold collapseComponentTm
  rw [appEval_lamSpine [] (omegaCtx Γo) (collapseBodyTm Γo Δo f j) finZeroElim,
    appChain_curryInterp, joinEnv_nil]
  refine (appEval_collapseBodyTm Γo Δo f j _).trans ?_
  rw [subEnvSem_collapseInputs]
  rfl

/-- The morphism map of the collapse functor at the object-context level: the
class of the landed tuple `collapseTupleER`, lifted along the hom-quotient.
Well-defined by the interpretative anchoring: related tuples have equal
classes, hence equal `ramifiedDenotation`, hence — through
`collapseTupleER_interp` — interp-related landed tuples. -/
def collapseHomER {n m : ℕ} (Γo : ObjCtx n) (Δo : ObjCtx m)
    (g : Hom (higherOrder natAlgSig) (interpQuotRel (higherOrder natAlgSig))
      Γo.toCtx Δo.toCtx) : ERMorNQuo n m :=
  Quotient.lift
    (fun f => Quotient.mk (erMorNSetoid n m) (collapseTupleER Γo Δo f))
    (fun f f' hff' => Quotient.sound (s := erMorNSetoid n m) fun v => by
      rw [collapseTupleER_interp, collapseTupleER_interp,
        Quotient.sound (s := homSetoid (higherOrder natAlgSig)
          (interpQuotRel (higherOrder natAlgSig)) Γo.toCtx Δo.toCtx) hff'])
    g

/-- The soundness functor (Leivant III Theorem 14, the arm (1) ⇒ (4), section
6.1): from the first-order syntactic category of the higher-type ramified
system to the Lawvere theory of elementary recursive functions. The object map
reads a context's arity; the morphism map lands each hom class on the class of
its collapse tuple `collapseTupleER`, the per-component atomic collapse
`collapseERN` of the applicative translation of the tuple. Functoriality is
interp-extensionality (`erMorNSetoid`) through the tupling lemma
`collapseTupleER_interp` and the denotation laws
`ramifiedDenotation_id`/`ramifiedDenotation_comp`. Novel packaging. -/
def collapseFunctor : SynCatFO ⥤ LawvereERCat where
  obj Γ := objLen Γ
  map {Γ Δ} g := collapseHomER Γ.toObjCtx.2 Δ.toObjCtx.2 (collapseHom g)
  map_id Γ := by
    rw [collapseHom_id]
    refine Quotient.sound (s := erMorNSetoid _ _) fun v => ?_
    rw [collapseTupleER_interp, ERMorN.interp_id]
    exact congrFun (ramifiedDenotation_id Γ.toObjCtx.2) v
  map_comp {Γ Δ Θ} g h := by
    rw [collapseHom_comp]
    generalize collapseHom g = G
    generalize collapseHom h = H
    induction G using Quotient.ind with
    | _ f₁ =>
    induction H using Quotient.ind with
    | _ f₂ =>
      refine Quotient.sound (s := erMorNSetoid _ _) fun v => ?_
      rw [ERMorN.interp_comp, collapseTupleER_interp, collapseTupleER_interp,
        collapseTupleER_interp]
      exact congrFun (ramifiedDenotation_comp (Quotient.mk _ f₁) (Quotient.mk _ f₂)) v

/-- The numeric reading is injective on each carrier copy: `objFromNat`
retracts it. -/
theorem objToNat_injective {s : RType} (hs : s.IsObj)
    {x y : RType.interp (FreeAlg natAlgSig) s}
    (h : objToNat hs x = objToNat hs y) : x = y := by
  rw [← objFromNat_objToNat hs x, ← objFromNat_objToNat hs y, h]

/-- The numeric denotation determines the morphism: two morphisms between
object-sort contexts with equal `ramifiedDenotation` are equal. Every
standard-model environment over an object-sort context is the numeric
environment of its numeric readings (`objFromNat_objToNat`), and the numeric
reading is injective on each carrier copy (`objToNat_injective`), so equal
denotations force equal evaluations at every environment — the interpretative
relation of the hom-quotient. -/
theorem ramifiedDenotation_injective {n m : ℕ} {Γo : ObjCtx n} {Δo : ObjCtx m}
    (g g' : Hom (higherOrder natAlgSig) (interpQuotRel (higherOrder natAlgSig))
      Γo.toCtx Δo.toCtx)
    (h : ramifiedDenotation g = ramifiedDenotation g') : g = g' := by
  induction g using Quotient.ind with
  | _ f =>
  induction g' using Quotient.ind with
  | _ f' =>
    refine Quotient.sound fun i ρ => ?_
    -- The numeric readings of `ρ`, whose numeric environment recovers `ρ`.
    have hρ : ramifiedEnv Γo (fun k =>
        objToNat (Γo.toCtx_get_isObj (Fin.cast Γo.toCtx_length.symm k))
          (ρ (Fin.cast Γo.toCtx_length.symm k))) = ρ := by
      funext k
      apply eq_of_heq
      refine (cast_heq _ _).trans ?_
      refine HEq.trans (heq_of_eq (natToFreeAlg_freeAlgToNat _)) ?_
      refine (cast_heq _ _).trans ?_
      exact congr_arg_heq ρ (Fin.ext rfl)
    have hj := congrFun (congrFun h fun k =>
      objToNat (Γo.toCtx_get_isObj (Fin.cast Γo.toCtx_length.symm k))
        (ρ (Fin.cast Γo.toCtx_length.symm k))) (Fin.cast Δo.toCtx_length i)
    rw [ramifiedDenotation_apply, ramifiedDenotation_apply, hρ] at hj
    have h2 := objToNat_injective _ hj
    exact (show Fin.cast Δo.toCtx_length.symm (Fin.cast Δo.toCtx_length i) = i from
      Fin.ext rfl) ▸ h2

/-- The morphism map of the collapse functor is injective at the
object-context level: equal landed classes have interp-equal landed tuples,
hence equal numeric denotations (`collapseTupleER_interp`), hence equal hom
classes (`ramifiedDenotation_injective`). -/
theorem collapseHomER_injective {n m : ℕ} (Γo : ObjCtx n) (Δo : ObjCtx m) :
    Function.Injective (collapseHomER Γo Δo) := by
  intro G H heq
  induction G using Quotient.ind with
  | _ f₁ =>
  induction H using Quotient.ind with
  | _ f₂ =>
    refine ramifiedDenotation_injective _ _ (funext fun v => ?_)
    have hrel := Quotient.exact (s := erMorNSetoid n m) heq
    have hv := hrel v
    rw [collapseTupleER_interp, collapseTupleER_interp] at hv
    exact hv

/-- The soundness functor is faithful (by construction with interpretative
hom-sets): its morphism map factors injectively through the numeric
denotation. Equal images force equal `collapseHom` transports
(`collapseHomER_injective`), hence equal underlying homs (`cast_injective`),
hence equal `SynCatFO` morphisms. -/
instance : collapseFunctor.Faithful where
  map_injective {Γ Δ} {g h} heq := by
    have h1 : collapseHom g = collapseHom h :=
      collapseHomER_injective Γ.toObjCtx.2 Δ.toObjCtx.2 heq
    exact CategoryTheory.ObjectProperty.hom_ext isObjCtx ((cast_inj _).mp h1)

end GebLean.Ramified
