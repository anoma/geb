import GebLean.Ramified.Polynomial.HigherOrderEquiv
import GebLean.Ramified.Characterization
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The primed collapse packaging

The first-order syntactic category `SynCatFO'` of the primed higher-order
system (`GebLean/Ramified/Polynomial/HigherOrder.lean`) and its numeric
denotation `collapseDenotation'`, mirroring the packaging half of the legacy
module `GebLean/Ramified/Soundness/Collapse.lean` and the object-context
machinery of `GebLean/Ramified/Definability/Top.lean` on the vendored
`SlicePFunctor` stack.

`SynCatFO'` is the full subcategory of `RMRecCat' natAlgSig` on the contexts
all of whose sorts are object sorts (`isObjCtx'`). `SynCatFO'.toObjCtx'`
bridges such an object to the length-indexed object-sort context `ObjCtx'`, and
`objLen'` reads its length. `collapseDenotation'` reads a full-subcategory
morphism through that bridge into `ramifiedDenotation'`, the numeric denotation
of a morphism between object-sort contexts, whose per-position numeric reading
is `objToNat'` (the primed carrier-copy transport, through `natFreeAlgEquiv'`).

The phase's central equivalence `rmRecCatSliceEquiv natAlgSig`
(`GebLean/Ramified/Polynomial/HigherOrderEquiv.lean`) restricts to the two
first-order full subcategories as `synCatFOSliceEquiv`, the object properties
corresponding sortwise by `rTypeSliceEquiv_isObj`, and
`collapseDenotation_sliceEquiv` identifies the legacy collapse denotation of a
transported morphism with the primed collapse denotation read across the arity
identifications `arityCongr`.

## Main definitions

* `isObjCtx'` — the object property selecting the contexts of
  `RMRecCat' natAlgSig` all of whose sorts are object sorts.
* `SynCatFO'` — the full subcategory of `RMRecCat' natAlgSig` on `isObjCtx'`.
* `ObjCtx'`, `ObjCtx'.toCtx`, `oObj'`, `oCtx'` — primed object-sort contexts of
  a given length, their underlying contexts, and the base-sort instances.
* `SynCatFO'.toObjCtx'`, `objLen'`, `ObjCtx'.toSynCatFO'` — the bridge between
  a `SynCatFO'` object and a primed object-sort context, and its length.
* `objToNat'`, `objFromNat'` — the primed numeric reading of an object-sort
  value and its inverse transport.
* `ramifiedEnv'`, `ramifiedDenotation'` — the primed numeric environment over an
  object-sort context and the numeric denotation of a morphism between such.
* `collapseHom'`, `collapseDenotation'` — the bridge transport of a `SynCatFO'`
  morphism and its numeric denotation.
* `synCatFOSliceEquiv` — the restriction of `rmRecCatSliceEquiv natAlgSig` to
  the first-order full subcategories.

## Main statements

* `objToNat'_objFromNat'`, `objFromNat'_objToNat'` — the primed carrier-copy
  round trips.
* `ramifiedDenotation'_id`, `ramifiedDenotation'_comp` — the identity and
  composition laws of primed standard-model evaluation.
* `collapseDenotation'_id`, `collapseDenotation'_comp` — the same laws for the
  collapse denotation.
* `collapseDenotation_apply`, `collapseDenotation'_apply` — the transport-free
  readings of the two collapse denotations.
* `isObjCtx_map`, `isObjCtx'_map_symm` — the sortwise correspondence of the two
  object properties across the bridge.
* `synHomMap_eval`, `rmRecCatSliceEquiv_map_eval` — the evaluation of a
  transported morphism, conjugated by the environment transport.
* `objToNat_carrierSliceEquiv`, `carrierSliceEquiv_objFromNat'` — the numeric
  transports agree across the carrier bridge.
* `collapseDenotation_sliceEquiv` — the collapse denotations agree across
  `synCatFOSliceEquiv`, read along the arity identifications.

## Implementation notes

The bridge from a full-subcategory object (a context with an object-sort proof)
to `ObjCtx'` threads the per-position object-sort proof; the underlying context
of the bridge equals the original object (`SynCatFO'.toObjCtx'_toCtx`), the
equality along which `collapseHom'` transports the full-subcategory morphism
into `ramifiedDenotation'`'s domain. `collapseDenotation_apply` and
`collapseDenotation'_apply` undo that transport, presenting each denotation
directly in terms of the underlying hom's evaluation; the agreement is then a
statement about `Hom.eval` against `Hom'.eval`, with no context transports left.

Mathlib's `CategoryTheory.Equivalence.congrFullSubcategory` restricts an
equivalence of categories to full subcategories, but requires the target
property to be closed under isomorphism, which is unavailable for `isObjCtx`:
an isomorphism of the syntactic category carries no sortwise information.
`synCatFOSliceEquiv` therefore reproduces that construction, with the inverse
functor's object property supplied directly by the sortwise correspondence
`isObjCtx'_map_symm`.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`. The first-order
sub-category of the higher-type system and its numeric denotation are Theorem
14, section 6.1; the object sorts and their carrier copies are sections 2.3 and
2.7.

D. Sannella, A. Tarlecki, "Foundations of Algebraic Specification and Formal
Software Development", Springer, 2012, DOI `10.1007/978-3-642-17336-3`, Chapter
1: signature morphisms and reducts, the pattern of the presentation-level
transport of environments and terms.

## Tags

ramified recurrence, object sort, syntactic category, full subcategory,
equivalence of categories, numeric denotation, slice category, W-type
-/

namespace GebLean.Ramified.Polynomial

open CategoryTheory GebLean.Ramified GebLean.Ramified.Definability

/-- The object property selecting the contexts of `RMRecCat' natAlgSig` all of
whose sorts are object sorts. Mirror of the legacy `isObjCtx`. -/
def isObjCtx' : ObjectProperty (RMRecCat' natAlgSig) :=
  fun Γ' => ∀ i : Fin Γ'.length, (Γ'.get i).IsObj

/-- The full subcategory of `RMRecCat' natAlgSig` on the object-sort contexts.
Mirror of the legacy `SynCatFO`. -/
abbrev SynCatFO' : Type := isObjCtx'.FullSubcategory

/-- Primed object-sort contexts of length `n`: every entry an object sort.
Mirror of the legacy `ObjCtx`. -/
def ObjCtx' (n : ℕ) : Type := Fin n → { s : RType' // s.IsObj }

/-- The underlying context of a primed object-sort context. -/
def ObjCtx'.toCtx {n : ℕ} (Γ' : ObjCtx' n) : Ctx RType' :=
  List.ofFn (fun i => (Γ' i).val)

/-- The underlying context has length `n`. -/
@[simp] theorem ObjCtx'.toCtx_length {n : ℕ} (Γ' : ObjCtx' n) : Γ'.toCtx.length = n :=
  List.length_ofFn

/-- The entry of the underlying context at a position. -/
theorem ObjCtx'.toCtx_get {n : ℕ} (Γ' : ObjCtx' n) (i : Fin Γ'.toCtx.length) :
    Γ'.toCtx.get i = (Γ' (Fin.cast Γ'.toCtx_length i)).val := by
  simp only [ObjCtx'.toCtx, List.get_ofFn]

/-- Every entry of the underlying context is an object sort. -/
theorem ObjCtx'.toCtx_get_isObj {n : ℕ} (Γ' : ObjCtx' n) (i : Fin Γ'.toCtx.length) :
    (Γ'.toCtx.get i).IsObj :=
  (Γ'.toCtx_get i).symm ▸ (Γ' (Fin.cast Γ'.toCtx_length i)).2

/-- The base object sort `o` as a primed object-sort witness. Mirror of the
legacy `oObj`. -/
def oObj' : { s : RType' // RType'.IsObj s } :=
  ⟨RType'.o, Or.inl (RType'.shape_mk RTypeShape.o Fin.elim0)⟩

/-- The all-object-sort context of `m` copies of the base sort `o`. Mirror of
the legacy `oCtx`. -/
def oCtx' (m : ℕ) : ObjCtx' m := fun _ => oObj'

/-- The bridge from a `SynCatFO'` object to the primed object-sort context: the
length-indexed family of object sorts read off the underlying context, each
tagged by its object-sort proof. -/
def SynCatFO'.toObjCtx' (Γ' : SynCatFO') : Σ n, ObjCtx' n :=
  ⟨Γ'.obj.length, fun i => ⟨Γ'.obj.get i, Γ'.property i⟩⟩

/-- The length of a `SynCatFO'` object. -/
def objLen' (Γ' : SynCatFO') : ℕ := Γ'.toObjCtx'.1

/-- The underlying context of the bridge equals the original object. -/
theorem SynCatFO'.toObjCtx'_toCtx (Γ' : SynCatFO') : (Γ'.toObjCtx'.2).toCtx = Γ'.obj := by
  simp only [SynCatFO'.toObjCtx', ObjCtx'.toCtx]
  exact List.ofFn_get Γ'.obj

/-- The lift of a primed object-sort context to the first-order syntactic
category: the underlying context, all of whose sorts are object sorts. -/
def ObjCtx'.toSynCatFO' {n : ℕ} (Γ' : ObjCtx' n) : SynCatFO' :=
  ⟨Γ'.toCtx, Γ'.toCtx_get_isObj⟩

/-- The length of a lifted primed object-sort context is its arity. -/
@[simp] theorem objLen'_toSynCatFO' {n : ℕ} (Γ' : ObjCtx' n) :
    objLen' Γ'.toSynCatFO' = n :=
  Γ'.toCtx_length

/-- The primed numeric reading of an object-sort carrier value, through the
carrier-copy equality of the object sort (Leivant III section 2.7): for `s` an
object sort, `RType'.interp (FreeAlg' natAlgSig) s` is a copy of
`FreeAlg' natAlgSig`, read as a natural by `natFreeAlgEquiv'`. Mirror of the
legacy `objToNat`. -/
def objToNat' {s : RType'} (hs : s.IsObj)
    (x : RType'.interp (FreeAlg' natAlgSig) s) : ℕ :=
  natFreeAlgEquiv' (cast (RType'.interp_isObj (FreeAlg' natAlgSig) hs) x)

/-- The primed carrier-copy transport of a natural into an object-sort
denotation, the inverse direction of `objToNat'`. Mirror of the legacy
`objFromNat`. -/
def objFromNat' {s : RType'} (hs : s.IsObj) (k : ℕ) :
    RType'.interp (FreeAlg' natAlgSig) s :=
  cast (RType'.interp_isObj (FreeAlg' natAlgSig) hs).symm (natFreeAlgEquiv'.symm k)

/-- The numeric reading inverts the carrier-copy transport. -/
theorem objToNat'_objFromNat' {s : RType'} (hs : s.IsObj) (k : ℕ) :
    objToNat' hs (objFromNat' hs k) = k := by
  unfold objToNat' objFromNat'
  rw [cast_cast, cast_eq]
  exact natFreeAlgEquiv'.apply_symm_apply k

/-- The carrier-copy transport inverts the numeric reading. -/
theorem objFromNat'_objToNat' {s : RType'} (hs : s.IsObj)
    (x : RType'.interp (FreeAlg' natAlgSig) s) : objFromNat' hs (objToNat' hs x) = x := by
  unfold objToNat' objFromNat'
  rw [natFreeAlgEquiv'.symm_apply_apply, cast_cast, cast_eq]

/-- The carrier-copy transports of a natural at two primed object sorts are
heterogeneously equal: both are the numeral read through
`natFreeAlgEquiv'.symm`. -/
theorem objFromNat'_heq {s s' : RType'} (hs : s.IsObj) (hs' : s'.IsObj) (k : ℕ) :
    objFromNat' hs k ≍ objFromNat' hs' k :=
  (cast_heq _ _).trans (cast_heq _ _).symm

/-- The primed numeric reading is invariant under heterogeneous equality of the
values read: object sorts denote copies of the carrier, so the reading forgets
the copy. -/
theorem objToNat'_heq {s s' : RType'} (hs : s.IsObj) (hs' : s'.IsObj)
    {x : RType'.interp (FreeAlg' natAlgSig) s} {y : RType'.interp (FreeAlg' natAlgSig) s'}
    (h : x ≍ y) : objToNat' hs x = objToNat' hs' y :=
  congrArg natFreeAlgEquiv'
    (eq_of_heq ((cast_heq _ _).trans (h.trans (cast_heq _ _).symm)))

/-- The legacy numeric reading is invariant under heterogeneous equality of the
values read. -/
theorem objToNat_heq {s s' : RType} (hs : s.IsObj) (hs' : s'.IsObj)
    {x : RType.interp (FreeAlg natAlgSig) s} {y : RType.interp (FreeAlg natAlgSig) s'}
    (h : x ≍ y) : objToNat hs x = objToNat hs' y :=
  congrArg freeAlgToNat
    (eq_of_heq ((cast_heq _ _).trans (h.trans (cast_heq _ _).symm)))

/-- The carrier-copy transports of a natural at two object sorts agree across a
transport of the carrier copies. -/
theorem cast_objFromNat {s s' : RType} (hs : s.IsObj) (hs' : s'.IsObj)
    (h : RType.interp (FreeAlg natAlgSig) s = RType.interp (FreeAlg natAlgSig) s')
    (k : ℕ) : cast h (objFromNat hs k) = objFromNat hs' k := by
  unfold objFromNat
  rw [cast_cast]

/-- The primed numeric environment over an object-sort context: position `i`
carries the numeral of `v` at that position, transported into the object sort's
carrier copy. Mirror of the legacy `ramifiedEnv`. -/
def ramifiedEnv' {n : ℕ} (Γ' : ObjCtx' n) (v : Fin n → ℕ) :
    (standardModel (higherOrder' natAlgSig)).Env Γ'.toCtx :=
  fun i => objFromNat' (Γ'.toCtx_get_isObj i) (v (Fin.cast Γ'.toCtx_length i))

/-- The primed numeric denotation of a morphism between object-sort contexts:
build the environment from `v` through `objFromNat'`, evaluate by `Hom'.eval` at
the standard model, and read each output position back through `objToNat'`.
Mirror of the legacy `ramifiedDenotation`. -/
def ramifiedDenotation' {n m : ℕ} {Γ' : ObjCtx' n} {Δ' : ObjCtx' m}
    (g : Hom' (higherOrder' natAlgSig) (interpQuotRel' (higherOrder' natAlgSig))
      Γ'.toCtx Δ'.toCtx) :
    (Fin n → ℕ) → (Fin m → ℕ) :=
  fun v j =>
    objToNat' (Δ'.toCtx_get_isObj (Fin.cast (Δ'.toCtx_length).symm j))
      (g.eval (ramifiedEnv' Γ' v) (Fin.cast (Δ'.toCtx_length).symm j))

/-- The primed numeric denotation at a value and codomain position. -/
theorem ramifiedDenotation'_apply {n m : ℕ} {Γ' : ObjCtx' n} {Δ' : ObjCtx' m}
    (g : Hom' (higherOrder' natAlgSig) (interpQuotRel' (higherOrder' natAlgSig))
      Γ'.toCtx Δ'.toCtx) (v : Fin n → ℕ) (j : Fin m) :
    ramifiedDenotation' g v j
      = objToNat' (Δ'.toCtx_get_isObj (Fin.cast (Δ'.toCtx_length).symm j))
          (g.eval (ramifiedEnv' Γ' v) (Fin.cast (Δ'.toCtx_length).symm j)) :=
  rfl

/-- The primed numeric denotation of an identity morphism is the identity. -/
theorem ramifiedDenotation'_id {n : ℕ} (Γ' : ObjCtx' n) :
    ramifiedDenotation'
      (Hom'.id (higherOrder' natAlgSig) (interpQuotRel' (higherOrder' natAlgSig))
        Γ'.toCtx)
      = id := by
  funext v j
  rw [ramifiedDenotation'_apply, Hom'.eval_id]
  exact objToNat'_objFromNat' _ _

/-- The primed numeric denotation of a composite is the composition of the
primed numeric denotations (the composition law of standard-model
evaluation). -/
theorem ramifiedDenotation'_comp {n m k : ℕ}
    {Γ' : ObjCtx' n} {Δ' : ObjCtx' m} {Θ' : ObjCtx' k}
    (g : Hom' (higherOrder' natAlgSig) (interpQuotRel' (higherOrder' natAlgSig))
      Γ'.toCtx Δ'.toCtx)
    (h : Hom' (higherOrder' natAlgSig) (interpQuotRel' (higherOrder' natAlgSig))
      Δ'.toCtx Θ'.toCtx) :
    ramifiedDenotation' (g.comp h)
      = ramifiedDenotation' h ∘ ramifiedDenotation' g := by
  funext v j
  have hmid : ramifiedEnv' Δ' (ramifiedDenotation' g v) = g.eval (ramifiedEnv' Γ' v) := by
    funext i
    change objFromNat' (Δ'.toCtx_get_isObj i)
        (objToNat' (Δ'.toCtx_get_isObj i) (g.eval (ramifiedEnv' Γ' v) i))
      = g.eval (ramifiedEnv' Γ' v) i
    exact objFromNat'_objToNat' _ _
  change ramifiedDenotation' (g.comp h) v j
    = ramifiedDenotation' h (ramifiedDenotation' g v) j
  rw [ramifiedDenotation'_apply, ramifiedDenotation'_apply, Hom'.eval_comp, hmid]

/-- The bridge transport of a primed identity morphism is the identity
morphism. -/
theorem cast_hom'_id {P : Presentation} {r : QuotRel' P.sig} {A B : Ctx P.S}
    (hAB : A = B) (h : Hom' P r A A = Hom' P r B B) :
    cast h (Hom'.id P r A) = Hom'.id P r B := by
  subst hAB
  simp only [cast_eq]

/-- The bridge transport of a primed composite is the composite of the bridge
transports. -/
theorem cast_hom'_comp {P : Presentation} {r : QuotRel' P.sig}
    {A A' B B' C C' : Ctx P.S} (hA : A = A') (hB : B = B') (hC : C = C')
    (f : Hom' P r A B) (g : Hom' P r B C)
    (hac : Hom' P r A C = Hom' P r A' C') (hab : Hom' P r A B = Hom' P r A' B')
    (hbc : Hom' P r B C = Hom' P r B' C') :
    cast hac (Hom'.comp f g) = Hom'.comp (cast hab f) (cast hbc g) := by
  subst hA
  subst hB
  subst hC
  simp only [cast_eq]

/-- The bridge transport of a `SynCatFO'` morphism into a morphism between the
underlying contexts of the bridged object-sort contexts. Mirror of the legacy
`collapseHom`. -/
def collapseHom' {Γ' Δ' : SynCatFO'} (g : Γ' ⟶ Δ') :
    Hom' (higherOrder' natAlgSig) (interpQuotRel' (higherOrder' natAlgSig))
      (Γ'.toObjCtx'.2).toCtx (Δ'.toObjCtx'.2).toCtx :=
  cast (by rw [Γ'.toObjCtx'_toCtx, Δ'.toObjCtx'_toCtx]; rfl) g.hom

/-- The bridge transport of an identity `SynCatFO'` morphism is the identity. -/
theorem collapseHom'_id (Γ' : SynCatFO') :
    collapseHom' (𝟙 Γ')
      = Hom'.id (higherOrder' natAlgSig) (interpQuotRel' (higherOrder' natAlgSig))
          (Γ'.toObjCtx'.2).toCtx := by
  unfold collapseHom'
  rw [CategoryTheory.ObjectProperty.FullSubcategory.id_hom]
  exact cast_hom'_id Γ'.toObjCtx'_toCtx.symm _

/-- The bridge transport of a composite `SynCatFO'` morphism is the
composite. -/
theorem collapseHom'_comp {Γ' Δ' Θ' : SynCatFO'} (g : Γ' ⟶ Δ') (h : Δ' ⟶ Θ') :
    collapseHom' (g ≫ h) = (collapseHom' g).comp (collapseHom' h) := by
  unfold collapseHom'
  rw [CategoryTheory.ObjectProperty.FullSubcategory.comp_hom]
  exact cast_hom'_comp Γ'.toObjCtx'_toCtx.symm Δ'.toObjCtx'_toCtx.symm
    Θ'.toObjCtx'_toCtx.symm g.hom h.hom _ _ _

/-- The primed numeric denotation of a `SynCatFO'` morphism, read through the
bridge `SynCatFO'.toObjCtx'`. Mirror of the legacy `collapseDenotation`. -/
def collapseDenotation' {Γ' Δ' : SynCatFO'} (g : Γ' ⟶ Δ') :
    (Fin (objLen' Γ') → ℕ) → (Fin (objLen' Δ') → ℕ) :=
  ramifiedDenotation' (collapseHom' g)

/-- The primed collapse denotation of an identity morphism is the identity. -/
theorem collapseDenotation'_id (Γ' : SynCatFO') : collapseDenotation' (𝟙 Γ') = id := by
  unfold collapseDenotation'
  rw [collapseHom'_id]
  exact ramifiedDenotation'_id Γ'.toObjCtx'.2

/-- The primed collapse denotation of a composite is the composition of the
primed collapse denotations. -/
theorem collapseDenotation'_comp {Γ' Δ' Θ' : SynCatFO'} (g : Γ' ⟶ Δ') (h : Δ' ⟶ Θ') :
    collapseDenotation' (g ≫ h) = collapseDenotation' h ∘ collapseDenotation' g := by
  unfold collapseDenotation'
  rw [collapseHom'_comp]
  exact ramifiedDenotation'_comp (collapseHom' g) (collapseHom' h)

/-- Evaluation of a context-transported legacy morphism agrees, heterogeneously,
with evaluation of the untransported morphism at the corresponding environment
and codomain position. -/
theorem Hom.eval_heq_cast {P : Presentation} {A A' B B' : Ctx P.S}
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

/-- Evaluation of a context-transported primed morphism agrees, heterogeneously,
with evaluation of the untransported morphism at the corresponding environment
and codomain position. -/
theorem Hom'.eval_heq_cast {P : Presentation} {A A' B B' : Ctx P.S}
    (hA : A = A') (hB : B = B')
    (h : Hom' P (interpQuotRel' P) A B = Hom' P (interpQuotRel' P) A' B')
    (f : Hom' P (interpQuotRel' P) A B)
    (ρ : (standardModel P).Env A) (ρ' : (standardModel P).Env A') (hρ : ρ ≍ ρ')
    (i : Fin B.length) (i' : Fin B'.length) (hi : i ≍ i') :
    (cast h f).eval ρ' i' ≍ f.eval ρ i := by
  subst hA
  subst hB
  obtain rfl := eq_of_heq hρ
  obtain rfl := eq_of_heq hi
  rw [cast_eq]

/-- The transport-free reading of the legacy collapse denotation: the numeric
reading of the underlying hom's evaluation at the numeric environment over the
underlying context. -/
theorem collapseDenotation_apply {Γ Δ : SynCatFO} (g : Γ ⟶ Δ)
    (v : Fin (objLen Γ) → ℕ) (j : Fin (objLen Δ)) :
    collapseDenotation g v j
      = objToNat (Δ.property j)
          (Hom.eval g.hom (fun i => objFromNat (Γ.property i) (v i)) j) := by
  refine Eq.trans (ramifiedDenotation_apply (collapseHom g) v j) ?_
  refine objToNat_heq _ _ ?_
  refine Hom.eval_heq_cast Γ.toObjCtx_toCtx.symm Δ.toObjCtx_toCtx.symm _ g.hom
    (fun i => objFromNat (Γ.property i) (v i)) (ramifiedEnv Γ.toObjCtx.2 v) ?_ j _ ?_
  · refine Function.hfunext (congrArg Fin (congrArg List.length Γ.toObjCtx_toCtx.symm)) ?_
    intro a a' haa
    have hval : a.val = a'.val :=
      (Fin.heq_ext_iff (congrArg List.length Γ.toObjCtx_toCtx.symm)).mp haa
    have hv : v a = v (Fin.cast (Γ.toObjCtx.2).toCtx_length a') := congrArg v (Fin.ext hval)
    rw [hv]
    exact objFromNat_heq _ _ _
  · exact (Fin.heq_ext_iff (congrArg List.length Δ.toObjCtx_toCtx.symm)).mpr rfl

/-- The transport-free reading of the primed collapse denotation. -/
theorem collapseDenotation'_apply {Γ' Δ' : SynCatFO'} (g : Γ' ⟶ Δ')
    (v : Fin (objLen' Γ') → ℕ) (j : Fin (objLen' Δ')) :
    collapseDenotation' g v j
      = objToNat' (Δ'.property j)
          (Hom'.eval g.hom (fun i => objFromNat' (Γ'.property i) (v i)) j) := by
  refine Eq.trans (ramifiedDenotation'_apply (collapseHom' g) v j) ?_
  refine objToNat'_heq _ _ ?_
  refine Hom'.eval_heq_cast Γ'.toObjCtx'_toCtx.symm Δ'.toObjCtx'_toCtx.symm _ g.hom
    (fun i => objFromNat' (Γ'.property i) (v i)) (ramifiedEnv' Γ'.toObjCtx'.2 v) ?_ j _ ?_
  · refine Function.hfunext (congrArg Fin (congrArg List.length Γ'.toObjCtx'_toCtx.symm)) ?_
    intro a a' haa
    have hval : a.val = a'.val :=
      (Fin.heq_ext_iff (congrArg List.length Γ'.toObjCtx'_toCtx.symm)).mp haa
    have hv : v a = v (Fin.cast (Γ'.toObjCtx'.2).toCtx_length a') := congrArg v (Fin.ext hval)
    rw [hv]
    exact objFromNat'_heq _ _ _
  · exact (Fin.heq_ext_iff (congrArg List.length Δ'.toObjCtx'_toCtx.symm)).mpr rfl

/-- The object property transfers forward along the bridge: the image of a
primed object-sort context is a legacy object-sort context, sortwise by
`rTypeSliceEquiv_isObj`. -/
theorem isObjCtx_map {Γ' : Ctx RType'} (h : isObjCtx' Γ') :
    isObjCtx (Γ'.map rTypeSliceEquiv) := by
  intro i
  have hi := h (Fin.cast (List.length_map ..) i)
  rw [rTypeSliceEquiv_isObj] at hi
  refine Eq.mpr (congrArg RType.IsObj ?_) hi
  simp only [List.get_eq_getElem, List.getElem_map]
  rfl

/-- The object property transfers backward along the bridge: the preimage of a
legacy object-sort context is a primed object-sort context. -/
theorem isObjCtx'_map_symm {Δ : Ctx RType} (h : isObjCtx Δ) :
    isObjCtx' (Δ.map rTypeSliceEquiv.symm) := by
  intro i
  have key : RType'.IsObj (rTypeSliceEquiv.symm (Δ.get (Fin.cast (List.length_map ..) i))) := by
    rw [rTypeSliceEquiv_isObj, Equiv.apply_symm_apply]
    exact h _
  refine Eq.mpr (congrArg RType'.IsObj ?_) key
  simp only [List.get_eq_getElem, List.getElem_map]
  rfl

/-- The restriction of `rmRecCatSliceEquiv natAlgSig` to the first-order full
subcategories: the functor and inverse are the lifts of the composites with the
inclusions, their object properties supplied by the sortwise correspondences
`isObjCtx_map` and `isObjCtx'_map_symm`, and the unit and counit are the
preimages of the parent equivalence's unit and counit under the fully faithful
inclusions. -/
def synCatFOSliceEquiv : SynCatFO' ≌ SynCatFO where
  functor := isObjCtx.lift (isObjCtx'.ι ⋙ (rmRecCatSliceEquiv natAlgSig).functor)
    (fun Γ' => isObjCtx_map Γ'.property)
  inverse := isObjCtx'.lift (isObjCtx.ι ⋙ (rmRecCatSliceEquiv natAlgSig).inverse)
    (fun Δ => isObjCtx'_map_symm Δ.property)
  unitIso := (isObjCtx'.fullyFaithfulι.whiskeringRight _).preimageIso
    (isObjCtx'.ι.isoWhiskerLeft (rmRecCatSliceEquiv natAlgSig).unitIso)
  counitIso := (isObjCtx.fullyFaithfulι.whiskeringRight _).preimageIso
    (isObjCtx.ι.isoWhiskerLeft (rmRecCatSliceEquiv natAlgSig).counitIso)
  functor_unitIso_comp X :=
    ObjectProperty.hom_ext _ ((rmRecCatSliceEquiv natAlgSig).functor_unit_comp X.obj)

/-- Evaluation of a translated hom at the term layer is evaluation of the
original: the bridge equivalence `tmSliceEquiv` preserves standard-model
evaluation componentwise. -/
theorem synHomMap_eval (P : Presentation) {Γ Δ : Ctx P.S}
    (f : Hom' P (interpQuotRel' P) Γ Δ) (ρ : (standardModel P).Env Γ) :
    Hom.eval (synHomMap P Γ Δ f) ρ = Hom'.eval f ρ := by
  induction f using Quotient.ind with
  | _ f' => exact funext fun i => tmSliceEquiv_eval _ ρ (f' i)

/-- Evaluation of the image of a primed hom under the phase's central
equivalence: the presentation-level environment transport conjugates primed
evaluation. -/
theorem rmRecCatSliceEquiv_map_eval (A : AlgSig) {Γ' Δ' : RMRecCat' A} (f : Γ' ⟶ Δ')
    (ρ : (standardModel (higherOrder A)).Env ((rmRecCatSliceEquiv A).functor.obj Γ')) :
    Hom.eval ((rmRecCatSliceEquiv A).functor.map f) ρ
      = (higherOrderPresEquiv A).mapEnv
          (Hom'.eval f ((higherOrderPresEquiv A).unmapEnv ρ)) := by
  refine Eq.trans ((higherOrderPresEquiv A).mapHom_eval
    ((synCatSliceEquiv (higherOrder' A)).functor.map f) ρ) ?_
  exact congrArg (higherOrderPresEquiv A).mapEnv (synHomMap_eval (higherOrder' A) f _)

/-- The numeric readings agree across the carrier bridge: the legacy reading of
the bridge image of an object-sort value is the primed reading of the value
(Leivant III section 2.7). -/
theorem objToNat_carrierSliceEquiv {t' : RType'} (h : t'.IsObj)
    (hL : RType.IsObj (rTypeSliceEquiv t')) (x : RType'.interp (FreeAlg' natAlgSig) t') :
    objToNat hL (carrierSliceEquiv natAlgSig t' x) = objToNat' h x := by
  unfold objToNat objToNat'
  rw [carrierSliceEquiv_isObj h x, natFreeAlgEquiv'_slice, Equiv.trans_apply,
    natFreeAlgEquiv_apply]

/-- The carrier-copy transports agree across the carrier bridge: the bridge
image of the primed transport of a natural is the legacy transport. -/
theorem carrierSliceEquiv_objFromNat' {t' : RType'} (h : t'.IsObj)
    (hL : RType.IsObj (rTypeSliceEquiv t')) (k : ℕ) :
    carrierSliceEquiv natAlgSig t' (objFromNat' h k) = objFromNat hL k := by
  refine (cast_inj (RType.interp_isObj (FreeAlg natAlgSig) hL)).mp ?_
  refine Eq.trans (carrierSliceEquiv_isObj h (objFromNat' h k)) ?_
  have hx : cast (RType'.interp_isObj (FreeAlg' natAlgSig) h) (objFromNat' h k)
      = natFreeAlgEquiv'.symm k := by
    unfold objFromNat'
    rw [cast_cast, cast_eq]
  have hy : cast (RType.interp_isObj (FreeAlg natAlgSig) hL) (objFromNat hL k)
      = natToFreeAlg k := by
    unfold objFromNat
    rw [cast_cast, cast_eq]
  rw [hx, hy]
  exact (freeAlgSliceEquiv natAlgSig).apply_symm_apply (natToFreeAlg k)

/-- The arity identification across the restriction equivalence: the transported
object has the same length. -/
theorem objLen_functor_obj (Γ' : SynCatFO') :
    objLen' Γ' = objLen (synCatFOSliceEquiv.functor.obj Γ') :=
  (List.length_map ..).symm

/-- The legacy numeric reading of a transported environment at a codomain
position is the primed numeric reading at the corresponding position. -/
theorem objToNat_mapEnv {Δ' : SynCatFO'}
    (u : (standardModel (higherOrder' natAlgSig)).Env Δ'.obj)
    (j : Fin (objLen (synCatFOSliceEquiv.functor.obj Δ'))) :
    objToNat ((synCatFOSliceEquiv.functor.obj Δ').property j)
        ((higherOrderPresEquiv natAlgSig).mapEnv u j)
      = objToNat' (Δ'.property (Fin.cast (objLen_functor_obj Δ').symm j))
          (u (Fin.cast (objLen_functor_obj Δ').symm j)) := by
  have hL : RType.IsObj
      (rTypeSliceEquiv (Δ'.obj.get (Fin.cast (objLen_functor_obj Δ').symm j))) :=
    cast (rTypeSliceEquiv_isObj _) (Δ'.property (Fin.cast (objLen_functor_obj Δ').symm j))
  unfold PresentationEquiv.mapEnv
  refine Eq.trans (objToNat_heq _ hL (cast_heq _ _)) ?_
  exact objToNat_carrierSliceEquiv _ hL _

/-- The inverse environment transport of a legacy numeric environment is the
primed numeric environment of the same numeric input. -/
theorem unmapEnv_objFromNat {Γ' : SynCatFO'}
    (v : Fin (objLen (synCatFOSliceEquiv.functor.obj Γ')) → ℕ) :
    (higherOrderPresEquiv natAlgSig).unmapEnv
        (fun i => objFromNat ((synCatFOSliceEquiv.functor.obj Γ').property i) (v i))
      = fun i => objFromNat' (Γ'.property i) (v (Fin.cast (objLen_functor_obj Γ') i)) := by
  funext i
  have hL : RType.IsObj (rTypeSliceEquiv (Γ'.obj.get i)) :=
    cast (rTypeSliceEquiv_isObj _) (Γ'.property i)
  unfold PresentationEquiv.unmapEnv
  refine ((higherOrderPresEquiv natAlgSig).carrierEquiv (Γ'.obj.get i)).symm_apply_eq.mpr ?_
  exact (cast_objFromNat _ hL _ _).trans
    (carrierSliceEquiv_objFromNat' (Γ'.property i) hL _).symm

/-- The collapse denotations agree across the restriction equivalence: the
legacy collapse denotation of the image of a primed first-order morphism is the
primed collapse denotation, read along the arity identifications. -/
theorem collapseDenotation_sliceEquiv {Γ' Δ' : SynCatFO'} (g' : Γ' ⟶ Δ') :
    collapseDenotation (synCatFOSliceEquiv.functor.map g')
      = arityCongr (objLen_functor_obj Γ') (objLen_functor_obj Δ')
          (collapseDenotation' g') := by
  funext v j
  rw [collapseDenotation_apply, arityCongr_apply, collapseDenotation'_apply]
  have hmap : Hom.eval (synCatFOSliceEquiv.functor.map g').hom
        (fun i => objFromNat ((synCatFOSliceEquiv.functor.obj Γ').property i) (v i))
      = (higherOrderPresEquiv natAlgSig).mapEnv (Hom'.eval g'.hom
          ((higherOrderPresEquiv natAlgSig).unmapEnv
            (fun i => objFromNat ((synCatFOSliceEquiv.functor.obj Γ').property i) (v i)))) :=
    rmRecCatSliceEquiv_map_eval natAlgSig g'.hom _
  refine Eq.trans (congrArg (objToNat
    ((synCatFOSliceEquiv.functor.obj Δ').property j)) (congrFun hmap j)) ?_
  refine Eq.trans (objToNat_mapEnv _ j) ?_
  exact congrArg (fun w => objToNat'
      (Δ'.property (Fin.cast (objLen_functor_obj Δ').symm j))
      (Hom'.eval g'.hom w (Fin.cast (objLen_functor_obj Δ').symm j)))
    (unmapEnv_objFromNat v)

end GebLean.Ramified.Polynomial
