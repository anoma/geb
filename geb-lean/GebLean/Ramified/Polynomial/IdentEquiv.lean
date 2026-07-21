import GebLean.Ramified.Polynomial.Ident
import GebLean.Ramified.Polynomial.Term
import GebLean.Ramified.HigherOrder
import GebLean.Ramified.SigEquiv
import GebLean.Ramified.PresentationEquiv
import GebLean.SliceW.Reindex
import GebLean.SliceW.Iso
import GebLean.PolyBridge.WEquiv
import Mathlib.Logic.Equiv.List
import Mathlib.Logic.Equiv.Basic

/-!
# The identifier bridge equivalence

The syntactic bridge relating the primed schema identifiers `RIdent'`
(`GebLean/Ramified/Polynomial/Ident.lean`), realized on the vendored slice
`W`-type stack, to the legacy schema identifiers `RIdent`
(`GebLean/Ramified/HigherOrder.lean`), realized on the `PolyFix` W-type. The
two identifier layers present the same schema-generated identifiers over a
base algebra; the bridge `identSliceEquiv` is that identification, fibrewise
over the index `(Γ', τ')` and mapped across `rTypeSliceEquiv`.

The equivalence is assembled the Phase B way (the `polyFreeMSliceEquiv`
pattern of `GebLean/PolyBridge/FreeMEquiv.lean`): a container isomorphism
`identEndoIso` of the two identifier signature endofunctors — its shape
equivalence the sigma congruence over the schema-former equivalences
`identShapeEquiv`, its positions the identity on holes and constructor
labels — composed with the base change `SlicePFunctor.reindex` along the
context equivalence `identCtxEquiv` and the initial-algebra comparison
`polyFixSliceEquiv`. The schema-former equivalence `defnShapeEquiv` carries a
defining term across the signature isomorphism `defnSigEquiv` and the term
translations `tmSliceEquiv` (Phase B) and `SortedSigEquiv.tmEquiv` (Task C.8).

## Main definitions

* `identCtxEquiv` — the index equivalence `List RType' × RType' ≃
  List RType × RType`.
* `defnSigEquiv` — the signature isomorphism of the base signatures of an
  explicit definition's body.
* `defnShapeEquiv`, `mrecShapeEquiv`, `frecShapeEquiv` — the schema-former
  data equivalences.
* `identShapeEquiv` — the identifier shape-type equivalence.
* `identEndoIso` — the container isomorphism of the identifier signature
  endofunctors.
* `identSliceEquiv` — the identifier bridge equivalence
  `RIdent' A Γ' τ' ≃ RIdent A (Γ'.map rTypeSliceEquiv) (rTypeSliceEquiv τ')`.
* `RIdent.reindCtx` — the transport of a legacy identifier along a
  propositional context equality.
* `envSlice` — the environment transport across the carrier bridge.
* `envCtxCast` — the transport of a legacy environment along a context
  equality.
* `EnvAgree` — pointwise agreement of a primed environment with a legacy
  environment across the carrier bridge.
* `defnPres'`, `defnPres`, `defnPresEquiv` — the two defn-body presentations
  and the presentation equivalence between them.

## Main statements

* `identSliceEquiv_defn`, `identSliceEquiv_mrec`, `identSliceEquiv_frec` — the
  former naturality of the bridge equivalence.
* `carrierSliceEquiv_arrow`, `carrierSliceEquiv_o`, `carrierSliceEquiv_omega`
  — the carrier bridge at an arrow sort and at the two object sorts.
* `curryInterp'_agree` — the currying of a denotation agrees with the legacy
  currying across the bridge.
* `stdConstructorInterp_agree` — the constructor interpretation agrees across
  the bridge.
* `defnModel_agree` — the defn-body evaluation agreement.
* `RIdent'.induction` — fibrewise structural induction for the primed
  identifiers.
* `RIdent.interp_defn`, `RIdent.interp_mrec`, `RIdent.interp_frec`,
  `RIdent.interp_reindCtx` — the computation rules of the legacy identifier
  denotation.
* `freeAlgSliceEquiv_recurse_map` — the paramorphism agreement across the
  bridge under a change of result carrier.
* `envAgree_envHead`, `envAgree_childEnv`, `envLast_agree` — the
  recurrence-context environment matchings.
* `identSliceEquiv_interp` — the identifier denotation agrees across the
  bridge.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher
type recurrence and elementary complexity", Annals of Pure and Applied Logic
96 (1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`, section 2.3.

N. Gambino and J. Kock, "Polynomial functors and polynomial monads",
Mathematical Proceedings of the Cambridge Philosophical Society 154 (2013)
153-192, DOI `10.1017/S0305004112000394`, base change (section 1).

D. Sannella, A. Tarlecki, "Foundations of Algebraic Specification and Formal
Software Development", Springer, 2012, DOI `10.1007/978-3-642-17336-3`,
Chapter 1 (signature morphisms and reducts).

## Tags

ramified recurrence, higher type, schema identifier, signature isomorphism,
W-type, base change, slice category, bridge equivalence
-/

namespace GebLean.Ramified.Polynomial

open GebLean.Ramified GebLean.PolyBridge SlicePFunctor

/-- The index equivalence between the primed and legacy identifier index
types (context, result sort): the product of the pointwise context
equivalence `List.map rTypeSliceEquiv` and `rTypeSliceEquiv`. -/
def identCtxEquiv : List RType' × RType' ≃ List RType × RType :=
  Equiv.prodCongr (Equiv.listEquivOfEquiv rTypeSliceEquiv) rTypeSliceEquiv

/-- The signature isomorphism between the primed and legacy base signatures
of an explicit definition's body: `rTypeSliceEquiv` on sorts, the summand-wise
congruence on operations (the object-sort subtype congruence and the
application, hole, and hole-constant congruences), with arities and result
sorts transported by `List.map_replicate`, `rTypeSliceEquiv_arrow`, and
`rTypeSliceEquiv_curried`. -/
def defnSigEquiv (A : AlgSig) (n : Nat) (h : Fin n → List RType' × RType') :
    SortedSigEquiv (defnSig' A n h) (defnSig A n (fun j => identCtxEquiv (h j))) where
  sortEquiv := rTypeSliceEquiv
  opEquiv :=
    Equiv.sumCongr (Equiv.sumCongr (Equiv.sumCongr
      (Equiv.prodCongr
        (Equiv.subtypeEquiv rTypeSliceEquiv (fun a => Iff.of_eq (rTypeSliceEquiv_isObj a)))
        (Equiv.refl A.B))
      (Equiv.prodCongr rTypeSliceEquiv rTypeSliceEquiv)) (Equiv.refl (Fin n))) (Equiv.refl (Fin n))
  arity_comm := by
    rintro (((c | a) | j) | j)
    · change List.replicate (A.ar c.2) (rTypeSliceEquiv c.1.val)
        = List.map rTypeSliceEquiv (List.replicate (A.ar c.2) c.1.val)
      exact List.map_replicate.symm
    · change [RType.arrow (rTypeSliceEquiv a.1) (rTypeSliceEquiv a.2), rTypeSliceEquiv a.1]
        = [rTypeSliceEquiv (RType'.arrow a.1 a.2), rTypeSliceEquiv a.1]
      rw [rTypeSliceEquiv_arrow]
    · rfl
    · rfl
  result_comm := by
    rintro (((c | a) | j) | j)
    · rfl
    · rfl
    · rfl
    · exact (rTypeSliceEquiv_curried (h j).1 (h j).2).symm

/-- The explicit-definition data as a sigma of its number of holes, hole
indices, and body. -/
def defnShapeSigma' (A : AlgSig) (Γ' : List RType') (τ' : RType') :
    DefnShape' A Γ' τ' ≃
      Σ n : Nat, Σ hi : Fin n → List RType' × RType', Tm' (defnSig' A n hi) Γ' τ' where
  toFun d := ⟨d.numHoles, d.holeIdx', d.body⟩
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The legacy explicit-definition data as a sigma of its number of holes,
hole indices, and body. -/
def defnShapeSigma (A : AlgSig) (Γ : List RType) (τ : RType) :
    DefnShape A Γ τ ≃
      Σ n : Nat, Σ hi : Fin n → List RType × RType, Tm (defnSig A n hi) Γ τ where
  toFun d := ⟨d.numHoles, d.holeIdx, d.body⟩
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The explicit-definition data equivalence: the number of holes and the hole
indices transported pointwise, and the defining term carried across the
signature isomorphism `defnSigEquiv` by `tmSliceEquiv` and
`SortedSigEquiv.tmEquiv`. -/
def defnShapeEquiv (A : AlgSig) (Γ' : List RType') (τ' : RType') :
    DefnShape' A Γ' τ' ≃ DefnShape A (Γ'.map rTypeSliceEquiv) (rTypeSliceEquiv τ') :=
  (defnShapeSigma' A Γ' τ').trans
    ((Equiv.sigmaCongr (Equiv.refl Nat) (fun n =>
      Equiv.sigmaCongr (Equiv.piCongrRight (fun _ => identCtxEquiv)) (fun hi =>
        (tmSliceEquiv Γ' τ').trans ((defnSigEquiv A n hi).tmEquiv Γ' τ')))).trans
      (defnShapeSigma A (Γ'.map rTypeSliceEquiv) (rTypeSliceEquiv τ')).symm)

/-- The monotonic-recurrence data as the subtype of recurrence parameters. -/
def mrecShapeSubtype' (A : AlgSig) (Γ' : List RType') (τ' : RType') :
    MrecShape' A Γ' τ' ≃ { params : List RType' // Γ' = params ++ [RType'.omega τ'] } where
  toFun m := ⟨m.params, m.hΓ⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The legacy monotonic-recurrence data as the subtype of recurrence
parameters. -/
def mrecShapeSubtype (A : AlgSig) (Γ : List RType) (τ : RType) :
    MrecShape A Γ τ ≃ { params : List RType // Γ = params ++ [RType.omega τ] } where
  toFun m := ⟨m.params, m.hΓ⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The monotonic-recurrence data equivalence: the recurrence parameters
transported pointwise, the context equation transported by `List.map_append`
and `rTypeSliceEquiv_omega`. -/
def mrecShapeEquiv (A : AlgSig) (Γ' : List RType') (τ' : RType') :
    MrecShape' A Γ' τ' ≃ MrecShape A (Γ'.map rTypeSliceEquiv) (rTypeSliceEquiv τ') :=
  (mrecShapeSubtype' A Γ' τ').trans
    ((Equiv.subtypeEquiv (Equiv.listEquivOfEquiv rTypeSliceEquiv) (fun params => by
      rw [← (Equiv.listEquivOfEquiv rTypeSliceEquiv).apply_eq_iff_eq
        (x := Γ') (y := params ++ [RType'.omega τ'])]
      change List.map rTypeSliceEquiv Γ' = List.map rTypeSliceEquiv (params ++ [RType'.omega τ']) ↔
        List.map rTypeSliceEquiv Γ' =
          List.map rTypeSliceEquiv params ++ [RType.omega (rTypeSliceEquiv τ')]
      rw [List.map_append, List.map_singleton, rTypeSliceEquiv_omega])).trans
      (mrecShapeSubtype A (Γ'.map rTypeSliceEquiv) (rTypeSliceEquiv τ')).symm)

/-- The flat-recurrence data as the subtype of recurrence parameters. -/
def frecShapeSubtype' (A : AlgSig) (Γ' : List RType') (τ' : RType') :
    FrecShape' A Γ' τ' ≃ { params : List RType' // Γ' = params ++ [RType'.o] } where
  toFun fr := ⟨fr.params, fr.hΓ⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The legacy flat-recurrence data as the subtype of recurrence parameters. -/
def frecShapeSubtype (A : AlgSig) (Γ : List RType) (τ : RType) :
    FrecShape A Γ τ ≃ { params : List RType // Γ = params ++ [RType.o] } where
  toFun fr := ⟨fr.params, fr.hΓ⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The flat-recurrence data equivalence: the recurrence parameters
transported pointwise, the context equation transported by `List.map_append`
and `rTypeSliceEquiv_o`. -/
def frecShapeEquiv (A : AlgSig) (Γ' : List RType') (τ' : RType') :
    FrecShape' A Γ' τ' ≃ FrecShape A (Γ'.map rTypeSliceEquiv) (rTypeSliceEquiv τ') :=
  (frecShapeSubtype' A Γ' τ').trans
    ((Equiv.subtypeEquiv (Equiv.listEquivOfEquiv rTypeSliceEquiv) (fun params => by
      rw [← (Equiv.listEquivOfEquiv rTypeSliceEquiv).apply_eq_iff_eq
        (x := Γ') (y := params ++ [RType'.o])]
      change List.map rTypeSliceEquiv Γ' = List.map rTypeSliceEquiv (params ++ [RType'.o]) ↔
        List.map rTypeSliceEquiv Γ' = List.map rTypeSliceEquiv params ++ [RType.o]
      rw [List.map_append, List.map_singleton, rTypeSliceEquiv_o])).trans
      (frecShapeSubtype A (Γ'.map rTypeSliceEquiv) (rTypeSliceEquiv τ')).symm)

/-- The identifier shape-type equivalence: the sum of the three schema-former
data equivalences. -/
def identShapeEquiv (A : AlgSig) (Γ' : List RType') (τ' : RType') :
    IdentShape' A Γ' τ' ≃ IdentShape A (Γ'.map rTypeSliceEquiv) (rTypeSliceEquiv τ') :=
  Equiv.sumCongr (defnShapeEquiv A Γ' τ')
    (Equiv.sumCongr (mrecShapeEquiv A Γ' τ') (frecShapeEquiv A Γ' τ'))

/-- The container isomorphism of the identifier signature endofunctors: the
primed identifier endofunctor and the base change of the legacy identifier
endofunctor along `identCtxEquiv.symm`. Shapes are matched by the sigma
congruence over `identShapeEquiv`; positions are the identity on holes and on
constructor labels; the shape-output and direction-input maps agree by the
`identCtxEquiv` round trip and the translation of `identTarget`. -/
def identEndoIso (A : AlgSig) :
    SlicePFunctor.Iso (toSlice (identEndo' A))
      (SlicePFunctor.reindex identCtxEquiv.symm (toSlice (identEndo A))) where
  shapeEquiv := Equiv.sigmaCongr identCtxEquiv (fun x => identShapeEquiv A x.1 x.2)
  posEquiv := fun a => match a with
    | ⟨_, Sum.inl _⟩ => Equiv.refl _
    | ⟨_, Sum.inr (Sum.inl _)⟩ => Equiv.refl _
    | ⟨_, Sum.inr (Sum.inr _)⟩ => Equiv.refl _
  q_comm := fun a => by
    obtain ⟨x, _s⟩ := a
    exact identCtxEquiv.symm_apply_apply x
  r_comm := fun a b => match a, b with
    | ⟨_x, Sum.inl d⟩, b => identCtxEquiv.symm_apply_apply (d.holeIdx' b)
    | ⟨x, Sum.inr (Sum.inl m)⟩, b => by
        change identCtxEquiv.symm
            (List.map rTypeSliceEquiv m.params
              ++ List.replicate (A.ar b) (rTypeSliceEquiv x.2), rTypeSliceEquiv x.2)
          = (m.params ++ List.replicate (A.ar b) x.2, x.2)
        rw [Equiv.symm_apply_eq]
        refine Prod.ext ?_ rfl
        change List.map rTypeSliceEquiv m.params ++ List.replicate (A.ar b) (rTypeSliceEquiv x.2)
          = List.map rTypeSliceEquiv (m.params ++ List.replicate (A.ar b) x.2)
        rw [List.map_append, List.map_replicate]
    | ⟨x, Sum.inr (Sum.inr fr)⟩, b => by
        change identCtxEquiv.symm
            (List.map rTypeSliceEquiv fr.params
              ++ List.replicate (A.ar b) RType.o, rTypeSliceEquiv x.2)
          = (fr.params ++ List.replicate (A.ar b) RType'.o, x.2)
        rw [Equiv.symm_apply_eq]
        refine Prod.ext ?_ rfl
        change List.map rTypeSliceEquiv fr.params ++ List.replicate (A.ar b) RType.o
          = List.map rTypeSliceEquiv (fr.params ++ List.replicate (A.ar b) RType'.o)
        rw [List.map_append, List.map_replicate, rTypeSliceEquiv_o]

/-- The identifier bridge equivalence: the primed schema identifiers over the
index `(Γ', τ')` are equivalent to the legacy schema identifiers over the
translated index. The fiberwise composite of the container isomorphism
`identEndoIso`, the base change `SlicePFunctor.reindex.wEquivFiber`, and the
initial-algebra comparison `polyFixSliceEquiv`. -/
def identSliceEquiv {A : AlgSig} {Γ' : List RType'} {τ' : RType'} :
    RIdent' A Γ' τ' ≃ RIdent A (Γ'.map rTypeSliceEquiv) (rTypeSliceEquiv τ') :=
  ((identEndoIso A).wEquivFiber (Γ', τ')).trans
    ((SlicePFunctor.reindex.wEquivFiber identCtxEquiv.symm (toSlice (identEndo A))
      (Γ', τ')).symm.trans
      (polyFixSliceEquiv (identEndo A) (identCtxEquiv (Γ', τ'))).symm)

/-- The underlying tree of the bridge equivalence applied to an identifier is
the image of the identifier's tree under the container isomorphism: the
identity witnessing that `identSliceEquiv` composes `polyFixSliceEquiv` and the
base change with `identEndoIso`. -/
theorem identSliceEquiv_apply_val {A : AlgSig} {Γ' : List RType'} {τ' : RType'}
    (X : RIdent' A Γ' τ') :
    ((polyFixSliceEquiv (identEndo A) (identCtxEquiv (Γ', τ')) (identSliceEquiv X)).1).1
      = ((identEndoIso A).wMap X.1).1 := by
  have h : polyFixSliceEquiv (identEndo A) (identCtxEquiv (Γ', τ')) (identSliceEquiv X)
      = (SlicePFunctor.reindex.wEquivFiber identCtxEquiv.symm (toSlice (identEndo A))
          (Γ', τ')).symm ((identEndoIso A).wEquivFiber (Γ', τ') X) :=
    Equiv.apply_symm_apply _ _
  rw [h]
  rfl

/-- Former naturality at an explicit definition. -/
theorem identSliceEquiv_defn {A : AlgSig} {Γ' : List RType'} {τ' : RType'}
    (d : DefnShape' A Γ' τ')
    (children : (j : Fin d.numHoles) → RIdent' A (d.holeIdx' j).1 (d.holeIdx' j).2) :
    identSliceEquiv (RIdent'.defn d children)
      = RIdent.defn (defnShapeEquiv A Γ' τ' d) (fun j => identSliceEquiv (children j)) := by
  have key :
      (SlicePFunctor.reindex.wEquivFiber identCtxEquiv.symm (toSlice (identEndo A))
        (Γ', τ')).symm ((identEndoIso A).wEquivFiber (Γ', τ') (RIdent'.defn d children))
      = polyFixSliceEquiv (identEndo A) (identCtxEquiv (Γ', τ'))
          (RIdent.defn (defnShapeEquiv A Γ' τ' d) (fun j => identSliceEquiv (children j))) := by
    apply Subtype.ext
    change (SlicePFunctor.reindex.wEquiv identCtxEquiv.symm (toSlice (identEndo A))).symm
        ((identEndoIso A).wMap (RIdent'.defn d children).1)
      = (polyFixSliceEquiv (identEndo A) (identCtxEquiv (Γ', τ'))
          (RIdent.defn (defnShapeEquiv A Γ' τ' d) (fun j => identSliceEquiv (children j)))).1
    rw [RIdent'.val_defn, SlicePFunctor.Iso.wMap_mk]
    apply Subtype.ext
    refine congrArg (WType.mk _) ?_
    funext b'
    exact (identSliceEquiv_apply_val (children b')).symm
  have h1 : identSliceEquiv (RIdent'.defn d children)
      = (polyFixSliceEquiv (identEndo A) (identCtxEquiv (Γ', τ'))).symm
          ((SlicePFunctor.reindex.wEquivFiber identCtxEquiv.symm (toSlice (identEndo A))
            (Γ', τ')).symm ((identEndoIso A).wEquivFiber (Γ', τ') (RIdent'.defn d children))) := rfl
  rw [h1, key]
  exact Equiv.symm_apply_apply _ _

/-- The transport of a legacy identifier along a propositional context
equality. The recurrence formers `RIdent.mrec` / `RIdent.frec` sit at the
concatenated legacy context, while the bridge equivalence lands at the mapped
primed context; the two are propositionally equal, and this transport carries
the former naturality statements across that equality. -/
def _root_.GebLean.Ramified.RIdent.reindCtx {A : AlgSig} {Γ Δ : List RType} {τ : RType}
    (h : Γ = Δ) (f : RIdent A Γ τ) : RIdent A Δ τ :=
  h ▸ f

/-- `RIdent.reindCtx` at a reflexive context equality is the identity. -/
theorem _root_.GebLean.Ramified.RIdent.reindCtx_rfl {A : AlgSig} {Γ : List RType}
    {τ : RType} (f : RIdent A Γ τ) : RIdent.reindCtx rfl f = f :=
  rfl

/-- Context transport does not change the underlying slice tree of the
initial-algebra comparison: `polyFixSliceEquiv` reads `RIdent.reindCtx` as a
re-typing of the same tree. -/
theorem polyFixSliceEquiv_reindCtx {A : AlgSig} {Γ Δ : List RType} {τ : RType}
    (h : Γ = Δ) (f : RIdent A Γ τ) :
    (polyFixSliceEquiv (identEndo A) (Δ, τ) (RIdent.reindCtx h f)).1
      = (polyFixSliceEquiv (identEndo A) (Γ, τ) f).1 := by
  subst h
  rfl

/-- The underlying slice tree of the comparison at a context-transported
monotonic recurrence: the `W.mk` node at the transported index, with the
context equation absorbed into the `MrecShape` field `hΓ` and the steps
reduced to their comparison trees. -/
theorem polyFixSliceEquiv_reindCtx_mrec {A : AlgSig} (params : List RType) (τ : RType)
    (steps : (i : A.B) → RIdent A (params ++ List.replicate (A.ar i) τ) τ)
    {Δ : List RType} (h : params ++ [RType.omega τ] = Δ) :
    (polyFixSliceEquiv (identEndo A) (Δ, τ)
        (RIdent.reindCtx h (RIdent.mrec params τ steps))).1
      = SlicePFunctor.W.mk (F := toSlice (identEndo A))
          ⟨⟨⟨(Δ, τ), Sum.inr (Sum.inl ⟨params, h.symm⟩)⟩,
            fun i => (polyFixSliceEquiv (identEndo A) _ (steps i)).1⟩,
            ((toSlice (identEndo A)).toSliceDomPFunctor.compatible_iff
                (toSlice (identEndo A)).wIndex
                ⟨(Δ, τ), Sum.inr (Sum.inl ⟨params, h.symm⟩)⟩ _).mpr
              (fun i => (polyFixSliceEquiv (identEndo A) _ (steps i)).2)⟩ := by
  subst h
  rfl

/-- The underlying slice tree of the comparison at a context-transported flat
recurrence: the `W.mk` node at the transported index, with the context
equation absorbed into the `FrecShape` field `hΓ` and the clauses reduced to
their comparison trees. -/
theorem polyFixSliceEquiv_reindCtx_frec {A : AlgSig} (params : List RType) (τ : RType)
    (clauses : (i : A.B) → RIdent A (params ++ List.replicate (A.ar i) RType.o) τ)
    {Δ : List RType} (h : params ++ [RType.o] = Δ) :
    (polyFixSliceEquiv (identEndo A) (Δ, τ)
        (RIdent.reindCtx h (RIdent.frec params τ clauses))).1
      = SlicePFunctor.W.mk (F := toSlice (identEndo A))
          ⟨⟨⟨(Δ, τ), Sum.inr (Sum.inr ⟨params, h.symm⟩)⟩,
            fun i => (polyFixSliceEquiv (identEndo A) _ (clauses i)).1⟩,
            ((toSlice (identEndo A)).toSliceDomPFunctor.compatible_iff
                (toSlice (identEndo A)).wIndex
                ⟨(Δ, τ), Sum.inr (Sum.inr ⟨params, h.symm⟩)⟩ _).mpr
              (fun i => (polyFixSliceEquiv (identEndo A) _ (clauses i)).2)⟩ := by
  subst h
  rfl

/-- Former naturality at a monotonic recurrence: the bridge image is the
legacy monotonic recurrence of the translated data, transported by
`RIdent.reindCtx` along the context equations `hctx` (at the root) and
`hstep` (at each step). -/
theorem identSliceEquiv_mrec {A : AlgSig} (params : List RType') (τ' : RType')
    (steps : (i : A.B) → RIdent' A (params ++ List.replicate (A.ar i) τ') τ')
    (hctx : List.map rTypeSliceEquiv params ++ [RType.omega (rTypeSliceEquiv τ')]
      = List.map rTypeSliceEquiv (params ++ [RType'.omega τ']))
    (hstep : ∀ i : A.B, List.map rTypeSliceEquiv (params ++ List.replicate (A.ar i) τ')
      = List.map rTypeSliceEquiv params ++ List.replicate (A.ar i) (rTypeSliceEquiv τ')) :
    identSliceEquiv (RIdent'.mrec params τ' steps)
      = RIdent.reindCtx hctx
          (RIdent.mrec (List.map rTypeSliceEquiv params) (rTypeSliceEquiv τ')
            (fun i => RIdent.reindCtx (hstep i) (identSliceEquiv (steps i)))) := by
  have key :
      (SlicePFunctor.reindex.wEquivFiber identCtxEquiv.symm (toSlice (identEndo A))
        (params ++ [RType'.omega τ'], τ')).symm
        ((identEndoIso A).wEquivFiber (params ++ [RType'.omega τ'], τ')
          (RIdent'.mrec params τ' steps))
      = polyFixSliceEquiv (identEndo A) (identCtxEquiv (params ++ [RType'.omega τ'], τ'))
          (RIdent.reindCtx hctx
            (RIdent.mrec (List.map rTypeSliceEquiv params) (rTypeSliceEquiv τ')
              (fun i => RIdent.reindCtx (hstep i) (identSliceEquiv (steps i))))) := by
    apply Subtype.ext
    change (SlicePFunctor.reindex.wEquiv identCtxEquiv.symm (toSlice (identEndo A))).symm
        ((identEndoIso A).wMap (RIdent'.mrec params τ' steps).1)
      = (polyFixSliceEquiv (identEndo A) (identCtxEquiv (params ++ [RType'.omega τ'], τ'))
          (RIdent.reindCtx hctx
            (RIdent.mrec (List.map rTypeSliceEquiv params) (rTypeSliceEquiv τ')
              (fun i => RIdent.reindCtx (hstep i) (identSliceEquiv (steps i)))))).1
    refine Eq.trans ?_ (polyFixSliceEquiv_reindCtx_mrec _ _ _ hctx).symm
    rw [RIdent'.val_mrec, SlicePFunctor.Iso.wMap_mk]
    apply Subtype.ext
    refine congrArg (WType.mk _) ?_
    funext i
    exact ((congrArg Subtype.val (polyFixSliceEquiv_reindCtx (hstep i)
      (identSliceEquiv (steps i)))).trans (identSliceEquiv_apply_val (steps i))).symm
  have h1 : identSliceEquiv (RIdent'.mrec params τ' steps)
      = (polyFixSliceEquiv (identEndo A)
          (identCtxEquiv (params ++ [RType'.omega τ'], τ'))).symm
          ((SlicePFunctor.reindex.wEquivFiber identCtxEquiv.symm (toSlice (identEndo A))
            (params ++ [RType'.omega τ'], τ')).symm
            ((identEndoIso A).wEquivFiber (params ++ [RType'.omega τ'], τ')
              (RIdent'.mrec params τ' steps))) := rfl
  rw [h1, key]
  exact Equiv.symm_apply_apply _ _

/-- Former naturality at a flat recurrence: the bridge image is the legacy
flat recurrence of the translated data, transported by `RIdent.reindCtx`
along the context equations `hctx` (at the root) and `hstep` (at each
clause). -/
theorem identSliceEquiv_frec {A : AlgSig} (params : List RType') (τ' : RType')
    (clauses : (i : A.B) → RIdent' A (params ++ List.replicate (A.ar i) RType'.o) τ')
    (hctx : List.map rTypeSliceEquiv params ++ [RType.o]
      = List.map rTypeSliceEquiv (params ++ [RType'.o]))
    (hstep : ∀ i : A.B,
      List.map rTypeSliceEquiv (params ++ List.replicate (A.ar i) RType'.o)
        = List.map rTypeSliceEquiv params ++ List.replicate (A.ar i) RType.o) :
    identSliceEquiv (RIdent'.frec params τ' clauses)
      = RIdent.reindCtx hctx
          (RIdent.frec (List.map rTypeSliceEquiv params) (rTypeSliceEquiv τ')
            (fun i => RIdent.reindCtx (hstep i) (identSliceEquiv (clauses i)))) := by
  have key :
      (SlicePFunctor.reindex.wEquivFiber identCtxEquiv.symm (toSlice (identEndo A))
        (params ++ [RType'.o], τ')).symm
        ((identEndoIso A).wEquivFiber (params ++ [RType'.o], τ')
          (RIdent'.frec params τ' clauses))
      = polyFixSliceEquiv (identEndo A) (identCtxEquiv (params ++ [RType'.o], τ'))
          (RIdent.reindCtx hctx
            (RIdent.frec (List.map rTypeSliceEquiv params) (rTypeSliceEquiv τ')
              (fun i => RIdent.reindCtx (hstep i) (identSliceEquiv (clauses i))))) := by
    apply Subtype.ext
    change (SlicePFunctor.reindex.wEquiv identCtxEquiv.symm (toSlice (identEndo A))).symm
        ((identEndoIso A).wMap (RIdent'.frec params τ' clauses).1)
      = (polyFixSliceEquiv (identEndo A) (identCtxEquiv (params ++ [RType'.o], τ'))
          (RIdent.reindCtx hctx
            (RIdent.frec (List.map rTypeSliceEquiv params) (rTypeSliceEquiv τ')
              (fun i => RIdent.reindCtx (hstep i) (identSliceEquiv (clauses i)))))).1
    refine Eq.trans ?_ (polyFixSliceEquiv_reindCtx_frec _ _ _ hctx).symm
    rw [RIdent'.val_frec, SlicePFunctor.Iso.wMap_mk]
    apply Subtype.ext
    refine congrArg (WType.mk _) ?_
    funext i
    exact ((congrArg Subtype.val (polyFixSliceEquiv_reindCtx (hstep i)
      (identSliceEquiv (clauses i)))).trans (identSliceEquiv_apply_val (clauses i))).symm
  have h1 : identSliceEquiv (RIdent'.frec params τ' clauses)
      = (polyFixSliceEquiv (identEndo A)
          (identCtxEquiv (params ++ [RType'.o], τ'))).symm
          ((SlicePFunctor.reindex.wEquivFiber identCtxEquiv.symm (toSlice (identEndo A))
            (params ++ [RType'.o], τ')).symm
            ((identEndoIso A).wEquivFiber (params ++ [RType'.o], τ')
              (RIdent'.frec params τ' clauses))) := rfl
  rw [h1, key]
  exact Equiv.symm_apply_apply _ _

/-- The environment transport across the carrier bridge: an environment over a
primed context `Γ'` becomes an environment over the translated legacy context,
each value pushed forward by `carrierSliceEquiv` and transported along the
mapped-context sort equality `get_map`. -/
def envSlice (A : AlgSig) (Γ' : List RType')
    (ρ' : ∀ i : Fin Γ'.length, RType'.interp (FreeAlg' A) (Γ'.get i)) :
    ∀ j : Fin (Γ'.map rTypeSliceEquiv).length,
      RType.interp (FreeAlg A) ((Γ'.map rTypeSliceEquiv).get j) :=
  fun j => cast (congrArg (RType.interp (FreeAlg A)) (get_map rTypeSliceEquiv Γ' j).symm)
    (carrierSliceEquiv A _ (ρ' (Fin.cast (by simp) j)))

/-- The transport of a legacy environment along a context equality. -/
def envCtxCast {A : AlgSig} {Γ Δ : List RType} (h : Γ = Δ)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg A) (Γ.get i)) :
    ∀ j : Fin Δ.length, RType.interp (FreeAlg A) (Δ.get j) :=
  cast (congrArg (fun c : List RType => ∀ i : Fin c.length,
    RType.interp (FreeAlg A) (c.get i)) h) ρ

/-- Pointwise agreement of a primed environment with a legacy environment
across the carrier bridge: at every pair of positions with the same index, the
legacy value is heterogeneously equal to the carrier-bridge image of the primed
value. The contexts are related only through these equations, so the relation
survives the propositional context equalities that the recurrence formers
introduce. -/
def EnvAgree {A : AlgSig} {Γ' : List RType'} {Δ : List RType}
    (ρ' : ∀ i : Fin Γ'.length, RType'.interp (FreeAlg' A) (Γ'.get i))
    (ρ : ∀ j : Fin Δ.length, RType.interp (FreeAlg A) (Δ.get j)) : Prop :=
  ∀ (i : Fin Γ'.length) (j : Fin Δ.length), i.val = j.val →
    HEq (ρ j) (carrierSliceEquiv A (Γ'.get i) (ρ' i))

/-- Transport of a function along an equality of function types acts as
transport of the argument and of the value. -/
theorem cast_arrow {α β γ δ : Type} (hα : α = γ) (hβ : β = δ) (h : (α → β) = (γ → δ))
    (f : α → β) (x : α) : cast h f (cast hα x) = cast hβ (f x) := by
  subst hα; subst hβ; rfl

/-- Transport along an equality is injective. -/
theorem cast_left_inj {α β : Type} (h : α = β) {a b : α} (hab : cast h a = cast h b) : a = b := by
  subst h; exact hab

/-- Transport along an equality and back is the identity. -/
theorem cast_symm_cast {α β : Type} (h : α = β) (a : β) : cast h (cast h.symm a) = a := by
  subst h; rfl

/-- Transport of a function along an equality of its codomain acts as transport
of the value. -/
theorem cast_cod {α β δ : Type} (hβ : β = δ) (h : (α → β) = (α → δ)) (f : α → β) (x : α) :
    cast h f x = cast hβ (f x) := by
  subst hβ; rfl

/-- The denotation congruence commutes with transport along an r-type
equality. -/
theorem interpCongr_cast {C D : Type} (e : C ≃ D) {t u : RType} (h : t = u)
    (w : RType.interp C t) :
    cast (congrArg (RType.interp D) h) (RType.interpCongr e t w)
      = RType.interpCongr e u (cast (congrArg (RType.interp C) h) w) := by
  subst h; rfl

/-- The denotation congruence at an arrow acts by the congruences at the
subterms: it precomposes with the inverse at the domain and postcomposes with
the congruence at the codomain. -/
theorem interpCongr_arrow {C D : Type} (e : C ≃ D) (a b : RType)
    (w : RType.interp C (RType.arrow a b)) (x : RType.interp D a) :
    RType.interpCongr e (RType.arrow a b) w x
      = RType.interpCongr e b (w ((RType.interpCongr e a).symm x)) :=
  rfl

/-- The carrier bridge at an arrow sort: the bridge image of a function,
read at the translated arrow, is the conjugate of the function by the bridges
at the domain and codomain. -/
theorem carrierSliceEquiv_arrow {A : AlgSig} (a b : RType')
    (f : RType'.interp (FreeAlg' A) (RType'.arrow a b))
    (x : RType'.interp (FreeAlg' A) a) :
    cast (congrArg (RType.interp (FreeAlg A)) (rTypeSliceEquiv_arrow a b))
        (carrierSliceEquiv A (RType'.arrow a b) f) (carrierSliceEquiv A a x)
      = carrierSliceEquiv A b (f x) := by
  change cast (congrArg (RType.interp (FreeAlg A)) (rTypeSliceEquiv_arrow a b))
      (RType.interpCongr (freeAlgSliceEquiv A) (rTypeSliceEquiv (RType'.arrow a b))
        (cast (rTypeSliceEquiv_interp (FreeAlg' A) (RType'.arrow a b)) f))
      (RType.interpCongr (freeAlgSliceEquiv A) (rTypeSliceEquiv a)
        (cast (rTypeSliceEquiv_interp (FreeAlg' A) a) x))
    = RType.interpCongr (freeAlgSliceEquiv A) (rTypeSliceEquiv b)
        (cast (rTypeSliceEquiv_interp (FreeAlg' A) b) (f x))
  rw [interpCongr_cast (freeAlgSliceEquiv A) (rTypeSliceEquiv_arrow a b),
    interpCongr_arrow, Equiv.symm_apply_apply]
  refine congrArg (RType.interpCongr (freeAlgSliceEquiv A) (rTypeSliceEquiv b)) ?_
  exact cast_arrow (rTypeSliceEquiv_interp (FreeAlg' A) a)
    (rTypeSliceEquiv_interp (FreeAlg' A) b) _ f x

/-- The base object sort is an object sort. -/
theorem isObj_o' : RType'.IsObj RType'.o :=
  Or.inl (RType'.shape_mk RTypeShape.o Fin.elim0)

/-- Every `Omega` sort is an object sort. -/
theorem isObj_omega' (t' : RType') : RType'.IsObj (RType'.omega t') :=
  Or.inr (RType'.shape_mk RTypeShape.omega ![t'])

/-- The carrier bridge at an object sort, solved for the bridge image: it is
the free-algebra bridge read through the object-sort denotation equalities. -/
theorem carrierSliceEquiv_isObj' {A : AlgSig} {t' : RType'} (h : t'.IsObj)
    (x : RType'.interp (FreeAlg' A) t') :
    carrierSliceEquiv A t' x
      = cast (RType.interp_isObj (FreeAlg A) (cast (rTypeSliceEquiv_isObj t') h)).symm
          (freeAlgSliceEquiv A (cast (RType'.interp_isObj (FreeAlg' A) h) x)) := by
  rw [← carrierSliceEquiv_isObj h x, cast_cast, cast_eq]

/-- The carrier bridge at the base object sort computes to the free-algebra
bridge: both denotations are copies of the base carrier. -/
theorem carrierSliceEquiv_o {A : AlgSig} (x : RType'.interp (FreeAlg' A) RType'.o) :
    cast (congrArg (RType.interp (FreeAlg A)) rTypeSliceEquiv_o)
        (carrierSliceEquiv A RType'.o x)
      = freeAlgSliceEquiv A x :=
  carrierSliceEquiv_isObj isObj_o' x

/-- The carrier bridge at an `Omega` sort computes to the free-algebra bridge:
both denotations are copies of the base carrier. -/
theorem carrierSliceEquiv_omega {A : AlgSig} (t' : RType')
    (x : RType'.interp (FreeAlg' A) (RType'.omega t')) :
    cast (congrArg (RType.interp (FreeAlg A)) (rTypeSliceEquiv_omega t'))
        (carrierSliceEquiv A (RType'.omega t') x)
      = freeAlgSliceEquiv A x :=
  carrierSliceEquiv_isObj (isObj_omega' t') x

/-- The pushed-forward environment agrees with its source. -/
theorem envAgree_envSlice {A : AlgSig} (Γ' : List RType')
    (ρ' : ∀ i : Fin Γ'.length, RType'.interp (FreeAlg' A) (Γ'.get i)) :
    EnvAgree ρ' (envSlice A Γ' ρ') := by
  intro i j hij
  refine HEq.trans (cast_heq _ _) ?_
  have : Fin.cast (by simp : (Γ'.map rTypeSliceEquiv).length = Γ'.length) j = i :=
    Fin.ext hij.symm
  rw [this]

/-- Environment agreement survives a legacy context transport. -/
theorem envAgree_envCtxCast {A : AlgSig} {Γ' : List RType'} {Δ E : List RType}
    (h : Δ = E) {ρ' : ∀ i : Fin Γ'.length, RType'.interp (FreeAlg' A) (Γ'.get i)}
    {ρ : ∀ j : Fin Δ.length, RType.interp (FreeAlg A) (Δ.get j)} (hρ : EnvAgree ρ' ρ) :
    EnvAgree ρ' (envCtxCast h ρ) := by
  subst h
  exact hρ

/-- The pushed-forward environment at a cons context splits as the bridge image
of the head followed by the pushed-forward tail. -/
theorem envSlice_cons {A : AlgSig} (σ' : RType') (Γ' : List RType')
    (x : RType'.interp (FreeAlg' A) σ')
    (ρ' : ∀ i : Fin Γ'.length, RType'.interp (FreeAlg' A) (Γ'.get i)) :
    envSlice A (σ' :: Γ') (Fin.cons x ρ')
      = Fin.cons (carrierSliceEquiv A σ' x) (envSlice A Γ' ρ') := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j <;>
    (simp only [envSlice, Fin.cons_zero, Fin.cons_succ]; rfl)

/-- The currying of a denotation agrees with the legacy currying across the
bridge: for a primed denotation and a legacy denotation matched on
pushed-forward environments, the legacy currying at the translated context is
the carrier-bridge image of the primed currying, read at the translated curried
sort. By induction on the context, the step splitting the leading argument off
through `carrierSliceEquiv_arrow`. -/
theorem curryInterp'_agree (A : AlgSig) : (Γ' : List RType') → (τ' : RType') →
    (g' : (∀ i : Fin Γ'.length, RType'.interp (FreeAlg' A) (Γ'.get i)) →
      RType'.interp (FreeAlg' A) τ') →
    (g : (∀ j : Fin (Γ'.map rTypeSliceEquiv).length,
        RType.interp (FreeAlg A) ((Γ'.map rTypeSliceEquiv).get j)) →
      RType.interp (FreeAlg A) (rTypeSliceEquiv τ')) →
    (∀ ρ', g (envSlice A Γ' ρ') = carrierSliceEquiv A τ' (g' ρ')) →
    curryInterp A (Γ'.map rTypeSliceEquiv) (rTypeSliceEquiv τ') g
      = cast (congrArg (RType.interp (FreeAlg A)) (rTypeSliceEquiv_curried Γ' τ'))
          (carrierSliceEquiv A (RType'.curried Γ' τ') (curryInterp' A Γ' τ' g'))
  | [], τ', g', g, hg => by
    have he : envSlice A [] (finZeroElim :
        ∀ i : Fin ([] : List RType').length,
          RType'.interp (FreeAlg' A) (([] : List RType').get i)) = finZeroElim :=
      funext fun i => i.elim0
    have h := hg finZeroElim
    rw [he] at h
    exact h
  | σ' :: Γ'', τ', g', g, hg => by
    funext y
    obtain ⟨x, rfl⟩ : ∃ x, carrierSliceEquiv A σ' x = y :=
      ⟨(carrierSliceEquiv A σ').symm y, Equiv.apply_symm_apply _ _⟩
    have hstep := curryInterp'_agree A Γ'' τ' (fun ρ'' => g' (Fin.cons x ρ''))
      (fun ρ => g (Fin.cons (carrierSliceEquiv A σ' x) ρ))
      (fun ρ'' => by
        have h := hg (Fin.cons x ρ'')
        rw [envSlice_cons] at h
        exact h)
    refine hstep.trans (Eq.symm ?_)
    have hcc :
        cast (congrArg (RType.interp (FreeAlg A)) (rTypeSliceEquiv_curried (σ' :: Γ'') τ'))
            (carrierSliceEquiv A (RType'.curried (σ' :: Γ'') τ')
              (curryInterp' A (σ' :: Γ'') τ' g'))
          = cast (congrArg (RType.interp (FreeAlg A))
                (congrArg (RType.arrow (rTypeSliceEquiv σ')) (rTypeSliceEquiv_curried Γ'' τ')))
              (cast (congrArg (RType.interp (FreeAlg A))
                  (rTypeSliceEquiv_arrow σ' (RType'.curried Γ'' τ')))
                (carrierSliceEquiv A (RType'.arrow σ' (RType'.curried Γ'' τ'))
                  (curryInterp' A (σ' :: Γ'') τ' g'))) :=
      (cast_cast _ _ _).symm
    rw [hcc]
    refine Eq.trans (cast_cod (congrArg (RType.interp (FreeAlg A))
      (rTypeSliceEquiv_curried Γ'' τ')) _ _ _) ?_
    exact congrArg (cast _) (carrierSliceEquiv_arrow σ' (RType'.curried Γ'' τ')
      (curryInterp' A (σ' :: Γ'') τ' g') x)

/-- The constructor interpretation agrees across the bridge: the legacy
interpretation of the translated constructor operation, on arguments read
through the carrier bridge and transported along the translated arity, is the
carrier-bridge image of the primed interpretation. By
`carrierSliceEquiv_isObj` at each argument position and `freeAlgSliceEquiv_mk`
at the node. -/
theorem stdConstructorInterp_agree {A : AlgSig} (c : (constructorSig A RType'.IsObj).Op)
    (args : ∀ i : Fin ((constructorSig A RType'.IsObj).arity c).length,
      RType'.interp (FreeAlg' A) (((constructorSig A RType'.IsObj).arity c).get i))
    (hlen : ((constructorSig A RType.IsObj).arity
        (⟨⟨rTypeSliceEquiv c.1.val, cast (rTypeSliceEquiv_isObj c.1.val) c.1.2⟩, c.2⟩ :
          (constructorSig A RType.IsObj).Op)).length
      = ((constructorSig A RType'.IsObj).arity c).length)
    (hget : ∀ j, rTypeSliceEquiv (((constructorSig A RType'.IsObj).arity c).get (Fin.cast hlen j))
      = ((constructorSig A RType.IsObj).arity
          (⟨⟨rTypeSliceEquiv c.1.val, cast (rTypeSliceEquiv_isObj c.1.val) c.1.2⟩, c.2⟩ :
            (constructorSig A RType.IsObj).Op)).get j) :
    stdConstructorInterp A
        ⟨⟨rTypeSliceEquiv c.1.val, cast (rTypeSliceEquiv_isObj c.1.val) c.1.2⟩, c.2⟩
        (fun j => cast (congrArg (RType.interp (FreeAlg A)) (hget j))
          (carrierSliceEquiv A _ (args (Fin.cast hlen j))))
      = carrierSliceEquiv A c.1.val (stdConstructorInterp' A c args) := by
  have hlt : ∀ i : Fin (A.ar c.2), i.val < ((constructorSig A RType'.IsObj).arity c).length :=
    fun i => by simp only [constructorSig, List.length_replicate]; exact i.isLt
  have hs : ∀ i : Fin (A.ar c.2),
      RType'.IsObj (((constructorSig A RType'.IsObj).arity c).get ⟨i.val, hlt i⟩) := by
    intro i
    have hgs : ((constructorSig A RType'.IsObj).arity c).get ⟨i.val, hlt i⟩ = c.1.val := by
      simp only [constructorSig, List.get_eq_getElem, List.getElem_replicate]
    rw [hgs]
    exact c.1.2
  have hltL : ∀ i : Fin (A.ar c.2), i.val < ((constructorSig A RType.IsObj).arity
      (⟨⟨rTypeSliceEquiv c.1.val, cast (rTypeSliceEquiv_isObj c.1.val) c.1.2⟩, c.2⟩ :
        (constructorSig A RType.IsObj).Op)).length :=
    fun i => by simp only [constructorSig, List.length_replicate]; exact i.isLt
  have hsL : ∀ i : Fin (A.ar c.2), RType.IsObj (((constructorSig A RType.IsObj).arity
      (⟨⟨rTypeSliceEquiv c.1.val, cast (rTypeSliceEquiv_isObj c.1.val) c.1.2⟩, c.2⟩ :
        (constructorSig A RType.IsObj).Op)).get ⟨i.val, hltL i⟩) := by
    intro i
    have hgs : ((constructorSig A RType.IsObj).arity
        (⟨⟨rTypeSliceEquiv c.1.val, cast (rTypeSliceEquiv_isObj c.1.val) c.1.2⟩, c.2⟩ :
          (constructorSig A RType.IsObj).Op)).get ⟨i.val, hltL i⟩ = rTypeSliceEquiv c.1.val := by
      simp only [constructorSig, List.get_eq_getElem, List.getElem_replicate]
    rw [hgs]
    exact cast (rTypeSliceEquiv_isObj c.1.val) c.1.2
  have hQ : cast (RType'.interp_isObj (FreeAlg' A) c.1.2) (stdConstructorInterp' A c args)
      = FreeAlg'.mk c.2 (fun i =>
          cast (RType'.interp_isObj (FreeAlg' A) (hs i)) (args ⟨i.val, hlt i⟩)) :=
    cast_symm_cast _ _
  have hP : cast (RType.interp_isObj (FreeAlg A) (cast (rTypeSliceEquiv_isObj c.1.val) c.1.2))
        (stdConstructorInterp A
          ⟨⟨rTypeSliceEquiv c.1.val, cast (rTypeSliceEquiv_isObj c.1.val) c.1.2⟩, c.2⟩
          (fun j => cast (congrArg (RType.interp (FreeAlg A)) (hget j))
            (carrierSliceEquiv A _ (args (Fin.cast hlen j)))))
      = FreeAlg.mk c.2 (fun i => cast (RType.interp_isObj (FreeAlg A) (hsL i))
          (cast (congrArg (RType.interp (FreeAlg A)) (hget ⟨i.val, hltL i⟩))
            (carrierSliceEquiv A _ (args (Fin.cast hlen ⟨i.val, hltL i⟩))))) :=
    cast_symm_cast _ _
  refine cast_left_inj
    (RType.interp_isObj (FreeAlg A) (cast (rTypeSliceEquiv_isObj c.1.val) c.1.2)) ?_
  rw [carrierSliceEquiv_isObj c.1.2, hP, hQ, freeAlgSliceEquiv_mk]
  refine congrArg (FreeAlg.mk c.2) (funext fun i => ?_)
  exact (cast_cast _ _ _).trans (carrierSliceEquiv_isObj (hs i) (args _))

/-- The primed defn-body presentation: the base signature of an explicit
definition's body, with the body-interpretation model `defnModel'` as its
designated model. -/
def defnPres' (A : AlgSig) (n : Nat) (hi : Fin n → List RType' × RType')
    (ih : ∀ j : Fin n,
      (∀ i : Fin (hi j).1.length, RType'.interp (FreeAlg' A) ((hi j).1.get i)) →
        RType'.interp (FreeAlg' A) (hi j).2) : Presentation where
  S := RType'
  sig := defnSig' A n hi
  IsObj := RType'.IsObj
  alg := A
  std := defnModel' A n hi ih

/-- The legacy defn-body presentation: the base signature of an explicit
definition's body, with the body-interpretation model `defnModel` as its
designated model. -/
def defnPres (A : AlgSig) (n : Nat) (hi : Fin n → List RType × RType)
    (ih : ∀ j : Fin n,
      (∀ i : Fin (hi j).1.length, RType.interp (FreeAlg A) ((hi j).1.get i)) →
        RType.interp (FreeAlg A) (hi j).2) : Presentation where
  S := RType
  sig := defnSig A n hi
  IsObj := RType.IsObj
  alg := A
  std := defnModel A n hi ih

/-- The defn-body presentation equivalence: the signature isomorphism
`defnSigEquiv` together with the carrier bridge, whose commutation with the
operation interpretations is the constructor case (`carrierSliceEquiv_isObj`
and `freeAlgSliceEquiv_mk`), the application case
(`carrierSliceEquiv_arrow`), the saturated-hole case (the matching hypothesis
`hmatch`), and the curried-hole case (`curryInterp'_agree`). -/
def defnPresEquiv (A : AlgSig) (n : Nat) (hi : Fin n → List RType' × RType')
    (ih' : ∀ j : Fin n,
      (∀ i : Fin (hi j).1.length, RType'.interp (FreeAlg' A) ((hi j).1.get i)) →
        RType'.interp (FreeAlg' A) (hi j).2)
    (ih : ∀ j : Fin n,
      (∀ i : Fin ((hi j).1.map rTypeSliceEquiv).length,
        RType.interp (FreeAlg A) (((hi j).1.map rTypeSliceEquiv).get i)) →
        RType.interp (FreeAlg A) (rTypeSliceEquiv (hi j).2))
    (hmatch : ∀ (j : Fin n)
        (ρ' : ∀ i : Fin (hi j).1.length, RType'.interp (FreeAlg' A) ((hi j).1.get i)),
      ih j (envSlice A (hi j).1 ρ') = carrierSliceEquiv A (hi j).2 (ih' j ρ')) :
    PresentationEquiv (defnPres' A n hi ih')
      (defnPres A n (fun j => identCtxEquiv (hi j)) ih) where
  sigEquiv := defnSigEquiv A n hi
  carrierEquiv := carrierSliceEquiv A
  interpOp_comm := by
    rintro (((c | a) | j) | j) args
    · exact stdConstructorInterp_agree c args
        ((defnSigEquiv A n hi).arity_length (Sum.inl (Sum.inl (Sum.inl c))))
        (fun j => (defnSigEquiv A n hi).get_arity (Sum.inl (Sum.inl (Sum.inl c))) j)
    · exact carrierSliceEquiv_arrow a.1 a.2 (args ⟨0, Nat.succ_pos 1⟩) (args ⟨1, Nat.le_refl 2⟩)
    · exact hmatch j args
    · exact (congrArg (cast _)
        (curryInterp'_agree A (hi j).1 (hi j).2 (ih' j) (ih j) (hmatch j))).trans
        ((cast_cast _ _ _).trans (cast_eq _ _))

/-- The defn-body evaluation agreement: for hole interpretations matched
pointwise by the carrier bridge, the primed evaluation of a `DefnShape'` body
against `defnModel'` maps by `carrierSliceEquiv` to the legacy evaluation of
the translated body against `defnModel`. The composite of `tmSliceEquiv_eval`
(the primed-to-legacy term layer) with `PresentationEquiv.tmMap_eval` at the
defn-body presentation equivalence. -/
theorem defnModel_agree {A : AlgSig} {n : Nat} (hi : Fin n → List RType' × RType')
    (ih' : ∀ j : Fin n,
      (∀ i : Fin (hi j).1.length, RType'.interp (FreeAlg' A) ((hi j).1.get i)) →
        RType'.interp (FreeAlg' A) (hi j).2)
    (ih : ∀ j : Fin n,
      (∀ i : Fin ((hi j).1.map rTypeSliceEquiv).length,
        RType.interp (FreeAlg A) (((hi j).1.map rTypeSliceEquiv).get i)) →
        RType.interp (FreeAlg A) (rTypeSliceEquiv (hi j).2))
    (hmatch : ∀ (j : Fin n)
        (ρ' : ∀ i : Fin (hi j).1.length, RType'.interp (FreeAlg' A) ((hi j).1.get i)),
      ih j (envSlice A (hi j).1 ρ') = carrierSliceEquiv A (hi j).2 (ih' j ρ'))
    {Γ' : List RType'} {τ' : RType'} (t : Tm' (defnSig' A n hi) Γ' τ')
    (ρ' : ∀ i : Fin Γ'.length, RType'.interp (FreeAlg' A) (Γ'.get i)) :
    Tm.eval (defnModel A n (fun j => identCtxEquiv (hi j)) ih) (envSlice A Γ' ρ')
        ((defnSigEquiv A n hi).tmMap (tmSliceEquiv Γ' τ' t))
      = carrierSliceEquiv A τ' (Tm'.eval (defnModel' A n hi ih') ρ' t) := by
  rw [← tmSliceEquiv_eval (defnModel' A n hi ih') ρ' t]
  exact (defnPresEquiv A n hi ih' ih hmatch).tmMap_eval (tmSliceEquiv Γ' τ' t) ρ'


/-- The computation rule of the legacy `RIdent.interp` at an explicit
definition. -/
theorem RIdent.interp_defn {A : AlgSig} {Γ : List RType} {τ : RType} (d : DefnShape A Γ τ)
    (children : (j : Fin d.numHoles) → RIdent A (d.holeIdx j).1 (d.holeIdx j).2) :
    (RIdent.defn d children).interp
      = fun ρ => Tm.eval (defnModel A d.numHoles d.holeIdx (fun j => (children j).interp))
          ρ d.body :=
  rfl

/-- The computation rule of the legacy `RIdent.interp` at a monotonic
recurrence. -/
theorem RIdent.interp_mrec {A : AlgSig} (params : List RType) (τ : RType)
    (steps : (i : A.B) → RIdent A (params ++ List.replicate (A.ar i) τ) τ) :
    (RIdent.mrec params τ steps).interp
      = fun ρ => FreeAlg.recurse (A := A) (P := Unit)
          (fun i _ _sub phi => (steps i).interp
            (childEnv params τ (A.ar i) (envHead params (RType.omega τ) ρ) phi))
          () (envLast params (RType.omega τ) ρ) :=
  rfl

/-- The computation rule of the legacy `RIdent.interp` at a flat recurrence. -/
theorem RIdent.interp_frec {A : AlgSig} (params : List RType) (τ : RType)
    (clauses : (i : A.B) → RIdent A (params ++ List.replicate (A.ar i) RType.o) τ) :
    (RIdent.frec params τ clauses).interp
      = fun ρ => FreeAlg.recurse (A := A) (P := Unit)
          (fun i _ sub _phi => (clauses i).interp
            (childEnv params RType.o (A.ar i) (envHead params RType.o ρ) (fun j => sub j)))
          () (envLast params RType.o ρ) :=
  rfl

/-- The denotation of a context-transported identifier is the denotation of the
identifier at the pulled-back environment. -/
theorem RIdent.interp_reindCtx {A : AlgSig} {Γ Δ : List RType} {τ : RType} (h : Γ = Δ)
    (f : RIdent A Γ τ) (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg A) (Δ.get i)) :
    (RIdent.reindCtx h f).interp ρ = f.interp (envCtxCast h.symm ρ) := by
  subst h; rfl

/-- The primed paramorphism agrees with the legacy paramorphism across the
bridge under a change of result carrier: for a map `e` of result carriers
intertwining the two step functions, the `e`-image of the primed recurrence on
`x` is the legacy recurrence on the image of `x`. The result-carrier
generalization of `freeAlgSliceEquiv_recurse`, by `FreeAlg'.induction`. -/
theorem freeAlgSliceEquiv_recurse_map {A : AlgSig} {P C' C : Type} (e : C' → C)
    (g' : (b : A.B) → P → (Fin (A.ar b) → FreeAlg' A) → (Fin (A.ar b) → C') → C')
    (g : (b : A.B) → P → (Fin (A.ar b) → FreeAlg A) → (Fin (A.ar b) → C) → C)
    (hg : ∀ b q sub rec, e (g' b q sub rec)
      = g b q (fun j => freeAlgSliceEquiv A (sub j)) (fun j => e (rec j)))
    (p : P) (x : FreeAlg' A) :
    e (FreeAlg'.recurse g' p x) = FreeAlg.recurse g p (freeAlgSliceEquiv A x) := by
  refine FreeAlg'.induction
    (motive := fun x =>
      e (FreeAlg'.recurse g' p x) = FreeAlg.recurse g p (freeAlgSliceEquiv A x))
    (fun b sub ih => ?_) x
  dsimp only
  rw [FreeAlg'.recurse_mk, hg, freeAlgSliceEquiv_mk, FreeAlg.recurse_mk]
  exact congrArg (g b p (fun j => freeAlgSliceEquiv A (sub j))) (funext ih)

/-- Structural induction for the primed identifiers, fibrewise over the index:
a predicate holds of every identifier once it holds of each schema former
whose children satisfy it. The fibre wrapping of `SlicePFunctor.W.induction`
at the identifier endofunctor. -/
theorem RIdent'.induction {A : AlgSig} {motive : ∀ Γ' τ', RIdent' A Γ' τ' → Prop}
    (hdefn : ∀ (Γ' : List RType') (τ' : RType') (d : DefnShape' A Γ' τ')
      (children : (j : Fin d.numHoles) → RIdent' A (d.holeIdx' j).1 (d.holeIdx' j).2),
      (∀ j, motive (d.holeIdx' j).1 (d.holeIdx' j).2 (children j)) →
        motive Γ' τ' (RIdent'.defn d children))
    (hmrec : ∀ (params : List RType') (τ' : RType')
      (steps : (i : A.B) → RIdent' A (params ++ List.replicate (A.ar i) τ') τ'),
      (∀ i, motive (params ++ List.replicate (A.ar i) τ') τ' (steps i)) →
        motive (params ++ [RType'.omega τ']) τ' (RIdent'.mrec params τ' steps))
    (hfrec : ∀ (params : List RType') (τ' : RType')
      (clauses : (i : A.B) → RIdent' A (params ++ List.replicate (A.ar i) RType'.o) τ'),
      (∀ i, motive (params ++ List.replicate (A.ar i) RType'.o) τ' (clauses i)) →
        motive (params ++ [RType'.o]) τ' (RIdent'.frec params τ' clauses))
    {Γ' : List RType'} {τ' : RType'} (f : RIdent' A Γ' τ') : motive Γ' τ' f := by
  have key : ∀ w : (toSlice (identEndo' A)).W, ∀ (Δ : List RType') (σ : RType')
      (h : (toSlice (identEndo' A)).wIndex w = (Δ, σ)), motive Δ σ ⟨w, h⟩ := by
    refine SlicePFunctor.W.induction (F := toSlice (identEndo' A)) ?_
    intro x ihc Δ σ h
    obtain ⟨⟨⟨⟨Γ₀, τ₀⟩, shape⟩, fch⟩, hcompat⟩ := x
    have hidx : (toSlice (identEndo' A)).wIndex
        (SlicePFunctor.W.mk (F := toSlice (identEndo' A)) ⟨⟨⟨(Γ₀, τ₀), shape⟩, fch⟩, hcompat⟩)
        = (Γ₀, τ₀) := by
      rw [SlicePFunctor.W.wIndex_mk]; rfl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (hidx.symm.trans h)
    clear hidx
    rcases shape with d | m | fr
    · have hpf := ((toSlice (identEndo' A)).toSliceDomPFunctor.compatible_iff
        (toSlice (identEndo' A)).wIndex ⟨(Γ₀, τ₀), Sum.inl d⟩ fch).mp hcompat
      exact hdefn _ _ d (fun j => ⟨fch j, hpf j⟩) (fun j => ihc j _ _ (hpf j))
    · change MrecShape' A Γ₀ τ₀ at m
      revert h hcompat fch ihc
      obtain ⟨params, rfl⟩ := m
      intro fch hcompat ihc h
      have hpf := ((toSlice (identEndo' A)).toSliceDomPFunctor.compatible_iff
        (toSlice (identEndo' A)).wIndex
        ⟨(params ++ [RType'.omega τ₀], τ₀), Sum.inr (Sum.inl ⟨params, rfl⟩)⟩ fch).mp hcompat
      exact hmrec params τ₀ (fun i => ⟨fch i, hpf i⟩) (fun i => ihc i _ _ (hpf i))
    · change FrecShape' A Γ₀ τ₀ at fr
      revert h hcompat fch ihc
      obtain ⟨params, rfl⟩ := fr
      intro fch hcompat ihc h
      have hpf := ((toSlice (identEndo' A)).toSliceDomPFunctor.compatible_iff
        (toSlice (identEndo' A)).wIndex
        ⟨(params ++ [RType'.o], τ₀), Sum.inr (Sum.inr ⟨params, rfl⟩)⟩ fch).mp hcompat
      exact hfrec params τ₀ (fun i => ⟨fch i, hpf i⟩) (fun i => ihc i _ _ (hpf i))
  exact key f.1 Γ' τ' f.2

/-- Environment agreement read at a pair of matching positions, as a transport
equation. -/
theorem EnvAgree.get {A : AlgSig} {Γ' : List RType'} {Δ : List RType}
    {ρ' : ∀ i : Fin Γ'.length, RType'.interp (FreeAlg' A) (Γ'.get i)}
    {ρ : ∀ j : Fin Δ.length, RType.interp (FreeAlg A) (Δ.get j)} (hρ : EnvAgree ρ' ρ)
    (i : Fin Γ'.length) (j : Fin Δ.length) (hij : i.val = j.val)
    (h : Δ.get j = rTypeSliceEquiv (Γ'.get i)) :
    cast (congrArg (RType.interp (FreeAlg A)) h) (ρ j) = carrierSliceEquiv A (Γ'.get i) (ρ' i) :=
  eq_of_heq ((cast_heq _ _).trans (hρ i j hij))

/-- The carrier bridge commutes with transport of its argument along a sort
equality, heterogeneously. -/
theorem carrierSliceEquiv_cast_heq {A : AlgSig} {s t : RType'} (h : s = t)
    (x : RType'.interp (FreeAlg' A) s) :
    HEq (carrierSliceEquiv A t (cast (congrArg (RType'.interp (FreeAlg' A)) h) x))
      (carrierSliceEquiv A s x) := by
  subst h; rfl

/-- Environment agreement is inherited by the parameter environments of a
recurrence context. -/
theorem envAgree_envHead {A : AlgSig} (params : List RType') (ω' : RType') (ω : RType)
    (ρ' : ∀ k : Fin (params ++ [ω']).length,
      RType'.interp (FreeAlg' A) ((params ++ [ω']).get k))
    (ρ : ∀ k : Fin (List.map rTypeSliceEquiv params ++ [ω]).length,
      RType.interp (FreeAlg A) ((List.map rTypeSliceEquiv params ++ [ω]).get k))
    (hρ : EnvAgree ρ' ρ) :
    EnvAgree (envHead' params ω' ρ') (envHead (List.map rTypeSliceEquiv params) ω ρ) := by
  intro i j hij
  refine (cast_heq _ _).trans ?_
  refine (hρ (finAppL params [ω'] i) (finAppL (List.map rTypeSliceEquiv params) [ω] j)
    hij).trans ?_
  exact (carrierSliceEquiv_cast_heq (get_finAppL params [ω'] i) _).symm

/-- The recurrence argument agrees across the bridge: at an object sort the two
readings of the last position of a recurrence context are related by the
free-algebra bridge. -/
theorem envLast_agree {A : AlgSig} (params : List RType') (ω' : RType') (ω : RType)
    (hω' : RType'.IsObj ω') (hω : RType.IsObj ω) (heq : ω = rTypeSliceEquiv ω')
    (ρ' : ∀ k : Fin (params ++ [ω']).length,
      RType'.interp (FreeAlg' A) ((params ++ [ω']).get k))
    (ρ : ∀ k : Fin (List.map rTypeSliceEquiv params ++ [ω]).length,
      RType.interp (FreeAlg A) ((List.map rTypeSliceEquiv params ++ [ω]).get k))
    (hρ : EnvAgree ρ' ρ) :
    cast (RType.interp_isObj (FreeAlg A) hω)
        (envLast (List.map rTypeSliceEquiv params) ω ρ)
      = freeAlgSliceEquiv A (cast (RType'.interp_isObj (FreeAlg' A) hω')
          (envLast' params ω' ρ')) := by
  have hsobj : RType'.IsObj ((params ++ [ω']).get (finAppR params [ω'] ⟨0, by simp⟩)) := by
    rw [get_finAppR]
    exact hω'
  have hget : (List.map rTypeSliceEquiv params ++ [ω]).get
      (finAppR (List.map rTypeSliceEquiv params) [ω] ⟨0, by simp⟩)
      = rTypeSliceEquiv ((params ++ [ω']).get (finAppR params [ω'] ⟨0, by simp⟩)) := by
    rw [get_finAppR, get_finAppR]
    exact heq
  have key := hρ.get (finAppR params [ω'] ⟨0, by simp⟩)
    (finAppR (List.map rTypeSliceEquiv params) [ω] ⟨0, by simp⟩) (by simp [finAppR]) hget
  have hRHS : cast (RType'.interp_isObj (FreeAlg' A) hω') (envLast' params ω' ρ')
      = cast (RType'.interp_isObj (FreeAlg' A) hsobj)
          (ρ' (finAppR params [ω'] ⟨0, by simp⟩)) :=
    cast_cast _ _ _
  have hLHS : cast (RType.interp_isObj (FreeAlg A) hω)
        (envLast (List.map rTypeSliceEquiv params) ω ρ)
      = cast (RType.interp_isObj (FreeAlg A)
            (cast (rTypeSliceEquiv_isObj ((params ++ [ω']).get (finAppR params [ω'] ⟨0, by simp⟩)))
              hsobj))
          (cast (congrArg (RType.interp (FreeAlg A)) hget)
            (ρ (finAppR (List.map rTypeSliceEquiv params) [ω] ⟨0, by simp⟩))) :=
    (cast_cast _ _ _).trans (cast_cast _ _ _).symm
  rw [hRHS, hLHS, key]
  exact carrierSliceEquiv_isObj hsobj _

/-- Environment agreement is inherited by the child environments of a
recurrence step. -/
theorem envAgree_childEnv {A : AlgSig} (params : List RType') (σ' : RType') (σ : RType)
    (n : Nat)
    (xvec' : ∀ i : Fin params.length, RType'.interp (FreeAlg' A) (params.get i))
    (xvec : ∀ i : Fin (List.map rTypeSliceEquiv params).length,
      RType.interp (FreeAlg A) ((List.map rTypeSliceEquiv params).get i))
    (hx : EnvAgree xvec' xvec)
    (rest' : Fin n → RType'.interp (FreeAlg' A) σ')
    (rest : Fin n → RType.interp (FreeAlg A) σ)
    (hrest : ∀ e, HEq (rest e) (carrierSliceEquiv A σ' (rest' e))) :
    EnvAgree (childEnv' params σ' n xvec' rest')
      (childEnv (List.map rTypeSliceEquiv params) σ n xvec rest) := by
  intro k' k hkk
  have hlenm : (List.map rTypeSliceEquiv params).length = params.length := by simp
  simp only [childEnv', childEnv]
  by_cases hlt : k'.val < params.length
  · have hlt2 : k.val < (List.map rTypeSliceEquiv params).length := by
      rw [hlenm, ← hkk]; exact hlt
    rw [dif_pos hlt, dif_pos hlt2]
    refine (cast_heq _ _).trans ?_
    refine (hx ⟨k'.val, hlt⟩ ⟨k.val, hlt2⟩ hkk).trans ?_
    exact (carrierSliceEquiv_cast_heq
      (get_append_lt params (List.replicate n σ') k' hlt).symm (xvec' ⟨k'.val, hlt⟩)).symm
  · have hlt2 : ¬ k.val < (List.map rTypeSliceEquiv params).length := by
      rw [hlenm, ← hkk]; exact hlt
    have hgetk : (params ++ List.replicate n σ').get k' = σ' := by
      rw [get_append_ge params (List.replicate n σ') k' hlt]
      simp [List.get_eq_getElem, List.getElem_replicate]
    rw [dif_neg hlt, dif_neg hlt2]
    simp only [hlenm, ← hkk]
    exact (cast_heq _ _).trans ((hrest _).trans
      (carrierSliceEquiv_cast_heq hgetk.symm _).symm)

/-- A legacy environment over the translated context agreeing with a primed
environment is the pushed-forward environment. -/
theorem envAgree_eq {A : AlgSig} {Γ' : List RType'}
    {ρ' : ∀ i : Fin Γ'.length, RType'.interp (FreeAlg' A) (Γ'.get i)}
    {ρ : ∀ j : Fin (Γ'.map rTypeSliceEquiv).length,
      RType.interp (FreeAlg A) ((Γ'.map rTypeSliceEquiv).get j)}
    (hρ : EnvAgree ρ' ρ) : ρ = envSlice A Γ' ρ' := by
  funext j
  exact eq_of_heq ((hρ (Fin.cast (by simp) j) j rfl).trans
    (envAgree_envSlice Γ' ρ' (Fin.cast (by simp) j) j rfl).symm)

/-- The identifier denotation agrees across the bridge: the legacy denotation
of a translated identifier, at the pushed-forward environment, is the
carrier-bridge image of the primed denotation. By induction on the identifier:
the explicit-definition case is `defnModel_agree` at the induction hypotheses;
the two recurrence cases are `freeAlgSliceEquiv_recurse_map` at the
recurrence-context environment matchings `envAgree_envHead`,
`envAgree_childEnv`, and `envLast_agree`. -/
theorem identSliceEquiv_interp {A : AlgSig} {Γ' : List RType'} {τ' : RType'}
    (f : RIdent' A Γ' τ')
    (ρ' : ∀ i : Fin Γ'.length, RType'.interp (FreeAlg' A) (Γ'.get i)) :
    (identSliceEquiv f).interp (envSlice A Γ' ρ') = carrierSliceEquiv A τ' (f.interp ρ') := by
  refine RIdent'.induction
    (motive := fun Γ' τ' f => ∀ ρ', (identSliceEquiv f).interp (envSlice A Γ' ρ')
      = carrierSliceEquiv A τ' (f.interp ρ')) ?_ ?_ ?_ f ρ'
  · intro Γ'' τ'' d children ihch ρ''
    rw [identSliceEquiv_defn]
    refine Eq.trans (congrFun (RIdent.interp_defn (defnShapeEquiv A Γ'' τ'' d)
      (fun j => identSliceEquiv (children j))) _) ?_
    refine Eq.trans ?_ (congrArg (carrierSliceEquiv A τ'')
      (congrFun (RIdent'.interp_defn d children) ρ'').symm)
    exact defnModel_agree d.holeIdx' (fun j => (children j).interp)
      (fun j => (identSliceEquiv (children j)).interp) ihch d.body ρ''
  · intro params τ'' steps ihst ρ''
    have hctx : List.map rTypeSliceEquiv params ++ [RType.omega (rTypeSliceEquiv τ'')]
        = List.map rTypeSliceEquiv (params ++ [RType'.omega τ'']) := by simp
    have hstep : ∀ i : A.B, List.map rTypeSliceEquiv (params ++ List.replicate (A.ar i) τ'')
        = List.map rTypeSliceEquiv params ++ List.replicate (A.ar i) (rTypeSliceEquiv τ'') := by
      intro i; simp
    have hρ₁ : EnvAgree ρ'' (envCtxCast hctx.symm
        (envSlice A (params ++ [RType'.omega τ'']) ρ'')) :=
      envAgree_envCtxCast hctx.symm (envAgree_envSlice _ ρ'')
    have hlast : envLast (List.map rTypeSliceEquiv params) (RType.omega (rTypeSliceEquiv τ''))
          (envCtxCast hctx.symm (envSlice A (params ++ [RType'.omega τ'']) ρ''))
        = freeAlgSliceEquiv A (envLast' params (RType'.omega τ'') ρ'') :=
      envLast_agree params (RType'.omega τ'') (RType.omega (rTypeSliceEquiv τ''))
        (isObj_omega' τ'') (Or.inr rfl) (rTypeSliceEquiv_omega τ'').symm ρ'' _ hρ₁
    rw [identSliceEquiv_mrec params τ'' steps hctx hstep, RIdent.interp_reindCtx]
    refine Eq.trans (congrFun (RIdent.interp_mrec _ _ _) _) ?_
    refine Eq.trans ?_ (congrArg (carrierSliceEquiv A τ'')
      (congrFun (RIdent'.interp_mrec params τ'' steps) ρ'').symm)
    rw [hlast]
    refine (freeAlgSliceEquiv_recurse_map (carrierSliceEquiv A τ'') _ _ ?_ () _).symm
    intro b _q _sub rec
    rw [RIdent.interp_reindCtx, envAgree_eq (envAgree_envCtxCast (hstep b).symm
      (envAgree_childEnv params τ'' (rTypeSliceEquiv τ'') (A.ar b) _ _
        (envAgree_envHead params (RType'.omega τ'')
          (RType.omega (rTypeSliceEquiv τ'')) ρ'' _ hρ₁)
        rec (fun j => carrierSliceEquiv A τ'' (rec j)) (fun _ => HEq.rfl)))]
    exact (ihst b _).symm
  · intro params τ'' clauses ihcl ρ''
    have hctx : List.map rTypeSliceEquiv params ++ [RType.o]
        = List.map rTypeSliceEquiv (params ++ [RType'.o]) := by simp
    have hstep : ∀ i : A.B, List.map rTypeSliceEquiv (params ++ List.replicate (A.ar i) RType'.o)
        = List.map rTypeSliceEquiv params ++ List.replicate (A.ar i) RType.o := by
      intro i; simp
    have hρ₁ : EnvAgree ρ'' (envCtxCast hctx.symm
        (envSlice A (params ++ [RType'.o]) ρ'')) :=
      envAgree_envCtxCast hctx.symm (envAgree_envSlice _ ρ'')
    have hlast : envLast (List.map rTypeSliceEquiv params) RType.o
          (envCtxCast hctx.symm (envSlice A (params ++ [RType'.o]) ρ''))
        = freeAlgSliceEquiv A (envLast' params RType'.o ρ'') :=
      envLast_agree params RType'.o RType.o isObj_o' (Or.inl rfl) rTypeSliceEquiv_o.symm
        ρ'' _ hρ₁
    rw [identSliceEquiv_frec params τ'' clauses hctx hstep, RIdent.interp_reindCtx]
    refine Eq.trans (congrFun (RIdent.interp_frec _ _ _) _) ?_
    refine Eq.trans ?_ (congrArg (carrierSliceEquiv A τ'')
      (congrFun (RIdent'.interp_frec params τ'' clauses) ρ'').symm)
    rw [hlast]
    refine (freeAlgSliceEquiv_recurse_map (carrierSliceEquiv A τ'') _ _ ?_ () _).symm
    intro b _q sub _rec
    rw [RIdent.interp_reindCtx, envAgree_eq (envAgree_envCtxCast (hstep b).symm
      (envAgree_childEnv params RType'.o RType.o (A.ar b) _ _
        (envAgree_envHead params RType'.o RType.o ρ'' _ hρ₁)
        sub (fun j => freeAlgSliceEquiv A (sub j))
        (fun e => (heq_of_eq (carrierSliceEquiv_o (sub e)).symm).trans (cast_heq _ _))))]
    exact (ihcl b _).symm

end GebLean.Ramified.Polynomial
