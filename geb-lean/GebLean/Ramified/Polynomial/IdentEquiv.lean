import GebLean.Ramified.Polynomial.Ident
import GebLean.Ramified.Polynomial.Term
import GebLean.Ramified.HigherOrder
import GebLean.Ramified.SigEquiv
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

## Main statements

* `identSliceEquiv_defn`, `identSliceEquiv_mrec`, `identSliceEquiv_frec` — the
  former naturality of the bridge equivalence.

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

end GebLean.Ramified.Polynomial
