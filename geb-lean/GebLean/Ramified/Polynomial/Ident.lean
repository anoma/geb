import GebLean.Ramified.HigherOrder
import GebLean.Ramified.Polynomial.RType
import GebLean.Ramified.Polynomial.Term
import GebLean.Ramified.Polynomial.Interp
import GebLean.PolyBridge.Slice
import GebLean.Utilities.Families

/-!
# The primed schema-identifier data on the slice `W`-type

A second realization of the higher-order presentation's non-recursive data
layer (`GebLean/Ramified/HigherOrder.lean`) on the vendored `geb-mathlib`
slice `W`-type stack: the application signature, the curried arrow sort and
its currying, the explicit-definition hole signatures, and the
schema-generated identifiers `RIdent'`, realized as the fiber of the slice
`W`-type `(toSlice (identEndo' A)).W` over the index `(Γ', τ')` rather than
the legacy `PolyFix` W-type. The three schema formers `RIdent'.defn`,
`RIdent'.mrec`, and `RIdent'.frec` build `W`-nodes directly, with children's
fiber proofs discharged pointwise through
`SliceDomPFunctor.compatible_iff`, mirroring `FreeAlg'.mk`'s idiom
extended to the indexed case (the shape of `SlicePFunctor.FreeM.node`,
`GebLean/SliceW/FreeM.lean`). The denotation `RIdent'.interp` folds an
identifier by a single `SlicePFunctor.W.elim` at a sigma-of-interpretations
carrier, the `SlicePFunctor.FreeM.elim` idiom at the identifier endofunctor.

## Main definitions

* `appSig'` — the application signature: one operation per `(σ, τ)`, of
  arity `[σ → τ, σ]` and result `τ`.
* `stdConstructorInterp'`, `stdAppInterp'` — the standard-carrier
  interpretations of a constructor and an application operation.
* `RType'.curried` — the curried arrow sort `σ₁ → ⋯ → σₙ → τ` of a context
  and result sort.
* `curryInterp'` — the currying of an identifier's denotation into the
  iterated function space at its curried sort.
* `holeSig'`, `holeConstSig'` — the two readings of an identifier occurrence
  in an explicit definition's body: the saturated application and the
  curried combinator value.
* `defnSig'` — the base signature of an explicit definition's body.
* `DefnShape'`, `MrecShape'`, `FrecShape'` — the non-recursive data of an
  explicit definition, a ramified monotonic recurrence (eq. (4)), and a flat
  recurrence (eq. (5)).
* `IdentShape'`, `IdentDir'`, `identTarget'` — the shape type, direction
  type, and direction-target map of the identifier signature endofunctor.
* `identEndo'` — the identifier signature endofunctor over the index type
  `List RType' × RType'` (context, result sort).
* `RIdent'` — the schema-generated identifiers over a base algebra `A`,
  indexed by context and result sort: the fiber of
  `(toSlice (identEndo' A)).W` over `(Γ', τ')`.
* `RIdent'.defn`, `RIdent'.mrec`, `RIdent'.frec` — the derived schema
  formers (explicit definition, ramified monotonic recurrence eq. (4), flat
  recurrence eq. (5)).
* `defnModel'` — the model interpreting an explicit definition's body.
* `childEnv'`, `envHead'`, `envLast'` — the recurrence-context environment
  helpers.
* `RIdent'.interpStep` — the recursion step of the identifier denotation at
  one node.
* `RIdent'.interpFam`, `RIdent'.interpAlg` — the interpretation carrier family
  and the slice algebra of the `SlicePFunctor.W.elim` fold.
* `RIdent'.interp` — the denotation of an identifier as a function on the
  environment at its context.

## Main statements

* `rTypeSliceEquiv_curried` — the curried arrow sort agrees with the legacy
  curried arrow sort across the bridge, mapped pointwise over the context.
* `RIdent'.val_defn`, `RIdent'.val_mrec`, `RIdent'.val_frec` — the
  underlying-tree characterization of each schema former, as
  `SlicePFunctor.W.mk` on the corresponding summand of `identEndo'`.
* `RIdent'.interpAlg_over` — the interpretation algebra lies over the index
  type.
* `RIdent'.interp_defn`, `RIdent'.interp_mrec`, `RIdent'.interp_frec` — the
  computation rules of the identifier denotation at the three schema formers.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher
type recurrence and elementary complexity", Annals of Pure and Applied
Logic 96 (1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`. The schema of
higher-type identifiers -- explicit definitions, ramified monotonic
recurrence (eq. (4)), and flat recurrence (eq. (5)) -- is section 2.3; every
object sort denotes a copy of the base carrier in section 2.7. The
data-types-a-la-carte factoring follows W. Swierstra, "Data types a la
carte", Journal of Functional Programming 18 (2008) 423-436, DOI
`10.1017/S0956796808006758`.

## Tags

ramified recurrence, higher type, application, schema identifier, explicit
definition, monotonic recurrence, flat recurrence, W-type, slice category
-/

namespace GebLean.Ramified.Polynomial

open GebLean.Ramified GebLean.PolyBridge CategoryTheory

/-- The application signature (Leivant III section 2.3, the higher-order
system): for each pair `(σ, τ)` of primed r-types, an operation of arity
`[σ → τ, σ]` and result `τ`, applying a function to an argument. Mirror of
the legacy `appSig` (`GebLean/Ramified/HigherOrder.lean`). -/
def appSig' : SortedSig RType' where
  Op := RType' × RType'
  arity op := [RType'.arrow op.1 op.2, op.1]
  result op := op.2

/-- The interpretation of a constructor operation over the primed standard
carriers: the free-algebra constructor `FreeAlg'.mk` at the label, on the
arguments read as base-carrier elements (every object sort denotes a copy of
`FreeAlg' A`). Mirror of the legacy `stdConstructorInterp`. -/
def stdConstructorInterp' (A : AlgSig)
    (op : (constructorSig A RType'.IsObj).Op)
    (args : ∀ i : Fin ((constructorSig A RType'.IsObj).arity op).length,
      RType'.interp (FreeAlg' A) (((constructorSig A RType'.IsObj).arity op).get i)) :
    RType'.interp (FreeAlg' A) ((constructorSig A RType'.IsObj).result op) := by
  refine cast (RType'.interp_isObj (FreeAlg' A) op.1.2).symm
    (FreeAlg'.mk op.2 (fun i => ?_))
  have hlt : i.val < ((constructorSig A RType'.IsObj).arity op).length := by
    simp only [constructorSig, List.length_replicate]; exact i.isLt
  have hg : ((constructorSig A RType'.IsObj).arity op).get ⟨i.val, hlt⟩ = op.1.val := by
    simp only [constructorSig, List.get_eq_getElem, List.getElem_replicate]
  exact cast (by rw [hg]; exact RType'.interp_isObj (FreeAlg' A) op.1.2)
    (args ⟨i.val, hlt⟩)

/-- The interpretation of an application operation over the primed standard
carriers: function application, reading the first argument at `σ → τ` as a
function and applying it to the second at `σ`. Mirror of the legacy
`stdAppInterp`. -/
def stdAppInterp' (A : AlgSig) (op : appSig'.Op)
    (args : ∀ i : Fin (appSig'.arity op).length,
      RType'.interp (FreeAlg' A) ((appSig'.arity op).get i)) :
    RType'.interp (FreeAlg' A) (appSig'.result op) :=
  have g : RType'.interp (FreeAlg' A) (RType'.arrow op.1 op.2) :=
    args ⟨0, by simp [appSig']⟩
  g (args ⟨1, by simp [appSig']⟩)

/-- The curried arrow sort of a context and result sort: `σ₁ → ⋯ → σₙ → τ`
for `Γ' = [σ₁, …, σₙ]`, the right fold of `RType'.arrow` over `Γ'` with base
`τ`. Mirror of the legacy `RType.curried`. -/
def RType'.curried (Γ' : List RType') (τ' : RType') : RType' := Γ'.foldr RType'.arrow τ'

@[simp] theorem RType'.curried_nil (τ' : RType') : RType'.curried [] τ' = τ' := rfl

@[simp] theorem RType'.curried_cons (σ' : RType') (Γ' : List RType') (τ' : RType') :
    RType'.curried (σ' :: Γ') τ' = RType'.arrow σ' (RType'.curried Γ' τ') := rfl

/-- The curried arrow sort agrees with the legacy curried arrow sort across
the bridge, mapped pointwise over the context: by induction on `Γ'`, the step
unfolding `RType'.curried_cons` and `RType.curried_cons` against
`rTypeSliceEquiv_arrow`. -/
theorem rTypeSliceEquiv_curried (Γ' : List RType') (τ' : RType') :
    rTypeSliceEquiv (RType'.curried Γ' τ') =
      RType.curried (Γ'.map rTypeSliceEquiv) (rTypeSliceEquiv τ') := by
  induction Γ' with
  | nil => rfl
  | cons σ' Γ' ih =>
    simp only [RType'.curried_cons, List.map_cons, RType.curried_cons, rTypeSliceEquiv_arrow, ih]

/-- The currying of a function on environments into the iterated function
space at the curried sort: from a map `Env Γ' → interp τ'` to a value at
`interp (RType'.curried Γ' τ')`, consuming the context sorts one at a time.
Mirror of the legacy `curryInterp`. -/
def curryInterp' (A : AlgSig) : (Γ' : List RType') → (τ' : RType') →
    ((∀ i : Fin Γ'.length, RType'.interp (FreeAlg' A) (Γ'.get i)) →
      RType'.interp (FreeAlg' A) τ') →
    RType'.interp (FreeAlg' A) (RType'.curried Γ' τ')
  | [], _τ', g => g finZeroElim
  | σ' :: Γ'', τ', g => fun x : RType'.interp (FreeAlg' A) σ' =>
      curryInterp' A Γ'' τ' (fun ρ' => g (Fin.cons x ρ'))

/-- The saturated hole signature of an explicit definition: one operation per
hole, of the hole's context as arity and the hole's result sort as result.
Mirror of the legacy `holeSig`. -/
def holeSig' (n : Nat) (holeIdx' : Fin n → List RType' × RType') : SortedSig RType' where
  Op := Fin n
  arity j := (holeIdx' j).1
  result j := (holeIdx' j).2

/-- The curried hole signature of an explicit definition: one nullary
operation per hole, of the hole's curried arrow sort as result. Mirror of the
legacy `holeConstSig`. -/
def holeConstSig' (n : Nat) (holeIdx' : Fin n → List RType' × RType') :
    SortedSig RType' where
  Op := Fin n
  arity _j := []
  result j := RType'.curried (holeIdx' j).1 (holeIdx' j).2

/-- The base signature of an explicit definition's body: the constructor
summand, application, the saturated holes for previously defined
identifiers, and their curried-combinator forms. Mirror of the legacy
`defnSig`. -/
def defnSig' (A : AlgSig) (n : Nat) (holeIdx' : Fin n → List RType' × RType') :
    SortedSig RType' :=
  (((constructorSig A RType'.IsObj).sum appSig').sum (holeSig' n holeIdx')).sum
    (holeConstSig' n holeIdx')

/-- The non-recursive data of an explicit definition (Leivant III section
2.3): a defining term over the base signature extended by hole operations,
one hole per occurrence of a previously defined identifier. Mirror of the
legacy `DefnShape`. -/
structure DefnShape' (A : AlgSig) (Γ' : List RType') (τ' : RType') where
  /-- The number of identifier holes in the body. -/
  numHoles : Nat
  /-- The context and result sort each hole's referenced identifier
  carries. -/
  holeIdx' : Fin numHoles → List RType' × RType'
  /-- The defining term over the base signature with holes, in context `Γ'`
  at sort `τ'`. -/
  body : Tm' (defnSig' A numHoles holeIdx') Γ' τ'

/-- The non-recursive data of a ramified monotonic recurrence (Leivant III
section 2.3, eq. (4)): the recurrence parameters, with the recurrence
argument sitting at `Ω τ'` at the end of the context. Mirror of the legacy
`MrecShape`. -/
structure MrecShape' (A : AlgSig) (Γ' : List RType') (τ' : RType') where
  /-- The recurrence parameters (the paper's `x_vec`). -/
  params : List RType'
  /-- The context is the parameters followed by the recurrence argument at
  `Ω τ'`. -/
  hΓ : Γ' = params ++ [RType'.omega τ']

/-- The non-recursive data of a flat recurrence (Leivant III section 2.3,
eq. (5)): the recurrence parameters, with the recurrence argument sitting at
`o` at the end of the context. Mirror of the legacy `FrecShape`. -/
structure FrecShape' (A : AlgSig) (Γ' : List RType') (τ' : RType') where
  /-- The recurrence parameters (the paper's `x_vec`). -/
  params : List RType'
  /-- The context is the parameters followed by the recurrence argument at
  `o`. -/
  hΓ : Γ' = params ++ [RType'.o]

/-- The shape type of the identifier signature endofunctor at index
`(Γ', τ')`: the disjoint union of the three schema formers' non-recursive
data. Mirror of the legacy `IdentShape`. -/
def IdentShape' (A : AlgSig) (Γ' : List RType') (τ' : RType') : Type :=
  DefnShape' A Γ' τ' ⊕ MrecShape' A Γ' τ' ⊕ FrecShape' A Γ' τ'

/-- The direction type at a shape: the holes of a `defn'`, and the
constructor labels of a `mrec'` or `frec'` (one step function or clause per
label). Mirror of the legacy `IdentDir`. -/
def IdentDir' (A : AlgSig) (Γ' : List RType') (τ' : RType') :
    IdentShape' A Γ' τ' → Type
  | Sum.inl d => Fin d.numHoles
  | Sum.inr (Sum.inl _) => A.B
  | Sum.inr (Sum.inr _) => A.B

/-- The target index of a direction: the context and result sort of the
referenced identifier. Mirror of the legacy `identTarget`. -/
def identTarget' (A : AlgSig) (Γ' : List RType') (τ' : RType') :
    (s : IdentShape' A Γ' τ') → IdentDir' A Γ' τ' s → List RType' × RType'
  | Sum.inl d, j => d.holeIdx' j
  | Sum.inr (Sum.inl m), i => (m.params ++ List.replicate (A.ar i) τ', τ')
  | Sum.inr (Sum.inr fr), i => (fr.params ++ List.replicate (A.ar i) RType'.o, τ')

/-- The identifier signature endofunctor over the index type
`List RType' × RType'` (context, result sort): shapes are the schema
formers' data, directions are the referenced identifiers. Mirror of the
legacy `identEndo` (decision 8). -/
def identEndo' (A : AlgSig) : PolyEndo (List RType' × RType') :=
  fun idx => ccrObjMk fun s : IdentShape' A idx.1 idx.2 =>
    Over.mk fun d : IdentDir' A idx.1 idx.2 s => identTarget' A idx.1 idx.2 s d

/-- The schema-generated identifiers over a base algebra `A`, indexed by
context and result sort (Leivant III section 2.3): explicit definitions and
ramified monotonic recurrences (eq. (4)) and flat recurrences (eq. (5)) over
previously defined identifiers. Realized as the fiber of the slice `W`-type
`(toSlice (identEndo' A)).W` over `(Γ', τ')`, the `FreeAlg'` fiber idiom
extended to a non-trivial index. A second realization of `RIdent`
(`GebLean/Ramified/HigherOrder.lean`). -/
def RIdent' (A : AlgSig) (Γ' : List RType') (τ' : RType') : Type :=
  { w : (toSlice (identEndo' A)).W // (toSlice (identEndo' A)).wIndex w = (Γ', τ') }

/-- An explicit definition (Leivant III section 2.3): the defining term `d`
together with the referenced identifiers filling its holes. A `W.mk` node at
the `defn'` shape, with children's fiber proofs discharged pointwise via
`compatible_iff`. Mirror of the legacy `RIdent.defn`. -/
def RIdent'.defn {A : AlgSig} {Γ' : List RType'} {τ' : RType'} (d : DefnShape' A Γ' τ')
    (children : (j : Fin d.numHoles) → RIdent' A (d.holeIdx' j).1 (d.holeIdx' j).2) :
    RIdent' A Γ' τ' :=
  ⟨SlicePFunctor.W.mk (F := toSlice (identEndo' A))
      ⟨⟨⟨(Γ', τ'), Sum.inl d⟩, fun j => (children j).1⟩,
        ((toSlice (identEndo' A)).toSliceDomPFunctor.compatible_iff
            (toSlice (identEndo' A)).wIndex ⟨(Γ', τ'), Sum.inl d⟩ _).mpr
          (fun j => (children j).2)⟩,
    by rw [SlicePFunctor.W.wIndex_mk]; rfl⟩

/-- The underlying tree of `RIdent'.defn d children` is the `W.mk` node at
the `defn'` shape `⟨(Γ', τ'), Sum.inl d⟩` with children reduced to their
underlying trees. Mirror of the `SlicePFunctor.FreeM.val_node` naming
pattern (`GebLean/SliceW/FreeM.lean`). -/
@[simp] theorem RIdent'.val_defn {A : AlgSig} {Γ' : List RType'} {τ' : RType'}
    (d : DefnShape' A Γ' τ')
    (children : (j : Fin d.numHoles) → RIdent' A (d.holeIdx' j).1 (d.holeIdx' j).2) :
    (RIdent'.defn d children).1 =
      SlicePFunctor.W.mk (F := toSlice (identEndo' A))
        ⟨⟨⟨(Γ', τ'), Sum.inl d⟩, fun j => (children j).1⟩,
          ((toSlice (identEndo' A)).toSliceDomPFunctor.compatible_iff
              (toSlice (identEndo' A)).wIndex ⟨(Γ', τ'), Sum.inl d⟩ _).mpr
            (fun j => (children j).2)⟩ :=
  rfl

/-- A ramified monotonic recurrence (Leivant III section 2.3, eq. (4)): with
parameters `x_vec` of sorts `params` and recurrence argument at `Ω τ'`, and
one step function per constructor of `A`. A `W.mk` node at the `mrec'`
shape, with children's fiber proofs discharged pointwise via
`compatible_iff`. Mirror of the legacy `RIdent.mrec`. -/
def RIdent'.mrec {A : AlgSig} (params : List RType') (τ' : RType')
    (steps : (i : A.B) → RIdent' A (params ++ List.replicate (A.ar i) τ') τ') :
    RIdent' A (params ++ [RType'.omega τ']) τ' :=
  ⟨SlicePFunctor.W.mk (F := toSlice (identEndo' A))
      ⟨⟨⟨(params ++ [RType'.omega τ'], τ'), Sum.inr (Sum.inl ⟨params, rfl⟩)⟩,
        fun i => (steps i).1⟩,
        ((toSlice (identEndo' A)).toSliceDomPFunctor.compatible_iff
            (toSlice (identEndo' A)).wIndex
            ⟨(params ++ [RType'.omega τ'], τ'), Sum.inr (Sum.inl ⟨params, rfl⟩)⟩ _).mpr
          (fun i => (steps i).2)⟩,
    by rw [SlicePFunctor.W.wIndex_mk]; rfl⟩

/-- The underlying tree of `RIdent'.mrec params τ' steps` is the `W.mk` node
at the `mrec'` shape with children reduced to their underlying trees. Mirror
of the `SlicePFunctor.FreeM.val_node` naming pattern. -/
@[simp] theorem RIdent'.val_mrec {A : AlgSig} (params : List RType') (τ' : RType')
    (steps : (i : A.B) → RIdent' A (params ++ List.replicate (A.ar i) τ') τ') :
    (RIdent'.mrec params τ' steps).1 =
      SlicePFunctor.W.mk (F := toSlice (identEndo' A))
        ⟨⟨⟨(params ++ [RType'.omega τ'], τ'), Sum.inr (Sum.inl ⟨params, rfl⟩)⟩,
          fun i => (steps i).1⟩,
          ((toSlice (identEndo' A)).toSliceDomPFunctor.compatible_iff
              (toSlice (identEndo' A)).wIndex
              ⟨(params ++ [RType'.omega τ'], τ'), Sum.inr (Sum.inl ⟨params, rfl⟩)⟩ _).mpr
            (fun i => (steps i).2)⟩ :=
  rfl

/-- A flat recurrence (Leivant III section 2.3, eq. (5)): with parameters
`x_vec` of sorts `params` and recurrence argument at `o`, and one clause per
constructor of `A`. A `W.mk` node at the `frec'` shape, with children's
fiber proofs discharged pointwise via `compatible_iff`. Mirror of the legacy
`RIdent.frec`. -/
def RIdent'.frec {A : AlgSig} (params : List RType') (τ' : RType')
    (clauses : (i : A.B) → RIdent' A (params ++ List.replicate (A.ar i) RType'.o) τ') :
    RIdent' A (params ++ [RType'.o]) τ' :=
  ⟨SlicePFunctor.W.mk (F := toSlice (identEndo' A))
      ⟨⟨⟨(params ++ [RType'.o], τ'), Sum.inr (Sum.inr ⟨params, rfl⟩)⟩,
        fun i => (clauses i).1⟩,
        ((toSlice (identEndo' A)).toSliceDomPFunctor.compatible_iff
            (toSlice (identEndo' A)).wIndex
            ⟨(params ++ [RType'.o], τ'), Sum.inr (Sum.inr ⟨params, rfl⟩)⟩ _).mpr
          (fun i => (clauses i).2)⟩,
    by rw [SlicePFunctor.W.wIndex_mk]; rfl⟩

/-- The underlying tree of `RIdent'.frec params τ' clauses` is the `W.mk`
node at the `frec'` shape with children reduced to their underlying trees.
Mirror of the `SlicePFunctor.FreeM.val_node` naming pattern. -/
@[simp] theorem RIdent'.val_frec {A : AlgSig} (params : List RType') (τ' : RType')
    (clauses : (i : A.B) → RIdent' A (params ++ List.replicate (A.ar i) RType'.o) τ') :
    (RIdent'.frec params τ' clauses).1 =
      SlicePFunctor.W.mk (F := toSlice (identEndo' A))
        ⟨⟨⟨(params ++ [RType'.o], τ'), Sum.inr (Sum.inr ⟨params, rfl⟩)⟩,
          fun i => (clauses i).1⟩,
          ((toSlice (identEndo' A)).toSliceDomPFunctor.compatible_iff
              (toSlice (identEndo' A)).wIndex
              ⟨(params ++ [RType'.o], τ'), Sum.inr (Sum.inr ⟨params, rfl⟩)⟩ _).mpr
            (fun i => (clauses i).2)⟩ :=
  rfl

/-- The model interpreting an explicit definition's body over the primed
standard carriers: constructors and application read as usual, each saturated
hole read by the recursive result `ih` of the referenced identifier, and each
curried hole by the currying (`curryInterp'`) of that recursive result. Mirror
of the legacy `defnModel`. -/
def defnModel' (A : AlgSig) (n : Nat) (holeIdx' : Fin n → List RType' × RType')
    (ih : ∀ j : Fin n,
      (∀ i : Fin (holeIdx' j).1.length,
        RType'.interp (FreeAlg' A) ((holeIdx' j).1.get i)) →
        RType'.interp (FreeAlg' A) (holeIdx' j).2) :
    SortedModel (defnSig' A n holeIdx') where
  carrier := RType'.interp (FreeAlg' A)
  interpOp op args :=
    match op with
    | Sum.inl (Sum.inl (Sum.inl cop)) => stdConstructorInterp' A cop args
    | Sum.inl (Sum.inl (Sum.inr aop)) => stdAppInterp' A aop args
    | Sum.inl (Sum.inr j) => ih j args
    | Sum.inr j => curryInterp' A (holeIdx' j).1 (holeIdx' j).2 (ih j)

/-- The environment over `params ++ replicate n σ` built from a parameter
environment and `n` values at sort `σ`: the recursive results (`mrec'`) or the
subterms (`frec'`) of a recurrence step. Mirror of the legacy `childEnv`. -/
def childEnv' {C : RType' → Type} (params : List RType') (σ : RType') (n : Nat)
    (xvec : ∀ i : Fin params.length, C (params.get i))
    (rest : Fin n → C σ)
    (k : Fin (params ++ List.replicate n σ).length) :
    C ((params ++ List.replicate n σ).get k) :=
  if h : k.val < params.length then
    cast (congrArg C (get_append_lt params (List.replicate n σ) k h).symm)
      (xvec ⟨k.val, h⟩)
  else
    have hb : k.val - params.length < n := by
      have hlen : (params ++ List.replicate n σ).length = params.length + n := by
        rw [List.length_append, List.length_replicate]
      have hk : k.val < params.length + n := Nat.lt_of_lt_of_eq k.isLt hlen
      omega
    have hget : (params ++ List.replicate n σ).get k = σ := by
      rw [get_append_ge params (List.replicate n σ) k h]
      simp [List.get_eq_getElem, List.getElem_replicate]
    cast (congrArg C hget.symm) (rest ⟨k.val - params.length, hb⟩)

/-- The parameter environment read off a recurrence context `params ++ [ω]`.
Mirror of the legacy `envHead`. -/
def envHead' {C : RType' → Type} (params : List RType') (ω : RType')
    (ρ : ∀ k : Fin (params ++ [ω]).length, C ((params ++ [ω]).get k)) :
    ∀ i : Fin params.length, C (params.get i) :=
  fun i => cast (congrArg C (get_finAppL params [ω] i)) (ρ (finAppL params [ω] i))

/-- The recurrence argument read off a recurrence context `params ++ [ω]`.
Mirror of the legacy `envLast`. -/
def envLast' {C : RType' → Type} (params : List RType') (ω : RType')
    (ρ : ∀ k : Fin (params ++ [ω]).length, C ((params ++ [ω]).get k)) : C ω :=
  let idx : Fin [ω].length := ⟨0, by simp⟩
  cast (congrArg C (get_finAppR params [ω] idx)) (ρ (finAppR params [ω] idx))

/-- The recursion step of `RIdent'.interp` at one identifier node: a `defn'`
folds its body against `defnModel'`; a `mrec'` recurses on the recurrence
argument with the monotonic step (parameters and recursive results); a `frec'`
recurses with the flat step (parameters and subterms). Mirror of the legacy
`RIdent.interpStep`. -/
def RIdent'.interpStep (A : AlgSig) (Γ' : List RType') (τ' : RType')
    (shape : IdentShape' A Γ' τ')
    (ih : ∀ d : IdentDir' A Γ' τ' shape,
      (∀ i : Fin (identTarget' A Γ' τ' shape d).1.length,
        RType'.interp (FreeAlg' A) ((identTarget' A Γ' τ' shape d).1.get i)) →
        RType'.interp (FreeAlg' A) (identTarget' A Γ' τ' shape d).2) :
    (∀ i : Fin Γ'.length, RType'.interp (FreeAlg' A) (Γ'.get i)) →
      RType'.interp (FreeAlg' A) τ' := by
  rcases shape with d | ⟨params, rfl⟩ | ⟨params, rfl⟩
  · exact fun ρ => Tm'.eval (defnModel' A d.numHoles d.holeIdx' ih) ρ d.body
  · exact fun ρ =>
      FreeAlg'.recurse (A := A) (P := Unit)
        (fun i _ _sub phi =>
          ih i (childEnv' params τ' (A.ar i) (envHead' params (RType'.omega τ') ρ) phi))
        () (envLast' params (RType'.omega τ') ρ)
  · exact fun ρ =>
      FreeAlg'.recurse (A := A) (P := Unit)
        (fun i _ sub _phi =>
          ih i (childEnv' params RType'.o (A.ar i) (envHead' params RType'.o ρ)
            (fun j => sub j)))
        () (envLast' params RType'.o ρ)

/-- The interpretation carrier family: at an index `(Γ', τ')`, functions from an
environment at the context `Γ'` to a value at the result sort `τ'`. The target
family of the `SlicePFunctor.W.elim` fold realizing `RIdent'.interp`. -/
def RIdent'.interpFam (A : AlgSig) (p : List RType' × RType') : Type :=
  (∀ i : Fin p.1.length, RType'.interp (FreeAlg' A) (p.1.get i)) →
    RType'.interp (FreeAlg' A) p.2

/-- The slice algebra of the `SlicePFunctor.W.elim` fold realizing
`RIdent'.interp`, at the sigma carrier `Σ p, RIdent'.interpFam A p` with index
map `Sigma.fst`: a node applies `RIdent'.interpStep` to the children's
interpretations, each transported along its pinned index (the compatibility of
the folded child). The `SlicePFunctor.FreeM.elimAlg` idiom
(`GebLean/SliceW/FreeM.lean`) at the identifier endofunctor. -/
def RIdent'.interpAlg (A : AlgSig) :
    (toSlice (identEndo' A)).toSliceDomPFunctor.Obj
        (Sigma.fst (β := RIdent'.interpFam A)) →
      Σ p, RIdent'.interpFam A p :=
  fun z => ⟨(toSlice (identEndo' A)).q z.1.1,
    RIdent'.interpStep A z.1.1.1.1 z.1.1.1.2 z.1.1.2
      (fun b => cast (congrArg (RIdent'.interpFam A)
        (((toSlice (identEndo' A)).toSliceDomPFunctor.compatible_iff
          (Sigma.fst (β := RIdent'.interpFam A)) z.1.1 z.1.2).mp z.2 b)) (z.1.2 b).2)⟩

/-- The `RIdent'.interpAlg` algebra lies over the index type: its sigma index is
the identifier endofunctor's output index, by the shape-output map `q`. -/
theorem RIdent'.interpAlg_over (A : AlgSig) :
    Sigma.fst ∘ RIdent'.interpAlg A =
      (toSlice (identEndo' A)).obj (Sigma.fst (β := RIdent'.interpFam A)) :=
  rfl

/-- The denotation of a primed identifier over the standard carriers
`RType'.interp (FreeAlg' A)`: a function from an environment at the identifier's
context to a value at its result sort. Realized by a single
`SlicePFunctor.W.elim` at the sigma carrier `Σ p, RIdent'.interpFam A p` with
index map `Sigma.fst`, transporting the final value along the fiber proof (the
`SlicePFunctor.FreeM.elim` idiom, `GebLean/SliceW/FreeM.lean`). Mirror of the
legacy `RIdent.interp`. -/
def RIdent'.interp {A : AlgSig} {Γ' : List RType'} {τ' : RType'} (f : RIdent' A Γ' τ') :
    (∀ i : Fin Γ'.length, RType'.interp (FreeAlg' A) (Γ'.get i)) →
      RType'.interp (FreeAlg' A) τ' :=
  cast (congrArg (RIdent'.interpFam A)
      ((congrFun (SlicePFunctor.W.comp_elim (toSlice (identEndo' A))
        (Σ p, RIdent'.interpFam A p) Sigma.fst (RIdent'.interpAlg A)
        (RIdent'.interpAlg_over A)) f.1).trans f.2))
    (SlicePFunctor.W.elim (toSlice (identEndo' A)) (Σ p, RIdent'.interpFam A p)
      Sigma.fst (RIdent'.interpAlg A) (RIdent'.interpAlg_over A) f.1).2

/-- The computation rule of `RIdent'.interp` at a `defn'` node: the
interpretation of an explicit definition folds the body against `defnModel'`,
with each hole read by the interpretation of the corresponding child. From the
`SlicePFunctor.W.elim` computation at the `val_defn` form (the `defn'` branch of
`RIdent'.interpStep`). -/
theorem RIdent'.interp_defn {A : AlgSig} {Γ' : List RType'} {τ' : RType'}
    (d : DefnShape' A Γ' τ')
    (children : (j : Fin d.numHoles) → RIdent' A (d.holeIdx' j).1 (d.holeIdx' j).2) :
    (RIdent'.defn d children).interp =
      fun ρ => Tm'.eval (defnModel' A d.numHoles d.holeIdx' (fun j => (children j).interp))
        ρ d.body :=
  rfl

/-- The computation rule of `RIdent'.interp` at a `mrec'` node: the
interpretation of a ramified monotonic recurrence recurses on the recurrence
argument by `FreeAlg'.recurse`, the monotonic step reading the parameters and
the recursive results. From the `SlicePFunctor.W.elim` computation at the
`val_mrec` form (the `mrec'` branch of `RIdent'.interpStep`). -/
theorem RIdent'.interp_mrec {A : AlgSig} (params : List RType') (τ' : RType')
    (steps : (i : A.B) → RIdent' A (params ++ List.replicate (A.ar i) τ') τ') :
    (RIdent'.mrec params τ' steps).interp =
      fun ρ => FreeAlg'.recurse (A := A) (P := Unit)
        (fun i _ _sub phi => (steps i).interp
          (childEnv' params τ' (A.ar i) (envHead' params (RType'.omega τ') ρ) phi))
        () (envLast' params (RType'.omega τ') ρ) :=
  rfl

/-- The computation rule of `RIdent'.interp` at a `frec'` node: the
interpretation of a flat recurrence recurses on the recurrence argument by
`FreeAlg'.recurse`, the flat step reading the parameters and the subterms. From
the `SlicePFunctor.W.elim` computation at the `val_frec` form (the `frec'`
branch of `RIdent'.interpStep`). -/
theorem RIdent'.interp_frec {A : AlgSig} (params : List RType') (τ' : RType')
    (clauses : (i : A.B) → RIdent' A (params ++ List.replicate (A.ar i) RType'.o) τ') :
    (RIdent'.frec params τ' clauses).interp =
      fun ρ => FreeAlg'.recurse (A := A) (P := Unit)
        (fun i _ sub _phi => (clauses i).interp
          (childEnv' params RType'.o (A.ar i) (envHead' params RType'.o ρ) (fun j => sub j)))
        () (envLast' params RType'.o ρ) :=
  rfl

end GebLean.Ramified.Polynomial
