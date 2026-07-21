import GebLean.Ramified.Polynomial.HigherOrder

/-!
# First-order sub-theories and the inclusion functor on the polynomial stack

The first-order sub-theories of the r-type instantiation of Leivant's
higher-type ramified recurrence, over the primed identifier layer `RIdent'`
(`GebLean/Ramified/Polynomial/Ident.lean`). A first-order identifier is one whose
arities and result are tower sorts `Omega^m o` and whose defining data stays
within the tower sorts: recurrences run at tower object sorts only ("recurrence
restricted to object types of the form `Omega^m o`", Leivant III section 2.4(3),
p. 216), and explicit-definition bodies use no genuine higher type (no
application, no curried identifier occurrence at an arrow sort). The restriction
is on identifier formation — signature-level, not on the objects (the sorts are
the full `RType'`, and the tower-context full subcategory is neither the
first-order system nor a collapse). `RIdent'.FirstOrder` carves out the permitted
identifiers, `firstOrderPresentation` is the sub-theory presentation (with the
identifier summands restricted to the `FirstOrder` subtype), and `foInclusion` is
the inclusion functor of the sub-theory's syntactic category into the host
`RMRecCat'`.

The inclusion is a genuine functor: unlike the algebra-transport of
`GebLean/Ramified/Algebras.lean`, which changes the base algebra and so does not
descend to the interpretative quotient, the first-order inclusion keeps the same
algebra and standard model. The restricted operations map onto the identical host
operations, interpretations agree on the nose (`foTm_eval`), and
well-definedness on the quotient is immediate: A-equal restricted terms are
A-equal host terms, since both sides denote in the same standard model.

In the tier-vector notation of Danner, Leivant, Marion, and others (DLMZ; DOI
`10.4204/EPTCS.23.4`, adopted for prose exposition only), a first-order
sub-theory sits at a pair of tiers `i < j`: the recurrence argument is drawn from
the object types of one tier and the recursive results from a strictly lower
tier. Over the `1 + X` word algebra the monadic sub-theory is the tier fragment
at `1 + X`, the polyadic one at `1 + 2X`. Here the tiers are read off the tower
sorts `Omega^m o` of the shared `RType'` sort object.

## Main definitions

* `Tm'.TowerSorts` — the body-level restriction: every subterm sort is a tower
  sort.
* `RIdent'.ShapeFO` — the former-specific first-order condition on an identifier
  shape.
* `RIdent'.FirstOrder` — first-order identifier formation over `A`.
* `foIdentSig`, `foIdentConstSig`, `firstOrderSig`, `firstOrderModel`,
  `firstOrderPresentation` — the first-order sub-theory presentation over `A`.
* `foOp`, `foTm` — the operation and term translations into the host
  higher-order signature.
* `foHomMap`, `foInclusion` — the morphism map and the inclusion functor of the
  sub-theory's syntactic category into `RMRecCat' A`.

## Main statements

* `Tm'.towerSorts_var`, `Tm'.towerSorts_op` — the unfolding of the body-level
  restriction at a variable and at an operation.
* `RIdent'.firstOrder_defn`, `RIdent'.firstOrder_mrec`, `RIdent'.firstOrder_frec`
  — the unfolding of first-order formation at the three schema formers.
* `foOp_eval` — the two standard models agree on a translated operation.
* `foTm_eval` — the term translation preserves interpretation at the standard
  model.

## Implementation notes

`Tm'.TowerSorts` and `RIdent'.FirstOrder` are recursive `Prop`s realized by
`SlicePFunctor.W.RecProp` over the underlying slice `W`-tree, following
`RType'.IsTower` (`GebLean/Ramified/Polynomial/RType.lean`): at each node
`RIdent'.FirstOrder` checks that the context and result are tower sorts, that the
former-specific data conforms (`RIdent'.ShapeFO`: for `defn'`, the body's subterm
sorts are all tower via `Tm'.TowerSorts`, which excludes application — whose
function argument sits at an arrow sort — and curried identifier occurrences at
arrow sorts; for `mrec'` / `frec'`, the tower conditions on the context already
restrict the recurrence argument to a tower object sort), and it recurses into the
referenced identifiers. The identifier summands of `firstOrderPresentation` range
over the subtype `{f : RIdent' A Γ' τ' // f.FirstOrder}`, in both the saturated
(`foIdentSig`) and constant (`foIdentConstSig`) forms.

`foOp` translates each restricted operation to the identical host operation
(dropping the `FirstOrder` proof); it preserves arity and result definitionally,
so `foTm` — a `SlicePFunctor.FreeM.elim` fold (`GebLean/SliceW/FreeM.lean`) —
rebuilds a restricted term as a host term with no transport beyond the reindexing
already present at each node. `foTm_eval` is a `SlicePFunctor.W.induction` over
the underlying tree, fibrewise over the sort index, whose operation case reduces
to `foOp_eval`. The functor's `map` lifts `foTm` through the interpretative
quotient; its identity and composition laws are discharged by `Quotient.sound`
from `foTm_eval` and `Tm'.eval_subst`, without a syntactic
substitution-commutation lemma.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`. The restriction of
recurrence to object types of the form `Omega^m o` is section 2.4(3), p. 216;
addition `+ : o, Omega o -> o` and multiplication `x : (Omega o)^2 -> o`, the
first-order examples, are section 2.4(2); every object sort denotes a copy of the
base carrier in section 2.7. The tier-vector notation for the sub-theories
follows N. Danner, D. Leivant, J.-Y. Marion, et al. (DLMZ), DOI
`10.4204/EPTCS.23.4` (adopted for prose exposition only). The first-order
polynomial-time results this layer is intended to carry are D. Leivant,
"Ramified recurrence and computational complexity I: Word recurrence and
poly-time", Feasible Mathematics II, Birkhauser, 1995, 320-343, DOI
`10.1007/978-1-4612-2566-9_11`.

## Tags

ramified recurrence, first-order, sub-theory, tower sort, tier, presentation,
syntactic category, inclusion functor, slice category, W-type
-/

namespace GebLean.Ramified.Polynomial

open GebLean.Ramified GebLean.PolyBridge SlicePFunctor CategoryTheory

/-- The body-level first-order restriction: every subterm sort of `t` is a tower
sort `Omega^m o`. A recursive `Prop` over the underlying slice `W`-tree, native
via `SlicePFunctor.W.RecProp`, with the `Sum` shape split of the translate
augmentation: at a variable leaf the sort is checked directly; at an operation
node the result sort is checked and the restriction recurses into the arguments.
Since a tower sort is never an arrow sort, this excludes any genuine higher type
in the body: an application has an arrow-sorted function argument, and a curried
identifier occurrence at a nonempty context has an arrow result sort. -/
def Tm'.TowerSorts {sig : SortedSig RType'} {Γ : Ctx RType'} {s : RType'}
    (t : Tm' sig Γ s) : Prop :=
  W.RecProp (F := translate Γ.get (toSlice sig.polyEndo))
    (fun x ih => match x, ih with
      | ⟨⟨Sum.inl i, _⟩, _⟩, _ => RType'.IsTower (Γ.get i)
      | ⟨⟨Sum.inr ⟨_, o, _⟩, _⟩, _⟩, ih => RType'.IsTower (sig.result o) ∧ ∀ e, ih e)
    t.1

/-- The body-level restriction at a variable term is the tower-sort condition on
the variable's sort. -/
@[simp] theorem Tm'.towerSorts_var {sig : SortedSig RType'} {Γ : Ctx RType'}
    (i : Fin Γ.length) :
    (Tm'.var (sig := sig) i).TowerSorts = RType'.IsTower (Γ.get i) := rfl

/-- The body-level restriction at an operation term is the tower-sort condition
on the result sort together with the restriction at each argument. -/
@[simp] theorem Tm'.towerSorts_op {sig : SortedSig RType'} {Γ : Ctx RType'}
    (o : sig.Op)
    (args : ∀ i : Fin (sig.arity o).length, Tm' sig Γ ((sig.arity o).get i)) :
    (Tm'.op o args).TowerSorts
      = (RType'.IsTower (sig.result o) ∧ ∀ e, (args e).TowerSorts) := rfl

/-- The former-specific first-order condition on an identifier shape: an explicit
definition's body has all-tower subterm sorts (`Tm'.TowerSorts`); a `mrec'` or
`frec'` imposes no extra shape condition, the tower conditions on the context and
result already restricting the recurrence argument (at `Omega tau` / `o`) to a
tower object sort (Leivant III section 2.4(3), p. 216). -/
def RIdent'.ShapeFO {A : AlgSig} {Γ' : List RType'} {τ' : RType'} :
    IdentShape' A Γ' τ' → Prop
  | Sum.inl d => d.body.TowerSorts
  | Sum.inr _ => True

/-- First-order identifier formation over `A` (Leivant III section 2.4(3),
p. 216, DOI `10.1016/S0168-0072(98)00040-2`): the identifiers whose context and
result are tower sorts `Omega^m o`, whose former-specific data conforms
(`RIdent'.ShapeFO`), and whose referenced identifiers are themselves first-order.
A recursive `Prop` over the identifier tree, native via
`SlicePFunctor.W.RecProp`, following `RType'.IsTower`
(`GebLean/Ramified/Polynomial/RType.lean`). The sub-theory keeps the host's term
and category layers; only identifier formation is restricted. -/
def RIdent'.FirstOrder {A : AlgSig} {Γ' : List RType'} {τ' : RType'}
    (f : RIdent' A Γ' τ') : Prop :=
  W.RecProp (F := toSlice (identEndo' A))
    (fun x ih => match x, ih with
      | ⟨⟨⟨idx, shape⟩, _⟩, _⟩, ih =>
        (∀ i : Fin idx.1.length, RType'.IsTower (idx.1.get i)) ∧ RType'.IsTower idx.2 ∧
          RIdent'.ShapeFO shape ∧ ∀ e, ih e)
    f.1

/-- First-order formation at an explicit definition: tower context and result,
all-tower body sorts, and first-order referenced identifiers. -/
@[simp] theorem RIdent'.firstOrder_defn {A : AlgSig} {Γ' : List RType'} {τ' : RType'}
    (d : DefnShape' A Γ' τ')
    (children : (j : Fin d.numHoles) → RIdent' A (d.holeIdx' j).1 (d.holeIdx' j).2) :
    (RIdent'.defn d children).FirstOrder
      = ((∀ i : Fin Γ'.length, RType'.IsTower (Γ'.get i)) ∧ RType'.IsTower τ' ∧
          d.body.TowerSorts ∧ ∀ j, (children j).FirstOrder) := rfl

/-- First-order formation at a ramified monotonic recurrence: tower context and
result, and first-order step identifiers. -/
@[simp] theorem RIdent'.firstOrder_mrec {A : AlgSig} (params : List RType') (τ' : RType')
    (steps : (i : A.B) → RIdent' A (params ++ List.replicate (A.ar i) τ') τ') :
    (RIdent'.mrec params τ' steps).FirstOrder
      = ((∀ i : Fin (params ++ [RType'.omega τ']).length,
            RType'.IsTower ((params ++ [RType'.omega τ']).get i)) ∧
          RType'.IsTower τ' ∧ ∀ i, (steps i).FirstOrder) :=
  propext ⟨fun h => ⟨h.1, h.2.1, h.2.2.2⟩, fun h => ⟨h.1, h.2.1, trivial, h.2.2⟩⟩

/-- First-order formation at a flat recurrence: tower context and result, and
first-order clause identifiers. -/
@[simp] theorem RIdent'.firstOrder_frec {A : AlgSig} (params : List RType') (τ' : RType')
    (clauses : (i : A.B) → RIdent' A (params ++ List.replicate (A.ar i) RType'.o) τ') :
    (RIdent'.frec params τ' clauses).FirstOrder
      = ((∀ i : Fin (params ++ [RType'.o]).length,
            RType'.IsTower ((params ++ [RType'.o]).get i)) ∧
          RType'.IsTower τ' ∧ ∀ i, (clauses i).FirstOrder) :=
  propext ⟨fun h => ⟨h.1, h.2.1, h.2.2.2⟩, fun h => ⟨h.1, h.2.1, trivial, h.2.2⟩⟩

/-- The saturated first-order identifier summand: one operation per first-order
identifier, of its context as arity and result sort as result. The restriction of
`identSig'` to the `FirstOrder` subtype (monadic at `1 + X`, polyadic at
`1 + 2X`). -/
def foIdentSig (A : AlgSig) : SortedSig RType' where
  Op := Σ Γ' : List RType', Σ τ' : RType', { f : RIdent' A Γ' τ' // f.FirstOrder }
  arity op := op.1
  result op := op.2.1

/-- The first-order identifier-constant summand: one nullary operation per
first-order identifier, of its curried arrow sort as result. The restriction of
`identConstSig'` to the `FirstOrder` subtype. -/
def foIdentConstSig (A : AlgSig) : SortedSig RType' where
  Op := Σ Γ' : List RType', Σ τ' : RType', { f : RIdent' A Γ' τ' // f.FirstOrder }
  arity _op := []
  result op := RType'.curried op.1 op.2.1

/-- The signature of the first-order sub-theory over `A`: the constructor summand
at every object sort, application, and the first-order identifiers as saturated
operations and as nullary constants at the curried arrow sorts. The first-order
restriction is on the identifier summands only; the constructor and application
summands are those of `higherOrder' A`. -/
def firstOrderSig (A : AlgSig) : SortedSig RType' :=
  ((((constructorSig A RType'.IsObj).sum appSig').sum (foIdentSig A)).sum
    (foIdentConstSig A))

/-- The standard model of the first-order sub-theory over `A`: the standard
carriers, with constructors and application read as usual and each first-order
identifier (saturated or constant) read by its underlying identifier's
denotation. Agrees with `higherOrderModel' A` on the shared operations. -/
def firstOrderModel (A : AlgSig) : SortedModel (firstOrderSig A) where
  carrier := RType'.interp (FreeAlg' A)
  interpOp op args :=
    match op with
    | Sum.inl (Sum.inl (Sum.inl cop)) => stdConstructorInterp' A cop args
    | Sum.inl (Sum.inl (Sum.inr aop)) => stdAppInterp' A aop args
    | Sum.inl (Sum.inr iop) => iop.2.2.val.interp args
    | Sum.inr icop => curryInterp' A icop.1 icop.2.1 icop.2.2.val.interp

/-- The first-order sub-theory presentation over `A` (Leivant III section
2.4(3)): the first-order signature with the standard model. Monadic at `1 + X`,
polyadic at `1 + 2X`; the tiers are read off the tower sorts `Omega^m o` of the
shared `RType'` sort object. -/
def firstOrderPresentation (A : AlgSig) : Presentation where
  S := RType'
  sig := firstOrderSig A
  IsObj := RType'.IsObj
  alg := A
  std := firstOrderModel A

/-- The host term for one restricted operation node applied to already-translated
argument terms: the identical host operation, dropping the `FirstOrder` proof
from the identifier summands. Defined by cases on the operation so that its arity
and result reduce to the restricted ones in each branch (they are not
definitionally equal for a generic operation). -/
def foOp (A : AlgSig) {Γ : Ctx RType'} (op : (firstOrderSig A).Op)
    (args : ∀ e : Fin ((firstOrderSig A).arity op).length,
      Tm' (higherOrder' A).sig Γ (((firstOrderSig A).arity op).get e)) :
    Tm' (higherOrder' A).sig Γ ((firstOrderSig A).result op) :=
  match op with
  | Sum.inl (Sum.inl x) =>
    Tm'.op (sig := (higherOrder' A).sig) (Sum.inl (Sum.inl x)) args
  | Sum.inl (Sum.inr iop) =>
    Tm'.op (sig := (higherOrder' A).sig)
      (Sum.inl (Sum.inr ⟨iop.1, iop.2.1, iop.2.2.val⟩)) args
  | Sum.inr icop =>
    Tm'.op (sig := (higherOrder' A).sig)
      (Sum.inr ⟨icop.1, icop.2.1, icop.2.2.val⟩) args

/-- The term translation of the inclusion: rebuild a restricted term as a host
term, translating each operation node by `foOp` and keeping variables. Realized
by the slice free monad's fold `SlicePFunctor.FreeM.elim`
(`GebLean/SliceW/FreeM.lean`), following `Tm'.eval`'s pattern. -/
def foTm (A : AlgSig) {Γ : Ctx RType'} {s : RType'}
    (t : Tm' (firstOrderSig A) Γ s) : Tm' (higherOrder' A).sig Γ s :=
  FreeM.elim (v := Γ.get) (F := toSlice (firstOrderSig A).polyEndo)
    (fun x => Tm' (higherOrder' A).sig Γ x)
    (fun _ a => Tm'.reind a.2 (Tm'.var a.1))
    (fun a ih => match a, ih with
      | ⟨_, o, h⟩, ih => Tm'.reind h (foOp A o ih))
    t

/-- Evaluating the host translation of an operation node in `higherOrderModel' A`
equals interpreting the restricted operation in `firstOrderModel A`, on the
evaluated arguments: the two standard models agree on a translated operation.
Holds by cases on the operation. -/
theorem foOp_eval (A : AlgSig) {Γ : Ctx RType'} (op : (firstOrderSig A).Op)
    (args : ∀ e : Fin ((firstOrderSig A).arity op).length,
      Tm' (higherOrder' A).sig Γ (((firstOrderSig A).arity op).get e))
    (ρ : (standardModel (higherOrder' A)).Env Γ) :
    (foOp A op args).eval (standardModel (higherOrder' A)) ρ
      = (firstOrderModel A).interpOp op
          (fun e => (args e).eval (standardModel (higherOrder' A)) ρ) := by
  rcases op with ((cop | aop) | iop) | icop <;> rfl

/-- The term translation preserves interpretation at the standard model: a
restricted term and its host translation denote the same value under every
environment. Proved by `SlicePFunctor.W.induction` over the underlying tree,
fibrewise over the sort index; the operation case reduces to `foOp_eval`. -/
theorem foTm_eval (A : AlgSig) {Γ : Ctx RType'} {s : RType'}
    (t : Tm' (firstOrderSig A) Γ s)
    (ρ : (standardModel (higherOrder' A)).Env Γ) :
    (foTm A t).eval (standardModel (higherOrder' A)) ρ
      = t.eval (standardModel (firstOrderPresentation A)) ρ := by
  have key : ∀ w : (translate Γ.get (toSlice (firstOrderSig A).polyEndo)).W,
      ∀ (x : RType')
        (hx : (translate Γ.get (toSlice (firstOrderSig A).polyEndo)).wIndex w = x),
      (foTm A (⟨w, hx⟩ : Tm' (firstOrderSig A) Γ x)).eval
          (standardModel (higherOrder' A)) ρ
        = Tm'.eval (standardModel (firstOrderPresentation A)) ρ
            (⟨w, hx⟩ : Tm' (firstOrderSig A) Γ x) := by
    refine W.induction (F := translate Γ.get (toSlice (firstOrderSig A).polyEndo)) ?_
    intro y ihc x hx
    subst hx
    obtain ⟨⟨a, fch⟩, hc⟩ := y
    cases a with
    | inl i =>
      have hterm : (⟨W.mk ⟨⟨Sum.inl i, fch⟩, hc⟩, rfl⟩ :
          Tm' (firstOrderSig A) Γ _) = Tm'.var i :=
        Subtype.ext (congrArg W.mk
          (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun e => e.elim)))))
      have hvar : foTm A (Tm'.var (sig := firstOrderSig A) (Γ := Γ) i) = Tm'.var i :=
        FreeM.elim_pure _ _ _ ⟨i, rfl⟩
      rw [hterm]
      change Tm'.eval (standardModel (higherOrder' A)) ρ
            (foTm A (Tm'.var (sig := firstOrderSig A) (Γ := Γ) i))
          = Tm'.eval (standardModel (firstOrderPresentation A)) ρ
            (Tm'.var (sig := firstOrderSig A) (Γ := Γ) i)
      rw [hvar]
      exact (Tm'.eval_var _ ρ i).trans (Tm'.eval_var _ ρ i).symm
    | inr a =>
      obtain ⟨xa, o, hres⟩ := a
      subst hres
      have hpf :=
        ((translate Γ.get (toSlice (firstOrderSig A).polyEndo)).toSliceDomPFunctor.compatible_iff
          (translate Γ.get (toSlice (firstOrderSig A).polyEndo)).wIndex
          (Sum.inr ⟨(firstOrderSig A).result o, o, rfl⟩) fch).mp hc
      have hterm : (⟨W.mk ⟨⟨Sum.inr ⟨(firstOrderSig A).result o, o, rfl⟩, fch⟩, hc⟩, rfl⟩ :
          Tm' (firstOrderSig A) Γ _) = Tm'.op o (fun b => ⟨fch b, hpf b⟩) := Subtype.ext rfl
      have hfo : foTm A (Tm'.op (sig := firstOrderSig A) (Γ := Γ) o (fun b => ⟨fch b, hpf b⟩))
          = foOp A o (fun b => foTm A (⟨fch b, hpf b⟩ : Tm' (firstOrderSig A) Γ _)) :=
        FreeM.elim_node (v := Γ.get) (F := toSlice (firstOrderSig A).polyEndo) _ _ _
          ⟨(firstOrderSig A).result o, o, rfl⟩ _
      rw [hterm]
      change Tm'.eval (standardModel (higherOrder' A)) ρ
            (foTm A (Tm'.op (sig := firstOrderSig A) (Γ := Γ) o (fun b => ⟨fch b, hpf b⟩)))
          = Tm'.eval (standardModel (firstOrderPresentation A)) ρ
            (Tm'.op (sig := firstOrderSig A) (Γ := Γ) o (fun b => ⟨fch b, hpf b⟩))
      rw [hfo, foOp_eval]
      exact (congrArg ((firstOrderModel A).interpOp o)
        (funext fun b => ihc b _ (hpf b))).trans
          (Tm'.eval_op (standardModel (firstOrderPresentation A)) ρ o _).symm
  exact key t.1 s t.2

/-- The morphism map of the inclusion: translate a representative tuple by `foTm`
and re-quotient. Well-defined on the interpretative quotient because `foTm`
preserves interpretation (`foTm_eval`), so A-equal restricted tuples map to
A-equal host tuples. -/
def foHomMap (A : AlgSig) (Γ Δ : Ctx RType')
    (f : Hom' (firstOrderPresentation A) (interpQuotRel' (firstOrderPresentation A)) Γ Δ) :
    Hom' (higherOrder' A) (interpQuotRel' (higherOrder' A)) Γ Δ :=
  Quotient.liftOn f (fun f' => Quotient.mk _ (fun i => foTm A (f' i)))
    (fun f₁ f₂ h => Quotient.sound (fun i ρ => by
      rw [foTm_eval, foTm_eval]; exact h i ρ))

/-- The inclusion functor of the first-order sub-theory's syntactic category into
the host `RMRecCat' A` (Leivant III section 2.4(3)): the identity on objects
(contexts) and `foHomMap` on morphisms. A genuine functor — the inclusion keeps
the same algebra and standard model, so its identity and composition laws hold by
interpretative equality (`foTm_eval`, `Tm'.eval_subst`), with no quotient
obstruction. -/
def foInclusion (A : AlgSig) :
    SynCat' (firstOrderPresentation A) (interpQuotRel' (firstOrderPresentation A)) ⥤
      RMRecCat' A where
  obj Γ := Γ
  map {Γ Δ} f := foHomMap A Γ Δ f
  map_id Γ := rfl
  map_comp {Γ Δ E} f g := by
    induction f using Quotient.ind with
    | _ f' =>
    induction g using Quotient.ind with
    | _ g' =>
      refine Quotient.sound (fun i ρ => ?_)
      simp only [HomTuple'.comp, foTm_eval, Tm'.eval_subst]
      exact Tm'.eval_subst (standardModel (firstOrderPresentation A)) (g' i) f' ρ

end GebLean.Ramified.Polynomial
