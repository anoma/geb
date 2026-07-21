import GebLean.Ramified.Interp
import GebLean.Ramified.Polynomial.Term

/-!
# Primed evaluation and the interpretative quotient

Evaluation of primed terms (`GebLean/Ramified/Polynomial/Term.lean`) in a
sorted model, the interpretative setoid they induce, and the agreement of primed
evaluation with the legacy evaluation across the bridge equivalence. `Tm'.eval`
folds a primed term against a model over an environment, realized by the slice
free monad's fold `SlicePFunctor.FreeM.elim` (`GebLean/SliceW/FreeM.lean`);
`Tm'.eval_subst` is the semantic clone law. `QuotRel'`, `interpSetoid'`, and
`interpQuotRel'` mirror the legacy `QuotRel`, `interpSetoid`, `interpQuotRel`
(`GebLean/Ramified/Interp.lean`) for the primed layer, reusing the sort-generic
`SortedModel`, `Presentation`, and `standardModel`. `tmSliceEquiv_eval` records
that primed evaluation agrees with the legacy `Tm.eval` across `tmSliceEquiv`.

## Main definitions

* `Tm'.eval` — the value of a primed term in a model over an environment (the
  slice free monad's fold).
* `QuotRel'` — a quotient relation for the primed syntactic category: a per-hom
  setoid family closed under substitution in both positions.
* `interpSetoid'` — extensional equality of `Tm'.eval` at the standard model.
* `interpQuotRel'` — the `interpSetoid'` family with its
  substitution-congruence law, as a `QuotRel'`.

## Main statements

* `Tm'.eval_var` — evaluation of a variable reads the environment.
* `Tm'.eval_op` — evaluation of an operation applies `interpOp` to the
  evaluated arguments.
* `Tm'.eval_transport` — evaluation commutes with reindexing of its input term.
* `Tm'.eval_subst` — evaluation of a substituted term equals evaluation of the
  term under the environment that evaluates the substitution (the semantic
  clone law).
* `QuotRel'.rel_reind` — a quotient relation is preserved by reindexing.
* `tmSliceEquiv_eval` — primed evaluation agrees with the legacy `Tm.eval`
  across the bridge equivalence `tmSliceEquiv`.

## Implementation notes

`Tm'.eval` is a `SlicePFunctor.FreeM.elim` into the model's carrier family: a
leaf function reading the environment (transported along the fiber equality of a
variable's sort) and a node algebra reading the `toSlice`-shape's operation and
result equality. `Tm'.eval_var` and `Tm'.eval_op` are the fold's computation
rules `elim_pure` and `elim_node`. `tmSliceEquiv_eval` is proved by
`PolyFix.ind` on the legacy term (a bridge consumption of the legacy side),
using the bridge naturality lemmas `polyFreeMSliceEquiv_pure` /
`polyFreeMSliceEquiv_node` and the computation rules of both evaluations.
`Tm'.eval_subst` is a `SlicePFunctor.FreeM.induction` over the primed term,
independent of the bridge: the variable case reduces by `Tm'.var_subst` and
`Tm'.eval_var`, the operation case by `SlicePFunctor.FreeM.bind_node`,
`Tm'.eval_op`, and the induction hypotheses.

## References

The standard-model semantics — every object sort denotes a copy of the base
algebra's carrier — follows D. Leivant, "Ramified recurrence and computational
complexity III: Higher type recurrence and elementary complexity", Annals of
Pure and Applied Logic 96 (1999) 209-229, DOI
`10.1016/S0168-0072(98)00040-2`, section 2.7, transcribed by the legacy
`GebLean/Ramified/Interp.lean`.

## Tags

ramified recurrence, sorted model, interpretation, evaluation, setoid,
quotient, standard model, free monad, slice category
-/

namespace GebLean.Ramified.Polynomial

open GebLean.Ramified GebLean.PolyBridge SlicePFunctor CategoryTheory

variable {S : Type}

/-- The leaf function of primed evaluation: a variable leaf reads the
environment at its position and transports the value along the fiber equality
of its sort. -/
private def evalLeafFn {sig : SortedSig S} {Γ : Ctx S} (M : SortedModel sig)
    (ρ : M.Env Γ) : ∀ i, { y : Fin Γ.length // Γ.get y = i } → M.carrier i :=
  fun _ a => cast (congrArg M.carrier a.2) (ρ a.1)

/-- The node algebra of primed evaluation: a non-recursive split of the
`toSlice`-shape reading its operation and result equality, applying
`M.interpOp` to the children's values and transporting along the result-sort
equality. -/
private def evalNodeFn {sig : SortedSig S} (M : SortedModel sig) :
    ∀ a : (toSlice sig.polyEndo).A,
      ((b : (toSlice sig.polyEndo).B a) →
        M.carrier ((toSlice sig.polyEndo).rCurried a b)) →
      M.carrier ((toSlice sig.polyEndo).q a) :=
  fun a ih => match a, ih with
    | ⟨_, o, h⟩, ih => cast (congrArg M.carrier h) (M.interpOp o ih)

/-- The value of a primed term `t` in a model `M` over an environment `ρ`: the
fold of the slice free monad `Tm' sig Γ`. A variable leaf reads the environment
at its position and transports the value along the fiber equality of its sort;
an operation node applies `M.interpOp` to the recursively evaluated arguments
and transports the result along the operation's result-sort equality. Realized
by the slice free monad's fold `SlicePFunctor.FreeM.elim`
(`GebLean/SliceW/FreeM.lean`). Mirrors the legacy `Tm.eval`
(`GebLean/Ramified/Interp.lean`). -/
def Tm'.eval {sig : SortedSig S} {Γ : Ctx S} (M : SortedModel sig)
    (ρ : M.Env Γ) {s : S} (t : Tm' sig Γ s) : M.carrier s :=
  FreeM.elim M.carrier (evalLeafFn M ρ) (evalNodeFn M) t

/-- Evaluation of a variable term reads the environment at its position (the
fold's left-unit computation rule; the `rfl`-cast vanishes). Mirrors the legacy
variable evaluation. -/
theorem Tm'.eval_var {sig : SortedSig S} {Γ : Ctx S} (M : SortedModel sig)
    (ρ : M.Env Γ) (i : Fin Γ.length) :
    (Tm'.var (sig := sig) i).eval M ρ = ρ i :=
  FreeM.elim_pure M.carrier (evalLeafFn M ρ) (evalNodeFn M) ⟨i, rfl⟩

/-- Evaluation of an operation term applies `M.interpOp` to the evaluated
arguments (the fold's node computation rule; the `rfl`-cast vanishes). Mirrors
the legacy operation evaluation. -/
theorem Tm'.eval_op {sig : SortedSig S} {Γ : Ctx S} (M : SortedModel sig)
    (ρ : M.Env Γ) (o : sig.Op)
    (args : ∀ i : Fin (sig.arity o).length, Tm' sig Γ ((sig.arity o).get i)) :
    (Tm'.op o args).eval M ρ = M.interpOp o (fun i => (args i).eval M ρ) :=
  FreeM.elim_node M.carrier (evalLeafFn M ρ) (evalNodeFn M) ⟨sig.result o, ⟨o, rfl⟩⟩ args

/-- Evaluation commutes with transport of its input term along a sort equality.
A fact local to `Tm'.eval`, proved by transport elimination. Mirrors the legacy
`Tm.eval_transport`. -/
theorem Tm'.eval_transport {sig : SortedSig S} {Γ : Ctx S} (M : SortedModel sig)
    (ρ : M.Env Γ) {x y : S} (h : x = y) (t : Tm' sig Γ x) :
    (Tm'.reind h t).eval M ρ = cast (congrArg M.carrier h) (t.eval M ρ) := by
  subst h; rfl

/-- Primed evaluation agrees with the legacy `Tm.eval` across the bridge
equivalence `tmSliceEquiv`. Proved by `PolyFix.ind` on the legacy term (a bridge
consumption of the legacy side): the leaf case reduces both evaluations through
`polyFreeMSliceEquiv`-of-`pure` and `elim_pure`; the node case through
`polyFreeMSliceEquiv_node`, `elim_node`, and the legacy operation reduction with
the induction hypotheses. Mirrors the legacy operation-agreement route. -/
theorem tmSliceEquiv_eval {sig : SortedSig S} {Γ : Ctx S} {s : S}
    (M : SortedModel sig) (ρ : M.Env Γ) (t : Tm' sig Γ s) :
    (tmSliceEquiv Γ s t).eval M ρ = t.eval M ρ := by
  have aux : ∀ (x : S) (u : Tm sig Γ x),
      Tm'.eval M ρ (polyFreeMSliceEquiv (varOver Γ) sig.polyEndo x u) = Tm.eval M ρ u := by
    intro x u
    induction u using PolyFix.ind with
    | @step y i children ih =>
      cases i with
      | inl a =>
          have hpure : polyFreeMSliceEquiv (varOver Γ) sig.polyEndo y
              (PolyFix.mk y (Sum.inl a) children) = FreeM.pure a :=
            Subtype.ext (congrArg W.mk
              (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun e => e.elim)))))
          rw [hpure]
          exact FreeM.elim_pure M.carrier (evalLeafFn M ρ) (evalNodeFn M) a
      | inr o =>
          rw [polyFreeMSliceEquiv_node]
          refine Eq.trans
            (FreeM.elim_node M.carrier (evalLeafFn M ρ) (evalNodeFn M) ⟨y, o⟩ _) ?_
          exact congrArg (cast (congrArg M.carrier o.2))
            (congrArg (M.interpOp o.val) (funext ih))
  have h := aux s (tmSliceEquiv Γ s t)
  rw [show polyFreeMSliceEquiv (varOver Γ) sig.polyEndo s (tmSliceEquiv Γ s t) = t from
    Equiv.apply_symm_apply _ t] at h
  exact h.symm

/-- Evaluation of a substituted term equals evaluation of the term under the
environment obtained by evaluating the substitution (the semantic clone law).
Proved by `SlicePFunctor.FreeM.induction` over the term: the variable case by
`Tm'.var_subst` and `Tm'.eval_var`, the operation case by
`SlicePFunctor.FreeM.bind_node`, `Tm'.eval_op`, and the induction hypotheses.
Mirrors the legacy `Tm.eval_subst`. -/
theorem Tm'.eval_subst {sig : SortedSig S} {Γ Δ : Ctx S} {s : S}
    (M : SortedModel sig) (t : Tm' sig Γ s)
    (σ : ∀ i : Fin Γ.length, Tm' sig Δ (Γ.get i)) (ρ : M.Env Δ) :
    (t.subst σ).eval M ρ = t.eval M (fun i => (σ i).eval M ρ) :=
  FreeM.induction
    (motive := fun x u => Tm'.eval M ρ (Tm'.subst (u : Tm' sig Γ x) σ)
      = Tm'.eval M (fun i => (σ i).eval M ρ) u)
    (fun _ a => by
      obtain ⟨i, hi⟩ := a
      subst hi
      change Tm'.eval M ρ ((Tm'.var (sig := sig) (Γ := Γ) i).subst σ)
        = Tm'.eval M (fun j => (σ j).eval M ρ) (Tm'.var (sig := sig) (Γ := Γ) i)
      rw [Tm'.var_subst, Tm'.eval_var])
    (fun a args ih => by
      obtain ⟨_, o, hres⟩ := a
      subst hres
      change Tm'.eval M ρ ((Tm'.op (sig := sig) (Γ := Γ) o args).subst σ)
        = Tm'.eval M (fun j => (σ j).eval M ρ) (Tm'.op (sig := sig) (Γ := Γ) o args)
      rw [show (Tm'.op (sig := sig) (Γ := Γ) o args).subst σ
            = Tm'.op o (fun b => Tm'.subst (args b) σ) from FreeM.bind_node _ _ _,
        Tm'.eval_op, Tm'.eval_op]
      exact congrArg (M.interpOp o) (funext ih))
    t

/-- A quotient relation for the primed syntactic category: a per-hom setoid
family on primed terms together with the congruence law composition needs
(substitution respects the relation in both positions). Mirrors the legacy
`QuotRel`. -/
structure QuotRel' (sig : SortedSig S) where
  /-- The per-context, per-sort setoid on primed terms. -/
  rel : (Γ : Ctx S) → (s : S) → Setoid (Tm' sig Γ s)
  /-- Substitution respects the relation in both positions: related terms
  substituted by pointwise-related tuples yield related results. -/
  subst_congr :
    ∀ {Γ Δ s} (t t' : Tm' sig Γ s)
      (σ σ' : ∀ i, Tm' sig Δ (Γ.get i)),
      (rel Γ s) t t' → (∀ i, (rel Δ _) (σ i) (σ' i)) →
      (rel Δ s) (t.subst σ) (t'.subst σ')

/-- A quotient relation is preserved by reindexing along a sort equality.
Mirrors the legacy `QuotRel.rel_reind`. -/
theorem QuotRel'.rel_reind {sig : SortedSig S} (r : QuotRel' sig) {T : Ctx S}
    {a b : S} (h : a = b) {x y : Tm' sig T a} (hxy : (r.rel T a) x y) :
    (r.rel T b) (Tm'.reind h x) (Tm'.reind h y) := by
  subst h; exact hxy

/-- Extensional equality of primed evaluation at the standard model: two terms
are related when they evaluate equally under every environment. Mirrors the
legacy `interpSetoid`. -/
def interpSetoid' (P : Presentation) (Γ : Ctx P.S) (s : P.S) :
    Setoid (Tm' P.sig Γ s) where
  r t t' := ∀ ρ : (standardModel P).Env Γ,
    t.eval (standardModel P) ρ = t'.eval (standardModel P) ρ
  iseqv :=
    { refl := fun _ _ => rfl
      symm := fun h ρ => (h ρ).symm
      trans := fun h₁ h₂ ρ => (h₁ ρ).trans (h₂ ρ) }

/-- The primed interpretative quotient relation: the `interpSetoid'` family
bundled with its substitution-congruence law, discharged by `Tm'.eval_subst`.
Mirrors the legacy `interpQuotRel`. -/
def interpQuotRel' (P : Presentation) : QuotRel' P.sig where
  rel := interpSetoid' P
  subst_congr := fun t t' σ σ' htt' hσσ' ρ => by
    show (t.subst σ).eval (standardModel P) ρ =
      (t'.subst σ').eval (standardModel P) ρ
    rw [Tm'.eval_subst, Tm'.eval_subst]
    refine (htt' _).trans ?_
    congr 1
    funext i
    exact hσσ' i ρ

end GebLean.Ramified.Polynomial
