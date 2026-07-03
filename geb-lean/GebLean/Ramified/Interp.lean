import GebLean.Ramified.Term

/-!
# Sorted models and the interpretative setoid

Set-theoretic models of a multi-sorted signature, the evaluation of terms in a
model, and the setoid on terms induced by evaluation at a designated standard
model. A `SortedModel` assigns a carrier to each sort and an interpretation to
each operation; `Tm.eval` folds a term against a model over an environment;
`Tm.eval_subst` is the semantic clone law relating substitution to
reinterpretation of the environment. A `Presentation` bundles a sort type, a
signature, an object-sort predicate, the base algebra, and a standard model;
`interpSetoid` relates two terms when they evaluate equally at the standard
model under every environment, and `interpQuotRel` packages that setoid family
with its substitution-congruence law.

These definitions are novel packaging: they present the standard-model
semantics of the free-algebra conventions of Leivant III section 2.1 through
this development's polynomial-endofunctor stack (decision 8). `Tm.eval` is the
fold of the free monad `Tm sig Γ` of `GebLean/Ramified/Term.lean`, realized by
the dependent eliminator `PolyFix.ind` (`GebLean/PolyAlg.lean`); the existing
free-monad algebra machinery is phrased for `Over`-valued carriers and a single
`PolyAlg`, whereas a sorted model's carriers form an arbitrary sort-indexed
family, so the eliminator is applied directly (following the precedent
`FreeAlg.recurse` of `GebLean/Ramified/AlgSig.lean`).

## Main definitions

* `SortedModel` — a model of a sorted signature: a carrier per sort and an
  interpretation per operation.
* `SortedModel.Env` — an environment over a context: a carrier element at each
  position, of that position's sort.
* `Tm.eval` — the value of a term in a model over an environment (the free
  monad's fold).
* `Presentation` — a sort type, signature, object-sort predicate (as data), a
  base algebra, and a standard model.
* `standardModel` — the standard model of a presentation (the designated-model
  projection).
* `interpSetoid` — extensional equality of `Tm.eval` at the standard model.
* `interpQuotRel` — the `interpSetoid` family with its substitution-congruence
  law, as a `QuotRel`.

## Main statements

* `Tm.eval_subst` — evaluation of a substituted term equals evaluation of the
  term under the environment that evaluates the substitution (the semantic
  clone law).

## Implementation notes

`Tm.eval` recurses over the free monad by cases on the node index: a leaf is a
variable, whose value is read from the environment and transported along the
fiber equality of its sort; a node is an operation applied to argument terms,
whose value is `interpOp` of the recursively evaluated arguments, transported
along the operation's result-sort equality. `Tm.eval_subst`'s leaf case needs
that evaluation commutes with transport of its input term; this fact
(`Tm.eval_transport`) is local to `Tm.eval` and is proved here by transport
elimination.

## References

The standard-model semantics — every object sort denotes a copy of the base
algebra's carrier — follows D. Leivant, "Ramified recurrence and computational
complexity III: Higher type recurrence and elementary complexity", Annals of
Pure and Applied Logic 96 (1999) 209-229, DOI
`10.1016/S0168-0072(98)00040-2`, section 2.7. The interpretative-setoid
construction follows the repository precedent `GebLean.erMorNSetoid`
(`GebLean/LawvereERQuot.lean`).

## Tags

ramified recurrence, sorted model, interpretation, evaluation, setoid,
quotient, standard model, free monad
-/

namespace GebLean.Ramified

open CategoryTheory

variable {S : Type}

/-- A model of a sorted signature: a carrier type per sort and an
interpretation of each operation as a function from argument values (a value at
each arity position, of that position's sort) to a result value at the
operation's result sort. Novel packaging of the standard-model semantics of
Leivant III section 2.1. -/
structure SortedModel (sig : SortedSig S) where
  /-- The carrier of each sort. -/
  carrier : S → Type
  /-- The interpretation of each operation as a function on carrier values. -/
  interpOp : (o : sig.Op) →
    (∀ i : Fin (sig.arity o).length, carrier ((sig.arity o).get i)) →
    carrier (sig.result o)

/-- An environment over a context `Γ` in a model `M`: a carrier element at each
position of `Γ`, of that position's sort. Novel packaging. -/
def SortedModel.Env {sig : SortedSig S} (M : SortedModel sig) (Γ : Ctx S) :
    Type :=
  ∀ i : Fin Γ.length, M.carrier (Γ.get i)

/-- The value of a term `t` in a model `M` over an environment `ρ`: the fold of
the free monad `Tm sig Γ`. A variable leaf reads the environment at its position
and transports the value along the fiber equality of its sort; an operation node
applies `M.interpOp` to the recursively evaluated arguments and transports the
result along the operation's result-sort equality. Realized by the dependent
eliminator `PolyFix.ind` (decision 8; the free-monad layer of
`GebLean/PolyAlg.lean` is consumed, not rebuilt), following the precedent
`FreeAlg.recurse`. Novel packaging. -/
def Tm.eval {sig : SortedSig S} {Γ : Ctx S} (M : SortedModel sig)
    (ρ : M.Env Γ) : {s : S} → Tm sig Γ s → M.carrier s
  | _, PolyFix.mk _ (Sum.inl a) _ => a.2 ▸ ρ a.1
  | _, PolyFix.mk _ (Sum.inr o) children =>
    o.2 ▸ M.interpOp o.val (fun i => Tm.eval M ρ (children i))

/-- Evaluation commutes with transport of its input term along a sort equality.
A fact local to `Tm.eval`, proved by transport elimination. -/
theorem Tm.eval_transport {sig : SortedSig S} {Γ : Ctx S} (M : SortedModel sig)
    (ρ : M.Env Γ) {x y : S} (h : x = y) (t : Tm sig Γ x) :
    (h ▸ t).eval M ρ = h ▸ t.eval M ρ := by
  subst h; rfl

/-- Evaluation of a substituted term equals evaluation of the term under the
environment obtained by evaluating the substitution (the semantic clone law).
The fact that later makes syntactic-category composition respect the
interpretative setoid. Proved by induction on the term via `PolyFix.ind`;
the variable case uses `Tm.eval_transport`. Novel packaging. -/
theorem Tm.eval_subst {sig : SortedSig S} {Γ Δ : Ctx S} {s : S}
    (M : SortedModel sig) (t : Tm sig Γ s)
    (σ : ∀ i : Fin Γ.length, Tm sig Δ (Γ.get i)) (ρ : M.Env Δ) :
    (t.subst σ).eval M ρ = t.eval M (fun i => (σ i).eval M ρ) := by
  induction t using PolyFix.ind with
  | step i children ih =>
    cases i with
    | inl a => exact Tm.eval_transport M ρ a.2 (σ a.1)
    | inr o =>
      change o.2 ▸ M.interpOp o.val (fun i => Tm.eval M ρ (Tm.subst (children i) σ)) =
          o.2 ▸ M.interpOp o.val
            (fun i => Tm.eval M (fun i => Tm.eval M ρ (σ i)) (children i))
      congr 1
      exact congrArg (M.interpOp o.val) (funext fun i => ih i)

/-- A presentation: a sort type, a multi-sorted signature, an object-sort
predicate as plain data (plan decision 6), the base algebra whose carrier the
object sorts denote (every object sort a copy — Leivant III, DOI
`10.1016/S0168-0072(98)00040-2`, section 2.7), and the standard model. The
construction of the standard model for the higher-order system is Phase 2's
`RIdent.interp`; here it is carried as data. Novel packaging. -/
structure Presentation where
  /-- The sort type. -/
  S : Type
  /-- The multi-sorted signature. -/
  sig : SortedSig S
  /-- The object-sort predicate (plan decision 6: carried as plain data). -/
  IsObj : S → Prop
  /-- The base algebra whose carrier the object sorts denote. -/
  alg : AlgSig
  /-- The standard model. -/
  std : SortedModel sig

/-- The standard model of a presentation: the designated-model projection. In
the standard model an object sort denotes a copy of the base algebra's carrier
(Leivant III section 2.7); its construction for the higher-order system is
supplied in Phase 2. Novel packaging. -/
abbrev standardModel (P : Presentation) : SortedModel P.sig := P.std

/-- Extensional equality of evaluation at the standard model: two terms are
related when they evaluate equally under every environment. The model
dependence is structural (spec s4.2); the construction follows the repository
precedent `GebLean.erMorNSetoid` (`GebLean/LawvereERQuot.lean`). Novel
packaging. -/
def interpSetoid (P : Presentation) (Γ : Ctx P.S) (s : P.S) :
    Setoid (Tm P.sig Γ s) where
  r t t' := ∀ ρ : (standardModel P).Env Γ,
    t.eval (standardModel P) ρ = t'.eval (standardModel P) ρ
  iseqv :=
    { refl := fun _ _ => rfl
      symm := fun h ρ => (h ρ).symm
      trans := fun h₁ h₂ ρ => (h₁ ρ).trans (h₂ ρ) }

/-- The interpretative quotient relation: the `interpSetoid` family bundled with
its substitution-congruence law, discharged by `Tm.eval_subst`. The in-scope
instantiation of the relation-parametric syntactic category. Novel packaging. -/
def interpQuotRel (P : Presentation) : QuotRel P.sig where
  rel := interpSetoid P
  subst_congr := fun t t' σ σ' htt' hσσ' ρ => by
    show (t.subst σ).eval (standardModel P) ρ =
      (t'.subst σ').eval (standardModel P) ρ
    rw [Tm.eval_subst, Tm.eval_subst]
    refine (htt' _).trans ?_
    congr 1
    funext i
    exact hσσ' i ρ

end GebLean.Ramified
