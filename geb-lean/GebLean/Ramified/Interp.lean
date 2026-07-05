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
* `Tm.eval_model_morphism` — evaluation commutes with a model morphism: a
  sort-indexed family commuting with `interpOp` and matching the environments
  carries `Tm.eval` in one model to `Tm.eval` in the other.

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
    (ρ : M.Env Γ) {s : S} (t : Tm sig Γ s) : M.carrier s :=
  PolyFix.ind (P := polyTranslate (varOver Γ) sig.polyEndo)
    (motive := fun {s} _ => M.carrier s)
    (fun i children ih =>
      match i, children, ih with
      | Sum.inl a, _, _ => cast (congrArg M.carrier a.2) (ρ a.1)
      | Sum.inr o, _, ih =>
        cast (congrArg M.carrier o.2) (M.interpOp o.val ih)) t

/-- Evaluation commutes with transport of its input term along a sort equality.
A fact local to `Tm.eval`, proved by transport elimination. -/
theorem Tm.eval_transport {sig : SortedSig S} {Γ : Ctx S} (M : SortedModel sig)
    (ρ : M.Env Γ) {x y : S} (h : x = y) (t : Tm sig Γ x) :
    (Tm.reind h t).eval M ρ = cast (congrArg M.carrier h) (t.eval M ρ) := by
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
      exact congrArg (cast (congrArg M.carrier o.2))
        (congrArg (M.interpOp o.val) (funext fun i => ih i))

/-- Evaluation commutes with a model morphism. Given two models `M₁ M₂` of the
same signature, a sort-indexed family `φ` sending `M₁`-values to `M₂`-values that
commutes with every operation's interpretation, and environments `ρ₁ ρ₂` matched
by `φ` (`φ (ρ₁ i) = ρ₂ i`), the value of any term under `M₁, ρ₁` maps by `φ` to
its value under `M₂, ρ₂`. Proved by induction on the term via `PolyFix.ind`; the
variable case transports `φ` across the fiber cast, the operation case rewrites by
the commutation hypothesis and the recursive child equalities. The soundness
route (1)⟹(4) instantiates it with an interpreting `φ` to reduce the applicative
translation of a definition body to its standard-model value (Leivant III §4.1).
Novel packaging. -/
theorem Tm.eval_model_morphism {sig : SortedSig S} {Γ : Ctx S}
    (M₁ M₂ : SortedModel sig) (φ : ∀ {σ : S}, M₁.carrier σ → M₂.carrier σ)
    (hop : ∀ (o : sig.Op)
        (args : ∀ i : Fin (sig.arity o).length, M₁.carrier ((sig.arity o).get i)),
      φ (M₁.interpOp o args) = M₂.interpOp o (fun i => φ (args i)))
    (ρ₁ : M₁.Env Γ) (ρ₂ : M₂.Env Γ) (hρ : ∀ i : Fin Γ.length, φ (ρ₁ i) = ρ₂ i)
    {s : S} (t : Tm sig Γ s) :
    φ (t.eval M₁ ρ₁) = t.eval M₂ ρ₂ := by
  have φcast : ∀ {x y : S} (h : x = y) (v : M₁.carrier x),
      φ (cast (congrArg M₁.carrier h) v) = cast (congrArg M₂.carrier h) (φ v) := by
    intro x y h v
    subst h
    rfl
  induction t using PolyFix.ind with
  | step i children ih =>
    cases i with
    | inl a => exact (φcast a.2 _).trans (congrArg (cast (congrArg M₂.carrier a.2)) (hρ a.1))
    | inr o =>
      refine (φcast o.2 _).trans (congrArg (cast (congrArg M₂.carrier o.2)) ?_)
      exact (hop o.val _).trans (congrArg (M₂.interpOp o.val) (funext ih))

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
