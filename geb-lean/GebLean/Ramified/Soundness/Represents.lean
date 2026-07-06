import GebLean.Ramified.Soundness.BarRep

/-!
# The representation relation

The logical relation `Represents` tying a closed source term of the
object-sorted applicative calculus `RλMR_o^ω` (`GebLean/Ramified/Soundness/
Applicative.lean`) to a closed term of the simply-typed calculus `1λ(A)`
(`GebLean/Ramified/Soundness/OneLambda.lean`) that computes its value, following
Leivant III section 4.2 (p. 223). Defined by structural recursion on the r-type
`τ` (via `PolyFix.ind`, decision 8): at the object sorts `o` and `Ω τ'` a closed
term `Fhat` represents `F` when `Fhat` reduces to the Berarducci-Böhm value term of
`F`'s denotation, and at an arrow `σ → τ'` representation is the logical-relation
implication carrying represented arguments to represented applications.

## Main definitions

* `sourceApp` — closed-term application of the object-sorted applicative
  calculus, the empty-context specialization of `Ramified.app'`.
* `Represents` — the representation relation of Leivant III section 4.2.
* `RepresentsEnv` — two closing environments related pointwise through
  `Represents`, the hypothesis of Lemma 10.
* `LamFree` — the variable-application (λ-free, recur-free, constant-free)
  fragment over which Lemma 10 quantifies.

## Main statements

* `lemma8` — target-reduction closure of `Represents` (Leivant III section 4.2,
  Lemma 8): a `1λ(A)` reduction may be prepended to a representative.
* `lemma9_o`, `lemma9_omega` — self-representation of a closed source term at
  the object sorts (Leivant III section 4.2, Lemma 9, weakened): a closed term
  is represented by the canonical bar-term of its own denotation.
* `lemma10` — the fundamental lemma of `Represents` restricted to the λ-free
  terms (Leivant III section 4.2, Lemma 10): substituting represented terms for
  the free variables of a λ-free term yields a represented substitution into its
  bar image.
* `sub_app'`, `OneLambda.sub_app'`, `barTm_app'`, `barTm_var`, `barTm_op`,
  `represents_arrow` — the substitution/bar-map distribution and relation-
  unfolding facts the Lemma 10 induction consumes; `sub_underBinder_nil` and
  `weakAppend_nil` are the empty-binder coherence they rest on. `barTm_op` is
  the general operation-node reduction of the term bar-map (`barTm_var` and
  `barTm_app'` are its leaf and application instances).
* `recurBridge` — the source-side recurrence semantics of Proposition 11's
  recurrence case (Leivant III section 4.2–4.3): the denotation of a saturated
  recurrence combinator applied to an argument is the free-algebra recurrence of
  the argument's denotation.
* `represents_app` — the application case of Proposition 11's fundamental
  induction (Leivant III section 4.2–4.3), standalone: representation of a
  substituted function and argument yields representation of the substituted
  application.
* `barRecur_appSpine_reduces` — the recurrence bar-map saturated with represented
  step terms reduces to its instantiated inner body, the recurrence-combinator
  counterpart of `OneLambda.bbRep_appSpine_reduces`.

## Implementation notes

`Represents` is a decision-2 denotational reformulation of Leivant III section
4.2's operational `Represents`: the object and `Ω` clauses anchor the source
value denotationally through `appEval` rather than by measuring a source-side
reduction, since the source side is never measured downstream and `appEval` is
total and ties to `RIdent.interp` via `prop7Translate_interp`. This is novel
packaging (an approved internal-lemma deviation), not a verbatim transcription.

The relation is `Prop`-valued, so decision 8's requirement that recursive data be
a `PolyFix` W-type does not constrain it; the `PolyFix.ind` recursion carries a
dependent motive `fun {_} (t : RType) => Tm [] t → Tm [] (barTy t) → Prop`, and
the arrow clause recurses into both children through the eliminator's induction
hypothesis. The source-side application transports `F` across the node
reconstruction `arrow_node_eq`, since a term-valued position cannot avoid the
transport the way `RType.interp` (a `Type`-valued recursion) does. The
object-clause denotations `appEval F finZeroElim` supply the empty semantic
environment at the empty context through `finZeroElim`, the dependent empty
eliminator, rather than the non-dependent `Fin.elim0`, which does not match the
dependent environment Pi.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`, section 4.2 (p. 223): the
representation of a closed term of the ramified calculus by a closed term of the
simply-typed calculus `1λ(A)`.

## Tags

ramified recurrence, logical relation, representation, simply-typed lambda
calculus, Berarducci-Böhm representation, reduction
-/

namespace GebLean.Ramified

open GebLean.Binding

/-- Closed-term application of the object-sorted applicative calculus
`RλMR_o^ω(natAlgSig)`: the empty-context specialization of `Ramified.app'`,
applying a closed function term `F : arrow σ τ'` to a closed argument term
`G : σ` to yield a closed term of sort `τ'`. Named so that the representation
relation and its downstream consumers reference the closed-term application by a
stable name. -/
def sourceApp {σ τ' : RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) [] (RType.arrow σ τ'))
    (G : Binding.Tm (rlmrOSig natAlgSig) [] σ) :
    Binding.Tm (rlmrOSig natAlgSig) [] τ' :=
  app' F G

/-- The representation relation of the bar-translation (Leivant III section 4.2,
p. 223), a decision-2 denotational reformulation: a closed source term `F` of the
object-sorted applicative calculus at r-type `τ` is represented by a closed term
`Fhat` of the simply-typed calculus `1λ(A)` at the barred type `barTy τ` when

* at the base sort `o`, `Fhat` reduces (`OneLambdaStep`, reflexive-transitively) to
  the concrete `o`-term `conc` of `F`'s denotation `appEval F finZeroElim`;
* at an object sort `Ω τ'`, `Fhat` reduces to the Berarducci-Böhm representation
  `bbRep` of `F`'s denotation at the barred sort `barTy τ'`;
* at an arrow `σ → τ'`, `Fhat` represents `F` exactly when it carries every
  represented argument to a represented application — the logical-relation
  clause, recursing into both arrow children.

Realized by the dependent eliminator `PolyFix.ind` (decision 8) with the motive
`fun {_} (t : RType) => Tm [] t → Tm [] (barTy t) → Prop`. The denotational
anchoring of the object clauses is novel packaging; see the module docstring. -/
def Represents (τ : RType) (F : Binding.Tm (rlmrOSig natAlgSig) [] τ)
    (Fhat : Binding.Tm (oneLambdaSig natAlgSig) [] (barTy τ)) : Prop :=
  PolyFix.ind (P := rTypeSig.polyEndo)
    (motive := fun {_} (t : RType) =>
      Binding.Tm (rlmrOSig natAlgSig) [] t →
        Binding.Tm (oneLambdaSig natAlgSig) [] (barTy t) → Prop)
    (fun {x} i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ =>
        fun F Fhat => Relation.ReflTransGen OneLambdaStep Fhat (conc (appEval F finZeroElim))
      | RTypeShape.arrow, childx, ih =>
        fun F Fhat =>
          ∀ (G : Binding.Tm (rlmrOSig natAlgSig) []
                (childx (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow))))
            (Ghat : Binding.Tm (oneLambdaSig natAlgSig) []
                (barTy (childx (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow))))),
            ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)) G Ghat →
              ih (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow))
                (sourceApp (arrow_node_eq x childx ▸ F) G) (OneLambda.app' Fhat Ghat)
      | RTypeShape.omega, childx, _ =>
        fun F Fhat =>
          Relation.ReflTransGen OneLambdaStep Fhat
            (bbRep (appEval F finZeroElim)
              (barTy (childx (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.omega)))))) τ F Fhat

/-- Target-reduction closure of `Represents` (Leivant III section 4.2, Lemma 8),
a decision-2 denotational reformulation: a `1λ(A)` reduction may be prepended to a
representative. If `Fhat` represents `F` at r-type `τ` and `Fhat'` reduces to
`Fhat` (`OneLambdaStep`, reflexive-transitively), then `Fhat'` also represents `F`.

Because the source side is read only through `appEval` (decision 2), no source
metatheory is required: at the object sorts `o` and `Ω τ'` closure is target
transitivity of the reduction to the anchoring value, and at an arrow the reduction
is carried under the application spine by `OneLambda.reduces_app'_left` before the
recursion. Proved by the dependent eliminator `PolyFix.ind` (decision 8) on `τ`
with a motive quantifying over the terms, the representation, and the reduction. -/
theorem lemma8 {τ : RType} {F : Binding.Tm (rlmrOSig natAlgSig) [] τ}
    {Fhat' Fhat : Binding.Tm (oneLambdaSig natAlgSig) [] (barTy τ)}
    (h : Represents τ F Fhat)
    (hred : Relation.ReflTransGen OneLambdaStep Fhat' Fhat) :
    Represents τ F Fhat' :=
  PolyFix.ind (P := rTypeSig.polyEndo)
    (motive := fun {_} (t : RType) =>
      ∀ (F : Binding.Tm (rlmrOSig natAlgSig) [] t)
        (Fhat' Fhat : Binding.Tm (oneLambdaSig natAlgSig) [] (barTy t)),
        Represents t F Fhat →
          Relation.ReflTransGen OneLambdaStep Fhat' Fhat → Represents t F Fhat')
    (fun {x} i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ => fun _ _ _ h hred => hred.trans h
      | RTypeShape.arrow, childx, ih =>
        fun F Fhat' Fhat h hred G Ghat hGG =>
          have hApp : Represents (childx (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)))
              (sourceApp (arrow_node_eq x childx ▸ F) G) (OneLambda.app' Fhat Ghat) :=
            h G Ghat hGG
          ih (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)) _
            (OneLambda.app' Fhat' Ghat) (OneLambda.app' Fhat Ghat) hApp
            (OneLambda.reduces_app'_left Ghat hred)
      | RTypeShape.omega, _, _ => fun _ _ _ h hred => hred.trans h) τ F Fhat' Fhat h hred

/-- Self-representation at the base object sort `o` (Leivant III section 4.2,
Lemma 9, weakened): a closed source term `F : o` is represented by the concrete
`o`-term of its own denotation, `conc (appEval F finZeroElim)`. Leivant's Lemma
9 additionally asserts that this representative is the *unique* normal `1λ(A)`
term representing `F`; under decision 2's denotational reformulation that
uniqueness content is dropped as unneeded (`Prop11` case 7 reads `F̂`'s normal
form from the `Represents` hypothesis directly, not from this lemma). What
remains is existence, and at `o` the object clause of `Represents` *is* the
statement that its target reduces to this term, so the anchor represents
itself reflexively. -/
theorem lemma9_o (F : Binding.Tm (rlmrOSig natAlgSig) [] RType.o) :
    Represents RType.o F (conc (appEval F finZeroElim)) :=
  Relation.ReflTransGen.refl

/-- Self-representation at an object sort `Ω τ'` (Leivant III section 4.2,
Lemma 9, weakened): a closed source term `F : Ω τ'` is represented by the
Berarducci-Böhm representation of its own denotation, `bbRep (appEval F
finZeroElim) (barTy τ')`. See `lemma9_o` for the dropped uniqueness content. -/
theorem lemma9_omega (τ' : RType) (F : Binding.Tm (rlmrOSig natAlgSig) [] (RType.omega τ')) :
    Represents (RType.omega τ') F (bbRep (appEval F finZeroElim) (barTy τ')) :=
  Relation.ReflTransGen.refl

/-- The arrow clause of `Represents` unfolds to the logical-relation quantifier
(Leivant III section 4.2): at `σ → τ'`, `F` is represented by `Fhat` exactly
when every represented argument is carried to a represented application. The
`PolyFix.ind` β-reduction of the `arrow` case at a concrete arrow node. -/
theorem represents_arrow {σ τ' : RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) [] (RType.arrow σ τ'))
    (Fhat : Binding.Tm (oneLambdaSig natAlgSig) [] (barTy (RType.arrow σ τ'))) :
    Represents (RType.arrow σ τ') F Fhat ↔
      ∀ (G : Binding.Tm (rlmrOSig natAlgSig) [] σ)
        (Ghat : Binding.Tm (oneLambdaSig natAlgSig) [] (barTy σ)),
        Represents σ G Ghat →
          Represents τ' (sourceApp F G) (OneLambda.app' Fhat Ghat) :=
  Iff.rfl

/-- The term bar-map at a variable leaf is the barred variable (Leivant III
section 4.2): `barTm (var x) = var (barVar x)`. The `PolyFix.ind` β-reduction of
the leaf case, following `appEval_var`. -/
theorem barTm_var {Γ : Binding.Ctx RType} {s : RType} (x : Binding.Var Γ s) :
    barTm (Binding.Tm.var x) = Binding.Tm.var (barVar x) := by
  obtain ⟨i, hi⟩ := x
  subst hi
  rfl

/-- The term bar-map commutes with a source-context transport: for `h : Γ = Γ'`,
`barTm (h ▸ t) = (congrArg (·.map barTy) h) ▸ barTm t`. Proved by `subst`.
Internal packaging for `barTm_app'`. -/
theorem barTm_congr_ctx {Γ Γ' : Binding.Ctx RType} {s : RType} (h : Γ = Γ')
    (t : Binding.Tm (rlmrOSig natAlgSig) Γ s) :
    barTm (h ▸ t) = (congrArg (List.map barTy) h) ▸ barTm t := by
  subst h; rfl

/-- The append-nil transport cancellation of the term bar-map: transporting the
bar image of an append-nil-transported term back cancels, `(congrArg (·.map
barTy) e) ▸ barTm (e.symm ▸ g) = barTm g`. Proved by `subst`. The per-argument
step of `barTm_app'`. -/
theorem barTm_transport_cancel {G Γ : Binding.Ctx RType} {s : RType} (e : G = Γ)
    (g : Binding.Tm (rlmrOSig natAlgSig) Γ s) :
    (congrArg (List.map barTy) e) ▸ barTm (e.symm ▸ g) = barTm g := by
  subst e; rfl

/-- The term bar-map at an application node is the `1λ(A)` application of the bar
images (Leivant III section 4.2): `barTm (app' f x) = OneLambda.app' (barTm f)
(barTm x)`. The `barTmOp` app-branch dispatch, with the barred child contexts
reconciled to `Γ.map barTy` through the append-nil transport cancellation
`barTm_transport_cancel`. -/
theorem barTm_app' {Γ : Binding.Ctx RType} {σ' τ' : RType}
    (f : Binding.Tm (rlmrOSig natAlgSig) Γ (RType.arrow σ' τ'))
    (x : Binding.Tm (rlmrOSig natAlgSig) Γ σ') :
    barTm (app' f x) = OneLambda.app' (barTm f) (barTm x) := by
  exact congrArg₂ OneLambda.app'
    (barTm_transport_cancel (List.append_nil Γ) f)
    (barTm_transport_cancel (List.append_nil Γ) x)

/-- Transport of the source context of a traversal along a context equality:
transport the term into the equal source and pre-compose the environment.
Proved by `subst`. Internal packaging for `sub_underBinder_nil`. -/
theorem traverse_congr_dom {S : Binding.BinderSig RType}
    {V : Binding.Ctx RType → RType → Type} (K : Binding.Kit S V)
    {Γ Γ' Δ : Binding.Ctx RType} {s : RType} (h : Γ = Γ') (ρ : Binding.Env V Γ' Δ)
    (t : Binding.Tm S Γ s) :
    Binding.traverse K ρ (h ▸ t) = Binding.traverse K (fun b x => ρ b (h ▸ x)) t := by
  subst h; rfl

/-- Transport of the target context of a traversal along a context equality:
transport each environment value and pull the transport out of the traversal.
Proved by `subst`. Internal packaging for `sub_underBinder_nil`. -/
theorem traverse_congr_cod {S : Binding.BinderSig RType}
    {V : Binding.Ctx RType → RType → Type} (K : Binding.Kit S V)
    {Γ Δ Δ' : Binding.Ctx RType} {s : RType} (h : Δ = Δ') (ρ : Binding.Env V Γ Δ)
    (t : Binding.Tm S Γ s) :
    Binding.traverse K (fun b x => h ▸ ρ b x) t = h ▸ Binding.traverse K ρ t := by
  subst h; rfl

/-- Renaming along a codomain-transported thinning pulls the transport out: for
`h : Δ = Δ'`, `ren (h ▸ ρ) t = h ▸ ren ρ t`. Proved by `subst`. Internal
packaging for the empty-binder coherence `sub_underBinder_nil`. -/
theorem ren_transport_cod {S : Binding.BinderSig RType} {Γ Δ Δ' : Binding.Ctx RType}
    {s : RType} (h : Δ = Δ') (ρ : Binding.Thinning Γ Δ) (t : Binding.Tm S Γ s) :
    Binding.ren (h ▸ ρ) t = h ▸ Binding.ren ρ t := by
  subst h; rfl

/-- Applying a codomain-transported thinning to a variable pulls the transport
out: for `h : Δ = Δ'`, `(h ▸ ρ).app x = h ▸ ρ.app x`. Proved by `subst`.
Internal packaging for `weakAppend_app_nil`. -/
theorem thinning_app_transport_cod {Γ Δ Δ' : Binding.Ctx RType} {s : RType}
    (h : Δ = Δ') (ρ : Binding.Thinning Γ Δ) (x : Binding.Var Γ s) :
    (h ▸ ρ).app x = h ▸ ρ.app x := by
  subst h; rfl

/-- Prepending a bound sort commutes with a codomain transport of a thinning:
`keep a (h ▸ ρ) = (congrArg (a :: ·) h) ▸ keep a ρ`. Proved by `subst`. The cons
step of `weakAppend_nil`. -/
theorem keep_transport_cod {Γ Δ Δ' : Binding.Ctx RType} (a : RType) (h : Δ = Δ')
    (ρ : Binding.Thinning Γ Δ) :
    Binding.Thinning.keep a (h ▸ ρ)
      = (congrArg (a :: ·) h) ▸ Binding.Thinning.keep a ρ := by
  subst h; rfl

/-- The suffix-embedding thinning at the empty suffix is the append-nil
transport of the identity thinning: `weakAppend (Ξ := []) = (append_nil).symm ▸
id`. Recursion on `Γ`, the `keep`-transport commutation of the cons step
(`keep_transport_cod`) closed by kernel proof-irrelevance of the context
equalities. The Thinning-level source of the empty-binder coherence. -/
theorem weakAppend_nil : {Γ : Binding.Ctx RType} →
    (Binding.Thinning.weakAppend (Γ := Γ) (Ξ := []) : Binding.Thinning Γ (Γ ++ []))
      = (List.append_nil Γ).symm ▸ (Binding.Thinning.id : Binding.Thinning Γ Γ)
  | [] => rfl
  | a :: Γ' => by
      rw [Binding.Thinning.weakAppend, weakAppend_nil (Γ := Γ')]
      exact keep_transport_cod a (List.append_nil Γ').symm Binding.Thinning.id

/-- Renaming along the empty-suffix embedding is the append-nil transport:
`ren (weakAppend (Ξ := [])) t = (append_nil).symm ▸ t`. From `weakAppend_nil`,
`ren_transport_cod`, and `ren_id`. -/
theorem ren_weakAppend_nil {S : Binding.BinderSig RType} {Γ : Binding.Ctx RType}
    {s : RType} (t : Binding.Tm S Γ s) :
    Binding.ren (Binding.Thinning.weakAppend (Ξ := [])) t = (List.append_nil Γ).symm ▸ t := by
  rw [weakAppend_nil, ren_transport_cod, Binding.ren_id]

/-- Applying the empty-suffix embedding to a variable is the append-nil
transport: `weakAppend.app (Ξ := []) x = (append_nil).symm ▸ x`. From
`weakAppend_nil`, `thinning_app_transport_cod`, and `Thinning.app_id`. -/
theorem weakAppend_app_nil {Γ : Binding.Ctx RType} {s : RType} (x : Binding.Var Γ s) :
    (Binding.Thinning.weakAppend (Ξ := [])).app x = (List.append_nil Γ).symm ▸ x := by
  rw [weakAppend_nil, thinning_app_transport_cod, Binding.Thinning.app_id]

/-- The empty-binder coherence of `sub` (the fundamental substitution fact
underlying `sub_app'`): substituting under an empty binder, along the append-nil
context transport, is substitution along the original environment, again up to
the append-nil transport. Reduces, through `traverse_congr_dom`/`_cod`, to the
per-variable computation of `Env.underBinder` at the empty suffix
(`Var.appendCases_weakAppend`), whose weakening is the append-nil transport
(`ren_weakAppend_nil`) on the argument recovered by `weakAppend_app_nil`. -/
theorem sub_underBinder_nil {S : Binding.BinderSig RType} {Γ Δ : Binding.Ctx RType}
    {s : RType} (ρ : Binding.Env (Binding.Tm S) Γ Δ) (t : Binding.Tm S Γ s) :
    Binding.traverse (Binding.subKit S)
        (Binding.Env.underBinder (Binding.subKit S) (Ξ := []) ρ) ((List.append_nil Γ).symm ▸ t)
      = (List.append_nil Δ).symm ▸ Binding.traverse (Binding.subKit S) ρ t := by
  have henv :
      (fun (b : RType) (x : Binding.Var Γ b) =>
          Binding.Env.underBinder (Binding.subKit S) (Ξ := []) ρ b ((List.append_nil Γ).symm ▸ x))
        = (fun (b : RType) (x : Binding.Var Γ b) => (List.append_nil Δ).symm ▸ ρ b x) := by
    funext b x
    rw [← weakAppend_app_nil]
    simp only [Binding.Env.underBinder, Binding.subKit]
    rw [Binding.Var.appendCases_weakAppend]
    exact ren_weakAppend_nil (ρ b x)
  calc Binding.traverse (Binding.subKit S)
          (Binding.Env.underBinder (Binding.subKit S) (Ξ := []) ρ) ((List.append_nil Γ).symm ▸ t)
      = Binding.traverse (Binding.subKit S)
          (fun b x => Binding.Env.underBinder (Binding.subKit S) (Ξ := []) ρ b
            ((List.append_nil Γ).symm ▸ x)) t :=
        traverse_congr_dom (Binding.subKit S) (List.append_nil Γ).symm _ t
    _ = Binding.traverse (Binding.subKit S)
          (fun b x => (List.append_nil Δ).symm ▸ ρ b x) t := by rw [henv]
    _ = (List.append_nil Δ).symm ▸ Binding.traverse (Binding.subKit S) ρ t :=
        traverse_congr_cod (Binding.subKit S) (List.append_nil Δ).symm ρ t

/-- Substitution distributes over the application node of the applicative
calculus `RλMR_o^ω`: `sub ρ (app' f x) = app' (sub ρ f) (sub ρ x)`. The two
`app'`-argument slots carry the empty binder, so their `sub` is the empty-binder
coherence `sub_underBinder_nil`; the outer reassembly is definitional
(`traverse_op`). -/
theorem sub_app' {Γ Δ : Binding.Ctx RType} {σ' τ' : RType}
    (ρ : Binding.Env (Binding.Tm (rlmrOSig natAlgSig)) Γ Δ)
    (f : Binding.Tm (rlmrOSig natAlgSig) Γ (RType.arrow σ' τ'))
    (x : Binding.Tm (rlmrOSig natAlgSig) Γ σ') :
    Binding.sub ρ (app' f x) = app' (Binding.sub ρ f) (Binding.sub ρ x) := by
  refine Eq.trans (b := Binding.Tm.op (S := rlmrOSig natAlgSig) (RlmrOOp.app σ' τ')
      (fun j => Binding.traverse (Binding.subKit (rlmrOSig natAlgSig))
        (Binding.Env.underBinder (Binding.subKit (rlmrOSig natAlgSig)) ρ)
        (Fin.cases ((List.append_nil Γ).symm ▸ f)
          (fun k => Fin.cases ((List.append_nil Γ).symm ▸ x) (fun l => l.elim0) k) j)))
    rfl ?_
  refine Eq.trans ?_ (rfl : Binding.Tm.op (S := rlmrOSig natAlgSig) (RlmrOOp.app σ' τ')
      (fun j => Fin.cases ((List.append_nil Δ).symm ▸ Binding.sub ρ f)
        (fun k => Fin.cases ((List.append_nil Δ).symm ▸ Binding.sub ρ x)
          (fun l => l.elim0) k) j)
    = app' (Binding.sub ρ f) (Binding.sub ρ x))
  refine congrArg (Binding.Tm.op (S := rlmrOSig natAlgSig) (RlmrOOp.app σ' τ')) ?_
  funext j
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => l.elim0) k) j
  · exact sub_underBinder_nil ρ f
  · exact sub_underBinder_nil ρ x

/-- Substitution distributes over the application node of the simply-typed
calculus `1λ(A)`: `sub ρ (OneLambda.app' f x) = OneLambda.app' (sub ρ f)
(sub ρ x)`. The `oneLambdaSig` counterpart of `sub_app'`, with the same
empty-binder coherence argument. -/
theorem OneLambda.sub_app' {Γ Δ : Binding.Ctx RType} {σ' τ' : RType}
    (ρ : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) Γ Δ)
    (f : Binding.Tm (oneLambdaSig natAlgSig) Γ (RType.arrow σ' τ'))
    (x : Binding.Tm (oneLambdaSig natAlgSig) Γ σ') :
    Binding.sub ρ (OneLambda.app' f x)
      = OneLambda.app' (Binding.sub ρ f) (Binding.sub ρ x) := by
  refine Eq.trans (b := Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.app σ' τ')
      (fun j => Binding.traverse (Binding.subKit (oneLambdaSig natAlgSig))
        (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig)) ρ)
        (Fin.cases ((List.append_nil Γ).symm ▸ f)
          (fun k => Fin.cases ((List.append_nil Γ).symm ▸ x) (fun l => l.elim0) k) j)))
    rfl ?_
  refine Eq.trans ?_ (rfl : Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.app σ' τ')
      (fun j => Fin.cases ((List.append_nil Δ).symm ▸ Binding.sub ρ f)
        (fun k => Fin.cases ((List.append_nil Δ).symm ▸ Binding.sub ρ x)
          (fun l => l.elim0) k) j)
    = OneLambda.app' (Binding.sub ρ f) (Binding.sub ρ x))
  refine congrArg (Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.app σ' τ')) ?_
  funext j
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => l.elim0) k) j
  · exact sub_underBinder_nil ρ f
  · exact sub_underBinder_nil ρ x

/-- Substitution distributes over the abstraction node of the simply-typed
calculus `1λ(A)`: `sub ρ (OneLambda.lam' b) = OneLambda.lam' (sub (underBinder ρ)
b)`, pushing the substitution under the bound variable of sort `σ'` by weakening
the environment with `Env.underBinder`. The `oneLambdaSig` abstraction
counterpart of `OneLambda.sub_app'`; the sole subterm slot carries the binder
`[σ']`, so no append-nil transport intervenes and the bound branch is
definitional. -/
theorem OneLambda.sub_lam' {Γ Δ : Binding.Ctx RType} {σ' τ' : RType}
    (ρ : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) Γ Δ)
    (b : Binding.Tm (oneLambdaSig natAlgSig) (Γ ++ [σ']) τ') :
    Binding.sub ρ (OneLambda.lam' b)
      = OneLambda.lam' (Binding.sub
          (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig)) ρ) b) := by
  refine Eq.trans (b := Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.lam σ' τ')
      (fun j => Binding.traverse (Binding.subKit (oneLambdaSig natAlgSig))
        (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig)) ρ)
        (Fin.cases b (fun k => k.elim0) j)))
    rfl ?_
  refine Eq.trans ?_ (rfl : Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.lam σ' τ')
      (fun j => Fin.cases (Binding.sub
          (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig)) ρ) b)
        (fun k => k.elim0) j)
    = OneLambda.lam' (Binding.sub
        (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig)) ρ) b))
  refine congrArg (Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.lam σ' τ')) ?_
  funext j
  refine Fin.cases ?_ (fun k => k.elim0) j
  rfl

/-- A context-`cast` of a term equals the corresponding `Eq.rec` transport
`h ▸ t`: both realize the same context equality. Proved by `subst`. Bridges
`OneLambda.lamSpine`'s `cast` presentation to the `▸` presentation of
`traverse_congr_dom`/`traverse_congr_cod`. -/
theorem tm_cast_eq_eqRec {S : Binding.BinderSig RType} {Γ Γ' : Binding.Ctx RType}
    {s : RType} (h : Γ = Γ') (t : Binding.Tm S Γ s) :
    cast (congrArg (fun c => Binding.Tm S c s) h) t = h ▸ t := by
  cases h; rfl

/-- A context transport followed by its inverse cancels. Proved by `subst`. -/
theorem eqRec_symm_eqRec {motive : Binding.Ctx RType → Type} {a b : Binding.Ctx RType}
    (h : a = b) (x : motive a) : (h.symm ▸ (h ▸ x : motive b) : motive a) = x := by
  cases h; rfl

/-- An inverse context transport followed by the transport cancels. Proved by
`subst`. -/
theorem eqRec_eqRec_symm {motive : Binding.Ctx RType → Type} {a b : Binding.Ctx RType}
    (h : a = b) (y : motive b) : (h ▸ (h.symm ▸ y : motive a) : motive b) = y := by
  cases h; rfl

/-- Substitution commutes with the iterated abstraction `OneLambda.lamSpine`:
`sub ρ (lamSpine Δ body) = lamSpine Δ (sub (underBinder (Ξ := Δ) ρ) body)`,
pushing the substitution under all of the abstracted binders `Δ` at once by
weakening the environment with `Env.underBinder` at the combined binder context.
The spine dual of `OneLambda.sub_lam'`. Proved by recursion on `Δ`: the base
case is the empty-binder coherence `sub_underBinder_nil`, and the cons case peels
one binder via `OneLambda.sub_lam'`, applies the recursion, and reconciles the
two nested `Env.underBinder` weakenings with the single combined one through the
append-associativity keystone `Binding.underBinder_append`. -/
theorem OneLambda.sub_lamSpine :
    {Γ Γ' : Binding.Ctx RType} → (Δ : List RType) → {τ : RType} →
    (ρ : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) Γ Γ') →
    (body : Binding.Tm (oneLambdaSig natAlgSig) (Γ ++ Δ) τ) →
    Binding.sub ρ (OneLambda.lamSpine Δ body)
      = OneLambda.lamSpine Δ (Binding.sub
          (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig)) (Ξ := Δ) ρ) body)
  | Γ, Γ', [], τ, ρ, body => by
      unfold Binding.sub
      change Binding.traverse (Binding.subKit (oneLambdaSig natAlgSig)) ρ
          (cast (congrArg (fun c => Binding.Tm (oneLambdaSig natAlgSig) c τ)
            (List.append_nil Γ)) body)
        = cast (congrArg (fun c => Binding.Tm (oneLambdaSig natAlgSig) c τ) (List.append_nil Γ'))
            (Binding.traverse (Binding.subKit (oneLambdaSig natAlgSig))
              (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig)) (Ξ := []) ρ) body)
      rw [tm_cast_eq_eqRec (List.append_nil Γ) body,
        tm_cast_eq_eqRec (List.append_nil Γ')
          (Binding.traverse (Binding.subKit (oneLambdaSig natAlgSig))
            (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig)) (Ξ := []) ρ) body)]
      have key := sub_underBinder_nil ρ ((List.append_nil Γ) ▸ body)
      rw [eqRec_symm_eqRec (motive := fun c => Binding.Tm (oneLambdaSig natAlgSig) c τ)
        (List.append_nil Γ) body] at key
      rw [key, eqRec_eqRec_symm (motive := fun c => Binding.Tm (oneLambdaSig natAlgSig) c τ)]
  | Γ, Γ', σ :: Δ', τ, ρ, body => by
      rw [OneLambda.lamSpine]
      refine (OneLambda.sub_lam' ρ _).trans ?_
      refine (congrArg OneLambda.lam' (OneLambda.sub_lamSpine Δ' _ _)).trans ?_
      conv_rhs => rw [OneLambda.lamSpine]
      refine congrArg OneLambda.lam' ?_
      refine congrArg (OneLambda.lamSpine Δ') ?_
      unfold Binding.sub
      rw [tm_cast_eq_eqRec (List.append_assoc Γ [σ] Δ').symm body]
      refine (traverse_congr_dom (Binding.subKit (oneLambdaSig natAlgSig))
        (List.append_assoc Γ [σ] Δ').symm
        (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig))
          (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig)) ρ)) body).trans ?_
      have henv :
          (fun (b : RType) (x : Binding.Var (Γ ++ σ :: Δ') b) =>
              Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig))
                (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig)) ρ) b
                ((List.append_assoc Γ [σ] Δ').symm ▸ x))
            = (fun (b : RType) (x : Binding.Var (Γ ++ σ :: Δ') b) =>
                (List.append_assoc Γ' [σ] Δ').symm ▸
                  Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig))
                    (Ξ := σ :: Δ') ρ b x) := by
        funext b x
        exact Binding.underBinder_append (Ξ₁ := [σ]) (Ξ₂ := Δ') ρ b x
      refine (congrArg (fun e =>
        Binding.traverse (Binding.subKit (oneLambdaSig natAlgSig)) e body) henv).trans ?_
      rw [tm_cast_eq_eqRec (List.append_assoc Γ' [σ] Δ').symm]
      exact traverse_congr_cod (Binding.subKit (oneLambdaSig natAlgSig))
        (List.append_assoc Γ' [σ] Δ').symm
        (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig)) (Ξ := σ :: Δ') ρ) body

/-- Instantiating the empty append-at-end suffix is the append-nil context
transport: `instantiate m body = (append_nil Γ) ▸ body` for any (vacuous)
meta-map `m` on `[]`. The empty-suffix base of the generic λ-spine β-reduction.
Reduces, through `traverse_congr_dom`, to the pointwise fact that the extended
environment reads the append-nil transport of a variable as its identity image
(`extendEnv_weakAppend`, `weakAppend_app_nil`), closed by `sub_id`. -/
theorem instantiate_nil {S : Binding.BinderSig RType} {Γ : Binding.Ctx RType} {τ : RType}
    (m : ∀ t, Binding.Var ([] : Binding.Ctx RType) t → Binding.Tm S Γ t)
    (body : Binding.Tm S (Γ ++ []) τ) :
    Binding.instantiate m body = (List.append_nil Γ) ▸ body := by
  have h := traverse_congr_dom (Binding.subKit S) (List.append_nil Γ).symm
    (Binding.extendEnv Binding.idEnv m) ((List.append_nil Γ) ▸ body)
  rw [eqRec_symm_eqRec (motive := fun c => Binding.Tm S c τ)] at h
  have henv : (fun (b : RType) (x : Binding.Var Γ b) =>
      Binding.extendEnv Binding.idEnv m b ((List.append_nil Γ).symm ▸ x))
        = (Binding.idEnv : Binding.Env (Binding.Tm S) Γ Γ) := by
    funext b x
    rw [← weakAppend_app_nil]
    exact Binding.extendEnv_weakAppend Binding.idEnv m b x
  rw [Binding.instantiate]
  unfold Binding.sub
  rw [h, henv]
  exact traverse_idEnv _

/-- The generic λ-spine β-reduction of the simply-typed calculus `1λ(A)` (the
reduction dual of the denotational `appEval_lamSpine`, Leivant III section 4.1):
saturating the iterated abstraction `lamSpine Δ body` with an argument tuple
`args` along the application spine reduces (`OneLambdaStep`, reflexive-
transitively) to the simultaneous substitution `instantiate (metaTuple args) body`
of the arguments for the abstracted binders. Proved by recursion on `Δ`: the base
case is the empty-suffix instantiation `instantiate_nil`, and the cons case peels
one binder by β (`reduces_beta` under `reduces_appSpine`), pushes the resulting
single substitution through the residual `lamSpine` (`sub_lamSpine`), and
reconciles the peeled substitution with the tuple instantiation through the cons
recurrence `instantiate_metaTuple_cons`. -/
theorem OneLambda.reduces_betaSpine :
    {Γ : Binding.Ctx RType} → (Δ : List RType) → {τ : RType} →
    (body : Binding.Tm (oneLambdaSig natAlgSig) (Γ ++ Δ) τ) →
    (args : ∀ i : Fin Δ.length, Binding.Tm (oneLambdaSig natAlgSig) Γ (Δ.get i)) →
    Relation.ReflTransGen OneLambdaStep
      (OneLambda.appSpine Δ (OneLambda.lamSpine Δ body) args)
      (Binding.instantiate (Binding.metaTuple args) body)
  | Γ, [], τ, body, args => by
      rw [OneLambda.appSpine]
      change Relation.ReflTransGen OneLambdaStep
          (cast (congrArg (fun c => Binding.Tm (oneLambdaSig natAlgSig) c τ)
            (List.append_nil Γ)) body)
          (Binding.instantiate (Binding.metaTuple args) body)
      rw [tm_cast_eq_eqRec (List.append_nil Γ) body,
        instantiate_nil (Binding.metaTuple args) body]
  | Γ, σ :: Δ', τ, body, args => by
      have hlam : OneLambda.lamSpine (σ :: Δ') body
          = OneLambda.lam' (OneLambda.lamSpine Δ' ((List.append_assoc Γ [σ] Δ').symm ▸ body)) := by
        change OneLambda.lam' (OneLambda.lamSpine Δ'
            (cast (congrArg (fun c => Binding.Tm (oneLambdaSig natAlgSig) c τ)
              (List.append_assoc Γ [σ] Δ').symm) body))
          = OneLambda.lam' (OneLambda.lamSpine Δ' ((List.append_assoc Γ [σ] Δ').symm ▸ body))
        rw [tm_cast_eq_eqRec (List.append_assoc Γ [σ] Δ').symm body]
      rw [← Binding.instantiate_metaTuple_cons args body, OneLambda.appSpine, hlam]
      refine (OneLambda.reduces_appSpine Δ' _ _ (fun i => args i.succ)
        (OneLambda.reduces_beta _ (args ⟨0, Nat.succ_pos _⟩))).trans ?_
      have heq3 : Binding.instantiate₁ (args ⟨0, Nat.succ_pos _⟩)
          (OneLambda.lamSpine Δ' ((List.append_assoc Γ [σ] Δ').symm ▸ body))
          = OneLambda.lamSpine Δ' (Binding.sub
              (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig)) (Ξ := Δ')
                (Binding.extendEnv Binding.idEnv
                  (Binding.metaOne (a := σ) (args ⟨0, Nat.succ_pos _⟩))))
              ((List.append_assoc Γ [σ] Δ').symm ▸ body)) := by
        rw [Binding.instantiate₁, Binding.instantiate]
        exact OneLambda.sub_lamSpine Δ' (Binding.extendEnv Binding.idEnv
          (Binding.metaOne (a := σ) (args ⟨0, Nat.succ_pos _⟩))) _
      exact heq3 ▸ OneLambda.reduces_betaSpine Δ' _ (fun i => args i.succ)

/-- The Berarducci-Böhm representation `bbRep v σ` saturated with represented
step terms along its abstraction spine reduces to the instantiated fold body
(Leivant III section 4.2, Proposition 11's recurrence case): applying
`bbRep v σ` — the iterated abstraction of the `FreeAlg.recurse` fold of `v` over
the constructor-step types — to an argument tuple `Ghat` along the step-type
application spine reduces (`OneLambdaStep`, reflexive-transitively) to the fold
body with the step arguments simultaneously substituted for the abstracted
constructor variables (`instantiate (metaTuple Ghat)`). The direct instance of
the generic λ-spine β-reduction `reduces_betaSpine` at `bbRep`'s single
abstraction spine; the resulting substituted `ctorVar`-headed spine is the
variable-application template `lemma10` consumes. -/
theorem OneLambda.bbRep_appSpine_reduces (v : FreeAlg natAlgSig) (σ : RType)
    (Ghat : ∀ i : Fin (stepTypes natAlgSig σ σ).length,
      Binding.Tm (oneLambdaSig natAlgSig) [] ((stepTypes natAlgSig σ σ).get i)) :
    Relation.ReflTransGen OneLambdaStep
      (OneLambda.appSpine (stepTypes natAlgSig σ σ) (bbRep v σ) Ghat)
      (Binding.instantiate (Binding.metaTuple Ghat)
        (FreeAlg.recurse (A := natAlgSig) (P := Unit)
          (C := Binding.Tm (oneLambdaSig natAlgSig) (stepTypes natAlgSig σ σ) σ)
          (fun b _ _sub rec =>
            OneLambda.replicateSpine (natAlgSig.ar b) σ
              (Binding.Tm.var (ctorVar b)) rec) () v)) := by
  rw [bbRep]
  exact OneLambda.reduces_betaSpine (stepTypes natAlgSig σ σ) _ Ghat

/-- Two closing environments related pointwise through the representation
relation (Leivant III section 4.2, the hypothesis of Lemma 10): a source-side
environment `Eσ` substituting a closed source term for every variable of `Γ`,
and a target-side environment `Eσhat` substituting a closed `1λ(A)` term for
every barred variable of `Γ.map barTy`, such that at each variable the
substituted terms are `Represents`-related. The logical-relation environment
condition that `lemma10` carries through a substitution. -/
def RepresentsEnv {Γ : Binding.Ctx RType}
    (Eσ : Binding.Env (Binding.Tm (rlmrOSig natAlgSig)) Γ [])
    (Eσhat : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) (Γ.map barTy) []) : Prop :=
  ∀ {s : RType} (x : Binding.Var Γ s),
    Represents s (Eσ s x) (Eσhat (barTy s) (barVar x))

/-- The variable-application fragment of the λ-free terms of the applicative
calculus `RλMR_o^ω` (Leivant III section 4.2, the terms Lemma 10 quantifies
over, as consumed by Proposition 11's recurrence case): a term built from
variables by application alone, with no λ-abstraction (`lam`), no recurrence
combinator (`recur`), and no object constant (`con`, `dstr`, `case`).

This is precisely the fragment Proposition 11's recurrence case substitutes
into. There, the Berarducci-Böhm representation `bbRep a τ̄` of a recurrence
argument's value, applied to represented step terms, reduces to the value's
constructor template `a{g⃗}` — an application spine over the bound constructor
variables, hence a variable-application term. Proposition 11's other cases
(`con^o`, `case`/`dstr`, `con^{Ωτ}`) discharge the object constants directly,
not through Lemma 10, and `recur`'s compatibility is the separate recurrence
bridge; so the object constants are absent from the terms Lemma 10 serves and
are excluded from this predicate. -/
inductive LamFree {Γ : Binding.Ctx RType} :
    {τ : RType} → Binding.Tm (rlmrOSig natAlgSig) Γ τ → Prop where
  /-- A variable is λ-free. -/
  | var {s : RType} (x : Binding.Var Γ s) : LamFree (Binding.Tm.var x)
  /-- An application of λ-free terms is λ-free. -/
  | app {σ τ : RType} {f : Binding.Tm (rlmrOSig natAlgSig) Γ (RType.arrow σ τ)}
      {x : Binding.Tm (rlmrOSig natAlgSig) Γ σ} (hf : LamFree f) (hx : LamFree x) :
      LamFree (app' f x)

/-- The fundamental lemma of the representation relation restricted to the
λ-free terms (Leivant III section 4.2, Lemma 10, a decision-2 denotational
reformulation): substituting represented closed terms for the free variables of
a λ-free term `E` produces, on the source side, a term represented by the
parallel target-side substitution into the bar image `barTm E`. Given closing
environments `Eσ` and `Eσhat` that are pointwise `Represents`-related
(`RepresentsEnv`), `sub Eσ E` is represented by `sub Eσhat (barTm E)`.

Proved by induction on the λ-free derivation. At a variable the two sides read
the related environments (`sub_var`, `barTm_var`), closed by the environment
hypothesis. At an application, substitution distributes over both application
nodes (`sub_app'`, `OneLambda.sub_app'`) and the bar-map sends the node to the
`1λ(A)` application (`barTm_app'`), so the arrow clause of `Represents`
(`represents_arrow`) applied to the two induction hypotheses closes the goal.

This is the fragment consumed by Proposition 11's recurrence case: the term `E`
ranges over the variable-application value templates of the Berarducci-Böhm
representation, whose object constants and recurrence combinator are handled
elsewhere (see `LamFree`). -/
theorem lemma10 {Γ : Binding.Ctx RType} {τ : RType}
    {E : Binding.Tm (rlmrOSig natAlgSig) Γ τ} (hE : LamFree E)
    (Eσ : Binding.Env (Binding.Tm (rlmrOSig natAlgSig)) Γ [])
    (Eσhat : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) (Γ.map barTy) [])
    (hEnv : RepresentsEnv Eσ Eσhat) :
    Represents τ (Binding.sub Eσ E) (Binding.sub Eσhat (barTm E)) := by
  induction hE with
  | var x =>
    rw [Binding.sub_var, barTm_var, Binding.sub_var]
    exact hEnv x
  | @app σ' τ' f x _hf _hx ihf ihx =>
    rw [sub_app', barTm_app']
    exact (OneLambda.sub_app' Eσhat (barTm f) (barTm x)) ▸
      (represents_arrow (Binding.sub Eσ f) (Binding.sub Eσhat (barTm f))).mp ihf
        (Binding.sub Eσ x) (Binding.sub Eσhat (barTm x)) ihx

/-- The recurrence bridge (Leivant III section 4.2–4.3, Proposition 11's
recurrence case, a decision-2 denotational reformulation): the denotation of the
saturated recurrence combinator `recCombinator Estep` applied to a recurrence
argument `A` is the free-algebra recurrence `FreeAlg.recurse` of the
`appEval`-denoted argument `appEval A ρ`, with the step functions read
positionally from the `appEval`-denoted step terms (`stepEnvOfFun Estep`). The
source-side semantics the recurrence case of Proposition 11 consumes: the
Berarducci-Böhm fold body `barRecur` reduces (target side) to `a g⃗`, whose
denotation this equates to the recursor. Composes the applicative-fragment
denotation `appEval_app'` with the saturated-recurrence denotation
`appEval_recCombinator`. -/
theorem recurBridge {Γ : Binding.Ctx RType} {τ : RType}
    (Estep : ∀ b : natAlgSig.B,
      Binding.Tm (rlmrOSig natAlgSig) Γ (RType.curried (List.replicate (natAlgSig.ar b) τ) τ))
    (A : Binding.Tm (rlmrOSig natAlgSig) Γ (RType.omega τ))
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    appEval (app' (recCombinator Estep) A) ρ
      = FreeAlg.recurse (A := natAlgSig) (P := Unit)
          (fun i _ _sub phi =>
            appChain natAlgSig (List.replicate (natAlgSig.ar i) τ) τ
              (stepAtLabel (fun idx => appEval (stepEnvOfFun Estep idx) ρ) i)
              (childEnv [] τ (natAlgSig.ar i) finZeroElim phi))
          () (appEval A ρ) := by
  rw [appEval_app', appEval_recCombinator]
  rfl

/-- The term bar-map at an operation node dispatches through `barTmOp` on the bar
images of the node's subterms (Leivant III section 4.2): `barTm (Tm.op o args) =
barTmOp o (fun j => barTm (args j))`. The general reduction rule of the term
bar-map, the `PolyFix.ind` β-reduction of the operation case that `barTm_var`'s
leaf rule and `barTm_app'`'s app instance rest on, the syntactic counterpart of
`appEval_op`. Holds definitionally since the node's result-sort proof is `rfl`,
collapsing `barTm`'s reconstruction cast. -/
theorem barTm_op {Γ : Binding.Ctx RType} (o : RlmrOOp natAlgSig)
    (args : ∀ j : Fin ((rlmrOSig natAlgSig).args o).length,
      Binding.Tm (rlmrOSig natAlgSig) (Γ ++ (((rlmrOSig natAlgSig).args o).get j).1)
        (((rlmrOSig natAlgSig).args o).get j).2) :
    barTm (Binding.Tm.op o args) = barTmOp o (fun j => barTm (args j)) := rfl

/-- Compatibility of the representation relation with application (Leivant III
section 4.2, Proposition 11's application case, a decision-2 denotational
reformulation): if the substituted function `sub Eσ f` and argument `sub Eσ x`
are represented by the parallel target substitutions into their bar images, then
so is the substituted application `sub Eσ (app' f x)`. The application case of
Proposition 11's fundamental induction, standalone; substitution distributes over
both application nodes (`sub_app'`, `OneLambda.sub_app'`) and the bar-map sends
the node to the `1λ(A)` application (`barTm_app'`), so the arrow clause of
`Represents` (`represents_arrow`) applied to the two hypotheses closes the goal.
Generalizes `lemma10`'s application case away from the `LamFree` restriction. -/
theorem represents_app {Γ : Binding.Ctx RType} {σ' τ' : RType}
    (f : Binding.Tm (rlmrOSig natAlgSig) Γ (RType.arrow σ' τ'))
    (x : Binding.Tm (rlmrOSig natAlgSig) Γ σ')
    (Eσ : Binding.Env (Binding.Tm (rlmrOSig natAlgSig)) Γ [])
    (Eσhat : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) (Γ.map barTy) [])
    (ihf : Represents (RType.arrow σ' τ') (Binding.sub Eσ f) (Binding.sub Eσhat (barTm f)))
    (ihx : Represents σ' (Binding.sub Eσ x) (Binding.sub Eσhat (barTm x))) :
    Represents τ' (Binding.sub Eσ (app' f x)) (Binding.sub Eσhat (barTm (app' f x))) := by
  rw [sub_app', barTm_app']
  exact (OneLambda.sub_app' Eσhat (barTm f) (barTm x)) ▸
    (represents_arrow (Binding.sub Eσ f) (Binding.sub Eσhat (barTm f))).mp ihf
      (Binding.sub Eσ x) (Binding.sub Eσhat (barTm x)) ihx

/-- The recurrence bar-map `barRecur τ` saturated with represented step terms
along the outer abstraction spine reduces to the instantiated inner body (Leivant
III section 4.2–4.3, Proposition 11's recurrence case): applying `barRecur τ` —
whose outer `lamSpine` binds the `k` constructor step variables — to a step-term
tuple `Ghat` along the step-type application spine reduces (`OneLambdaStep`,
reflexive-transitively) to the residual abstraction `λ a. a g⃗` with the step
arguments simultaneously substituted for the abstracted step variables
(`instantiate (metaTuple Ghat)`). The direct instance of the generic λ-spine
β-reduction `reduces_betaSpine` at `barRecur`'s outer abstraction spine, the
recurrence-combinator counterpart of `bbRep_appSpine_reduces`; saturating the
residual with the recurrence argument and β-reducing yields the value spine the
recurrence case reads through `recurBridge`. -/
theorem barRecur_appSpine_reduces (τ : RType)
    (Ghat : ∀ i : Fin (stepTypes natAlgSig (barTy τ) (barTy τ)).length,
      Binding.Tm (oneLambdaSig natAlgSig) [] ((stepTypes natAlgSig (barTy τ) (barTy τ)).get i)) :
    Relation.ReflTransGen OneLambdaStep
      (OneLambda.appSpine (stepTypes natAlgSig (barTy τ) (barTy τ))
        (barRecur (Γ := []) τ) Ghat)
      (Binding.instantiate (Binding.metaTuple Ghat)
        (OneLambda.lamSpine [bbType natAlgSig (barTy τ)]
          (OneLambda.appSpine (stepTypes natAlgSig (barTy τ) (barTy τ))
            (Binding.Tm.var (Binding.Var.appendRight
              ([] ++ stepTypes natAlgSig (barTy τ) (barTy τ))
              (⟨⟨0, by simp⟩, rfl⟩ :
                Binding.Var [bbType natAlgSig (barTy τ)] (bbType natAlgSig (barTy τ)))))
            (fun idx =>
              Binding.Tm.var (Binding.Thinning.weakAppend.app
                (Binding.Var.appendRight []
                  (⟨idx, rfl⟩ :
                    Binding.Var (stepTypes natAlgSig (barTy τ) (barTy τ))
                      ((stepTypes natAlgSig (barTy τ) (barTy τ)).get idx)))))))) := by
  rw [barRecur]
  exact OneLambda.reduces_betaSpine _ _ Ghat

end GebLean.Ramified
