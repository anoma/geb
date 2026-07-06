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

/-- The empty-binder coherence of `ren` (the renaming counterpart of
`sub_underBinder_nil`, underlying `OneLambda.ren_app'`): renaming under an empty
binder, along the append-nil context transport, is renaming along the original
thinning, again up to the append-nil transport. Reduces, through
`traverse_congr_dom`/`_cod`, to the per-variable computation of `Env.underBinder`
at the empty suffix (`Var.appendCases_weakAppend`), whose weakening is the
append-nil transport (`weakAppend_app_nil`) on the variable recovered by the same
lemma. -/
theorem ren_underBinder_nil {S : Binding.BinderSig RType} {Γ Δ : Binding.Ctx RType}
    {s : RType} (ρ : Binding.Thinning Γ Δ) (t : Binding.Tm S Γ s) :
    Binding.traverse (Binding.varKit S)
        (Binding.Env.underBinder (Binding.varKit S) (Ξ := []) (Binding.renEnv ρ))
        ((List.append_nil Γ).symm ▸ t)
      = (List.append_nil Δ).symm ▸ Binding.traverse (Binding.varKit S) (Binding.renEnv ρ) t := by
  have henv :
      (fun (b : RType) (x : Binding.Var Γ b) =>
          Binding.Env.underBinder (Binding.varKit S) (Ξ := []) (Binding.renEnv ρ) b
            ((List.append_nil Γ).symm ▸ x))
        = (fun (b : RType) (x : Binding.Var Γ b) =>
            (List.append_nil Δ).symm ▸ Binding.renEnv ρ b x) := by
    funext b x
    rw [← weakAppend_app_nil x]
    simp only [Binding.Env.underBinder, Binding.varKit]
    rw [Var.appendCases_weakAppend]
    exact weakAppend_app_nil (Binding.renEnv ρ b x)
  calc Binding.traverse (Binding.varKit S)
          (Binding.Env.underBinder (Binding.varKit S) (Ξ := []) (Binding.renEnv ρ))
          ((List.append_nil Γ).symm ▸ t)
      = Binding.traverse (Binding.varKit S)
          (fun b x => Binding.Env.underBinder (Binding.varKit S) (Ξ := []) (Binding.renEnv ρ) b
            ((List.append_nil Γ).symm ▸ x)) t :=
        traverse_congr_dom (Binding.varKit S) (List.append_nil Γ).symm _ t
    _ = Binding.traverse (Binding.varKit S)
          (fun b x => (List.append_nil Δ).symm ▸ Binding.renEnv ρ b x) t := by rw [henv]
    _ = (List.append_nil Δ).symm ▸ Binding.traverse (Binding.varKit S) (Binding.renEnv ρ) t :=
        traverse_congr_cod (Binding.varKit S) (List.append_nil Δ).symm (Binding.renEnv ρ) t

/-- Renaming distributes over the application node of the simply-typed calculus
`1λ(A)`: `ren ρ (OneLambda.app' f x) = OneLambda.app' (ren ρ f) (ren ρ x)`. The
renaming counterpart of `OneLambda.sub_app'`; the two `app'`-argument slots carry
the empty binder, so their `ren` is the empty-binder coherence
`ren_underBinder_nil`, and the outer reassembly is definitional (`traverse_op`).
-/
theorem OneLambda.ren_app' {Γ Δ : Binding.Ctx RType} {σ' τ' : RType}
    (ρ : Binding.Thinning Γ Δ)
    (f : Binding.Tm (oneLambdaSig natAlgSig) Γ (RType.arrow σ' τ'))
    (x : Binding.Tm (oneLambdaSig natAlgSig) Γ σ') :
    Binding.ren ρ (OneLambda.app' f x)
      = OneLambda.app' (Binding.ren ρ f) (Binding.ren ρ x) := by
  refine Eq.trans (b := Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.app σ' τ')
      (fun j => Binding.traverse (Binding.varKit (oneLambdaSig natAlgSig))
        (Binding.Env.underBinder (Binding.varKit (oneLambdaSig natAlgSig)) (Binding.renEnv ρ))
        (Fin.cases ((List.append_nil Γ).symm ▸ f)
          (fun k => Fin.cases ((List.append_nil Γ).symm ▸ x) (fun l => l.elim0) k) j)))
    rfl ?_
  refine Eq.trans ?_ (rfl : Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.app σ' τ')
      (fun j => Fin.cases ((List.append_nil Δ).symm ▸ Binding.ren ρ f)
        (fun k => Fin.cases ((List.append_nil Δ).symm ▸ Binding.ren ρ x)
          (fun l => l.elim0) k) j)
    = OneLambda.app' (Binding.ren ρ f) (Binding.ren ρ x))
  refine congrArg (Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.app σ' τ')) ?_
  funext j
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => l.elim0) k) j
  · exact ren_underBinder_nil ρ f
  · exact ren_underBinder_nil ρ x

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

/-- A `Eq.mpr` transport is heterogeneously equal to its argument: `Eq.mpr h x`
carries `x` across the type equality `h` without changing its value. Proved by
`subst`. The heterogeneous counterpart of `tm_cast_eq_eqRec`, letting the
`barTmOp`-unfolding lemmas collapse the `Eq.mpr` chains the source-def's
`rw`-transports emit against a single `cast`. -/
theorem eq_mpr_heq.{u} {α β : Sort u} (h : α = β) (x : β) : HEq (Eq.mpr h x) x := by
  subst h; rfl

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

/-- Substitution distributes over the iterated application `OneLambda.appSpine`:
`sub ρ (appSpine Ts head args) = appSpine Ts (sub ρ head) (fun i => sub ρ (args
i))`, applying the substitution to the head and every argument of the spine. The
spine dual of `OneLambda.sub_app'`, by recursion on the argument-sort list `Ts`
peeling one application through `OneLambda.sub_app'`. Internal packaging for
`sub_barCase`. -/
theorem OneLambda.sub_appSpine {Γ Δ : Binding.Ctx RType} {result : RType} :
    (Ts : List RType) →
    (ρ : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) Γ Δ) →
    (head : Binding.Tm (oneLambdaSig natAlgSig) Γ (RType.curried Ts result)) →
    (args : ∀ i : Fin Ts.length, Binding.Tm (oneLambdaSig natAlgSig) Γ (Ts.get i)) →
    Binding.sub ρ (OneLambda.appSpine Ts head args)
      = OneLambda.appSpine Ts (Binding.sub ρ head) (fun i => Binding.sub ρ (args i))
  | [], _ρ, _head, _args => rfl
  | _T :: Ts', ρ, head, args => by
      rw [OneLambda.appSpine, OneLambda.sub_appSpine Ts', OneLambda.sub_app']
      rfl

/-- Heterogeneous congruence of substitution in the sort: substituting through
heterogeneously-equal terms at sorts related by `h : a = b` yields
heterogeneously-equal results. Proved by `cases h` then `eq_of_heq`. Internal
packaging for `sub_replicateSpine`, reconciling the `Eq.mpr` sort transports the
homogeneous spine emits. -/
theorem sub_heq_of_heq {S : Binding.BinderSig RType} {Γ Δ : Binding.Ctx RType}
    {a b : RType} (ρ : Binding.Env (Binding.Tm S) Γ Δ) (h : a = b)
    {t : Binding.Tm S Γ a} {u : Binding.Tm S Γ b} (ht : HEq t u) :
    HEq (Binding.sub ρ t) (Binding.sub ρ u) := by
  cases h; rw [eq_of_heq ht]

/-- Substitution distributes over the homogeneous iterated application
`OneLambda.replicateSpine`: `sub ρ (replicateSpine n base head args) =
replicateSpine n base (sub ρ head) (fun idx => sub ρ (args idx))`, applying the
substitution to the head and every argument. The homogeneous instance of
`OneLambda.sub_appSpine`, reconciling the per-index `Eq.mpr` sort transport
through `sub_heq_of_heq`. Internal packaging for `sub_barCase`. -/
theorem OneLambda.sub_replicateSpine {Γ Δ : Binding.Ctx RType} {result : RType}
    (n : Nat) (base : RType)
    (ρ : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) Γ Δ)
    (head : Binding.Tm (oneLambdaSig natAlgSig) Γ
      (RType.curried (List.replicate n base) result))
    (args : Fin n → Binding.Tm (oneLambdaSig natAlgSig) Γ base) :
    Binding.sub ρ (OneLambda.replicateSpine n base head args)
      = OneLambda.replicateSpine n base (Binding.sub ρ head)
          (fun idx => Binding.sub ρ (args idx)) := by
  rw [OneLambda.replicateSpine, OneLambda.sub_appSpine, OneLambda.replicateSpine]
  refine congrArg (OneLambda.appSpine (List.replicate n base) (Binding.sub ρ head)) ?_
  funext i
  have hs : (List.replicate n base).get i = base := by
    rw [List.get_eq_getElem, List.getElem_replicate]
  refine eq_of_heq ((sub_heq_of_heq ρ hs
    ((eq_mpr_heq _ _).trans (eq_mpr_heq _ _))).trans
    (HEq.symm ((eq_mpr_heq _ _).trans (eq_mpr_heq _ _))))

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

/-- Renaming a variable is the variable at the thinned position: `ren ρ (Tm.var
v) = Tm.var (ρ.app v)`. The renaming kit reads the variable through `ρ` and
re-embeds it (`traverse_var`). Internal packaging for `reduces_etaSpine`. -/
theorem ren_var {S : Binding.BinderSig RType} {Γ Δ : Binding.Ctx RType} {s : RType}
    (ρ : Binding.Thinning Γ Δ) (v : Binding.Var Γ s) :
    Binding.ren ρ (Binding.Tm.var v : Binding.Tm S Γ s)
      = Binding.Tm.var (ρ.app v) := by
  simp only [Binding.ren, Binding.traverse_var, Binding.renEnv, Binding.varKit]

/-- A source-context transport commutes with the application node of `1λ(A)`:
for `h : Γ = Γ'`, `h ▸ app' f x = app' (h ▸ f) (h ▸ x)`. Proved by `subst`.
Internal packaging for `reduces_etaSpine`. -/
theorem OneLambda.app'_transport_cod {A : AlgSig} [Fintype A.B]
    {Γ Γ' : Binding.Ctx RType} {σ τ : RType} (h : Γ = Γ')
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) :
    h ▸ OneLambda.app' f x = OneLambda.app' (h ▸ f) (h ▸ x) := by
  subst h; rfl

/-- A source-context transport commutes with the application spine of `1λ(A)`:
for `h : Γ = Γ'`, `h ▸ appSpine Ts head args = appSpine Ts (h ▸ head)
(fun i => h ▸ args i)`. Proved by `subst`. Internal packaging for
`reduces_etaSpine`. -/
theorem OneLambda.appSpine_transport_cod {A : AlgSig} [Fintype A.B]
    {Γ Γ' : Binding.Ctx RType} {result : RType} (h : Γ = Γ') (Ts : List RType)
    (head : Binding.Tm (oneLambdaSig A) Γ (RType.curried Ts result))
    (args : ∀ i : Fin Ts.length, Binding.Tm (oneLambdaSig A) Γ (Ts.get i)) :
    h ▸ OneLambda.appSpine Ts head args
      = OneLambda.appSpine Ts (h ▸ head) (fun i => h ▸ args i) := by
  subst h; rfl

/-- The multi-binder η collapse of the simply-typed calculus `1λ(A)`: the
iterated abstraction `lamSpine Δ` of the head `M` — pre-weakened past `Δ`
(`ren (weakAppend Δ)`) and re-applied along the spine to the freshly bound
variables `Var.appendRight Γ` in spine order — reduces (`OneLambdaStep`,
reflexive-transitively) back to `M`. The iterated form of the single-binder base
rule `OneLambdaStep.eta`, proved by recursion on `Δ` peeling the outermost `lam'`:
the base case is the append-nil transport cancellation, and the cons case moves
the residual spine under the peeled binder (`reduces_lamBody` on the inductive
hypothesis) and fires one `OneLambdaStep.eta`. Novel packaging of the standard
λ-calculus η collapse. -/
theorem OneLambda.reduces_etaSpine :
    {Γ : Binding.Ctx RType} → (Δ : List RType) → {σ : RType} →
    (M : Binding.Tm (oneLambdaSig natAlgSig) Γ (RType.curried Δ σ)) →
    Relation.ReflTransGen OneLambdaStep
      (OneLambda.lamSpine Δ
        (OneLambda.appSpine Δ (Binding.ren (Binding.Thinning.weakAppend (Ξ := Δ)) M)
          (fun i => Binding.Tm.var
            (Binding.Var.appendRight Γ (⟨i, rfl⟩ : Binding.Var Δ (Δ.get i))))))
      M
  | Γ, [], σ, M => by
      change Relation.ReflTransGen OneLambdaStep
          (cast (congrArg (fun c => Binding.Tm (oneLambdaSig natAlgSig) c (RType.curried [] σ))
              (List.append_nil Γ))
            (Binding.ren (Binding.Thinning.weakAppend (Ξ := [])) M)) M
      rw [tm_cast_eq_eqRec (List.append_nil Γ)
          (Binding.ren (Binding.Thinning.weakAppend (Ξ := [])) M),
        ren_weakAppend_nil M,
        eqRec_eqRec_symm
          (motive := fun c => Binding.Tm (oneLambdaSig natAlgSig) c (RType.curried [] σ))]
  | Γ, a :: Δ', σ, M => by
      rw [OneLambda.appSpine, OneLambda.lamSpine]
      refine (OneLambda.reduces_lamBody ?_).trans
        (Relation.ReflTransGen.single (OneLambdaStep.eta M))
      -- The residual body head, after peeling the outermost binder `a`: `M`
      -- applied to the freshly bound `a`-variable, weakened past the remaining
      -- binders `Δ'`. Fires the outer η once `reduces_etaSpine Δ'` collapses it.
      set Mstep : Binding.Tm (oneLambdaSig natAlgSig) (Γ ++ [a]) (RType.curried Δ' σ) :=
        OneLambda.app' (Binding.ren (Binding.Thinning.weakAppend (Ξ := [a])) M)
          (Binding.Tm.var (boundVar (Γ := Γ) (σ := a))) with hMstep
      have hhead :
          (List.append_assoc Γ [a] Δ').symm ▸ OneLambda.app'
              (Binding.ren (Binding.Thinning.weakAppend (Ξ := a :: Δ')) M)
              (Binding.Tm.var
                (Binding.Var.appendRight Γ (⟨⟨0, Nat.succ_pos _⟩, rfl⟩ : Binding.Var (a :: Δ') a)))
            = Binding.ren (Binding.Thinning.weakAppend (Ξ := Δ')) Mstep := by
        rw [hMstep, OneLambda.app'_transport_cod, OneLambda.ren_app', ren_var]
        refine congr_arg₂ OneLambda.app' ?_ ?_
        · exact (ren_weakAppend_append M).symm
        · rw [← Tm.var_transport_cod]
          refine congrArg Binding.Tm.var ?_
          exact (Var.appendRight_append_assoc Γ
            (⟨⟨0, Nat.succ_pos _⟩, rfl⟩ : Binding.Var ([a] ++ Δ') a)).trans rfl
      have hargs :
          (fun i : Fin Δ'.length => (List.append_assoc Γ [a] Δ').symm ▸ Binding.Tm.var
              (Binding.Var.appendRight Γ
                (⟨i.succ, rfl⟩ : Binding.Var (a :: Δ') ((a :: Δ').get i.succ))))
            = (fun i : Fin Δ'.length =>
                (Binding.Tm.var
                  (Binding.Var.appendRight (Γ ++ [a]) (⟨i, rfl⟩ : Binding.Var Δ' (Δ'.get i))) :
                  Binding.Tm (oneLambdaSig natAlgSig) ((Γ ++ [a]) ++ Δ') (Δ'.get i))) := by
        funext i
        rw [← Tm.var_transport_cod]
        refine congrArg Binding.Tm.var ?_
        exact (Var.appendRight_append_assoc Γ
          (⟨i.succ, rfl⟩ : Binding.Var ([a] ++ Δ') (([a] ++ Δ').get i.succ))).trans rfl
      have emid :
          (cast (congrArg (fun c => Binding.Tm (oneLambdaSig natAlgSig) c σ)
              (List.append_assoc Γ [a] Δ').symm)
            (OneLambda.appSpine Δ'
              (OneLambda.app' (Binding.ren (Binding.Thinning.weakAppend (Ξ := a :: Δ')) M)
                (Binding.Tm.var
                  (Binding.Var.appendRight Γ
                    (⟨⟨0, Nat.succ_pos _⟩, rfl⟩ : Binding.Var (a :: Δ') a))))
              (fun i => Binding.Tm.var
                (Binding.Var.appendRight Γ
                  (⟨i.succ, rfl⟩ : Binding.Var (a :: Δ') ((a :: Δ').get i.succ))))))
            = OneLambda.appSpine Δ' (Binding.ren (Binding.Thinning.weakAppend (Ξ := Δ')) Mstep)
                (fun i => Binding.Tm.var
                  (Binding.Var.appendRight (Γ ++ [a]) (⟨i, rfl⟩ : Binding.Var Δ' (Δ'.get i)))) := by
        rw [tm_cast_eq_eqRec (List.append_assoc Γ [a] Δ').symm]
        refine (OneLambda.appSpine_transport_cod (List.append_assoc Γ [a] Δ').symm Δ' _ _).trans ?_
        rw [hhead, hargs]
      exact (congrArg (OneLambda.lamSpine Δ') emid).symm ▸ OneLambda.reduces_etaSpine Δ' Mstep

/-- Substitution commutes with a sort transport of a term: for `h : s = s'`,
`sub ρ (cast (congrArg (Tm S Γ) h) t) = cast (congrArg (Tm S Δ) h) (sub ρ t)`,
carrying the sort equality through the substitution unchanged. Proved by `cases
h`. Internal packaging for `sub_barCase`, discharging `barCase`'s interposed
`cast h_ctd` reconciling the curried branch type to `barTy θ`. -/
theorem sub_cast_sort {S : Binding.BinderSig RType} {Γ Δ : Binding.Ctx RType}
    {s s' : RType} (ρ : Binding.Env (Binding.Tm S) Γ Δ) (h : s = s')
    (t : Binding.Tm S Γ s) :
    Binding.sub ρ (cast (congrArg (Binding.Tm S Γ) h) t)
      = cast (congrArg (Binding.Tm S Δ) h) (Binding.sub ρ t) := by
  cases h; rfl

/-- Substituting under a binder `Ξ` fixes a bound-suffix variable: for a variable
`v` of the binder `Ξ`, `sub (underBinder ρ) (var (appendRight Γ v)) = var
(appendRight Δ v)`, rebasing the ambient prefix `Γ ↦ Δ` while leaving the bound
position unchanged. The `appendRight`-branch computation of `Env.underBinder`
(`Var.appendCases_appendRight`). Internal packaging for `sub_barCase`. -/
theorem sub_underBinder_appendRight {S : Binding.BinderSig RType}
    {Γ Δ Ξ : Binding.Ctx RType} {s : RType} (ρ : Binding.Env (Binding.Tm S) Γ Δ)
    (v : Binding.Var Ξ s) :
    Binding.sub (Binding.Env.underBinder (Binding.subKit S) (Ξ := Ξ) ρ)
        (Binding.Tm.var (Binding.Var.appendRight Γ v))
      = Binding.Tm.var (Binding.Var.appendRight Δ v) := by
  rw [Binding.sub_var]
  simp only [Binding.Env.underBinder, Binding.subKit]
  rw [Binding.Var.appendCases_appendRight]

/-- Substituting under a binder `Ξ` weakens a prefix variable: for a variable `w`
of the ambient prefix, `sub (underBinder ρ) (var (weakAppend.app w)) = ren
weakAppend (sub ρ (var w))`, pushing the substitution past the suffix embedding.
The `weakAppend`-branch computation of `Env.underBinder`
(`Var.appendCases_weakAppend`). Internal packaging for `sub_barCase`. -/
theorem sub_underBinder_weakAppend {S : Binding.BinderSig RType}
    {Γ Δ Ξ : Binding.Ctx RType} {s : RType} (ρ : Binding.Env (Binding.Tm S) Γ Δ)
    (w : Binding.Var Γ s) :
    Binding.sub (Binding.Env.underBinder (Binding.subKit S) (Ξ := Ξ) ρ)
        (Binding.Tm.var (Binding.Thinning.weakAppend.app w))
      = Binding.ren Binding.Thinning.weakAppend (Binding.sub ρ (Binding.Tm.var w)) := by
  rw [Binding.sub_var, Binding.sub_var]
  simp only [Binding.Env.underBinder, Binding.subKit]
  rw [Binding.Var.appendCases_weakAppend]

/-- Substitution fixes the nullary case combinator of `1λ(A)`: `sub ρ (Tm.op case
elim0) = Tm.op case elim0`. The constant carries no subterms, so both environments
leave it unchanged (`traverse_op` over the empty argument family). Internal
packaging for `sub_barCase` and the `θ = o` arm of `represents_case`. -/
theorem OneLambda.sub_caseOp {Γ Δ : Binding.Ctx RType}
    (ρ : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) Γ Δ) :
    Binding.sub ρ (Binding.Tm.op (S := oneLambdaSig natAlgSig)
        OneLambdaOp.case (fun k => k.elim0))
      = Binding.Tm.op (S := oneLambdaSig natAlgSig) OneLambdaOp.case (fun k => k.elim0) := by
  rw [Binding.sub, Binding.traverse_op]
  congr 1
  funext k
  exact k.elim0

/-- Substitution fixes the case bar-map `barCase` (Leivant III section 4.2): `sub ρ
(barCase θ hθ) = barCase θ hθ`, rebasing only the ambient context marker from `Γ` to `Δ`.
`barCase`'s image is closed with respect to the ambient context: every variable occurring
in it points into `barCase`'s own local binders (its abstraction spines, replicate-spine,
and case-argument spine), never into `Γ`, so `ρ` has nothing reachable to act on. Proved by
cases on `θ.shape`: the `o` branch is `sub_caseOp`; the `omega` branch unfolds through
`sub_lamSpine`, `sub_cast_sort`, `sub_replicateSpine`, `sub_app'`, `sub_caseOp`, and
`sub_appSpine`, discharging the residual local variables with `sub_underBinder_weakAppend`
and `sub_underBinder_appendRight`. Novel packaging of section 4.2. -/
theorem OneLambda.sub_barCase {Γ Δ : Binding.Ctx RType} (θ : RType) (hθ : θ.IsObj)
    (ρ : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) Γ Δ) :
    Binding.sub ρ (barCase (Γ := Γ) θ hθ) = barCase (Γ := Δ) θ hθ := by
  cases hs : θ.shape with
  | o =>
    have hθo : θ = RType.o := RType.eq_o_of_shape_o hs
    subst hθo
    change Binding.sub ρ (Binding.Tm.op (S := oneLambdaSig natAlgSig)
        OneLambdaOp.case (fun k => k.elim0))
      = Binding.Tm.op (S := oneLambdaSig natAlgSig) OneLambdaOp.case (fun k => k.elim0)
    rw [Binding.sub, Binding.traverse_op]
    congr 1
    funext k
    exact k.elim0
  | arrow => exact absurd hθ (by unfold RType.IsObj; rw [hs]; decide)
  | omega =>
    obtain ⟨τ', rfl⟩ : ∃ τ', θ = RType.omega τ' :=
      ⟨θ.omegaArg, RType.eq_omega_omegaArg_of_shape hs⟩
    unfold barCase
    simp only [RType.shape_omega]
    refine (OneLambda.sub_lamSpine [RType.o] ρ _).trans ?_
    refine congrArg (OneLambda.lamSpine [RType.o]) ?_
    refine (OneLambda.sub_lamSpine
      (List.replicate natAlgSig.numCtors (barTy τ'.omega)) _ _).trans ?_
    refine congrArg
      (OneLambda.lamSpine (List.replicate natAlgSig.numCtors (barTy τ'.omega))) ?_
    rw [sub_cast_sort]
    · congr 1
      refine (OneLambda.sub_lamSpine (barTy τ'.omega).domains _ _).trans ?_
      refine congrArg (OneLambda.lamSpine (barTy τ'.omega).domains) ?_
      rw [OneLambda.sub_replicateSpine, OneLambda.sub_app']
      congr 1
      · refine congr (congrArg OneLambda.app' (OneLambda.sub_caseOp _)) ?_
        rw [sub_underBinder_weakAppend, sub_underBinder_weakAppend,
          sub_underBinder_appendRight, ren_var, ren_var]
      · funext idx
        simp only [OneLambda.sub_appSpine, sub_underBinder_appendRight]
        rw [sub_cast_sort, sub_underBinder_weakAppend, sub_underBinder_appendRight, ren_var]
        exact ((congrArg (RType.curried (barTy τ'.omega).domains)
          (RType.objTarget_of_isSimple (barTy τ'.omega) (barTy_isSimple _)).symm).trans
          (RType.curried_domains (barTy τ'.omega)).symm).symm
    · exact (congrArg (RType.curried (barTy τ'.omega).domains)
        (RType.objTarget_of_isSimple (barTy τ'.omega) (barTy_isSimple _)).symm).trans
        (RType.curried_domains (barTy τ'.omega)).symm

/-- Substitution fixes the constructor bar-map `barConOmega` (Leivant III section
4.2): `sub ρ (barConOmega b τ) = barConOmega b τ`, rebasing only the ambient
context marker from `Γ` to `Δ`. `barConOmega`'s image is closed with respect to
the ambient context: every variable occurring in it points into `barConOmega`'s
own local binders (its outer argument spine, its constructor-variable spine, and
its per-argument application spine), never into `Γ`, so `ρ` has nothing reachable
to act on. Proved by unfolding through the two abstraction spines
(`sub_lamSpine`), the homogeneous constructor spine (`sub_replicateSpine`), and
the per-argument application spine (`sub_appSpine`), discharging the residual
local variables with `sub_underBinder_weakAppend` and
`sub_underBinder_appendRight`. Novel packaging of section 4.2. -/
theorem OneLambda.sub_barConOmega {Γ Δ : Binding.Ctx RType} (b : natAlgSig.B) (τ : RType)
    (ρ : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) Γ Δ) :
    Binding.sub ρ (barConOmega (Γ := Γ) b τ) = barConOmega (Γ := Δ) b τ := by
  unfold barConOmega
  refine (OneLambda.sub_lamSpine
    (List.replicate (natAlgSig.ar b) (bbType natAlgSig (barTy τ))) ρ _).trans ?_
  refine congrArg
    (OneLambda.lamSpine (List.replicate (natAlgSig.ar b) (bbType natAlgSig (barTy τ)))) ?_
  refine (OneLambda.sub_lamSpine (stepTypes natAlgSig (barTy τ) (barTy τ)) _ _).trans ?_
  refine congrArg (OneLambda.lamSpine (stepTypes natAlgSig (barTy τ) (barTy τ))) ?_
  rw [OneLambda.sub_replicateSpine]
  congr 1
  · rw [sub_underBinder_appendRight]
  · funext j
    rw [OneLambda.sub_appSpine]
    congr 1
    · rw [sub_underBinder_weakAppend, sub_underBinder_appendRight, ren_var]
    · funext idx
      rw [sub_underBinder_appendRight]

/-- Renaming is substitution by the variable-embedding environment: `ren ρ t =
sub (fun s x => var (ρ.app x)) t`, presenting a thinning as the substitution that
sends each variable to the variable it is thinned to. The `σ = idEnv`
specialization of the sub-ren fusion law `sub_ren`, closed by the right-unit law
`sub_id`. Lets the substitution algebra (`sub_lamSpine`, `sub_sub`) act on renamed
terms without a parallel renaming-under-binder development. -/
theorem ren_eq_sub_var {S : Binding.BinderSig RType} {Γ Δ : Binding.Ctx RType} {s : RType}
    (ρ : Binding.Thinning Γ Δ) (t : Binding.Tm S Γ s) :
    Binding.ren ρ t = Binding.sub (fun _ x => Binding.Tm.var (ρ.app x)) t := by
  rw [← Binding.sub_id (Binding.ren ρ t), Binding.ren_sub]
  rfl

/-- Instantiating a binder-weakened abstraction spine with the freshly bound
variables cancels (Leivant III section 4.2, the β-collapse dual of
`reduces_etaSpine`): the iterated abstraction `lamSpine Δ M`, weakened past a
fresh copy of `Δ` and applied along the spine to the freshly bound `Δ`-variables,
reduces (`OneLambdaStep`, reflexive-transitively) back to the body `M`. Presents
the outer weakening as a substitution (`ren_eq_sub_var`), pushes it under the
abstraction spine (`sub_lamSpine`), β-reduces the saturated spine
(`reduces_betaSpine`), and cancels the composite substitution to the identity
(`sub_sub`, `sub_id`) by the variable computation that the freshly bound spine
inverts the weakening. Novel packaging of section 4.2. -/
theorem OneLambda.reduces_appSpine_ren_lamSpine {Γ : Binding.Ctx RType}
    (Δ : List RType) {σ : RType} (M : Binding.Tm (oneLambdaSig natAlgSig) (Γ ++ Δ) σ) :
    Relation.ReflTransGen OneLambdaStep
      (OneLambda.appSpine Δ
        (Binding.ren (Binding.Thinning.weakAppend (Ξ := Δ)) (OneLambda.lamSpine Δ M))
        (fun i => Binding.Tm.var
          (Binding.Var.appendRight Γ (⟨i, rfl⟩ : Binding.Var Δ (Δ.get i)))))
      M := by
  rw [ren_eq_sub_var, OneLambda.sub_lamSpine]
  refine (OneLambda.reduces_betaSpine Δ _ _).trans ?_
  have hcancel :
      Binding.instantiate
        (Binding.metaTuple (fun i => Binding.Tm.var
          (Binding.Var.appendRight Γ (⟨i, rfl⟩ : Binding.Var Δ (Δ.get i)))))
        (Binding.sub
          (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig)) (Ξ := Δ)
            (fun _ x => Binding.Tm.var (Binding.Thinning.weakAppend.app x))) M)
        = M := by
    rw [Binding.instantiate, Binding.sub_sub]
    have henv :
        (fun (s : RType) (x : Binding.Var (Γ ++ Δ) s) =>
          Binding.sub (Binding.extendEnv Binding.idEnv
            (Binding.metaTuple (fun i => Binding.Tm.var
              (Binding.Var.appendRight Γ (⟨i, rfl⟩ : Binding.Var Δ (Δ.get i))))))
            (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig)) (Ξ := Δ)
              (fun _ x => Binding.Tm.var (Binding.Thinning.weakAppend.app x)) s x))
          = (Binding.idEnv : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig))
              (Γ ++ Δ) (Γ ++ Δ)) := by
      funext s x
      set τ := Binding.extendEnv Binding.idEnv
        (Binding.metaTuple (fun i => Binding.Tm.var
          (Binding.Var.appendRight Γ (⟨i, rfl⟩ : Binding.Var Δ (Δ.get i)))))
        with hτ
      simp only [Binding.Env.underBinder, Binding.subKit]
      rw [Binding.Var.appendCases_natural (Binding.sub τ)]
      have hb1 : (fun y : Binding.Var Δ s =>
            Binding.sub τ (Binding.Tm.var (Binding.Var.appendRight (Γ ++ Δ) y)))
          = fun y => Binding.Tm.var (Binding.Var.appendRight Γ y) := by
        funext y
        rw [Binding.sub_var, hτ, Binding.extendEnv_appendRight]
        obtain ⟨i, hi⟩ := y
        subst hi
        rfl
      have hb2 : (fun v : Binding.Var Γ s =>
            Binding.sub τ (Binding.ren Binding.Thinning.weakAppend
              (Binding.Tm.var (Binding.Thinning.weakAppend.app v))))
          = fun v => Binding.Tm.var (Binding.Thinning.weakAppend.app v) := by
        funext v
        rw [ren_var, Binding.sub_var, hτ, Binding.extendEnv_weakAppend]
        rfl
      rw [hb1, hb2, ← Binding.Var.appendCases_natural Binding.Tm.var,
        Binding.Var.appendCases_self]
      rfl
    rw [henv, Binding.sub_id]
  rw [hcancel]

/-- Reduction of the arguments of an application spine lifts to a reduction of
the whole spine: if `args i ⇒* args' i` pointwise then `appSpine Ts head args ⇒*
appSpine Ts head args'`. By recursion on `Ts`, reducing the head application's
argument through `reduces_app'_right` under the residual spine
(`reduces_appSpine`) and the remaining arguments by the recursion. The
argument-side counterpart of `OneLambda.reduces_appSpine`. -/
theorem OneLambda.reduces_appSpine_args {Γ : Binding.Ctx RType} {result : RType} :
    (Ts : List RType) →
    (head : Binding.Tm (oneLambdaSig natAlgSig) Γ (RType.curried Ts result)) →
    (args args' : ∀ i : Fin Ts.length, Binding.Tm (oneLambdaSig natAlgSig) Γ (Ts.get i)) →
    (∀ i, Relation.ReflTransGen OneLambdaStep (args i) (args' i)) →
    Relation.ReflTransGen OneLambdaStep
      (OneLambda.appSpine Ts head args) (OneLambda.appSpine Ts head args')
  | [], _head, _args, _args', _h => Relation.ReflTransGen.refl
  | _T :: Ts', head, args, args', h => by
      rw [OneLambda.appSpine, OneLambda.appSpine]
      refine (OneLambda.reduces_appSpine Ts' _ _ (fun i => args i.succ)
        (OneLambda.reduces_app'_right head (h ⟨0, Nat.succ_pos _⟩))).trans ?_
      exact OneLambda.reduces_appSpine_args Ts' (OneLambda.app' head (args' ⟨0, Nat.succ_pos _⟩))
        (fun i => args i.succ) (fun i => args' i.succ) (fun i => h i.succ)

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

/-- The term bar-map at a destructor node is the base destructor constant of
`1λ(A)` (Leivant III section 4.2): `barTmOp (dstr j) ih = Tm.op (dstr j)`. The
destructor result sort `o → o` is bar-invariant (`barTy (arrow o o) = arrow o o`
definitionally), so the branch's `rw [barTy_arrow, barTy_o]` transport collapses
and the equation holds outright. The `barTmOp` dstr-branch unfolding, novel
packaging of section 4.2. -/
theorem barTmOp_dstr {Γ : Binding.Ctx RType} (j : Fin natAlgSig.maxArity)
    (ih : ∀ jj : Fin ((rlmrOSig natAlgSig).args (RlmrOOp.dstr j)).length,
      Binding.Tm (oneLambdaSig natAlgSig)
        ((Γ ++ (((rlmrOSig natAlgSig).args (RlmrOOp.dstr j)).get jj).1).map barTy)
        (barTy (((rlmrOSig natAlgSig).args (RlmrOOp.dstr j)).get jj).2)) :
    barTmOp (Γ := Γ) (RlmrOOp.dstr j) ih
      = Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.dstr j) (fun k => k.elim0) :=
  rfl

/-- The term bar-map at a base-object constructor node is the base constructor
constant of `1λ(A)` (Leivant III section 4.2): `barTmOp (con o b) ih = con b`,
modulo the type transport of the constructor result sort under the bar-map. The
result sort `o^{A.ar b} → o` is not bar-invariant syntactically — the bar-map
distributes over currying by induction (`barTy_curried`, not `rfl`) — so the
equation carries the residual `cast` along `hbar` from `barTy` of the source
result sort to the `1λ(A)` result sort, which the consumer discharges. The
`barTmOp` con-branch unfolding at `θ = o`, novel packaging of section 4.2. -/
theorem barTmOp_con_o {Γ : Binding.Ctx RType} (b : natAlgSig.B)
    (ih : ∀ jj : Fin ((rlmrOSig natAlgSig).args (RlmrOOp.con RType.o (Or.inl rfl) b)).length,
      Binding.Tm (oneLambdaSig natAlgSig)
        ((Γ ++ (((rlmrOSig natAlgSig).args
          (RlmrOOp.con RType.o (Or.inl rfl) b)).get jj).1).map barTy)
        (barTy (((rlmrOSig natAlgSig).args
          (RlmrOOp.con RType.o (Or.inl rfl) b)).get jj).2))
    (hbar : barTy ((rlmrOSig natAlgSig).result (RlmrOOp.con RType.o (Or.inl rfl) b))
      = (oneLambdaSig natAlgSig).result (OneLambdaOp.con b)) :
    barTmOp (Γ := Γ) (RlmrOOp.con RType.o (Or.inl rfl) b) ih
      = cast (congrArg (Binding.Tm (oneLambdaSig natAlgSig) (Γ.map barTy)) hbar.symm)
          (Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.con b) (fun k => k.elim0)) := by
  dsimp only [barTmOp, RType.shape_o]
  apply eq_of_heq
  rw [id_eq]
  exact (eq_mpr_heq _ _).trans
    ((eq_mpr_heq _ _).trans ((eq_mpr_heq _ _).trans (cast_heq _ _).symm))

/-- The term bar-map at a recurrence node is the recurrence bar-map `barRecur`
(Leivant III section 4.2): `barTmOp (recur τ) ih = barRecur τ`, modulo the type
transport of the recurrence result sort under the bar-map. The source result
sort `ξ⃗, Ωτ → τ` maps under `barTy` to `barRecur`'s type only after distributing
the bar-map over the curried step types (`barTy_curried`, `stepTypes_map_barTy`,
not `rfl`), so the equation carries the residual `cast` along `hbar`, which the
consumer discharges. The `barTmOp` recur-branch unfolding, novel packaging of
section 4.2. -/
theorem barTmOp_recur {Γ : Binding.Ctx RType} (τ : RType)
    (ih : ∀ jj : Fin ((rlmrOSig natAlgSig).args (RlmrOOp.recur τ)).length,
      Binding.Tm (oneLambdaSig natAlgSig)
        ((Γ ++ (((rlmrOSig natAlgSig).args (RlmrOOp.recur τ)).get jj).1).map barTy)
        (barTy (((rlmrOSig natAlgSig).args (RlmrOOp.recur τ)).get jj).2))
    (hbar : barTy ((rlmrOSig natAlgSig).result (RlmrOOp.recur τ))
      = RType.curried (stepTypes natAlgSig (barTy τ) (barTy τ))
          (RType.arrow (bbType natAlgSig (barTy τ)) (barTy τ))) :
    barTmOp (Γ := Γ) (RlmrOOp.recur τ) ih
      = cast (congrArg (Binding.Tm (oneLambdaSig natAlgSig) (Γ.map barTy)) hbar.symm)
          (barRecur τ) := by
  dsimp only [barTmOp]
  apply eq_of_heq
  rw [id_eq]
  exact (eq_mpr_heq _ _).trans
    ((eq_mpr_heq _ _).trans ((eq_mpr_heq _ _).trans (cast_heq _ _).symm))

/-- The term bar-map at a case node is the case bar-map `barCase` (Leivant III
section 4.2): `barTmOp (case θ hθ) ih = barCase θ hθ`, modulo the type transport
of the case result sort under the bar-map. The source result sort
`o, θ^k → θ` maps under `barTy` to `barCase`'s type only after distributing the
bar-map over the curried branch types (`barTy_curried`, not `rfl`), so the
equation carries the residual `cast` along `hbar`, which the consumer discharges.
The `barTmOp` case-branch unfolding, novel packaging of section 4.2. -/
theorem barTmOp_case {Γ : Binding.Ctx RType} (θ : RType) (hθ : θ.IsObj)
    (ih : ∀ jj : Fin ((rlmrOSig natAlgSig).args (RlmrOOp.case θ hθ)).length,
      Binding.Tm (oneLambdaSig natAlgSig)
        ((Γ ++ (((rlmrOSig natAlgSig).args (RlmrOOp.case θ hθ)).get jj).1).map barTy)
        (barTy (((rlmrOSig natAlgSig).args (RlmrOOp.case θ hθ)).get jj).2))
    (hbar : barTy ((rlmrOSig natAlgSig).result (RlmrOOp.case θ hθ))
      = RType.arrow RType.o
          (RType.curried (List.replicate natAlgSig.numCtors (barTy θ)) (barTy θ))) :
    barTmOp (Γ := Γ) (RlmrOOp.case θ hθ) ih
      = cast (congrArg (Binding.Tm (oneLambdaSig natAlgSig) (Γ.map barTy)) hbar.symm)
          (barCase θ hθ) := by
  dsimp only [barTmOp]
  apply eq_of_heq
  rw [id_eq]
  exact (eq_mpr_heq _ _).trans
    ((eq_mpr_heq _ _).trans ((eq_mpr_heq _ _).trans (cast_heq _ _).symm))

/-- The term bar-map at a shifted constructor node is the constructor bar-map
`barConOmega` (Leivant III section 4.2): `barTmOp (con (Ω τ) b) ih =
barConOmega b τ`, modulo the type transport of the constructor result sort under
the bar-map. The source result sort `(Ω τ)^{A.ar b} → Ω τ` maps under `barTy` to
`barConOmega`'s type only after distributing the bar-map over the curried shifted
domains (`barTy_curried`, not `rfl`) and recovering the shift argument
(`θ.omegaArg` at `θ = Ω τ` reduces to `τ`), so the equation carries the residual
`cast` along `hbar`, which the consumer discharges. The `barTmOp` con-branch
unfolding at `θ = Ω τ`, novel packaging of section 4.2. -/
theorem barTmOp_con_omega {Γ : Binding.Ctx RType} (τ : RType) (b : natAlgSig.B)
    (ih : ∀ jj : Fin
        ((rlmrOSig natAlgSig).args (RlmrOOp.con (RType.omega τ) (Or.inr rfl) b)).length,
      Binding.Tm (oneLambdaSig natAlgSig)
        ((Γ ++ (((rlmrOSig natAlgSig).args
          (RlmrOOp.con (RType.omega τ) (Or.inr rfl) b)).get jj).1).map barTy)
        (barTy (((rlmrOSig natAlgSig).args
          (RlmrOOp.con (RType.omega τ) (Or.inr rfl) b)).get jj).2))
    (hbar : barTy ((rlmrOSig natAlgSig).result (RlmrOOp.con (RType.omega τ) (Or.inr rfl) b))
      = RType.curried (List.replicate (natAlgSig.ar b) (bbType natAlgSig (barTy τ)))
          (bbType natAlgSig (barTy τ))) :
    barTmOp (Γ := Γ) (RlmrOOp.con (RType.omega τ) (Or.inr rfl) b) ih
      = cast (congrArg (Binding.Tm (oneLambdaSig natAlgSig) (Γ.map barTy)) hbar.symm)
          (barConOmega b τ) := by
  dsimp only [barTmOp, RType.shape_omega]
  apply eq_of_heq
  rw [id_eq]
  exact (eq_mpr_heq _ _).trans
    ((eq_mpr_heq _ _).trans ((eq_mpr_heq _ _).trans (cast_heq _ _).symm))

/-- The base destructor `1λ(A)` term applied to the concrete term of a
constructor node reduces to the concrete term of the destructed subterm (Leivant
III section 4.1–4.2, Proposition 11's destructor case): `dstr_j (conc (mk b s⃗))`
reduces (`OneLambdaStep`, reflexive-transitively) to `conc (dstrRead j (mk b s⃗))`,
the `j`-th concrete subterm when `j < r_b` (destructor hit) and the concrete term
of the whole node when `j ≥ r_b` (destructor miss). Unfolds the head through
`conc_mk` and fires the single base redex `OneLambdaStep.dstrHit`/`dstrMiss`,
whose contractum matches the two branches of `dstrRead`'s `FreeAlg.recurse`
(`FreeAlg.recurse_mk`). Novel packaging of section 4.2. -/
theorem conc_app_dstr_reduces (j : Fin natAlgSig.maxArity) (b : natAlgSig.B)
    (sub : Fin (natAlgSig.ar b) → FreeAlg natAlgSig) :
    Relation.ReflTransGen OneLambdaStep
      (OneLambda.app'
        (Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.dstr j) (fun k => k.elim0))
        (conc (FreeAlg.mk b sub)))
      (conc (dstrRead j.val (FreeAlg.mk b sub))) := by
  rw [conc_mk]
  by_cases h : j.val < natAlgSig.ar b
  · rw [show dstrRead j.val (FreeAlg.mk b sub) = sub ⟨j.val, h⟩ by
        rw [dstrRead, FreeAlg.recurse_mk, dif_pos h]]
    exact Relation.ReflTransGen.single (OneLambdaStep.dstrHit j h (fun i => conc (sub i)))
  · rw [show dstrRead j.val (FreeAlg.mk b sub) = FreeAlg.mk b sub by
        rw [dstrRead, FreeAlg.recurse_mk, dif_neg h], conc_mk]
    exact Relation.ReflTransGen.single
      (OneLambdaStep.dstrMiss j (Nat.le_of_not_lt h) (fun i => conc (sub i)))

/-- The base case `1λ(A)` spine over the concrete term of a constructor node
reduces to the selected branch (Leivant III section 4.1–4.2, Proposition 11's
case): the case spine `case (conc (mk (ctorAt idx) s⃗)) b₁…b_k` reduces
(`OneLambdaStep`, reflexive-transitively) to the branch `b_idx` at the scrutinee
constructor's enumeration position. Unfolds the scrutinee through `conc_mk` and
fires the single base redex `OneLambdaStep.case`. Novel packaging of section
4.2. -/
theorem conc_replicateSpine_case_reduces (idx : Fin natAlgSig.numCtors)
    (sub : Fin (natAlgSig.ar (ctorAt idx)) → FreeAlg natAlgSig)
    (branches : Fin natAlgSig.numCtors →
      Binding.Tm (oneLambdaSig natAlgSig) [] RType.o) :
    Relation.ReflTransGen OneLambdaStep
      (OneLambda.replicateSpine natAlgSig.numCtors RType.o
        (OneLambda.app'
          (Binding.Tm.op (S := oneLambdaSig natAlgSig) OneLambdaOp.case (fun k => k.elim0))
          (conc (FreeAlg.mk (ctorAt idx) sub)))
        branches)
      (branches idx) := by
  rw [conc_mk]
  exact Relation.ReflTransGen.single
    (OneLambdaStep.case idx (fun i => conc (sub i)) branches)

/-- Compatibility of the representation relation with a base-object constructor
constant (Leivant III section 4.2, Proposition 11's `con^o` case, a decision-2
denotational reformulation): the constructor node `con^o_b` is represented by the
parallel target substitution into its bar image `con_b` of `1λ(A)`. The nullary
node is fixed by both substitutions; the zero-arity constructor represents itself
reflexively (`barTm` of the zero constructor is definitionally `conc` of its
denotation), and the successor branch reduces the applied bar constructor to the
concrete term of the semantic node (`appChain_stdConstructorInterp`, `conc_mk`),
carrying the argument representative under the constructor by
`OneLambda.reduces_app'_right`. Uses `barTmOp_con_o` to strip the bar-image
transport. -/
theorem represents_con_succ {Γ : Binding.Ctx RType} (b : natAlgSig.B)
    (Eσ : Binding.Env (Binding.Tm (rlmrOSig natAlgSig)) Γ [])
    (Eσhat : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) (Γ.map barTy) []) :
    Represents (RType.curried (List.replicate (natAlgSig.ar b) RType.o) RType.o)
      (Binding.sub Eσ
        (Binding.Tm.op (S := rlmrOSig natAlgSig)
          (RlmrOOp.con RType.o (Or.inl rfl) b) (fun k => k.elim0)))
      (Binding.sub Eσhat
        (barTm (Binding.Tm.op (S := rlmrOSig natAlgSig)
          (RlmrOOp.con RType.o (Or.inl rfl) b) (fun k => k.elim0)))) := by
  cases b with
  | false =>
    have htgt : Binding.sub Eσhat
          (barTm (Binding.Tm.op (S := rlmrOSig natAlgSig)
            (RlmrOOp.con RType.o (Or.inl rfl) false) (fun k => k.elim0)))
        = Binding.Tm.op (S := oneLambdaSig natAlgSig)
            (OneLambdaOp.con false) (fun k => k.elim0) := by
      rw [barTm_op, barTmOp_con_o false _ rfl]
      change Binding.sub Eσhat
          (Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.con false) (fun k => k.elim0))
        = Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.con false) (fun k => k.elim0)
      rw [Binding.sub, Binding.traverse_op]; congr 1; funext k; exact k.elim0
    exact htgt ▸ Relation.ReflTransGen.refl
  | true =>
    have htgt : Binding.sub Eσhat
          (barTm (Binding.Tm.op (S := rlmrOSig natAlgSig)
            (RlmrOOp.con RType.o (Or.inl rfl) true) (fun k => k.elim0)))
        = Binding.Tm.op (S := oneLambdaSig natAlgSig)
            (OneLambdaOp.con true) (fun k => k.elim0) := by
      rw [barTm_op, barTmOp_con_o true _ rfl]
      change Binding.sub Eσhat
          (Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.con true) (fun k => k.elim0))
        = Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.con true) (fun k => k.elim0)
      rw [Binding.sub, Binding.traverse_op]; congr 1; funext k; exact k.elim0
    refine htgt ▸ ?_
    change Represents (RType.arrow RType.o RType.o)
      (Binding.sub Eσ (Binding.Tm.op (S := rlmrOSig natAlgSig)
        (RlmrOOp.con RType.o (Or.inl rfl) true) (fun k => k.elim0)))
      (Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.con true) (fun k => k.elim0))
    rw [represents_arrow]
    intro G Ghat hG
    have hsrc : Binding.sub Eσ (Binding.Tm.op (S := rlmrOSig natAlgSig)
          (RlmrOOp.con RType.o (Or.inl rfl) true) (fun k => k.elim0))
        = Binding.Tm.op (S := rlmrOSig natAlgSig)
            (RlmrOOp.con RType.o (Or.inl rfl) true) (fun k => k.elim0) := by
      rw [Binding.sub, Binding.traverse_op]; congr 1; funext k; exact k.elim0
    have hsem : appEval (sourceApp (Binding.sub Eσ (Binding.Tm.op (S := rlmrOSig natAlgSig)
          (RlmrOOp.con RType.o (Or.inl rfl) true) (fun k => k.elim0))) G) finZeroElim
        = FreeAlg.mk true (fun _ => appEval G finZeroElim) := by
      refine (congrArg (fun t => appEval (sourceApp t G) finZeroElim) hsrc).trans ?_
      rw [sourceApp, appEval_app']
      change stdConstructorInterp natAlgSig (⟨RType.o, Or.inl rfl⟩, true)
          (Fin.cons (appEval G finZeroElim) finZeroElim)
        = FreeAlg.mk true (fun _ => appEval G finZeroElim)
      simp only [stdConstructorInterp]
      refine congrArg (FreeAlg.mk (A := natAlgSig) true) ?_
      funext i
      have hi : i = (⟨0, by decide⟩ : Fin (natAlgSig.ar true)) :=
        Fin.ext (Nat.lt_one_iff.mp i.isLt)
      subst hi
      rfl
    have hconc : conc (FreeAlg.mk true (fun _ => appEval G finZeroElim))
        = OneLambda.app' (Binding.Tm.op (S := oneLambdaSig natAlgSig)
            (OneLambdaOp.con true) (fun k => k.elim0)) (conc (appEval G finZeroElim)) := by
      rw [conc_mk]
      rfl
    change Relation.ReflTransGen OneLambdaStep
      (OneLambda.app' (Binding.Tm.op (S := oneLambdaSig natAlgSig)
        (OneLambdaOp.con true) (fun k => k.elim0)) Ghat)
      (conc (appEval (sourceApp (Binding.sub Eσ (Binding.Tm.op (S := rlmrOSig natAlgSig)
        (RlmrOOp.con RType.o (Or.inl rfl) true) (fun k => k.elim0))) G) finZeroElim))
    rw [hsem, hconc]
    exact OneLambda.reduces_app'_right _ hG

/-- Compatibility of the representation relation with a destructor constant
(Leivant III section 4.2, Proposition 11's destructor case, a decision-2
denotational reformulation): the destructor node `dstr_j` is represented by the
parallel target substitution into its bar image `dstr_j` of `1λ(A)`. The nullary
node is fixed by both substitutions; the base destructor bar image needs no
transport (`barTmOp_dstr`), and on a represented argument the applied destructor
reduces to the concrete term of the destructed subterm through the shared
concrete-reduction lemma `conc_app_dstr_reduces`, after casing the argument's
value on its top constructor (`PolyFix.ind`). -/
theorem represents_dstr {Γ : Binding.Ctx RType} (j : Fin natAlgSig.maxArity)
    (Eσ : Binding.Env (Binding.Tm (rlmrOSig natAlgSig)) Γ [])
    (Eσhat : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) (Γ.map barTy) []) :
    Represents (RType.arrow RType.o RType.o)
      (Binding.sub Eσ (Binding.Tm.op (S := rlmrOSig natAlgSig)
        (RlmrOOp.dstr j) (fun k => k.elim0)))
      (Binding.sub Eσhat (barTm (Binding.Tm.op (S := rlmrOSig natAlgSig)
        (RlmrOOp.dstr j) (fun k => k.elim0)))) := by
  have htgt : Binding.sub Eσhat (barTm (Binding.Tm.op (S := rlmrOSig natAlgSig)
        (RlmrOOp.dstr j) (fun k => k.elim0)))
      = Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.dstr j) (fun k => k.elim0) := by
    rw [barTm_op, barTmOp_dstr]
    change Binding.sub Eσhat
        (Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.dstr j) (fun k => k.elim0))
      = Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.dstr j) (fun k => k.elim0)
    rw [Binding.sub, Binding.traverse_op]; congr 1; funext k; exact k.elim0
  refine htgt ▸ ?_
  rw [represents_arrow]
  intro G Ghat hG
  have hsrc : Binding.sub Eσ (Binding.Tm.op (S := rlmrOSig natAlgSig)
        (RlmrOOp.dstr j) (fun k => k.elim0))
      = Binding.Tm.op (S := rlmrOSig natAlgSig) (RlmrOOp.dstr j) (fun k => k.elim0) := by
    rw [Binding.sub, Binding.traverse_op]; congr 1; funext k; exact k.elim0
  have heq : appEval (sourceApp (Binding.sub Eσ (Binding.Tm.op (S := rlmrOSig natAlgSig)
        (RlmrOOp.dstr j) (fun k => k.elim0))) G) finZeroElim
      = dstrRead j.val (appEval G finZeroElim) := by
    refine (congrArg (fun t => appEval (sourceApp t G) finZeroElim) hsrc).trans ?_
    rw [sourceApp, appEval_app']
    rfl
  change Relation.ReflTransGen OneLambdaStep
    (OneLambda.app' (Binding.Tm.op (S := oneLambdaSig natAlgSig)
      (OneLambdaOp.dstr j) (fun k => k.elim0)) Ghat)
    (conc (appEval (sourceApp (Binding.sub Eσ (Binding.Tm.op (S := rlmrOSig natAlgSig)
      (RlmrOOp.dstr j) (fun k => k.elim0))) G) finZeroElim))
  rw [heq]
  have hG' : Relation.ReflTransGen OneLambdaStep Ghat (conc (appEval G finZeroElim)) := hG
  refine (OneLambda.reduces_app'_right _ hG').trans ?_
  generalize appEval G finZeroElim = v
  refine PolyFix.ind (P := natAlgSig.polyEndo)
    (motive := fun {_} v => Relation.ReflTransGen OneLambdaStep
      (OneLambda.app' (Binding.Tm.op (S := oneLambdaSig natAlgSig)
        (OneLambdaOp.dstr j) (fun k => k.elim0)) (conc v))
      (conc (dstrRead j.val v)))
    (fun {_} b sub _ => ?_) v
  exact conc_app_dstr_reduces j b sub

/-- The case bar-map at the base object sort `o` is the base case combinator of
`1λ(A)` (Leivant III section 4.2): `barCase o hθ = case`, independent of the
object-sort witness `hθ`. The `θ = o` branch of `barCase`'s shape split; holds
definitionally, since at `o` no push-under-λ intervenes. Novel packaging of
section 4.2. -/
theorem barCase_o {Γ : Binding.Ctx RType} (hθ : RType.o.IsObj) :
    barCase (Γ := Γ) RType.o hθ
      = Binding.Tm.op (S := oneLambdaSig natAlgSig) OneLambdaOp.case (fun k => k.elim0) :=
  rfl

/-- The branch selector `caseSelect` on a constructor node reads the branch at the
scrutinee constructor's enumeration position (Leivant III section 4.1): for
`idx : Fin natAlgSig.numCtors` and a branch family `bs`, `caseSelect (mk (ctorAt
idx) sub) (bs 0) (bs 1) = bs idx`. Over `natAlgSig` the enumeration is zero-first
(`ctorAt 0 = false`, `ctorAt 1 = true`), so `caseSelect (mk b sub)` is `cond b`,
matching the two branch positions. Novel packaging of section 4.1. -/
theorem caseSelect_mk_ctorAt {C : Type} (idx : Fin natAlgSig.numCtors)
    (sub : Fin (natAlgSig.ar (ctorAt idx)) → FreeAlg natAlgSig)
    (bs : Fin natAlgSig.numCtors → C) :
    caseSelect (FreeAlg.mk (ctorAt idx) sub)
        (bs ⟨0, by decide⟩) (bs ⟨1, by decide⟩) = bs idx := by
  obtain ⟨i, hi⟩ := idx
  have hnc : natAlgSig.numCtors = 2 := by decide
  match i, hi with
  | 0, h =>
    change cond (ctorAt (⟨0, h⟩ : Fin natAlgSig.numCtors))
        (bs ⟨1, by decide⟩) (bs ⟨0, by decide⟩) = bs ⟨0, h⟩
    rw [show ctorAt (⟨0, h⟩ : Fin natAlgSig.numCtors) = false from ctorAt_zero]; rfl
  | 1, h =>
    change cond (ctorAt (⟨1, h⟩ : Fin natAlgSig.numCtors))
        (bs ⟨1, by decide⟩) (bs ⟨0, by decide⟩) = bs ⟨1, h⟩
    rw [show ctorAt (⟨1, h⟩ : Fin natAlgSig.numCtors) = true from ctorAt_one]; rfl
  | (n + 2), h => exact absurd (hnc ▸ h) (by omega)

/-- The Berarducci-Böhm representation commutes with the branch selector
`caseSelect` (Leivant III section 4.2): `bbRep (caseSelect z v₀ v₁) σ = caseSelect
z (bbRep v₀ σ) (bbRep v₁ σ)`, since `caseSelect` on a constructor node is a plain
selection of one of `v₀`, `v₁` and `bbRep` distributes through it. The
push-through the case case of Proposition 11's case compatibility consumes at the
higher object type. Novel packaging of section 4.2. -/
theorem bbRep_caseSelect (z v0 v1 : FreeAlg natAlgSig) (σ : RType) :
    bbRep (caseSelect z v0 v1) σ = caseSelect z (bbRep v0 σ) (bbRep v1 σ) := by
  cases z with
  | mk _ b subs => cases b <;> rfl

/-- A singleton abstraction spine is a single abstraction (Leivant III section
4.1, structural): `lamSpine [σ] body = lam' body`, the two interposed casts of
`lamSpine`'s empty-suffix base case cancelling. Internal packaging for
`lamSpine_cons` and the `barCase` saturation keystone. -/
theorem OneLambda.lamSpine_single {A : AlgSig} [Fintype A.B] {Γ : Binding.Ctx RType}
    (σ : RType) {τ : RType} (body : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ) :
    OneLambda.lamSpine [σ] body = OneLambda.lam' body := by
  rw [OneLambda.lamSpine, OneLambda.lamSpine]
  exact congrArg OneLambda.lam' (eq_of_heq ((cast_heq _ _).trans (cast_heq _ _)))

/-- Nesting one outer abstraction over an iterated abstraction merges the two
into a single abstraction spine (Leivant III section 4.1, structural): abstracting
`Δ` and then a single sort `σ` equals abstracting the whole `σ :: Δ`, up to the
reassociation of the abstraction context `(Γ ++ [σ]) ++ Δ = Γ ++ (σ :: Δ)`.
Internal packaging for the `barCase` saturation keystone, folding `barCase`'s
outer `lamSpine [o]` / `lamSpine (replicate …)` into one spine that
`reduces_betaSpine` saturates. -/
theorem OneLambda.lamSpine_cons {A : AlgSig} [Fintype A.B] {Γ : Binding.Ctx RType}
    (σ : RType) (Δ : List RType) {τ : RType}
    (body : Binding.Tm (oneLambdaSig A) ((Γ ++ [σ]) ++ Δ) τ) :
    OneLambda.lamSpine [σ] (OneLambda.lamSpine Δ body)
      = OneLambda.lamSpine (σ :: Δ) ((List.append_assoc Γ [σ] Δ) ▸ body) := by
  rw [OneLambda.lamSpine_single, OneLambda.lamSpine]
  refine congrArg OneLambda.lam' (congrArg (OneLambda.lamSpine Δ) ?_)
  rw [tm_cast_eq_eqRec (List.append_assoc Γ [σ] Δ).symm]
  exact (eqRec_symm_eqRec (motive := fun c => Binding.Tm (oneLambdaSig A) c τ)
    (List.append_assoc Γ [σ] Δ) body).symm

/-- Renaming commutes with a sort transport of a term: for `h : s = s'`,
`ren ρ (cast (congrArg (Tm S Γ) h) t) = cast (congrArg (Tm S Δ) h) (ren ρ t)`,
carrying the sort equality through the renaming unchanged. Proved by `cases h`.
The renaming counterpart of `sub_cast_sort`; internal packaging for the `barCase`
saturation keystone. -/
theorem ren_cast_sort {S : Binding.BinderSig RType} {Γ Δ : Binding.Ctx RType}
    {s s' : RType} (ρ : Binding.Thinning Γ Δ) (h : s = s')
    (t : Binding.Tm S Γ s) :
    Binding.ren ρ (cast (congrArg (Binding.Tm S Γ) h) t)
      = cast (congrArg (Binding.Tm S Δ) h) (Binding.ren ρ t) := by
  cases h; rfl

/-- A `1λ(A)` reduction is carried through a sort transport of its endpoints: for
`h : s = s'`, `X ⇒* Y` gives `cast … X ⇒* cast … Y`, since a sort transport is a
type coercion inert on the reduction relation. Proved by `cases h`. Internal
packaging for the `barCase` saturation keystone, transporting the eta-collapsed
branch across the `curried domains o = barTy θ` reconciliation. -/
theorem reduces_cast_sort {Γ : Binding.Ctx RType} {s s' : RType} (h : s = s')
    {X Y : Binding.Tm (oneLambdaSig natAlgSig) Γ s}
    (hr : Relation.ReflTransGen OneLambdaStep X Y) :
    Relation.ReflTransGen OneLambdaStep
      (cast (congrArg (Binding.Tm (oneLambdaSig natAlgSig) Γ) h) X)
      (cast (congrArg (Binding.Tm (oneLambdaSig natAlgSig) Γ) h) Y) := by
  cases h; exact hr

/-- Reduction of the arguments of a homogeneous application spine lifts to a
reduction of the whole spine: if `args j ⇒* args' j` pointwise then
`replicateSpine n base head args ⇒* replicateSpine n base head args'`. The
homogeneous instance of `OneLambda.reduces_appSpine_args`, transporting the
per-index reduction across the `List.getElem_replicate` sort reindexing through
`reduces_cast_sort`. -/
theorem OneLambda.reduces_replicateSpine_args {Γ : Binding.Ctx RType} {result : RType}
    (n : Nat) (base : RType)
    (head : Binding.Tm (oneLambdaSig natAlgSig) Γ (RType.curried (List.replicate n base) result))
    (args args' : Fin n → Binding.Tm (oneLambdaSig natAlgSig) Γ base)
    (h : ∀ j, Relation.ReflTransGen OneLambdaStep (args j) (args' j)) :
    Relation.ReflTransGen OneLambdaStep
      (OneLambda.replicateSpine n base head args)
      (OneLambda.replicateSpine n base head args') := by
  rw [OneLambda.replicateSpine, OneLambda.replicateSpine]
  refine OneLambda.reduces_appSpine_args (List.replicate n base) head _ _ (fun idx => ?_)
  simp only [eq_mpr_eq_cast, cast_cast]
  have hs : base = (List.replicate n base).get idx := by
    rw [List.get_eq_getElem, List.getElem_replicate]
  exact reduces_cast_sort hs (h (idx.cast List.length_replicate))

/-- Renaming distributes over the iterated application `OneLambda.appSpine`:
`ren ρ (appSpine Ts head args) = appSpine Ts (ren ρ head) (fun i => ren ρ (args
i))`. The renaming counterpart of `OneLambda.sub_appSpine`, by recursion on the
argument-sort list `Ts` peeling one application through `OneLambda.ren_app'`.
Internal packaging for the `barCase` saturation keystone. -/
theorem OneLambda.ren_appSpine {Γ Δ : Binding.Ctx RType} {result : RType}
    (ρ : Binding.Thinning Γ Δ) :
    (Ts : List RType) →
    (head : Binding.Tm (oneLambdaSig natAlgSig) Γ (RType.curried Ts result)) →
    (args : ∀ i : Fin Ts.length, Binding.Tm (oneLambdaSig natAlgSig) Γ (Ts.get i)) →
    Binding.ren ρ (OneLambda.appSpine Ts head args)
      = OneLambda.appSpine Ts (Binding.ren ρ head) (fun i => Binding.ren ρ (args i))
  | [], _head, _args => rfl
  | _T :: Ts', head, args => by
      rw [OneLambda.appSpine, OneLambda.ren_appSpine ρ Ts', OneLambda.ren_app']
      rfl

/-- Heterogeneous congruence of renaming in the sort: renaming through
heterogeneously-equal terms at sorts related by `h : a = b` yields
heterogeneously-equal results. Proved by `cases h` then `eq_of_heq`. The renaming
counterpart of `sub_heq_of_heq`; internal packaging for `ren_replicateSpine`. -/
theorem ren_heq_of_heq {S : Binding.BinderSig RType} {Γ Δ : Binding.Ctx RType}
    {a b : RType} (ρ : Binding.Thinning Γ Δ) (h : a = b)
    {t : Binding.Tm S Γ a} {u : Binding.Tm S Γ b} (ht : HEq t u) :
    HEq (Binding.ren ρ t) (Binding.ren ρ u) := by
  cases h; rw [eq_of_heq ht]

/-- Renaming distributes over the homogeneous iterated application
`OneLambda.replicateSpine`: `ren ρ (replicateSpine n base head args) =
replicateSpine n base (ren ρ head) (fun idx => ren ρ (args idx))`. The homogeneous
instance of `OneLambda.ren_appSpine`, reconciling the per-index `Eq.mpr` sort
transport through `ren_cast_sort`'s heterogeneous analogue. Internal packaging for
the `barCase` saturation keystone. -/
theorem OneLambda.ren_replicateSpine {Γ Δ : Binding.Ctx RType} {result : RType}
    (n : Nat) (base : RType) (ρ : Binding.Thinning Γ Δ)
    (head : Binding.Tm (oneLambdaSig natAlgSig) Γ
      (RType.curried (List.replicate n base) result))
    (args : Fin n → Binding.Tm (oneLambdaSig natAlgSig) Γ base) :
    Binding.ren ρ (OneLambda.replicateSpine n base head args)
      = OneLambda.replicateSpine n base (Binding.ren ρ head)
          (fun idx => Binding.ren ρ (args idx)) := by
  rw [OneLambda.replicateSpine, OneLambda.ren_appSpine, OneLambda.replicateSpine]
  refine congrArg (OneLambda.appSpine (List.replicate n base) (Binding.ren ρ head)) ?_
  funext i
  have hs : (List.replicate n base).get i = base := by
    rw [List.get_eq_getElem, List.getElem_replicate]
  refine eq_of_heq ((ren_heq_of_heq ρ hs
    ((eq_mpr_heq _ _).trans (eq_mpr_heq _ _))).trans
    (HEq.symm ((eq_mpr_heq _ _).trans (eq_mpr_heq _ _))))

/-- Renaming distributes over the concrete term at a constructor node (Leivant
III section 4.2): `ren ρ (conc (mk b sub))` is the constructor constant `con b`
saturated along the homogeneous application spine with the renamed concrete
subterms, `replicateSpine (ar b) o (con b) (fun i => ren ρ (conc (sub i)))`. Since
`conc` is a spine of nullary constructor constants (`conc_mk`), renaming
distributes through the spine (`ren_replicateSpine`) and fixes the nullary `con b`.
The general-context bridge letting the saturated `barCase` fire its `case` redex on
the weakened scrutinee. Novel packaging of section 4.2. -/
theorem ren_conc_mk {Γ : Binding.Ctx RType} (ρ : Binding.Thinning [] Γ)
    (b : natAlgSig.B) (sub : Fin (natAlgSig.ar b) → FreeAlg natAlgSig) :
    Binding.ren ρ (conc (FreeAlg.mk b sub))
      = OneLambda.replicateSpine (natAlgSig.ar b) RType.o
          (Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.con b) (fun k => k.elim0))
          (fun i => Binding.ren ρ (conc (sub i))) := by
  rw [conc_mk, OneLambda.ren_replicateSpine]
  refine congrArg (OneLambda.replicateSpine (natAlgSig.ar b) RType.o · _) ?_
  rw [Binding.ren]
  refine Eq.trans (Binding.traverse_op _ _ _ _) ?_
  refine congrArg (Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.con b)) ?_
  funext k
  exact k.elim0

/-- The base case `1λ(A)` spine over a renamed concrete term of a constructor
node reduces to the selected branch (Leivant III section 4.2, Proposition 11's
case at the higher object type): with the scrutinee `ren ρ (conc (mk (ctorAt idx)
sub))` weakened into an ambient context `Γ`, the case spine reduces
(`OneLambdaStep`, reflexive-transitively) to the branch `branches idx`. The
general-context counterpart of `conc_replicateSpine_case_reduces`, recovering the
constructor-headed spine through `ren_conc_mk` before firing `OneLambdaStep.case`.
Novel packaging of section 4.2. -/
theorem ren_conc_replicateSpine_case_reduces {Γ : Binding.Ctx RType}
    (ρ : Binding.Thinning [] Γ) (idx : Fin natAlgSig.numCtors)
    (sub : Fin (natAlgSig.ar (ctorAt idx)) → FreeAlg natAlgSig)
    (branches : Fin natAlgSig.numCtors → Binding.Tm (oneLambdaSig natAlgSig) Γ RType.o) :
    Relation.ReflTransGen OneLambdaStep
      (OneLambda.replicateSpine natAlgSig.numCtors RType.o
        (OneLambda.app'
          (Binding.Tm.op (S := oneLambdaSig natAlgSig) OneLambdaOp.case (fun k => k.elim0))
          (Binding.ren ρ (conc (FreeAlg.mk (ctorAt idx) sub))))
        branches)
      (branches idx) := by
  rw [ren_conc_mk]
  exact Relation.ReflTransGen.single
    (OneLambdaStep.case idx (fun i => Binding.ren ρ (conc (sub i))) branches)

/-- A `1λ(A)` reduction is carried through a source-context transport of its
endpoints: for `h : Γ = Γ'`, `X ⇒* Y` gives `cast … X ⇒* cast … Y`, since a
context transport is a type coercion inert on the reduction relation. Proved by
`cases h`. The context counterpart of `reduces_cast_sort`; internal packaging for
the multi-binder reduction lift `reduces_lamSpine`. -/
theorem reduces_tm_ctx_cast {Γ Γ' : Binding.Ctx RType} {τ : RType} (h : Γ = Γ')
    {X Y : Binding.Tm (oneLambdaSig natAlgSig) Γ τ}
    (hr : Relation.ReflTransGen OneLambdaStep X Y) :
    Relation.ReflTransGen OneLambdaStep
      (cast (congrArg (fun c => Binding.Tm (oneLambdaSig natAlgSig) c τ) h) X)
      (cast (congrArg (fun c => Binding.Tm (oneLambdaSig natAlgSig) c τ) h) Y) := by
  cases h; exact hr

/-- Reduction under an iterated abstraction spine lifts to the whole spine
(Leivant III section 4.1, structural): if `b ⇒* b'` in `Γ ++ Δ` then
`lamSpine Δ b ⇒* lamSpine Δ b'`. The multi-binder counterpart of
`OneLambda.reduces_lamBody`, by recursion on `Δ` reducing under each peeled `lam'`
(`reduces_lamBody`) and carrying the interposed context reassociation
(`reduces_tm_ctx_cast`). Internal packaging for the `barCase` saturation keystone,
reducing the case redex under `barCase`'s residual domain binders. -/
theorem OneLambda.reduces_lamSpine {Γ : Binding.Ctx RType} :
    (Δ : List RType) → {τ : RType} →
    {b b' : Binding.Tm (oneLambdaSig natAlgSig) (Γ ++ Δ) τ} →
    Relation.ReflTransGen OneLambdaStep b b' →
    Relation.ReflTransGen OneLambdaStep (OneLambda.lamSpine Δ b) (OneLambda.lamSpine Δ b')
  | [], _τ, _b, _b', h => by
      rw [OneLambda.lamSpine, OneLambda.lamSpine]
      exact reduces_tm_ctx_cast (List.append_nil Γ) h
  | σ :: Δ', _τ, _b, _b', h => by
      rw [OneLambda.lamSpine, OneLambda.lamSpine]
      exact OneLambda.reduces_lamBody
        (OneLambda.reduces_lamSpine Δ' (reduces_tm_ctx_cast (List.append_assoc Γ [σ] Δ').symm h))

/-- The reconciliation of the curried branch type of the case bar-map at a shifted
object sort (Leivant III section 4.2): `curried (barTy (Ω τ')).domains o = barTy
(Ω τ')`, since `barTy (Ω τ')` is simple (`barTy_isSimple`) with object target `o`
(`objTarget_of_isSimple`) and equals the currying of its domains over that target
(`curried_domains`). The proof term `barCase` interposes as `cast h_ctd`; named so
the saturation keystone's intermediate bodies can reference it. Internal packaging
for the `barCase` saturation keystone. -/
theorem barCase_omega_ctd (τ' : RType) :
    RType.curried (barTy (RType.omega τ')).domains RType.o = barTy (RType.omega τ') :=
  (congrArg (RType.curried (barTy (RType.omega τ')).domains)
      (RType.objTarget_of_isSimple (barTy (RType.omega τ')) (barTy_isSimple _)).symm).trans
    (RType.curried_domains (barTy (RType.omega τ'))).symm

/-- The inner body of the case bar-map at a shifted object sort `Ω τ'`, after
folding its two outer abstraction spines into a single `lamSpine (o :: replicate
numCtors (barTy (Ω τ')))` (Leivant III section 4.2): the `cast`-reconciled
`lamSpine (barTy (Ω τ')).domains` over the case redex `replicateSpine numCtors o
(case (var a)) (fun j => appSpine domains (cast (var x_j)) yvars)`, in the closed
saturation context `[o, (barTy (Ω τ'))^numCtors]`. The named target of the
saturation keystone's fold step (`barCase_omega_fold`), the operand its
`reduces_betaSpine` instantiation substitutes into. Novel packaging of section
4.2. -/
def barCaseOmegaBodyBig (τ' : RType) :
    Binding.Tm (oneLambdaSig natAlgSig)
      (([] ++ [RType.o]) ++ List.replicate natAlgSig.numCtors (barTy (RType.omega τ')))
      (barTy (RType.omega τ')) :=
  cast (congrArg (Binding.Tm (oneLambdaSig natAlgSig)
      (([] ++ [RType.o]) ++ List.replicate natAlgSig.numCtors (barTy (RType.omega τ'))))
      (barCase_omega_ctd τ'))
    (OneLambda.lamSpine (barTy (RType.omega τ')).domains
      (OneLambda.replicateSpine natAlgSig.numCtors RType.o
        (OneLambda.app'
          (Binding.Tm.op (S := oneLambdaSig natAlgSig) OneLambdaOp.case (fun k => k.elim0))
          (Binding.Tm.var (Binding.Thinning.weakAppend.app (Binding.Thinning.weakAppend.app
            (Binding.Var.appendRight []
              (⟨⟨0, Nat.zero_lt_one⟩, rfl⟩ : Binding.Var [RType.o] RType.o))))))
        (fun j =>
          OneLambda.appSpine (barTy (RType.omega τ')).domains
            (cast (congrArg (Binding.Tm (oneLambdaSig natAlgSig)
                ((([] ++ [RType.o])
                    ++ List.replicate natAlgSig.numCtors (barTy (RType.omega τ')))
                  ++ (barTy (RType.omega τ')).domains)) (barCase_omega_ctd τ').symm)
              (Binding.Tm.var (Binding.Thinning.weakAppend.app
                (Binding.Var.appendRight ([] ++ [RType.o])
                  (⟨⟨j.val, by rw [List.length_replicate]; exact j.isLt⟩,
                    by rw [List.get_eq_getElem, List.getElem_replicate]⟩ :
                      Binding.Var (List.replicate natAlgSig.numCtors (barTy (RType.omega τ')))
                        (barTy (RType.omega τ')))))))
            (fun idx =>
              Binding.Tm.var (Binding.Var.appendRight
                (([] ++ [RType.o])
                  ++ List.replicate natAlgSig.numCtors (barTy (RType.omega τ')))
                (⟨idx, rfl⟩ :
                  Binding.Var (barTy (RType.omega τ')).domains
                    ((barTy (RType.omega τ')).domains.get idx)))))))

/-- The case bar-map at a shifted object sort `Ω τ'` folds into a single
abstraction spine over its saturating context (Leivant III section 4.2):
`barCase (Ω τ') hθ = lamSpine (o :: replicate numCtors (barTy (Ω τ')))
(barCaseOmegaBodyBig τ')`, merging its outer `lamSpine [o]` and `lamSpine
(replicate numCtors (barTy (Ω τ')))` through `lamSpine_cons` (the interposed
context reassociation `append_assoc [] [o] _` is `rfl` in the closed context). The
fold step of the saturation keystone, exposing the single spine that
`reduces_betaSpine` saturates. Novel packaging of section 4.2. -/
theorem barCase_omega_fold (τ' : RType) (hθ : (RType.omega τ').IsObj) :
    barCase (Γ := []) (RType.omega τ') hθ
      = OneLambda.lamSpine (RType.o :: List.replicate natAlgSig.numCtors (barTy (RType.omega τ')))
          (barCaseOmegaBodyBig τ') := by
  unfold barCase
  simp only [RType.shape_omega]
  exact OneLambda.lamSpine_cons RType.o
    (List.replicate natAlgSig.numCtors (barTy (RType.omega τ'))) _

/-- The case bar-map inner body after saturating substitution (Leivant III section
4.2): the result of instantiating `barCaseOmegaBodyBig`'s three outer binders with
a scrutinee `s : o` and branch family `g`, in the closed context. The scrutinee
`s` and each branch `g j` are weakened past the residual `domains` binder
(`ren weakAppend`); the domain variables `y` remain the freshly bound
`Var.appendRight []` positions. The named target of the saturation keystone's
substitution step (`barCase_omega_instantiate`), the operand its `case`-redex and
η-collapse consume. Novel packaging of section 4.2. -/
def barCaseOmegaBodySub (τ' : RType)
    (s : Binding.Tm (oneLambdaSig natAlgSig) [] RType.o)
    (g : Fin natAlgSig.numCtors →
      Binding.Tm (oneLambdaSig natAlgSig) [] (barTy (RType.omega τ'))) :
    Binding.Tm (oneLambdaSig natAlgSig) [] (barTy (RType.omega τ')) :=
  cast (congrArg (Binding.Tm (oneLambdaSig natAlgSig) []) (barCase_omega_ctd τ'))
    (OneLambda.lamSpine (barTy (RType.omega τ')).domains
      (OneLambda.replicateSpine natAlgSig.numCtors RType.o
        (OneLambda.app'
          (Binding.Tm.op (S := oneLambdaSig natAlgSig) OneLambdaOp.case (fun k => k.elim0))
          (Binding.ren
            (Binding.Thinning.weakAppend (Ξ := (barTy (RType.omega τ')).domains)) s))
        (fun j =>
          OneLambda.appSpine (barTy (RType.omega τ')).domains
            (cast (congrArg (Binding.Tm (oneLambdaSig natAlgSig) (barTy (RType.omega τ')).domains)
                (barCase_omega_ctd τ').symm)
              (Binding.ren
                (Binding.Thinning.weakAppend (Ξ := (barTy (RType.omega τ')).domains)) (g j)))
            (fun idx =>
              Binding.Tm.var (Binding.Var.appendRight []
                (⟨idx, rfl⟩ : Binding.Var (barTy (RType.omega τ')).domains
                  ((barTy (RType.omega τ')).domains.get idx)))))))

/-- The saturating substitution of the folded case bar-map body (Leivant III
section 4.2, the substitution step of Proposition 11's case at a shifted object
sort): instantiating `barCaseOmegaBodyBig`'s three outer binders with a scrutinee
`s` and branches `g` yields `barCaseOmegaBodySub τ' s g`, weakening `s` and each
`g j` past the residual domain binder while fixing the domain variables. Proved by
pushing the instantiation through the interposed `cast`, the domain `lamSpine`, the
`replicateSpine`, and the case redex's application spine, resolving each abstracted
variable to its substituted image. Internal packaging for the `barCase` saturation
keystone. -/
theorem barCase_omega_instantiate (τ' : RType)
    (s : Binding.Tm (oneLambdaSig natAlgSig) [] RType.o)
    (g : Fin natAlgSig.numCtors →
      Binding.Tm (oneLambdaSig natAlgSig) [] (barTy (RType.omega τ'))) :
    Binding.instantiate
        (Binding.metaTuple
          (fun i : Fin (RType.o :: List.replicate natAlgSig.numCtors
              (barTy (RType.omega τ'))).length =>
            Fin.cases s
              (fun j => Fin.cases (g ⟨0, by decide⟩)
                (fun k => Fin.cases (g ⟨1, by decide⟩) (fun l => l.elim0) k) j) i))
        (barCaseOmegaBodyBig τ')
      = barCaseOmegaBodySub τ' s g := by
  rw [Binding.instantiate]
  unfold barCaseOmegaBodyBig barCaseOmegaBodySub
  refine (sub_cast_sort _ (barCase_omega_ctd τ') _).trans ?_
  refine congrArg
    (cast (congrArg (Binding.Tm (oneLambdaSig natAlgSig) []) (barCase_omega_ctd τ'))) ?_
  refine (OneLambda.sub_lamSpine (barTy (RType.omega τ')).domains _ _).trans ?_
  refine congrArg (OneLambda.lamSpine (barTy (RType.omega τ')).domains) ?_
  refine (OneLambda.sub_replicateSpine _ _ _ _ _).trans ?_
  congr 1
  · refine (OneLambda.sub_app' _ _ _).trans ?_
    refine congr (congrArg OneLambda.app' (OneLambda.sub_caseOp _)) ?_
    exact sub_underBinder_weakAppend _ _
  · funext j
    refine (OneLambda.sub_appSpine _ _ _ _).trans ?_
    congr 1
    · refine (sub_cast_sort _ (barCase_omega_ctd τ').symm _).trans ?_
      refine congrArg (cast (congrArg (Binding.Tm (oneLambdaSig natAlgSig)
        (barTy (RType.omega τ')).domains) (barCase_omega_ctd τ').symm)) ?_
      refine (sub_underBinder_weakAppend _ _).trans ?_
      refine congrArg (Binding.ren Binding.Thinning.weakAppend) ?_
      obtain ⟨i, hi⟩ := j
      match i, hi with
      | 0, _ => rfl
      | 1, _ => rfl
      | (n + 2), h => exact absurd h (by have : natAlgSig.numCtors = 2 := rfl; omega)

/-- The case bar-map saturation keystone (Leivant III section 4.2, Proposition
11's case at a shifted object sort `Ω τ'`): applying `barCase (Ω τ')` to a
scrutinee `Ghat0` and the `numCtors` branch representatives `Ghats` along the
application spine reduces (`OneLambdaStep`, reflexive-transitively) to the branch
`Ghats idx` selected by the scrutinee's constructor, given that `Ghat0` reduces to
the concrete term of `mk (ctorAt idx) subv`. Folds the two outer abstraction spines
into one (`barCase_omega_fold`), saturates them by the generic λ-spine β-reduction
(`reduces_betaSpine`), simplifies the substituted body (`barCase_omega_instantiate`),
fires the case redex on the weakened scrutinee under the residual domain binders
(`reduces_lamSpine`, `ren_conc_replicateSpine_case_reduces`), and η-collapses the
selected branch (`reduces_etaSpine`), transporting across the branch-type
reconciliation cast (`reduces_cast_sort`). Novel packaging of section 4.2. -/
theorem barCase_appSpine_reduces (τ' : RType) (hθ : (RType.omega τ').IsObj)
    (idx : Fin natAlgSig.numCtors)
    (subv : Fin (natAlgSig.ar (ctorAt idx)) → FreeAlg natAlgSig)
    (Ghat0 : Binding.Tm (oneLambdaSig natAlgSig) [] RType.o)
    (Ghats : Fin natAlgSig.numCtors →
      Binding.Tm (oneLambdaSig natAlgSig) [] (barTy (RType.omega τ')))
    (h0 : Relation.ReflTransGen OneLambdaStep Ghat0
      (conc (FreeAlg.mk (ctorAt idx) subv))) :
    Relation.ReflTransGen OneLambdaStep
      (OneLambda.app'
        (OneLambda.app' (OneLambda.app' (barCase (Γ := []) (RType.omega τ') hθ) Ghat0)
          (Ghats ⟨0, by decide⟩))
        (Ghats ⟨1, by decide⟩))
      (Ghats idx) := by
  refine (OneLambda.reduces_app'_left _ (OneLambda.reduces_app'_left _
    (OneLambda.reduces_app'_right _ h0))).trans ?_
  rw [barCase_omega_fold]
  have happ : OneLambda.app'
      (OneLambda.app' (OneLambda.app'
        (OneLambda.lamSpine (RType.o :: List.replicate natAlgSig.numCtors (barTy (RType.omega τ')))
          (barCaseOmegaBodyBig τ')) (conc (FreeAlg.mk (ctorAt idx) subv)))
        (Ghats ⟨0, by decide⟩))
      (Ghats ⟨1, by decide⟩)
    = OneLambda.appSpine (RType.o :: List.replicate natAlgSig.numCtors (barTy (RType.omega τ')))
        (OneLambda.lamSpine (RType.o :: List.replicate natAlgSig.numCtors (barTy (RType.omega τ')))
          (barCaseOmegaBodyBig τ'))
        (fun i => Fin.cases (conc (FreeAlg.mk (ctorAt idx) subv))
          (fun j => Fin.cases (Ghats ⟨0, by decide⟩)
            (fun k => Fin.cases (Ghats ⟨1, by decide⟩) (fun l => l.elim0) k) j) i) := rfl
  rw [happ]
  have hbeta := OneLambda.reduces_betaSpine
    (RType.o :: List.replicate natAlgSig.numCtors (barTy (RType.omega τ')))
    (barCaseOmegaBodyBig τ')
    (fun i => Fin.cases (conc (FreeAlg.mk (ctorAt idx) subv))
      (fun j => Fin.cases (Ghats ⟨0, by decide⟩)
        (fun k => Fin.cases (Ghats ⟨1, by decide⟩) (fun l => l.elim0) k) j) i)
  refine hbeta.trans ?_
  rw [barCase_omega_instantiate]
  unfold barCaseOmegaBodySub
  have hgi : cast (congrArg (Binding.Tm (oneLambdaSig natAlgSig) []) (barCase_omega_ctd τ'))
      (cast (congrArg (Binding.Tm (oneLambdaSig natAlgSig) []) (barCase_omega_ctd τ').symm)
        (Ghats idx)) = Ghats idx :=
    eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))
  refine hgi ▸ ?_
  refine reduces_cast_sort (barCase_omega_ctd τ') ?_
  refine (OneLambda.reduces_lamSpine (barTy (RType.omega τ')).domains
    (ren_conc_replicateSpine_case_reduces Binding.Thinning.weakAppend idx subv _)).trans ?_
  have hhead : cast (congrArg (Binding.Tm (oneLambdaSig natAlgSig)
        (barTy (RType.omega τ')).domains) (barCase_omega_ctd τ').symm)
        (Binding.ren Binding.Thinning.weakAppend (Ghats idx))
      = Binding.ren Binding.Thinning.weakAppend
          (cast (congrArg (Binding.Tm (oneLambdaSig natAlgSig) []) (barCase_omega_ctd τ').symm)
            (Ghats idx)) :=
    (ren_cast_sort Binding.Thinning.weakAppend (barCase_omega_ctd τ').symm (Ghats idx)).symm
  exact hhead ▸ OneLambda.reduces_etaSpine (barTy (RType.omega τ')).domains
    (cast (congrArg (Binding.Tm (oneLambdaSig natAlgSig) []) (barCase_omega_ctd τ').symm)
      (Ghats idx))

/-- Re-labelling a free-algebra node along a constructor equality (Leivant III
section 4.1, structural): for `h : b = c`, `FreeAlg.mk b s = FreeAlg.mk c (h ▸ s)`,
transporting the subterm family across the arity change. Proved by `cases h`.
Internal packaging for `represents_case`, expressing a scrutinee constructor as the
enumerated `ctorAt idx`. -/
theorem freeAlg_mk_transport {b c : natAlgSig.B} (h : b = c)
    (s : Fin (natAlgSig.ar b) → FreeAlg natAlgSig) :
    FreeAlg.mk b s = FreeAlg.mk c (h ▸ s) := by cases h; rfl

/-- Compatibility of the representation relation with a case constant (Leivant III
section 4.2, Proposition 11's case case, a decision-2 denotational reformulation):
the case node `case θ hθ` is represented by the parallel target substitution into
its bar image `barCase θ hθ` of `1λ(A)`. The nullary node is fixed on the source
side (`sub` over `elim0`) and mapped to the case bar-map on the target side
(`barTmOp_case`, whose branch-type transport vanishes at the concrete `numCtors`,
then `sub_barCase`). Peeling the scrutinee and two branches with `represents_arrow`
exposes a `caseSelect` on the represented arguments (`appEval_caseRedex`); casing
the scrutinee's value on its top constructor (`ctorAt`) selects a branch through
`caseSelect_mk_ctorAt`, matched on the target side by the base case reduction
(`conc_replicateSpine_case_reduces`) at the base object sort `o` and the saturation
keystone (`barCase_appSpine_reduces`) at a shifted object sort `Ω τ'`, both closed
under `lemma8` against the branch representatives' self-representation (`lemma9_o`,
`lemma9_omega`). -/
theorem represents_case {Γ : Binding.Ctx RType} (θ : RType) (hθ : θ.IsObj)
    (Eσ : Binding.Env (Binding.Tm (rlmrOSig natAlgSig)) Γ [])
    (Eσhat : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) (Γ.map barTy) []) :
    Represents (RType.arrow RType.o (RType.curried (List.replicate natAlgSig.numCtors θ) θ))
      (Binding.sub Eσ (Binding.Tm.op (S := rlmrOSig natAlgSig)
        (RlmrOOp.case θ hθ) (fun k => k.elim0)))
      (Binding.sub Eσhat (barTm (Binding.Tm.op (S := rlmrOSig natAlgSig)
        (RlmrOOp.case θ hθ) (fun k => k.elim0)))) := by
  have hsrc : Binding.sub Eσ (Binding.Tm.op (S := rlmrOSig natAlgSig)
        (RlmrOOp.case θ hθ) (fun k => k.elim0))
      = Binding.Tm.op (S := rlmrOSig natAlgSig) (RlmrOOp.case θ hθ) (fun k => k.elim0) := by
    rw [Binding.sub, Binding.traverse_op]; congr 1; funext k; exact k.elim0
  have htgt : Binding.sub Eσhat (barTm (Binding.Tm.op (S := rlmrOSig natAlgSig)
        (RlmrOOp.case θ hθ) (fun k => k.elim0)))
      = barCase (Γ := []) θ hθ := by
    rw [barTm_op, barTmOp_case θ hθ _ rfl]
    change Binding.sub Eσhat (barCase (Γ := Γ.map barTy) θ hθ) = barCase (Γ := []) θ hθ
    exact OneLambda.sub_barCase θ hθ Eσhat
  refine htgt ▸ ?_
  rw [represents_arrow]
  intro G Ghat0 hG0
  change Represents (RType.arrow θ (RType.arrow θ θ))
    (sourceApp (Binding.sub Eσ (Binding.Tm.op (S := rlmrOSig natAlgSig)
      (RlmrOOp.case θ hθ) (fun k => k.elim0))) G)
    (OneLambda.app' (barCase (Γ := []) θ hθ) Ghat0)
  rw [represents_arrow]
  intro Gb0 Ghatb0 hGb0
  rw [represents_arrow]
  intro Gb1 Ghatb1 hGb1
  have hsem : appEval (sourceApp (sourceApp (sourceApp (Binding.sub Eσ
        (Binding.Tm.op (S := rlmrOSig natAlgSig) (RlmrOOp.case θ hθ) (fun k => k.elim0)))
        G) Gb0) Gb1) finZeroElim
      = caseSelect (appEval G finZeroElim)
          (appEval Gb0 finZeroElim) (appEval Gb1 finZeroElim) := by
    refine (congrArg (fun t => appEval
      (sourceApp (sourceApp (sourceApp t G) Gb0) Gb1) finZeroElim) hsrc).trans ?_
    exact appEval_caseRedex (θ := θ) hθ G
      (fun j => Fin.cases Gb0 (fun k => Fin.cases Gb1 (fun l => l.elim0) k) j) finZeroElim
  -- Express the scrutinee value as an enumerated constructor node.
  obtain ⟨idx, subv, hmk⟩ : ∃ (idx : Fin natAlgSig.numCtors)
      (subv : Fin (natAlgSig.ar (ctorAt idx)) → FreeAlg natAlgSig),
      appEval G finZeroElim = FreeAlg.mk (ctorAt idx) subv := by
    obtain ⟨b, subb, hv0⟩ : ∃ b subb, appEval G finZeroElim = FreeAlg.mk b subb :=
      PolyFix.ind (P := natAlgSig.polyEndo)
        (motive := fun {_} v => ∃ b subb, v = FreeAlg.mk b subb)
        (fun {_} b subb _ => ⟨b, subb, rfl⟩) (appEval G finZeroElim)
    cases b with
    | false => exact ⟨⟨0, by decide⟩, ctorAt_zero.symm ▸ subb,
        hv0.trans (freeAlg_mk_transport ctorAt_zero.symm subb)⟩
    | true => exact ⟨⟨1, by decide⟩, ctorAt_one.symm ▸ subb,
        hv0.trans (freeAlg_mk_transport ctorAt_one.symm subb)⟩
  rw [hmk] at hsem
  have hG0' : Relation.ReflTransGen OneLambdaStep Ghat0
      (conc (FreeAlg.mk (ctorAt idx) subv)) := hmk ▸ hG0
  -- Branch families over the enumeration, and the pointwise representation.
  set Ghatbt : Fin natAlgSig.numCtors →
      Binding.Tm (oneLambdaSig natAlgSig) [] (barTy θ) :=
    fun i => Fin.cases Ghatb0 (fun k => Fin.cases Ghatb1 (fun l => l.elim0) k) i with hGhatbt
  set Gbt : Fin natAlgSig.numCtors → Binding.Tm (rlmrOSig natAlgSig) [] θ :=
    fun i => Fin.cases Gb0 (fun k => Fin.cases Gb1 (fun l => l.elim0) k) i with hGbt
  have hGbtRep : ∀ i : Fin natAlgSig.numCtors, Represents θ (Gbt i) (Ghatbt i) := by
    intro i
    obtain ⟨iv, hiv⟩ := i
    match iv, hiv with
    | 0, _ => exact hGb0
    | 1, _ => exact hGb1
    | (n + 2), h => exact absurd h (by have : natAlgSig.numCtors = 2 := rfl; omega)
  have hae : appEval (sourceApp (sourceApp (sourceApp (Binding.sub Eσ
        (Binding.Tm.op (S := rlmrOSig natAlgSig) (RlmrOOp.case θ hθ) (fun k => k.elim0)))
        G) Gb0) Gb1) finZeroElim
      = appEval (Gbt idx) finZeroElim :=
    hsem.trans (caseSelect_mk_ctorAt idx subv (fun i => appEval (Gbt i) finZeroElim))
  cases hs : θ.shape with
  | o =>
    obtain rfl : θ = RType.o := RType.eq_o_of_shape_o hs
    have htargetred : Relation.ReflTransGen OneLambdaStep
        (OneLambda.app' (OneLambda.app' (OneLambda.app' (barCase (Γ := []) RType.o hθ) Ghat0)
          Ghatb0) Ghatb1) (Ghatbt idx) := by
      rw [barCase_o]
      refine (OneLambda.reduces_app'_left _ (OneLambda.reduces_app'_left _
        (OneLambda.reduces_app'_right _ hG0'))).trans ?_
      exact conc_replicateSpine_case_reduces idx subv Ghatbt
    exact lemma8 (lemma9_o _)
      (htargetred.trans ((congrArg conc hae).symm ▸
        (hGbtRep idx : Relation.ReflTransGen OneLambdaStep (Ghatbt idx)
          (conc (appEval (Gbt idx) finZeroElim)))))
  | arrow => exact absurd hθ (by unfold RType.IsObj; rw [hs]; decide)
  | omega =>
    obtain ⟨τ', rfl⟩ : ∃ τ', θ = RType.omega τ' :=
      ⟨θ.omegaArg, RType.eq_omega_omegaArg_of_shape hs⟩
    have htargetred : Relation.ReflTransGen OneLambdaStep
        (OneLambda.app' (OneLambda.app' (OneLambda.app'
          (barCase (Γ := []) (RType.omega τ') hθ) Ghat0) Ghatb0) Ghatb1) (Ghatbt idx) :=
      barCase_appSpine_reduces τ' hθ idx subv Ghat0 Ghatbt hG0'
    exact lemma8 (lemma9_omega τ' _)
      (htargetred.trans ((congrArg (fun v => bbRep v (barTy τ')) hae).symm ▸
        (hGbtRep idx : Relation.ReflTransGen OneLambdaStep (Ghatbt idx)
          (bbRep (appEval (Gbt idx) finZeroElim) (barTy τ')))))

/-- The abstraction body of the constructor bar-map `barConOmega` at the unary
constructor `true` in the closed ambient context (Leivant III section 4.2):
`λ c⃗. c_true (x c⃗)` as a term of the singleton saturation context
`[] ++ [Ω̄τ]`, whose sole outer binder `x` stands for the constructor's
Berarducci-Böhm argument. The named target of the saturation keystone's fold
step (`barConOmega_true_fold`), the operand its `reduces_beta` instantiation
substitutes into. Novel packaging of section 4.2. -/
def barConOmegaBody (τ : RType) :
    Binding.Tm (oneLambdaSig natAlgSig) ([] ++ [bbType natAlgSig (barTy τ)])
      (bbType natAlgSig (barTy τ)) :=
  OneLambda.lamSpine (stepTypes natAlgSig (barTy τ) (barTy τ))
    (OneLambda.replicateSpine (natAlgSig.ar true) (barTy τ)
      (Binding.Tm.var (Binding.Var.appendRight
        ([] ++ List.replicate (natAlgSig.ar true) (bbType natAlgSig (barTy τ)))
        (ctorVar true)))
      (fun j =>
        OneLambda.appSpine (stepTypes natAlgSig (barTy τ) (barTy τ))
          (Binding.Tm.var (Binding.Thinning.weakAppend.app
            (Binding.Var.appendRight []
              (⟨⟨j.val, by rw [List.length_replicate]; exact j.isLt⟩,
                by rw [List.get_eq_getElem, List.getElem_replicate]⟩ :
                  Binding.Var (List.replicate (natAlgSig.ar true) (bbType natAlgSig (barTy τ)))
                    (bbType natAlgSig (barTy τ))))))
          (fun idx =>
            Binding.Tm.var (Binding.Var.appendRight
              ([] ++ List.replicate (natAlgSig.ar true) (bbType natAlgSig (barTy τ)))
              ⟨idx, rfl⟩))))

/-- The constructor bar-map at the unary constructor `true` in the closed ambient
context folds into a single abstraction over its named body (Leivant III section
4.2): `barConOmega true τ = lam' (barConOmegaBody τ)`, the outer argument spine
`lamSpine (replicate 1 Ω̄τ)` collapsing to one `lam'` in the closed context, where
the interposed empty-suffix and reassociation transports reduce by definitional
proof irrelevance. The fold step of the `barConOmega` saturation keystone,
exposing the single binder that `reduces_beta` saturates. Novel packaging of
section 4.2. -/
theorem barConOmega_true_fold (τ : RType) :
    barConOmega (Γ := []) true τ = OneLambda.lam' (barConOmegaBody τ) := rfl

end GebLean.Ramified
