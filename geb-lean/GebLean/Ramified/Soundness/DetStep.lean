import GebLean.Ramified.Soundness.Normalization

/-!
# Ramified recurrence: the deterministic normalization step

A total computable one-step reducer `detStep` on the terms of the simply-typed
calculus `1λ(A)` (Leivant III section 4.2, p. 224), realizing the reduction
strategy behind Lemma 12's normalization bound (section 5, proof paragraphs (ii)
and (iii), p. 226) as a stateless function rather than an existential relation.

`detStep t` recomputes its dispatch at every call (plan decision P2): it reads
`q := betaRedexRank t`; if `q > 0` it applies the β worker `detStepAt q`, which
performs child-priority innermost descent contracting a rank-`q` β-redex; else
if `hasIota t` it applies the ι worker `detIotaStep`, which descends by
child-priority to the first ι-redex and contracts it (the `dstrHit`/`dstrMiss`/
`case` reduct of `OneLambdaStep`); else `t` is normal and is returned unchanged.

Both workers are `PolyFix.ind` folds following the measure-fold house pattern of
`Tm.size`/`Tm.height` and the detector layer of `Normalization.lean`. The β
contraction reads the applied abstraction's body through `appReduct`; the ι
contraction reads the destructor- or case-redex off the application spine through
`collectSpine`, `dstrReduct`, and `caseReduct`. All definitions are generic in
`A` with the `[Fintype A.B] [LinearOrder A.B]` ambient (spec D6).

## Main definitions

* `OneLambda.appReduct` — the β-contraction top-read: `appReduct (lam' b) x`
  contracts to `instantiate₁ x b`, and is the identity application `app' f x`
  when `f` is not an abstraction.
* `OneLambda.detStepAt` — the β worker: child-priority descent contracting an
  innermost rank-`q` β-redex; the identity when no rank-`q` redex remains.
* `OneLambda.collectSpine` — the application-spine decomposition of an object-sort
  term into its head operation and its sort-`o` argument list.
* `OneLambda.iotaContract` — the ι-contraction: the `dstr`/`case` reduct at a
  saturated ι-redex; the identity otherwise.
* `OneLambda.detIotaStep` — the ι worker: child-priority descent contracting the
  first ι-redex.
* `OneLambda.detStep` — the deterministic step (plan decision P2).
* `OneLambda.detIter` — the `n`-fold iteration of the deterministic step (plan
  decision P6).

## Main statements

* `OneLambda.detStepAt_var`, `OneLambda.detStepAt_app'`,
  `OneLambda.detStepAt_lam'` — the β-worker node equations, covering the three
  guard regimes (first qualifying child, root contraction, identity).
* `OneLambda.detIotaStep_var`, `OneLambda.detIotaStep_app'`,
  `OneLambda.detIotaStep_lam'` — the ι-worker node equations in the same shape.
* `OneLambda.appReduct_lam'` — the β-contraction node equation.
* `OneLambda.detStep_eq` — the dispatch unfolding of `detStep`.
* `OneLambda.detStep_normal` — `detStep` is the identity on `Normal` terms.
* `OneLambda.detStepAt_sound` — the β worker performs one genuine `OneLambdaStep`
  at every term of positive β-rank `q`.
* `OneLambda.detIotaStep_sound` — the ι worker performs one genuine
  `OneLambdaStep` at every term carrying an ι-redex.
* `OneLambda.detStep_sound` — the deterministic step performs one genuine
  `OneLambdaStep` at every non-`Normal` term.
* `OneLambda.iotaContract_cases_of_topIota` — the shape-and-value inversion of
  the ι-contraction at a saturated ι-redex: the destructor or case redex shape
  together with the selected reduct.
* `OneLambda.detIter_reduces` — the deterministic iteration is a reduction
  sequence under `Relation.ReflTransGen OneLambdaStep`.
* `OneLambda.detIter_normal_stable` — a `Normal` term is a fixpoint of the
  deterministic iteration.
* `OneLambda.det_cycle` — one deterministic rank-elimination cycle: at most
  `Tm.size t` iterations reach a term of β-rank below `q`, with `beta_cycle`'s
  height bound and shape invariant.
* `OneLambda.detIter_normal` — the deterministic Lemma 12 clock: iterating the
  deterministic step `(redexRank t + 1) * tower (redexRank t + 1) (Tm.height t)`
  times reaches a `Normal` term.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`, section 4.2 (p. 224): the
redexes of `1λ(A)`, their ranks, and normality; section 5, proof paragraphs (ii)
and (iii) (p. 226) with footnote 10: the reduction strategy of Lemma 12 whose
computable realization is this step. Novel realization.

## Tags

ramified recurrence, normalization, reduction strategy, beta reduction,
iota reduction, simply-typed lambda calculus
-/

namespace GebLean.Ramified

open GebLean.Binding

namespace OneLambda

variable {A : AlgSig} [Fintype A.B]

/-- Operation dispatch of the β-contraction top-read: at a `lam σ' τ'` head the
node is the applied abstraction `lam' b`, contracted to `instantiate₁ x b` (the
argument sorts identified through the arrow-sort equality `heq`); at every other
head the node is not an abstraction, so the result is the un-contracted
application `app' (Tm.op o children) x`. -/
def appReductOp {Γ : Binding.Ctx RType} {σ τ : RType} (o : OneLambdaOp A)
    (children : ∀ j : Fin ((oneLambdaSig A).args o).length,
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args o).get j).1)
        (((oneLambdaSig A).args o).get j).2)
    (heq : (oneLambdaSig A).result o = RType.arrow σ τ)
    (x : Binding.Tm (oneLambdaSig A) Γ σ) : Binding.Tm (oneLambdaSig A) Γ τ :=
  match o, children, heq with
  | OneLambdaOp.lam σ' τ', children, heq =>
      Binding.instantiate₁ x
        (cast (congrArg (fun p : RType × RType =>
            Binding.Tm (oneLambdaSig A) (Γ ++ [p.1]) p.2)
          (show (σ', τ') = (σ, τ) from by
            obtain ⟨hσ, hτ⟩ : σ' = σ ∧ τ' = τ := by simpa [oneLambdaSig] using heq
            subst hσ; subst hτ; rfl))
          (children ⟨0, Nat.zero_lt_one⟩))
  | o, children, heq =>
      OneLambda.app'
        (cast (congrArg (fun s => Binding.Tm (oneLambdaSig A) Γ s) heq)
          (Binding.Tm.op (S := oneLambdaSig A) o children :
            Binding.Tm (oneLambdaSig A) Γ ((oneLambdaSig A).result o))) x

/-- The β-contraction top-read (Leivant III section 4.2, p. 223): if `f` is an
abstraction `lam' b`, contract the β-redex `app' f x` to `instantiate₁ x b`;
otherwise return the un-contracted application `app' f x`. A non-recursive read
of the head of `f` by `PolyFix.ind` through `appReductOp`, following the
operation-directed dispatch of `headTag`. Novel realization. -/
def appReduct {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) : Binding.Tm (oneLambdaSig A) Γ τ :=
  PolyFix.ind (P := polyTranslate Binding.varOver (oneLambdaSig A).polyEndo)
    (motive := fun {y} _ =>
      y.2 = RType.arrow σ τ → Binding.Tm (oneLambdaSig A) y.1 σ →
        Binding.Tm (oneLambdaSig A) y.1 τ)
    (fun {_y} i children _ih =>
      match i, children with
      | Sum.inl a, _ => fun heq xx =>
          OneLambda.app' (heq ▸ Binding.Tm.var (leafVar a)) xx
      | Sum.inr p, children => fun heq xx =>
          appReductOp p.val (fun j => children ⟨j⟩) (p.2.trans heq) xx) f rfl x

/-- `appReduct` at an abstraction node contracts the β-redex: `appReduct (lam' b)
x = instantiate₁ x b`. -/
@[simp]
theorem appReduct_lam' {Γ : Binding.Ctx RType} {σ τ : RType}
    (b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ)
    (x : Binding.Tm (oneLambdaSig A) Γ σ) :
    appReduct (OneLambda.lam' b) x = Binding.instantiate₁ x b := rfl

/-- Transport a subterm out of the `Γ ++ [] = Γ` argument context that `app'`
imposes on its function and argument subterms, so a `PolyFix.ind` fold can hand
its children back to the `app'`/`lam'` combinators at the ambient context. -/
def toG {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) (Γ ++ []) s) : Binding.Tm (oneLambdaSig A) Γ s :=
  (List.append_nil Γ) ▸ t

/-- `toG` cancels the inverse `Γ = Γ ++ []` transport that `app'` applies to its
subterms: `toG ((List.append_nil Γ).symm ▸ t) = t`. -/
@[simp]
theorem toG_symm {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) : toG ((List.append_nil Γ).symm ▸ t) = t := by
  rw [toG]; simp only [eqRec_eq_cast, cast_cast, cast_eq]

/-- Operation dispatch of the β worker `detStepAt q` at an operation node
(Leivant III section 4.2, p. 224). At an application node `app' f x`: descend into
the first child whose β-rank equals `q` (function first, then argument), lifting
the recursive image `ih` through the congruence; if neither child qualifies and
the node is a rank-`q` root β-redex (`isLam f` with arrow order `q`), contract it
with `appReduct`; otherwise the identity. At an abstraction node `lam' b`: descend
into the body when it carries a rank-`q` redex, else the identity (an abstraction
head contributes no root β-rank). At every other operation node (the nullary
constants): the identity. -/
def detStepAtOp (q : ℕ) {Γ : Binding.Ctx RType} (o : OneLambdaOp A)
    (children : ∀ j : Fin ((oneLambdaSig A).args o).length,
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args o).get j).1)
        (((oneLambdaSig A).args o).get j).2)
    (ih : ∀ j : Fin ((oneLambdaSig A).args o).length,
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args o).get j).1)
        (((oneLambdaSig A).args o).get j).2) :
    Binding.Tm (oneLambdaSig A) Γ ((oneLambdaSig A).result o) :=
  match o, children, ih with
  | OneLambdaOp.app σ τ, children, ih =>
      let f := toG (children ⟨0, Nat.zero_lt_two⟩)
      let x := toG (children ⟨1, Nat.one_lt_two⟩)
      let f' := toG (ih ⟨0, Nat.zero_lt_two⟩)
      let x' := toG (ih ⟨1, Nat.one_lt_two⟩)
      if betaRedexRank f = q then OneLambda.app' f' x
      else if betaRedexRank x = q then OneLambda.app' f x'
      else if isLam f = true ∧ RType.ord (RType.arrow σ τ) = q then appReduct f x
      else OneLambda.app' f x
  | OneLambdaOp.lam _ _, children, ih =>
      let b := children ⟨0, Nat.zero_lt_one⟩
      let b' := ih ⟨0, Nat.zero_lt_one⟩
      if betaRedexRank b = q then OneLambda.lam' b'
      else OneLambda.lam' b
  | o, children, _ih => Binding.Tm.op (S := oneLambdaSig A) o children

/-- The β worker (Leivant III section 4.2, p. 224; spec §4.1): child-priority
innermost descent contracting an innermost rank-`q` β-redex, the identity when no
rank-`q` redex remains. A structure-preserving `PolyFix.ind` fold dispatching
through `detStepAtOp`, following the measure-fold house pattern of `Tm.size`. -/
def detStepAt (q : ℕ) {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) : Binding.Tm (oneLambdaSig A) Γ s :=
  PolyFix.ind (P := polyTranslate Binding.varOver (oneLambdaSig A).polyEndo)
    (motive := fun {y} _ => Binding.Tm (oneLambdaSig A) y.1 y.2)
    (fun {x} i children ih =>
      match i, children, ih with
      | Sum.inl a, _, _ => Binding.Tm.var (leafVar a)
      | Sum.inr p, children, ih =>
        cast (congrArg (fun s => Binding.Tm (oneLambdaSig A) x.1 s) p.2)
          (detStepAtOp q p.val (fun j => children ⟨j⟩) (fun j => ih ⟨j⟩))) t

/-- `detStepAt` at an operation node dispatches through `detStepAtOp` on the
worker images of its subterms. -/
theorem detStepAt_op (q : ℕ) {Γ : Binding.Ctx RType} (o : OneLambdaOp A)
    (args : ∀ j : Fin ((oneLambdaSig A).args o).length,
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args o).get j).1)
        (((oneLambdaSig A).args o).get j).2) :
    detStepAt q (Binding.Tm.op o args)
      = detStepAtOp q o args (fun j => detStepAt q (args j)) := rfl

/-- `detStepAt` is the identity at a variable (no redex to contract). -/
@[simp]
theorem detStepAt_var (q : ℕ) {Γ : Binding.Ctx RType} {s : RType}
    (x : Binding.Var Γ s) :
    detStepAt q (Binding.Tm.var x : Binding.Tm (oneLambdaSig A) Γ s)
      = Binding.Tm.var x := by
  obtain ⟨i, hi⟩ := x; subst hi; rfl

/-- `detStepAt` is invariant under transport of the context and sort indices. -/
theorem detStepAt_cast (q : ℕ) {Γ Γ' : Binding.Ctx RType} {s s' : RType}
    (hΓ : Γ = Γ') (hs : s = s') (t : Binding.Tm (oneLambdaSig A) Γ s) :
    detStepAt q (hs ▸ hΓ ▸ t) = hs ▸ hΓ ▸ detStepAt q t := by
  subst hΓ; subst hs; rfl

/-- `detStepAt` commutes with the `Γ ++ [] = Γ` transport that `app'` applies to
its subterms. -/
private theorem detStepAt_appendNil (q : ℕ) {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) (Γ ++ []) s) :
    detStepAt q (toG t) = toG (detStepAt q t) :=
  detStepAt_cast q (List.append_nil Γ) rfl t

/-- `detStepAt` at an application node in the three guard regimes: descend into
the function subterm when it carries a rank-`q` redex; else descend into the
argument subterm when it does; else contract the root β-redex to `appReduct f x`
when the node is a rank-`q` β-redex; else the identity. -/
theorem detStepAt_app' (q : ℕ) {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) :
    detStepAt q (OneLambda.app' f x)
      = (if betaRedexRank f = q then OneLambda.app' (detStepAt q f) x
         else if betaRedexRank x = q then OneLambda.app' f (detStepAt q x)
         else if isLam f = true ∧ RType.ord (RType.arrow σ τ) = q then appReduct f x
         else OneLambda.app' f x) := by
  have e : detStepAt q (OneLambda.app' f x)
      = detStepAtOp q (OneLambdaOp.app σ τ)
          (fun j => Fin.cases ((List.append_nil Γ).symm ▸ f)
            (fun k => Fin.cases ((List.append_nil Γ).symm ▸ x) (fun l => l.elim0) k) j)
          (fun j => detStepAt q (Fin.cases ((List.append_nil Γ).symm ▸ f)
            (fun k => Fin.cases ((List.append_nil Γ).symm ▸ x) (fun l => l.elim0) k) j)) := rfl
  rw [e]
  change (if betaRedexRank (toG ((List.append_nil Γ).symm ▸ f)) = q
        then OneLambda.app' (toG (detStepAt q ((List.append_nil Γ).symm ▸ f)))
          (toG ((List.append_nil Γ).symm ▸ x))
        else if betaRedexRank (toG ((List.append_nil Γ).symm ▸ x)) = q
        then OneLambda.app' (toG ((List.append_nil Γ).symm ▸ f))
          (toG (detStepAt q ((List.append_nil Γ).symm ▸ x)))
        else if isLam (toG ((List.append_nil Γ).symm ▸ f)) = true
            ∧ RType.ord (RType.arrow σ τ) = q
        then appReduct (toG ((List.append_nil Γ).symm ▸ f)) (toG ((List.append_nil Γ).symm ▸ x))
        else OneLambda.app' (toG ((List.append_nil Γ).symm ▸ f))
          (toG ((List.append_nil Γ).symm ▸ x))) = _
  have hdf : toG (detStepAt q ((List.append_nil Γ).symm ▸ f)) = detStepAt q f := by
    rw [← detStepAt_appendNil, toG_symm]
  have hdx : toG (detStepAt q ((List.append_nil Γ).symm ▸ x)) = detStepAt q x := by
    rw [← detStepAt_appendNil, toG_symm]
  rw [toG_symm, toG_symm, hdf, hdx]

/-- `detStepAt` at an abstraction node descends into the body when it carries a
rank-`q` redex, and is the identity otherwise. -/
theorem detStepAt_lam' (q : ℕ) {Γ : Binding.Ctx RType} {σ τ : RType}
    (b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ) :
    detStepAt q (OneLambda.lam' b)
      = (if betaRedexRank b = q then OneLambda.lam' (detStepAt q b)
         else OneLambda.lam' b) := rfl

/-! ### Head-form inversions

Local re-derivations of the head-form case principle and the `app'`/`lam'`
η-expansions, which are private to `Normalization.lean`; the soundness proofs
below invert the worker guards through them. -/

/-- Transporting a term along a context equality and back along its inverse is
the identity. -/
private theorem eqRec_symm_eqRec {Γ Γ' : Binding.Ctx RType} {s : RType} (h : Γ = Γ')
    (t : Binding.Tm (oneLambdaSig A) Γ s) :
    h.symm ▸ (h ▸ t : Binding.Tm (oneLambdaSig A) Γ' s) = t := by cases h; rfl

/-- Every application node is an `app'`: the η-expansion of `Tm.op` at an `app`
operation. -/
private theorem op_app_eta {Γ : Binding.Ctx RType} {σ τ : RType}
    (args : ∀ j : Fin (((oneLambdaSig A).args (OneLambdaOp.app σ τ)).length),
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args (OneLambdaOp.app σ τ)).get j).1)
        (((oneLambdaSig A).args (OneLambdaOp.app σ τ)).get j).2) :
    Binding.Tm.op (OneLambdaOp.app σ τ) args
      = OneLambda.app' (List.append_nil Γ ▸ (args ⟨0, Nat.succ_pos 1⟩ :
            Binding.Tm (oneLambdaSig A) (Γ ++ []) (RType.arrow σ τ)))
          (List.append_nil Γ ▸ (args ⟨1, Nat.one_lt_two⟩ :
            Binding.Tm (oneLambdaSig A) (Γ ++ []) σ)) := by
  unfold OneLambda.app'
  congr 1
  funext j
  match j with
  | ⟨0, _⟩ => exact (eqRec_symm_eqRec (List.append_nil Γ) _).symm
  | ⟨1, _⟩ => exact (eqRec_symm_eqRec (List.append_nil Γ) _).symm

/-- Every abstraction node is a `lam'`: the η-expansion of `Tm.op` at a `lam`
operation. -/
private theorem op_lam_eta {Γ : Binding.Ctx RType} {σ τ : RType}
    (args : ∀ j : Fin (((oneLambdaSig A).args (OneLambdaOp.lam σ τ)).length),
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args (OneLambdaOp.lam σ τ)).get j).1)
        (((oneLambdaSig A).args (OneLambdaOp.lam σ τ)).get j).2) :
    Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.lam σ τ) args
      = OneLambda.lam' (σ := σ) (τ := τ)
          (args ⟨0, Nat.one_pos⟩ : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ) := by
  unfold OneLambda.lam'
  congr 1
  funext j
  match j with
  | ⟨0, _⟩ => rfl

/-- Every application node is an `app'` of some function and argument at the
node's own context: the existential packaging of `op_app_eta`. -/
theorem op_app_inv {Γ : Binding.Ctx RType} {σ τ : RType}
    (args : ∀ j : Fin (((oneLambdaSig A).args (OneLambdaOp.app σ τ)).length),
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args (OneLambdaOp.app σ τ)).get j).1)
        (((oneLambdaSig A).args (OneLambdaOp.app σ τ)).get j).2) :
    ∃ (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
      (x : Binding.Tm (oneLambdaSig A) Γ σ),
      Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.app σ τ) args = OneLambda.app' f x :=
  ⟨_, _, op_app_eta args⟩

/-- Every abstraction node is a `lam'` of some body at the binder-extended
context: the existential packaging of `op_lam_eta`. -/
theorem op_lam_inv {Γ : Binding.Ctx RType} {σ τ : RType}
    (args : ∀ j : Fin (((oneLambdaSig A).args (OneLambdaOp.lam σ τ)).length),
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args (OneLambdaOp.lam σ τ)).get j).1)
        (((oneLambdaSig A).args (OneLambdaOp.lam σ τ)).get j).2) :
    ∃ b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ,
      Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.lam σ τ) args = OneLambda.lam' b :=
  ⟨_, op_lam_eta args⟩

/-- The head-form cases of a term of `1λ(A)`: a variable, or an operation node
whose result sort transports to the term's sort. -/
theorem tm_cases {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) :
    (∃ x : Binding.Var Γ s, t = Binding.Tm.var x) ∨
    ∃ (o : OneLambdaOp A) (hs : (oneLambdaSig A).result o = s)
      (args : ∀ j : Fin (((oneLambdaSig A).args o).length),
        Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args o).get j).1)
          (((oneLambdaSig A).args o).get j).2),
      t = (hs ▸ Binding.Tm.op (S := oneLambdaSig A) o args
            : Binding.Tm (oneLambdaSig A) Γ s) := by
  suffices haux : ∀ {y : Binding.Ctx RType × RType}
      (t : PolyFix (polyTranslate Binding.varOver (oneLambdaSig A).polyEndo) y),
      (∃ x : Binding.Var y.1 y.2,
        t = (Binding.Tm.var x : Binding.Tm (oneLambdaSig A) y.1 y.2)) ∨
      ∃ (o : OneLambdaOp A) (hs : (oneLambdaSig A).result o = y.2)
        (args : ∀ j : Fin (((oneLambdaSig A).args o).length),
          Binding.Tm (oneLambdaSig A) (y.1 ++ (((oneLambdaSig A).args o).get j).1)
            (((oneLambdaSig A).args o).get j).2),
        t = (hs ▸ Binding.Tm.op (S := oneLambdaSig A) o args
              : Binding.Tm (oneLambdaSig A) y.1 y.2) from haux t
  intro y t
  cases t with
  | mk y idx children =>
    cases idx with
    | inl a =>
      refine Or.inl ⟨Binding.leafVar a, ?_⟩
      obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
      congr 1
      funext e
      exact e.elim
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : OneLambdaOp A // (oneLambdaSig A).result o = s' } at p
      revert children
      obtain ⟨o, rfl⟩ := p
      intro children
      exact Or.inr ⟨o, rfl, fun j => children ⟨j⟩, rfl⟩

/-- The abstraction behind the `isLam` flag: an arrow-sorted term whose `isLam`
detector is set is an abstraction node `lam' b`. The inversion consumed by the
β worker's root-contraction regime, exposing the body that `appReduct`
instantiates. -/
theorem exists_lam'_of_isLam {Γ : Binding.Ctx RType} {σ τ : RType}
    {f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ)} (h : isLam f = true) :
    ∃ b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ, f = OneLambda.lam' b := by
  rcases tm_cases f with ⟨x, rfl⟩ | ⟨o, hs, args, rfl⟩
  · rw [isLam_var] at h
    exact Bool.noConfusion h
  · have h' : isLam (Binding.Tm.op (S := oneLambdaSig A) o args) = true :=
      (isLam_cast rfl hs (Binding.Tm.op (S := oneLambdaSig A) o args)).symm.trans h
    cases o with
    | lam σ' τ' =>
        have hs' : RType.arrow σ' τ' = RType.arrow σ τ := hs
        rw [RType.arrow_eq_arrow] at hs'
        obtain ⟨hσ, hτ⟩ := hs'
        subst hσ
        subst hτ
        obtain ⟨b, hb⟩ := op_lam_inv args
        exact ⟨b, hb⟩
    | app σ' τ' =>
        replace h' : false = true := h'
        exact Bool.noConfusion h'
    | con i =>
        replace h' : false = true := h'
        exact Bool.noConfusion h'
    | dstr j =>
        replace h' : false = true := h'
        exact Bool.noConfusion h'
    | case =>
        replace h' : false = true := h'
        exact Bool.noConfusion h'

/-! ### Redex-shape inversions

Local re-derivations of the constructor-spine and ι-spine inversions of
`Normalization.lean` (`conHeaded_inv_aux`, `iotaSpine_inv_aux`, and their
supporting head-form and transport lemmas), which are private to that file;
the ι-half soundness proof below inverts the saturated ι-redex through them. -/

/-- The operation node behind a `headTag` value: a term whose head tag is
`some o` is an operation node at `o`, its sort the transported result sort of
`o`. The inversion consumed by the redex-shape recognitions. -/
private theorem exists_op_of_headTag {Γ : Binding.Ctx RType} {s : RType}
    {t : Binding.Tm (oneLambdaSig A) Γ s} {o : OneLambdaOp A} (h : headTag t = some o) :
    ∃ (hs : (oneLambdaSig A).result o = s)
      (args : ∀ j : Fin (((oneLambdaSig A).args o).length),
        Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args o).get j).1)
          (((oneLambdaSig A).args o).get j).2),
      t = (hs ▸ Binding.Tm.op (S := oneLambdaSig A) o args
            : Binding.Tm (oneLambdaSig A) Γ s) := by
  rcases tm_cases t with ⟨x, rfl⟩ | ⟨o', hs, args, rfl⟩
  · rw [headTag_var] at h
    simp at h
  · have ho : o' = o := by
      have := (headTag_cast rfl hs (Binding.Tm.op (S := oneLambdaSig A) o' args)).symm.trans h
      rw [headTag_op] at this
      exact Option.some.inj this
    subst ho
    exact ⟨hs, args, rfl⟩

/-- An r-type of shape `o` is the base type `o`: the nullary shape determines
the node. -/
theorem eq_o_of_shape_o {s : RType} (h : s.shape = RTypeShape.o) : s = RType.o := by
  rcases s with ⟨_, i, children⟩
  have hi : i = RTypeShape.o := h
  subst hi
  change FreeAlg.mk (A := rTypeSig) RTypeShape.o children = RType.o
  exact congrArg (FreeAlg.mk (A := rTypeSig) RTypeShape.o) (funext fun e => e.elim0)

/-- An arrow type is not the base type `o`: their shapes differ. -/
private theorem arrow_ne_o (σ τ : RType) : RType.arrow σ τ ≠ RType.o := fun hcon => by
  have := congrArg RType.shape hcon
  simp at this

/-- The curried sort of a homogeneous spine absorbs one further `o`-argument of
its result sort: `o^n → (o → ρ) = o^{n+1} → ρ`. The sort-level accounting of
`replicateSpine_snoc`. -/
private theorem curried_replicate_snoc (n : ℕ) (ρ : RType) :
    RType.curried (List.replicate n RType.o) (RType.arrow RType.o ρ)
      = RType.curried (List.replicate (n + 1) RType.o) ρ := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (RType.arrow RType.o) ih

/-- Sort transport of a term, packaged as a definition so that its source and
target sorts are pinned by the equality proof's type and cast-commutation
lemmas match syntactically. -/
private def castSort {Γ : Binding.Ctx RType} {s s' : RType} (h : s = s')
    (t : Binding.Tm (oneLambdaSig A) Γ s) : Binding.Tm (oneLambdaSig A) Γ s' := h ▸ t

/-- Transport along a composite of sort equalities is the transport along the
composite equality. -/
private theorem castSort_trans {Γ : Binding.Ctx RType} {a b c : RType} (h₁ : a = b) (h₂ : b = c)
    (t : Binding.Tm (oneLambdaSig A) Γ a) :
    castSort h₂ (castSort h₁ t) = castSort (h₁.trans h₂) t := by
  cases h₂; rfl

/-- An application whose function is transported in its codomain sort is the
transport of the application: `app'` commutes with a codomain cast. -/
private theorem app'_castSort {Γ : Binding.Ctx RType} {σ τ τ' : RType} (hτ : τ = τ')
    (harr : RType.arrow σ τ = RType.arrow σ τ')
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) :
    app' (castSort harr f) x = castSort hτ (app' f x) := by
  cases hτ; rfl
/-- Peeling the first argument of a homogeneous spine: an `(n+1)`-argument spine
is the `n`-argument spine over the head applied to the first argument. -/
private theorem replicateSpine_cons {Γ : Binding.Ctx RType} {result : RType} (n : ℕ)
    (base : RType)
    (head : Binding.Tm (oneLambdaSig A) Γ (RType.curried (List.replicate (n + 1) base) result))
    (a : Fin (n + 1) → Binding.Tm (oneLambdaSig A) Γ base) :
    replicateSpine (n + 1) base head a
      = replicateSpine n base
          (app' (σ := base) (τ := RType.curried (List.replicate n base) result) head
            (a ⟨0, n.succ_pos⟩))
          (fun i => a i.succ) := rfl

/-- The last-index composite of a `Fin.snoc` with the successor embedding is the
`Fin.snoc` of the composite: reading a snoc-extended tuple at shifted indices
drops the first entry. -/
private theorem fin_snoc_comp_succ {n : ℕ} {C : Sort _} (a : Fin (n + 1) → C) (w : C) :
    (fun i : Fin (n + 1) => Fin.snoc (α := fun _ => C) a w i.succ)
      = Fin.snoc (α := fun _ => C) (fun i => a i.succ) w := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [Fin.succ_last]
  | cast i => simp only [Fin.succ_castSucc, Fin.snoc_castSucc]

/-- Appending one further argument to a homogeneous spine: applying an
`n`-argument spine to one more base-sort argument is the `(n+1)`-argument spine
at the sort-transported head over the `Fin.snoc`-extended argument tuple. -/
private theorem replicateSpine_snoc {Γ : Binding.Ctx RType} {ρ : RType} :
    (n : ℕ) →
    (head : Binding.Tm (oneLambdaSig A) Γ
      (RType.curried (List.replicate n RType.o) (RType.arrow RType.o ρ))) →
    (a : Fin n → Binding.Tm (oneLambdaSig A) Γ RType.o) →
    (w : Binding.Tm (oneLambdaSig A) Γ RType.o) →
    app' (replicateSpine n RType.o head a) w
      = replicateSpine (n + 1) RType.o (castSort (curried_replicate_snoc n ρ) head)
          (Fin.snoc a w)
  | 0, head, a, w => rfl
  | n + 1, head, a, w => by
      calc app' (replicateSpine (n + 1) RType.o head a) w
          = app' (replicateSpine n RType.o
              (app' (σ := RType.o) head (a ⟨0, n.succ_pos⟩)) (fun i => a i.succ)) w := by
            rw [replicateSpine_cons]
        _ = replicateSpine (n + 1) RType.o
              (castSort (curried_replicate_snoc n ρ)
                (app' (σ := RType.o) head (a ⟨0, n.succ_pos⟩)))
              (Fin.snoc (fun i => a i.succ) w) :=
            replicateSpine_snoc n _ _ w
        _ = replicateSpine (n + 1) RType.o
              (app' (σ := RType.o) (castSort (curried_replicate_snoc (n + 1) ρ) head)
                (a ⟨0, n.succ_pos⟩))
              (Fin.snoc (fun i => a i.succ) w) :=
            congrArg
              (fun H => replicateSpine (n + 1) RType.o H (Fin.snoc (fun i => a i.succ) w))
              (app'_castSort (curried_replicate_snoc n ρ)
                (curried_replicate_snoc (n + 1) ρ) head (a ⟨0, n.succ_pos⟩)).symm
        _ = replicateSpine (n + 1 + 1) RType.o
              (castSort (curried_replicate_snoc (n + 1) ρ) head) (Fin.snoc a w) := by
            rw [replicateSpine_cons (n + 1) RType.o
              (castSort (curried_replicate_snoc (n + 1) ρ) head) (Fin.snoc a w),
              fin_snoc_comp_succ]
            rfl
/-- The generalized constructor-spine inversion (Leivant III section 4.3's
head-form observation), tracking the pending-argument count: a `conHeaded` term
of sort `o^k → o` is a constructor constant `con i` applied along an
application spine to `n` arguments of sort `o`, with `A.ar i = n + k`. The
intrinsic sorts force the count accounting; the sort transports record the
curried-sort arithmetic. By strong induction on the term size. -/
private theorem conHeaded_inv_aux :
    (N : ℕ) → ∀ {Γ : Binding.Ctx RType} {s : RType} (t : Binding.Tm (oneLambdaSig A) Γ s),
    Tm.size t ≤ N → conHeaded t = true →
    ∃ (i : A.B) (n k : ℕ) (_ : A.ar i = n + k)
      (hs : s = RType.curried (List.replicate k RType.o) RType.o)
      (hh : RType.curried (List.replicate (A.ar i) RType.o) RType.o
          = RType.curried (List.replicate n RType.o)
              (RType.curried (List.replicate k RType.o) RType.o))
      (a : Fin n → Binding.Tm (oneLambdaSig A) Γ RType.o),
      t = castSort hs.symm (replicateSpine n RType.o
            (castSort hh (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i)
              (fun l => l.elim0))) a)
  | 0, _, _, t, hN, _ => absurd (Tm.one_le_size t) (by omega)
  | N + 1, Γ, s, t, hN, h => by
      rcases tm_cases t with ⟨x0, ht⟩ | ⟨o, hs0, args, ht⟩
      · subst ht
        rw [conHeaded_var] at h
        simp at h
      · cases o with
        | app σ τ =>
            have hs1 : τ = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.app σ τ) args :=
              ht
            obtain ⟨f, x, hfx⟩ := op_app_inv args
            rw [hfx] at ht
            subst ht
            rw [size_app'] at hN
            rw [conHeaded_app'] at h
            obtain ⟨i, n, k, hnk, hsf, hh, a, hf⟩ := conHeaded_inv_aux N f (by omega) h
            cases k with
            | zero =>
                rw [List.replicate_zero, RType.curried_nil] at hsf
                exact absurd hsf (arrow_ne_o σ τ)
            | succ k' =>
                have hsf' := hsf
                rw [List.replicate_succ, RType.curried_cons, RType.arrow_eq_arrow] at hsf'
                obtain ⟨hσ, hτ⟩ := hsf'
                subst hσ
                subst hτ
                replace hf : f = replicateSpine n RType.o
                    (castSort hh (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i)
                      (fun l => l.elim0))) a := hf
                refine ⟨i, n + 1, k', by omega, rfl,
                  hh.trans (curried_replicate_snoc n
                    (RType.curried (List.replicate k' RType.o) RType.o)),
                  Fin.snoc a x, ?_⟩
                rw [hf]
                exact (replicateSpine_snoc n _ a x).trans
                  (congrArg (fun H => replicateSpine (n + 1) RType.o H (Fin.snoc a x))
                    (castSort_trans hh (curried_replicate_snoc n _) _))
        | lam σ τ =>
            have hs1 : RType.arrow σ τ = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.lam σ τ) args :=
              ht
            subst ht
            replace h : false = true := h
            exact Bool.noConfusion h
        | con i =>
            have hs1 : RType.curried (List.replicate (A.ar i) RType.o) RType.o = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) args :=
              ht
            subst ht
            refine ⟨i, 0, A.ar i, (Nat.zero_add _).symm, rfl, rfl, fun l => l.elim0, ?_⟩
            change Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) args
              = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) fun l => l.elim0
            exact congrArg _ (funext fun j => j.elim0)
        | dstr j =>
            have hs1 : RType.arrow RType.o RType.o = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j) args :=
              ht
            subst ht
            replace h : false = true := h
            exact Bool.noConfusion h
        | case =>
            have hs1 : RType.arrow RType.o
                (RType.curried (List.replicate A.numCtors RType.o) RType.o) = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case args := ht
            subst ht
            replace h : false = true := h
            exact Bool.noConfusion h

/-- The constructor-headed inversion at the base sort (Leivant III section
4.3's head-form observation): a `conHeaded` term of sort `o` is a constructor
constant applied to a full argument tuple — `con`-headedness at sort `o`
implies saturation through the intrinsic sorts. -/
private theorem conHeaded_o_inv {Γ : Binding.Ctx RType}
    {x : Binding.Tm (oneLambdaSig A) Γ RType.o} (h : conHeaded x = true) :
    ∃ (i : A.B) (a : Fin (A.ar i) → Binding.Tm (oneLambdaSig A) Γ RType.o),
      x = replicateSpine (A.ar i) RType.o
          (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) (fun l => l.elim0)) a := by
  obtain ⟨i, n, k, hnk, hs, hh, a, hx⟩ := conHeaded_inv_aux (Tm.size x) x le_rfl h
  cases k with
  | succ k' =>
      have hs' := hs
      rw [List.replicate_succ, RType.curried_cons] at hs'
      exact absurd hs'.symm (arrow_ne_o _ _)
  | zero =>
      have hn : A.ar i = n := hnk
      subst hn
      exact ⟨i, a, hx⟩
/-- The ι-spine inversion (Leivant III section 4.2, p. 224), tracking the
pending-argument count: a term for which the `iotaSpine` detector applies is
either a destructor applied to a `con`-headed scrutinee — necessarily at sort
`o` — or a case combinator applied to a `con`-headed scrutinee and then, along
the application spine, to `n` branch arguments with `A.numCtors = n + k`
pending. By strong induction on the term size; the sort transports record the
curried-sort arithmetic. -/
private theorem iotaSpine_inv_aux :
    (N : ℕ) → ∀ {Γ : Binding.Ctx RType} {s : RType} (t : Binding.Tm (oneLambdaSig A) Γ s),
    Tm.size t ≤ N → iotaSpine t = true →
    (∃ (j : Fin A.maxArity) (w : Binding.Tm (oneLambdaSig A) Γ RType.o) (hs : s = RType.o),
      conHeaded w = true ∧
      t = castSort hs.symm (app' (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j)
            (fun l => l.elim0)) w)) ∨
    (∃ (n k : ℕ) (_ : A.numCtors = n + k)
      (hs : s = RType.curried (List.replicate k RType.o) RType.o)
      (hh : RType.arrow RType.o (RType.curried (List.replicate A.numCtors RType.o) RType.o)
          = RType.arrow RType.o (RType.curried (List.replicate n RType.o)
              (RType.curried (List.replicate k RType.o) RType.o)))
      (scrut : Binding.Tm (oneLambdaSig A) Γ RType.o)
      (b : Fin n → Binding.Tm (oneLambdaSig A) Γ RType.o),
      conHeaded scrut = true ∧
      t = castSort hs.symm (replicateSpine n RType.o
            (app' (castSort hh (Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case
              (fun l => l.elim0))) scrut) b))
  | 0, _, _, t, hN, _ => absurd (Tm.one_le_size t) (by omega)
  | N + 1, Γ, s, t, hN, h => by
      rcases tm_cases t with ⟨x0, ht⟩ | ⟨o, hs0, args, ht⟩
      · subst ht
        rw [iotaSpine_var] at h
        simp at h
      · cases o with
        | app σ τ =>
            have hs1 : τ = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.app σ τ) args :=
              ht
            obtain ⟨f, x, hfx⟩ := op_app_inv args
            rw [hfx] at ht
            subst ht
            rw [size_app'] at hN
            rw [iotaSpine_app'] at h
            rcases hhf : headTag f with _ | o'
            · rw [hhf] at h
              replace h : false = true := h
              exact Bool.noConfusion h
            · rw [hhf] at h
              cases o' with
              | app σ' τ' =>
                  replace h : iotaSpine f = true := h
                  rcases iotaSpine_inv_aux N f (by omega) h with
                    ⟨j, w, hso, hcw, hfA⟩ | ⟨n, k, hnk, hsB, hh, scrut, b, hcs, hfB⟩
                  · exact absurd hso (arrow_ne_o σ τ)
                  · cases k with
                    | zero =>
                        rw [List.replicate_zero, RType.curried_nil] at hsB
                        exact absurd hsB (arrow_ne_o σ τ)
                    | succ k' =>
                        have hsB' := hsB
                        rw [List.replicate_succ, RType.curried_cons,
                          RType.arrow_eq_arrow] at hsB'
                        obtain ⟨hσ, hτ⟩ := hsB'
                        subst hσ
                        subst hτ
                        replace hfB : f = replicateSpine n RType.o
                            (app' (castSort hh (Binding.Tm.op (S := oneLambdaSig A)
                              OneLambdaOp.case (fun l => l.elim0))) scrut) b := hfB
                        refine Or.inr ⟨n + 1, k', by omega, rfl,
                          hh.trans (congrArg (RType.arrow RType.o)
                            (curried_replicate_snoc n
                              (RType.curried (List.replicate k' RType.o) RType.o))),
                          scrut, Fin.snoc b x, hcs, ?_⟩
                        rw [hfB]
                        refine (replicateSpine_snoc n _ b x).trans ?_
                        refine congrArg
                          (fun H => replicateSpine (n + 1) RType.o H (Fin.snoc b x)) ?_
                        refine (app'_castSort (curried_replicate_snoc n _)
                          (congrArg (RType.arrow RType.o) (curried_replicate_snoc n _))
                          (castSort hh (Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case
                            (fun l => l.elim0))) scrut).symm.trans ?_
                        exact congrArg (fun F => app' F scrut)
                          (castSort_trans hh (congrArg (RType.arrow RType.o)
                            (curried_replicate_snoc n
                              (RType.curried (List.replicate k' RType.o) RType.o)))
                            (Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case
                              (fun l => l.elim0)))
              | dstr j =>
                  replace h : conHeaded x = true := h
                  obtain ⟨hsd, args', hfd⟩ := exists_op_of_headTag hhf
                  replace hsd : RType.arrow RType.o RType.o = RType.arrow σ τ := hsd
                  rw [RType.arrow_eq_arrow] at hsd
                  obtain ⟨hσ, hτ⟩ := hsd
                  subst hσ
                  subst hτ
                  refine Or.inl ⟨j, x, rfl, h, ?_⟩
                  replace hfd : f = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j)
                      args' := hfd
                  rw [hfd]
                  refine congrArg (fun F => app' F x) ?_
                  change Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j) args'
                    = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j)
                        fun l => l.elim0
                  exact congrArg _ (funext fun l => l.elim0)
              | case =>
                  replace h : conHeaded x = true := h
                  obtain ⟨hsc, args', hfc⟩ := exists_op_of_headTag hhf
                  replace hsc : RType.arrow RType.o (RType.curried
                      (List.replicate A.numCtors RType.o) RType.o) = RType.arrow σ τ := hsc
                  rw [RType.arrow_eq_arrow] at hsc
                  obtain ⟨hσ, hτ⟩ := hsc
                  subst hσ
                  subst hτ
                  refine Or.inr ⟨0, A.numCtors, (Nat.zero_add _).symm, rfl, rfl, x,
                    fun l => l.elim0, h, ?_⟩
                  replace hfc : f = Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case
                      args' := hfc
                  rw [hfc]
                  refine congrArg (fun F => app' F x) ?_
                  change Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case args'
                    = Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case fun l => l.elim0
                  exact congrArg _ (funext fun l => l.elim0)
              | lam σ' τ' =>
                  replace h : false = true := h
                  exact Bool.noConfusion h
              | con i =>
                  replace h : false = true := h
                  exact Bool.noConfusion h
        | lam σ τ =>
            have hs1 : RType.arrow σ τ = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.lam σ τ) args :=
              ht
            subst ht
            replace h : false = true := h
            exact Bool.noConfusion h
        | con i =>
            have hs1 : RType.curried (List.replicate (A.ar i) RType.o) RType.o = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) args :=
              ht
            subst ht
            replace h : false = true := h
            exact Bool.noConfusion h
        | dstr j =>
            have hs1 : RType.arrow RType.o RType.o = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j) args :=
              ht
            subst ht
            replace h : false = true := h
            exact Bool.noConfusion h
        | case =>
            have hs1 : RType.arrow RType.o
                (RType.curried (List.replicate A.numCtors RType.o) RType.o) = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case args := ht
            subst ht
            replace h : false = true := h
            exact Bool.noConfusion h

/-- The base type is not a curried sort with pending arguments: `o = o^k → o`
forces `k = 0`. -/
private theorem eq_zero_of_o_eq_curried {k : ℕ}
    (h : RType.o = RType.curried (List.replicate k RType.o) RType.o) : k = 0 := by
  cases k with
  | zero => rfl
  | succ k' =>
      rw [List.replicate_succ, RType.curried_cons] at h
      exact absurd h.symm (arrow_ne_o _ _)

/-- Every constructor label appears in the sorted enumeration: `ctorAt` is
surjective. -/
private theorem exists_ctorAt_eq [LinearOrder A.B] (i : A.B) :
    ∃ idx : Fin A.numCtors, ctorAt idx = i := by
  have hmem : i ∈ ctorList A := by
    unfold ctorList
    exact (Finset.mem_sort _).mpr (Finset.mem_univ i)
  obtain ⟨m, hm⟩ := List.get_of_mem hmem
  exact ⟨m.cast ctorList_length, hm⟩

variable [LinearOrder A.B]

/-- Operation dispatch of the application-spine decomposition. At an application
node `app' f x`, extend the spine decomposition of the function subterm `f` by the
argument `x` when `x` has the base object sort `o` (appending it after the
already-collected arguments, so the scrutinee stays first and the arguments follow
in application order); at a constructor, destructor, or case head, start a spine
with that head and no arguments; at an abstraction, report no spine. -/
def collectSpineOp {Γ : Binding.Ctx RType} (o : OneLambdaOp A)
    (children : ∀ j : Fin ((oneLambdaSig A).args o).length,
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args o).get j).1)
        (((oneLambdaSig A).args o).get j).2)
    (ih : ∀ j : Fin ((oneLambdaSig A).args o).length,
      Option (OneLambdaOp A × List (Binding.Tm (oneLambdaSig A)
        (Γ ++ (((oneLambdaSig A).args o).get j).1) RType.o))) :
    Option (OneLambdaOp A × List (Binding.Tm (oneLambdaSig A) Γ RType.o)) :=
  match o, children, ih with
  | OneLambdaOp.app σ _τ, children, ih =>
      (ih ⟨0, Nat.zero_lt_two⟩).bind (fun p =>
        if h : σ = RType.o then
          some (p.1, p.2.map toG
            ++ [toG ((h ▸ children ⟨1, Nat.one_lt_two⟩ : Binding.Tm (oneLambdaSig A)
              (Γ ++ []) RType.o))])
        else some (p.1, p.2.map toG))
  | OneLambdaOp.con b, _, _ => some (OneLambdaOp.con b, [])
  | OneLambdaOp.dstr j, _, _ => some (OneLambdaOp.dstr j, [])
  | OneLambdaOp.case, _, _ => some (OneLambdaOp.case, [])
  | OneLambdaOp.lam _ _, _, _ => none

/-- The application-spine decomposition (Leivant III section 4.2, p. 224): read a
term as an application spine `h a₁ … aₙ` whose ultimate head `h` is a single
operation and whose arguments (all of the base object sort `o` in a genuine redex)
are returned in application order. Structural recursion by `PolyFix.ind` through
`collectSpineOp`; the ι-contraction reads the destructor/case reduct off it. Novel
realization. -/
def collectSpine {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) :
    Option (OneLambdaOp A × List (Binding.Tm (oneLambdaSig A) Γ RType.o)) :=
  PolyFix.ind (P := polyTranslate Binding.varOver (oneLambdaSig A).polyEndo)
    (motive := fun {y} _ =>
      Option (OneLambdaOp A × List (Binding.Tm (oneLambdaSig A) y.1 RType.o)))
    (fun {_x} i children ih =>
      match i, children, ih with
      | Sum.inl _, _, _ => none
      | Sum.inr p, children, ih =>
        collectSpineOp p.val (fun j => children ⟨j⟩) (fun j => ih ⟨j⟩)) t

/-- The destructor reduct (Leivant III section 4.2, p. 223): for a `con`-headed
scrutinee `c_i a₁ … a_{r_i}`, `dstr_j` returns the argument `a_j` on a hit
(`j < r_i`) and the scrutinee itself on a miss (`OneLambdaStep.dstrHit`/
`dstrMiss`). The scrutinee is decomposed by `collectSpine`; a non-`con` scrutinee
returns the scrutinee unchanged. -/
def dstrReduct {Γ : Binding.Ctx RType} (j : Fin A.maxArity)
    (scrut : Binding.Tm (oneLambdaSig A) Γ RType.o) :
    Binding.Tm (oneLambdaSig A) Γ RType.o :=
  match collectSpine scrut with
  | some (OneLambdaOp.con _i, conArgs) =>
      match conArgs[j.val]? with
      | some aj => aj
      | none => scrut
  | _ => scrut

/-- The case reduct (Leivant III section 4.2, p. 223): for a `con`-headed
scrutinee whose constructor is `c_i`, `case` selects the branch at the
enumeration position of `c_i` in `ctorList A` (`OneLambdaStep.case`). The
scrutinee is decomposed by `collectSpine`; a non-`con` scrutinee or an
out-of-range branch index returns the scrutinee unchanged. -/
def caseReduct {Γ : Binding.Ctx RType}
    (scrut : Binding.Tm (oneLambdaSig A) Γ RType.o)
    (branches : List (Binding.Tm (oneLambdaSig A) Γ RType.o)) :
    Binding.Tm (oneLambdaSig A) Γ RType.o :=
  match collectSpine scrut with
  | some (OneLambdaOp.con i, _) =>
      match branches[(ctorList A).idxOf i]? with
      | some bi => bi
      | none => scrut
  | _ => scrut

/-- The ι-contraction at the base object sort (Leivant III section 4.2, p. 223):
decompose the term as an application spine; if it is a destructor spine
`dstr_j scrut`, take the destructor reduct; if a case spine `case scrut b₁ … b_k`,
take the case reduct; otherwise return the term unchanged. -/
def iotaContractO {Γ : Binding.Ctx RType}
    (t : Binding.Tm (oneLambdaSig A) Γ RType.o) :
    Binding.Tm (oneLambdaSig A) Γ RType.o :=
  match collectSpine t with
  | some (OneLambdaOp.dstr j, scrut :: _) => dstrReduct j scrut
  | some (OneLambdaOp.case, scrut :: branches) => caseReduct scrut branches
  | _ => t

/-- The ι-contraction: the destructor- or case-redex reduct `iotaContractO` at the
base object sort `o` (where every genuine ι-redex lives, `topIota`'s result-sort
guard), extended to every sort as the identity off `o`. -/
def iotaContract {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) : Binding.Tm (oneLambdaSig A) Γ s :=
  if h : s = RType.o then h.symm ▸ iotaContractO (h ▸ t) else t

/-- Operation dispatch of the ι worker `detIotaStep` at an operation node
(Leivant III section 4.2, p. 224). At an application node `app' f x`: descend into
the first child carrying an ι-redex (function first, then argument), lifting the
recursive image through the congruence; if neither child does and the node is a
saturated ι-redex (`topIota`), contract it with `iotaContract`; otherwise the
identity. At an abstraction node `lam' b`: descend into the body when it carries an
ι-redex, else the identity. At every other operation node: the identity. -/
def detIotaStepOp {Γ : Binding.Ctx RType} (o : OneLambdaOp A)
    (children : ∀ j : Fin ((oneLambdaSig A).args o).length,
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args o).get j).1)
        (((oneLambdaSig A).args o).get j).2)
    (ih : ∀ j : Fin ((oneLambdaSig A).args o).length,
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args o).get j).1)
        (((oneLambdaSig A).args o).get j).2) :
    Binding.Tm (oneLambdaSig A) Γ ((oneLambdaSig A).result o) :=
  match o, children, ih with
  | OneLambdaOp.app _ _, children, ih =>
      let f := toG (children ⟨0, Nat.zero_lt_two⟩)
      let x := toG (children ⟨1, Nat.one_lt_two⟩)
      let f' := toG (ih ⟨0, Nat.zero_lt_two⟩)
      let x' := toG (ih ⟨1, Nat.one_lt_two⟩)
      if hasIota f = true then OneLambda.app' f' x
      else if hasIota x = true then OneLambda.app' f x'
      else if topIota (OneLambda.app' f x) = true then iotaContract (OneLambda.app' f x)
      else OneLambda.app' f x
  | OneLambdaOp.lam _ _, children, ih =>
      let b := children ⟨0, Nat.zero_lt_one⟩
      let b' := ih ⟨0, Nat.zero_lt_one⟩
      if hasIota b = true then OneLambda.lam' b'
      else OneLambda.lam' b
  | o, children, _ih => Binding.Tm.op (S := oneLambdaSig A) o children

/-- The ι worker (Leivant III section 4.2, p. 224; spec §4.2): child-priority
descent contracting the first ι-redex. A structure-preserving `PolyFix.ind` fold
dispatching through `detIotaStepOp`. -/
def detIotaStep {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) : Binding.Tm (oneLambdaSig A) Γ s :=
  PolyFix.ind (P := polyTranslate Binding.varOver (oneLambdaSig A).polyEndo)
    (motive := fun {y} _ => Binding.Tm (oneLambdaSig A) y.1 y.2)
    (fun {x} i children ih =>
      match i, children, ih with
      | Sum.inl a, _, _ => Binding.Tm.var (leafVar a)
      | Sum.inr p, children, ih =>
        cast (congrArg (fun s => Binding.Tm (oneLambdaSig A) x.1 s) p.2)
          (detIotaStepOp p.val (fun j => children ⟨j⟩) (fun j => ih ⟨j⟩))) t

/-- `detIotaStep` at an operation node dispatches through `detIotaStepOp` on the
worker images of its subterms. -/
theorem detIotaStep_op {Γ : Binding.Ctx RType} (o : OneLambdaOp A)
    (args : ∀ j : Fin ((oneLambdaSig A).args o).length,
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args o).get j).1)
        (((oneLambdaSig A).args o).get j).2) :
    detIotaStep (Binding.Tm.op o args)
      = detIotaStepOp o args (fun j => detIotaStep (args j)) := rfl

/-- `detIotaStep` is the identity at a variable. -/
@[simp] theorem detIotaStep_var {Γ : Binding.Ctx RType} {s : RType}
    (x : Binding.Var Γ s) :
    detIotaStep (Binding.Tm.var x : Binding.Tm (oneLambdaSig A) Γ s)
      = Binding.Tm.var x := by
  obtain ⟨i, hi⟩ := x; subst hi; rfl

/-- `detIotaStep` is invariant under transport of the context and sort indices. -/
theorem detIotaStep_cast {Γ Γ' : Binding.Ctx RType} {s s' : RType}
    (hΓ : Γ = Γ') (hs : s = s') (t : Binding.Tm (oneLambdaSig A) Γ s) :
    detIotaStep (hs ▸ hΓ ▸ t) = hs ▸ hΓ ▸ detIotaStep t := by
  subst hΓ; subst hs; rfl

/-- `detIotaStep` commutes with the `Γ ++ [] = Γ` transport that `app'` applies to
its subterms. -/
private theorem detIotaStep_appendNil {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) (Γ ++ []) s) :
    detIotaStep (toG t) = toG (detIotaStep t) :=
  detIotaStep_cast (List.append_nil Γ) rfl t

/-- `detIotaStep` at an abstraction node descends into the body when it carries an
ι-redex, and is the identity otherwise. -/
theorem detIotaStep_lam' {Γ : Binding.Ctx RType} {σ τ : RType}
    (b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ) :
    detIotaStep (OneLambda.lam' b)
      = (if hasIota b = true then OneLambda.lam' (detIotaStep b)
         else OneLambda.lam' b) := rfl

/-- `detIotaStep` at an application node in the three guard regimes: descend into
the function subterm when it carries an ι-redex; else descend into the argument
subterm when it does; else contract the root ι-redex to `iotaContract` when the
node is a saturated ι-redex (`topIota`); else the identity. -/
theorem detIotaStep_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) :
    detIotaStep (OneLambda.app' f x)
      = (if hasIota f = true then OneLambda.app' (detIotaStep f) x
         else if hasIota x = true then OneLambda.app' f (detIotaStep x)
         else if topIota (OneLambda.app' f x) = true then iotaContract (OneLambda.app' f x)
         else OneLambda.app' f x) := by
  have e : detIotaStep (OneLambda.app' f x)
      = detIotaStepOp (OneLambdaOp.app σ τ)
          (fun j => Fin.cases ((List.append_nil Γ).symm ▸ f)
            (fun k => Fin.cases ((List.append_nil Γ).symm ▸ x) (fun l => l.elim0) k) j)
          (fun j => detIotaStep (Fin.cases ((List.append_nil Γ).symm ▸ f)
            (fun k => Fin.cases ((List.append_nil Γ).symm ▸ x) (fun l => l.elim0) k) j)) := rfl
  rw [e]
  change (if hasIota (toG ((List.append_nil Γ).symm ▸ f)) = true
        then OneLambda.app' (toG (detIotaStep ((List.append_nil Γ).symm ▸ f)))
          (toG ((List.append_nil Γ).symm ▸ x))
        else if hasIota (toG ((List.append_nil Γ).symm ▸ x)) = true
        then OneLambda.app' (toG ((List.append_nil Γ).symm ▸ f))
          (toG (detIotaStep ((List.append_nil Γ).symm ▸ x)))
        else if topIota (OneLambda.app' (toG ((List.append_nil Γ).symm ▸ f))
            (toG ((List.append_nil Γ).symm ▸ x))) = true
        then iotaContract (OneLambda.app' (toG ((List.append_nil Γ).symm ▸ f))
          (toG ((List.append_nil Γ).symm ▸ x)))
        else OneLambda.app' (toG ((List.append_nil Γ).symm ▸ f))
          (toG ((List.append_nil Γ).symm ▸ x))) = _
  have hdf : toG (detIotaStep ((List.append_nil Γ).symm ▸ f)) = detIotaStep f := by
    rw [← detIotaStep_appendNil, toG_symm]
  have hdx : toG (detIotaStep ((List.append_nil Γ).symm ▸ x)) = detIotaStep x := by
    rw [← detIotaStep_appendNil, toG_symm]
  rw [toG_symm, toG_symm, hdf, hdx]

/-- The deterministic step (Leivant III section 4.2, p. 224; plan decision P2):
read `q := betaRedexRank t`; if `q > 0` apply the β worker `detStepAt q`; else if
`t` carries an ι-redex apply the ι worker `detIotaStep`; else `t` is normal and is
returned unchanged. -/
def detStep {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) : Binding.Tm (oneLambdaSig A) Γ s :=
  if 0 < betaRedexRank t then detStepAt (betaRedexRank t) t
  else if hasIota t = true then detIotaStep t else t

/-- The dispatch unfolding of `detStep`. -/
theorem detStep_eq {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) :
    detStep t = (if 0 < betaRedexRank t then detStepAt (betaRedexRank t) t
      else if hasIota t = true then detIotaStep t else t) := rfl

/-- `detStep` is the identity on `Normal` terms: a normal term has β-rank `0` and
no ι-redex, so both dispatch guards fail. -/
theorem detStep_normal {Γ : Binding.Ctx RType} {s : RType}
    {t : Binding.Tm (oneLambdaSig A) Γ s} (h : Normal t) : detStep t = t := by
  obtain ⟨hb, hi⟩ := (normal_iff t).mp h
  rw [detStep_eq, hb, hi]
  simp

/-! ### Soundness of the β worker

The β half of the deterministic step's soundness (spec §8.2): at a term of
positive β-rank `q`, the worker `detStepAt q` performs one genuine
`OneLambdaStep`. The congruence regimes lift the descent by
`OneLambdaStep.appL`/`appR`/`lamBody`; the root-contraction regime is
`OneLambdaStep.beta`, with the abstraction body exposed by
`exists_lam'_of_isLam`; descent totality — some regime always applies at a
rank-`q` node — comes from the `betaRedexRank_app'` decomposition. -/

/-- The descent induction behind `detStepAt_sound`, by strong induction on the
term size: at every node of β-rank `q > 0`, one of the `detStepAtOp` guard
regimes applies and yields a `OneLambdaStep` onto the worker's image. -/
private theorem detStepAt_sound_aux (q : ℕ) (hq : 0 < q) :
    (N : ℕ) → ∀ {Γ : Binding.Ctx RType} {s : RType} (t : Binding.Tm (oneLambdaSig A) Γ s),
    Tm.size t ≤ N → betaRedexRank t = q → OneLambdaStep t (detStepAt q t)
  | 0, _, _, t, hN, _ => absurd (Tm.one_le_size t) (by omega)
  | N + 1, Γ, s, t, hN, hrank => by
      rcases tm_cases t with ⟨x0, ht⟩ | ⟨o, hs0, args, ht⟩
      · subst ht
        rw [betaRedexRank_var] at hrank
        omega
      · cases o with
        | app σ τ =>
            have hs1 : τ = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.app σ τ) args :=
              ht
            obtain ⟨f, x, hfx⟩ := op_app_inv args
            rw [hfx] at ht
            subst ht
            rw [size_app'] at hN
            rw [betaRedexRank_app'] at hrank
            have hf1 := Tm.one_le_size f
            have hx1 := Tm.one_le_size x
            rw [detStepAt_app']
            split_ifs with hf hx hguard
            · exact OneLambdaStep.appL x (detStepAt_sound_aux q hq N f (by omega) hf)
            · exact OneLambdaStep.appR f (detStepAt_sound_aux q hq N x (by omega) hx)
            · obtain ⟨hL, _⟩ := hguard
              obtain ⟨b, rfl⟩ := exists_lam'_of_isLam hL
              rw [appReduct_lam']
              exact OneLambdaStep.beta b x
            · exfalso
              rw [topBetaRank_app'] at hrank
              have htb : ¬ (if isLam f then RType.ord (RType.arrow σ τ) else 0) = q := by
                cases hL : isLam f with
                | false => simp only [Bool.false_eq_true, if_false]; omega
                | true =>
                    simp only [if_true]
                    exact fun hord => hguard ⟨hL, hord⟩
              omega
        | lam σ τ =>
            have hs1 : RType.arrow σ τ = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.lam σ τ) args :=
              ht
            obtain ⟨b, hb⟩ := op_lam_inv args
            rw [hb] at ht
            subst ht
            rw [size_lam'] at hN
            rw [betaRedexRank_lam'] at hrank
            rw [detStepAt_lam', if_pos hrank]
            exact OneLambdaStep.lamBody (detStepAt_sound_aux q hq N b (by omega) hrank)
        | con i =>
            have hs1 : RType.curried (List.replicate (A.ar i) RType.o) RType.o = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) args :=
              ht
            subst ht
            have h0 : betaRedexRank (Binding.Tm.op (S := oneLambdaSig A) (Γ := Γ)
                (OneLambdaOp.con i) args) = 0 := by
              rw [betaRedexRank_op]
              change max 0 ((Finset.univ : Finset (Fin 0)).sup _) = 0
              simp
            exact absurd (h0.symm.trans hrank) (Nat.ne_of_lt hq)
        | dstr j =>
            have hs1 : RType.arrow RType.o RType.o = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j) args :=
              ht
            subst ht
            have h0 : betaRedexRank (Binding.Tm.op (S := oneLambdaSig A) (Γ := Γ)
                (OneLambdaOp.dstr j) args) = 0 := by
              rw [betaRedexRank_op]
              change max 0 ((Finset.univ : Finset (Fin 0)).sup _) = 0
              simp
            exact absurd (h0.symm.trans hrank) (Nat.ne_of_lt hq)
        | case =>
            have hs1 : RType.arrow RType.o
                (RType.curried (List.replicate A.numCtors RType.o) RType.o) = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case args := ht
            subst ht
            have h0 : betaRedexRank (Binding.Tm.op (S := oneLambdaSig A) (Γ := Γ)
                OneLambdaOp.case args) = 0 := by
              rw [betaRedexRank_op]
              change max 0 ((Finset.univ : Finset (Fin 0)).sup _) = 0
              simp
            exact absurd (h0.symm.trans hrank) (Nat.ne_of_lt hq)

/-- The β worker is sound (spec §8.2): at a term of positive β-rank `q`, the
worker `detStepAt q` performs one genuine `OneLambdaStep` — the congruence
regimes lift the descent by `OneLambdaStep.appL`/`appR`/`lamBody`, and the
root-contraction regime is `OneLambdaStep.beta`. The deterministic
strengthening of Lemma 12's β-step existence (Leivant III section 5, proof
paragraph (ii), p. 226). -/
theorem detStepAt_sound {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) {q : ℕ} (hq : 0 < q)
    (hrank : betaRedexRank t = q) : OneLambdaStep t (detStepAt q t) :=
  detStepAt_sound_aux q hq (Tm.size t) t le_rfl hrank

/-! ### Measure of the β worker

The rank half of the deterministic step's measure accounting (spec §8.3): the β
worker `detStepAt q` does not raise the β-rank above `q`. The congruence regimes
are inductions over the node equations; the root-contraction regime consumes the
substitution bound `betaRedexRank_instantiate₁_le` (note N2) with the arrow-order
bookkeeping `RType.ord σ < RType.ord (RType.arrow σ τ) = q`. The chain-decomposition
lemmas are the iterate-level counterparts of the 6.4.1 congruence node equations,
consumed by `det_cycle`'s structural induction (Task 6.4.4). -/

omit [LinearOrder A.B] in
/-- The combined measure invariant behind `betaRedexRank_detStepAt_le`, by strong
induction on the term size: the β worker `detStepAt q` does not raise the β-rank
above `q`, and it exposes an abstraction head only where the original term is
already an abstraction or its sort has order at most `q`. The head clause feeds the
`app'`-congruence β-rank bookkeeping, where a stepped function subterm turning into
an abstraction would otherwise create an uncontrolled top β-redex. -/
private theorem detStepAt_measure_aux (q : ℕ) :
    (N : ℕ) → ∀ {Γ : Binding.Ctx RType} {s : RType} (t : Binding.Tm (oneLambdaSig A) Γ s),
    Tm.size t ≤ N → betaRedexRank t ≤ q →
    betaRedexRank (detStepAt q t) ≤ q ∧
      (isLam (detStepAt q t) = true → isLam t = true ∨ RType.ord s ≤ q)
  | 0, _, _, t, hN, _ => absurd (Tm.one_le_size t) (by omega)
  | N + 1, Γ, s, t, hN, hrank => by
      rcases tm_cases t with ⟨x0, ht⟩ | ⟨o, hs0, args, ht⟩
      · subst ht
        exact ⟨by rw [detStepAt_var, betaRedexRank_var]; omega,
          fun h => by rw [detStepAt_var, isLam_var] at h; exact absurd h (by simp)⟩
      · cases o with
        | app σ τ =>
            have hs1 : τ = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.app σ τ) args := ht
            obtain ⟨f, x, hfx⟩ := op_app_inv args
            rw [hfx] at ht
            subst ht
            rw [size_app'] at hN
            have hf1 := Tm.one_le_size f
            have hx1 := Tm.one_le_size x
            have hrank2 := hrank
            rw [betaRedexRank_app'] at hrank2
            have hrf : betaRedexRank f ≤ q := by omega
            have hrx : betaRedexRank x ≤ q := by omega
            have htb : topBetaRank (app' f x) ≤ q := by omega
            rw [detStepAt_app']
            split_ifs with hf hx hguard
            · have ihf := detStepAt_measure_aux q N f (by omega) hrf
              refine ⟨?_, fun h => by rw [isLam_app'] at h; exact absurd h (by simp)⟩
              rw [betaRedexRank_app']
              refine max_le ?_ (max_le ihf.1 hrx)
              rw [topBetaRank_app']
              split_ifs with hlam
              · rcases ihf.2 hlam with hLf | hord
                · have hval : topBetaRank (app' f x) = RType.ord (RType.arrow σ τ) := by
                    simp [topBetaRank_app', hLf]
                  rw [hval] at htb; exact htb
                · exact hord
              · exact Nat.zero_le q
            · have ihx := detStepAt_measure_aux q N x (by omega) hrx
              refine ⟨?_, fun h => by rw [isLam_app'] at h; exact absurd h (by simp)⟩
              rw [betaRedexRank_app']
              refine max_le ?_ (max_le hrf ihx.1)
              rw [topBetaRank_app']
              have h2 := htb
              rw [topBetaRank_app'] at h2
              exact h2
            · obtain ⟨hLf, hordq⟩ := hguard
              obtain ⟨b, rfl⟩ := exists_lam'_of_isLam hLf
              rw [appReduct_lam']
              rw [RType.ord_arrow] at hordq
              refine ⟨?_, fun _ => Or.inr (by omega)⟩
              have hbound := betaRedexRank_instantiate₁_le x b
              have hbb : betaRedexRank b ≤ q := by
                rw [← betaRedexRank_lam' (σ := σ)]; exact hrf
              omega
            · exact ⟨by rw [betaRedexRank_app']; omega,
                fun h => by rw [isLam_app'] at h; exact absurd h (by simp)⟩
        | lam σ τ =>
            have hs1 : RType.arrow σ τ = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.lam σ τ) args := ht
            obtain ⟨b, hb⟩ := op_lam_inv args
            rw [hb] at ht
            subst ht
            rw [size_lam'] at hN
            have hrb : betaRedexRank b ≤ q := by rw [betaRedexRank_lam'] at hrank; exact hrank
            rw [detStepAt_lam']
            split_ifs with hbq
            · exact ⟨by
                rw [betaRedexRank_lam']
                exact (detStepAt_measure_aux q N b (by omega) hrb).1,
                fun _ => Or.inl (isLam_lam' _)⟩
            · exact ⟨by rw [betaRedexRank_lam']; exact hrb, fun _ => Or.inl (isLam_lam' b)⟩
        | con i =>
            have hs1 : RType.curried (List.replicate (A.ar i) RType.o) RType.o = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) args := ht
            subst ht
            refine ⟨hrank, fun h => ?_⟩
            have h' : isLam (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) args)
                = true := h
            simp [isLam, headTag_op] at h'
        | dstr j =>
            have hs1 : RType.arrow RType.o RType.o = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j) args := ht
            subst ht
            refine ⟨hrank, fun h => ?_⟩
            have h' : isLam (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j) args)
                = true := h
            simp [isLam, headTag_op] at h'
        | case =>
            have hs1 : RType.arrow RType.o
                (RType.curried (List.replicate A.numCtors RType.o) RType.o) = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case args := ht
            subst ht
            refine ⟨hrank, fun h => ?_⟩
            have h' : isLam (Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case args)
                = true := h
            simp [isLam, headTag_op] at h'

omit [LinearOrder A.B] in
/-- Rank non-increase of the β worker (spec §8.3, note N2): the β worker
`detStepAt q` does not raise the β-rank above `q`. The congruence regimes are
inductions over the node equations; the root-contraction regime consumes
`betaRedexRank_instantiate₁_le` with `RType.ord σ < RType.ord (RType.arrow σ τ)
= q`. Consumed by `det_cycle`'s rank-invariant (Task 6.4.4). -/
theorem betaRedexRank_detStepAt_le (q : ℕ) {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) (ht : betaRedexRank t ≤ q) :
    betaRedexRank (detStepAt q t) ≤ q :=
  (detStepAt_measure_aux q (Tm.size t) t le_rfl ht).1

omit [LinearOrder A.B] in
/-- Iterate-level chain decomposition at the `app'` function position (N1 item 2):
while the function subterm carries a rank-`q` redex along its own `detStepAt q`
chain, iterating the worker on the application equals the congruence image of
iterating on the function subterm. The `appL` counterpart of `detStepAt_app'`,
consumed by `det_cycle`'s structural induction (Task 6.4.4). -/
theorem detStepAt_iterate_appL (q : ℕ) {Γ : Binding.Ctx RType} {σ τ : RType} :
    (n : ℕ) → (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ)) →
    (x : Binding.Tm (oneLambdaSig A) Γ σ) →
    (∀ k, k < n → betaRedexRank ((detStepAt q)^[k] f) = q) →
    (detStepAt q)^[n] (OneLambda.app' f x) = OneLambda.app' ((detStepAt q)^[n] f) x
  | 0, _f, _x, _ => rfl
  | n + 1, f, x, hchain => by
      simp only [Function.iterate_succ_apply]
      have h0 : betaRedexRank f = q := hchain 0 (Nat.succ_pos n)
      rw [detStepAt_app', if_pos h0]
      exact detStepAt_iterate_appL q n (detStepAt q f) x
        (fun k hk => by
          rw [← Function.iterate_succ_apply]; exact hchain (k + 1) (Nat.succ_lt_succ hk))

omit [LinearOrder A.B] in
/-- Iterate-level chain decomposition at the `app'` argument position (N1 item 2):
while the function subterm carries no rank-`q` redex and the argument subterm
carries one along its own `detStepAt q` chain, iterating the worker on the
application equals the congruence image of iterating on the argument subterm. The
`appR` counterpart of `detStepAt_app'`, consumed by `det_cycle`'s structural
induction (Task 6.4.4). -/
theorem detStepAt_iterate_appR (q : ℕ) {Γ : Binding.Ctx RType} {σ τ : RType} :
    (n : ℕ) → (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ)) →
    (x : Binding.Tm (oneLambdaSig A) Γ σ) → betaRedexRank f ≠ q →
    (∀ k, k < n → betaRedexRank ((detStepAt q)^[k] x) = q) →
    (detStepAt q)^[n] (OneLambda.app' f x) = OneLambda.app' f ((detStepAt q)^[n] x)
  | 0, _f, _x, _, _ => rfl
  | n + 1, f, x, hf, hchain => by
      simp only [Function.iterate_succ_apply]
      have h0 : betaRedexRank x = q := hchain 0 (Nat.succ_pos n)
      rw [detStepAt_app', if_neg hf, if_pos h0]
      exact detStepAt_iterate_appR q n f (detStepAt q x) hf
        (fun k hk => by
          rw [← Function.iterate_succ_apply]; exact hchain (k + 1) (Nat.succ_lt_succ hk))

omit [LinearOrder A.B] in
/-- Iterate-level chain decomposition at the `lam'` body position (N1 item 2):
while the body carries a rank-`q` redex along its own `detStepAt q` chain,
iterating the worker on the abstraction equals the congruence image of iterating
on the body. The `lamBody` counterpart of `detStepAt_lam'`, consumed by
`det_cycle`'s structural induction (Task 6.4.4). -/
theorem detStepAt_iterate_lamBody (q : ℕ) {Γ : Binding.Ctx RType} {σ τ : RType} :
    (n : ℕ) → (b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ) →
    (∀ k, k < n → betaRedexRank ((detStepAt q)^[k] b) = q) →
    (detStepAt q)^[n] (OneLambda.lam' b) = OneLambda.lam' ((detStepAt q)^[n] b)
  | 0, _b, _ => rfl
  | n + 1, b, hchain => by
      simp only [Function.iterate_succ_apply]
      have h0 : betaRedexRank b = q := hchain 0 (Nat.succ_pos n)
      rw [detStepAt_lam', if_pos h0]
      exact detStepAt_iterate_lamBody q n (detStepAt q b)
        (fun k hk => by
          rw [← Function.iterate_succ_apply]; exact hchain (k + 1) (Nat.succ_lt_succ hk))

/-! ### Soundness of the ι worker

The ι half of the deterministic step's soundness (spec §8.2): at a term with an
ι-redex, the worker `detIotaStep` performs one genuine `OneLambdaStep`. The
congruence regimes lift the descent as in the β half; at the root-contraction
regime, `iotaSpine_inv_aux` and `conHeaded_o_inv` expose the saturated
destructor- or case-redex shape, the `collectSpine` computation lemmas below
evaluate `iotaContract` on that shape, and the matching
`OneLambdaStep.dstrHit`/`dstrMiss`/`case` rule concludes. -/

omit [LinearOrder A.B] in
/-- `collectSpine` transports along context and sort equalities by transporting
each collected argument. -/
private theorem collectSpine_cast {Γ Γ' : Binding.Ctx RType} {s s' : RType}
    (hΓ : Γ = Γ') (hs : s = s') (t : Binding.Tm (oneLambdaSig A) Γ s) :
    collectSpine (hs ▸ hΓ ▸ t)
      = (collectSpine t).map (fun p => (p.1, p.2.map (fun u => hΓ ▸ u))) := by
  subst hΓ; subst hs
  cases collectSpine t <;> simp

omit [LinearOrder A.B] in
/-- `collectSpine` commutes with the `Γ ++ [] = Γ` transport that `app'` applies
to its subterms, transporting each collected argument. -/
private theorem collectSpine_appendNil {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) :
    collectSpine ((List.append_nil Γ).symm ▸ t)
      = (collectSpine t).map (fun p =>
          (p.1, p.2.map (fun u => (List.append_nil Γ).symm ▸ u))) :=
  collectSpine_cast (List.append_nil Γ).symm rfl t

omit [LinearOrder A.B] in
/-- `collectSpine` at an application node with a base-sorted argument appends
that argument to the function subterm's spine. -/
private theorem collectSpine_app'_o {Γ : Binding.Ctx RType} {τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow RType.o τ))
    (x : Binding.Tm (oneLambdaSig A) Γ RType.o) :
    collectSpine (OneLambda.app' f x)
      = (collectSpine f).map (fun p => (p.1, p.2 ++ [x])) := by
  have e : collectSpine (OneLambda.app' f x)
      = (collectSpine ((List.append_nil Γ).symm ▸ f)).bind (fun p =>
          if h : RType.o = RType.o then
            some (p.1, p.2.map toG
              ++ [toG ((h ▸ ((List.append_nil Γ).symm ▸ x) : Binding.Tm (oneLambdaSig A)
                    (Γ ++ []) RType.o))])
          else some (p.1, p.2.map toG)) := rfl
  rw [e, collectSpine_appendNil]
  cases collectSpine f with
  | none => rfl
  | some p =>
      obtain ⟨op, l⟩ := p
      simp only [Option.map_some, Option.bind_some, dif_pos]
      refine congrArg some (congrArg (Prod.mk op) ?_)
      rw [List.map_map]
      have hcomp : toG ∘ (fun u : Binding.Tm (oneLambdaSig A) Γ RType.o =>
          (List.append_nil Γ).symm ▸ u) = id := funext fun u => toG_symm u
      rw [hcomp, List.map_id]
      exact congrArg (l ++ [·]) (toG_symm x)

omit [LinearOrder A.B] in
/-- `collectSpine` on a homogeneous base-sorted spine appends the spine's
arguments, in application order, to the head's spine. -/
private theorem collectSpine_replicateSpine {Γ : Binding.Ctx RType} {ρ : RType} :
    (n : ℕ) →
    (head : Binding.Tm (oneLambdaSig A) Γ (RType.curried (List.replicate n RType.o) ρ)) →
    (a : Fin n → Binding.Tm (oneLambdaSig A) Γ RType.o) →
    collectSpine (replicateSpine n RType.o head a)
      = (collectSpine head).map (fun p => (p.1, p.2 ++ List.ofFn a))
  | 0, head, _a => by
      change collectSpine head = _
      cases collectSpine head with
      | none => rfl
      | some p => simp
  | n + 1, head, a => by
      rw [replicateSpine_cons,
        collectSpine_replicateSpine n _ (fun i => a i.succ),
        collectSpine_app'_o (τ := RType.curried (List.replicate n RType.o) ρ)
          head (a ⟨0, n.succ_pos⟩)]
      have hfuse : ∀ z : Option (OneLambdaOp A × List (Binding.Tm (oneLambdaSig A) Γ RType.o)),
          (z.map (fun p => (p.1, p.2 ++ [a ⟨0, n.succ_pos⟩]))).map
              (fun p => (p.1, p.2 ++ List.ofFn (fun i => a i.succ)))
            = z.map (fun p => (p.1, p.2 ++ List.ofFn a)) := by
        intro z
        cases z with
        | none => rfl
        | some p =>
            obtain ⟨op, l⟩ := p
            simp [List.ofFn_succ, List.append_assoc]
      exact hfuse _

/-- `iotaContract` at the base sort is the base-sort contraction
`iotaContractO`. -/
private theorem iotaContract_o {Γ : Binding.Ctx RType}
    (t : Binding.Tm (oneLambdaSig A) Γ RType.o) : iotaContract t = iotaContractO t :=
  dif_pos rfl

/-- The enumeration position of the constructor at position `idx` is `idx`:
`List.idxOf` inverts `ctorAt` on the duplicate-free enumeration `ctorList`. -/
private theorem idxOf_ctorAt (idx : Fin A.numCtors) :
    (ctorList A).idxOf (ctorAt idx) = idx.val := by
  have hget : ctorAt idx = (ctorList A)[idx.val]'(by rw [ctorList_length]; exact idx.isLt) := by
    unfold ctorAt
    simp only [List.get_eq_getElem, Fin.val_cast]
  rw [hget]
  exact (Finset.sort_nodup _ _).idxOf_getElem idx.val _

omit [LinearOrder A.B] in
/-- The function subterm of an application is no larger than the application. -/
private theorem size_le_size_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) : Tm.size f ≤ Tm.size (app' f x) := by
  rw [size_app']; omega

omit [LinearOrder A.B] in
/-- The argument subterm of an application is strictly smaller than the
application. -/
private theorem size_arg_lt_size_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) : Tm.size x < Tm.size (app' f x) := by
  rw [size_app']; have := Tm.one_le_size f; omega

omit [LinearOrder A.B] in
/-- The head of a homogeneous spine is no larger than the spine. -/
private theorem size_head_le_replicateSpine {Γ : Binding.Ctx RType} {result : RType} :
    (n : ℕ) → (base : RType) →
    (head : Binding.Tm (oneLambdaSig A) Γ (RType.curried (List.replicate n base) result)) →
    (a : Fin n → Binding.Tm (oneLambdaSig A) Γ base) →
    Tm.size head ≤ Tm.size (replicateSpine n base head a)
  | 0, _base, _head, _a => le_refl _
  | n + 1, base, head, a => by
      rw [replicateSpine_cons]
      exact le_trans (size_le_size_app' head (a ⟨0, n.succ_pos⟩))
        (size_head_le_replicateSpine n base _ _)

omit [LinearOrder A.B] in
/-- Every argument of a homogeneous spine is strictly smaller than the spine. -/
private theorem size_arg_lt_replicateSpine {Γ : Binding.Ctx RType} {result : RType} :
    (n : ℕ) → (base : RType) →
    (head : Binding.Tm (oneLambdaSig A) Γ (RType.curried (List.replicate n base) result)) →
    (a : Fin n → Binding.Tm (oneLambdaSig A) Γ base) → (i : Fin n) →
    Tm.size (a i) < Tm.size (replicateSpine n base head a)
  | n + 1, base, head, a, ⟨0, _⟩ => by
      rw [replicateSpine_cons]
      exact lt_of_lt_of_le (size_arg_lt_size_app' head (a ⟨0, n.succ_pos⟩))
        (size_head_le_replicateSpine n base _ _)
  | n + 1, base, head, a, ⟨iv + 1, hi⟩ => by
      rw [replicateSpine_cons]
      exact size_arg_lt_replicateSpine n base _ (fun i => a i.succ)
        ⟨iv, Nat.lt_of_succ_lt_succ hi⟩

omit [LinearOrder A.B] in
/-- The β-rank of the function subterm of an application is bounded by the
application's β-rank. -/
private theorem betaRedexRank_le_betaRedexRank_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) :
    betaRedexRank f ≤ betaRedexRank (app' f x) := by
  rw [betaRedexRank_app']; omega

omit [LinearOrder A.B] in
/-- The β-rank of the argument subterm of an application is bounded by the
application's β-rank. -/
private theorem betaRedexRank_arg_le_betaRedexRank_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) :
    betaRedexRank x ≤ betaRedexRank (app' f x) := by
  rw [betaRedexRank_app']; omega

omit [LinearOrder A.B] in
/-- The β-rank of the head of a homogeneous spine is bounded by the spine's
β-rank. -/
private theorem betaRedexRank_head_le_replicateSpine {Γ : Binding.Ctx RType} {result : RType} :
    (n : ℕ) → (base : RType) →
    (head : Binding.Tm (oneLambdaSig A) Γ (RType.curried (List.replicate n base) result)) →
    (a : Fin n → Binding.Tm (oneLambdaSig A) Γ base) →
    betaRedexRank head ≤ betaRedexRank (replicateSpine n base head a)
  | 0, _base, _head, _a => le_refl _
  | n + 1, base, head, a => by
      rw [replicateSpine_cons]
      exact le_trans (betaRedexRank_le_betaRedexRank_app' head (a ⟨0, n.succ_pos⟩))
        (betaRedexRank_head_le_replicateSpine n base _ _)

omit [LinearOrder A.B] in
/-- The β-rank of every argument of a homogeneous spine is bounded by the
spine's β-rank. -/
private theorem betaRedexRank_arg_le_replicateSpine {Γ : Binding.Ctx RType} {result : RType} :
    (n : ℕ) → (base : RType) →
    (head : Binding.Tm (oneLambdaSig A) Γ (RType.curried (List.replicate n base) result)) →
    (a : Fin n → Binding.Tm (oneLambdaSig A) Γ base) → (i : Fin n) →
    betaRedexRank (a i) ≤ betaRedexRank (replicateSpine n base head a)
  | n + 1, base, head, a, ⟨0, _⟩ => by
      rw [replicateSpine_cons]
      exact le_trans (betaRedexRank_arg_le_betaRedexRank_app' head (a ⟨0, n.succ_pos⟩))
        (betaRedexRank_head_le_replicateSpine n base _ _)
  | n + 1, base, head, a, ⟨iv + 1, hi⟩ => by
      rw [replicateSpine_cons]
      exact betaRedexRank_arg_le_replicateSpine n base _ (fun i => a i.succ)
        ⟨iv, Nat.lt_of_succ_lt_succ hi⟩

/-- The ι-contraction at a saturated ι-redex is a genuine `OneLambdaStep` that
strictly decreases the size and does not raise the β-rank: the inversion of
`topIota` exposes the destructor- or case-redex shape, on which `iotaContract`
computes the matching `OneLambdaStep.dstrHit`/`dstrMiss`/`case` reduct — a proper
constituent of the redex, hence smaller and of no greater β-rank. -/
private theorem iotaContract_measures_of_topIota {Γ : Binding.Ctx RType} {s : RType}
    {t : Binding.Tm (oneLambdaSig A) Γ s} (htop : topIota t = true) :
    OneLambdaStep t (iotaContract t) ∧ Tm.size (iotaContract t) < Tm.size t ∧
      betaRedexRank (iotaContract t) ≤ betaRedexRank t := by
  have hsh : s.shape = RTypeShape.o := by
    by_contra hcon
    unfold topIota at htop
    rw [if_neg hcon] at htop
    exact Bool.noConfusion htop
  have hso := eq_o_of_shape_o hsh
  subst hso
  have hio : iotaSpine t = true := by
    unfold topIota at htop
    rwa [if_pos hsh] at htop
  rw [iotaContract_o]
  rcases iotaSpine_inv_aux (Tm.size t) t le_rfl hio with
    ⟨j, w, _, hcw, htEq⟩ | ⟨n, k, hnk, hsB, _, scrut, b, hcs, htEq⟩
  · -- destructor redex
    replace htEq : t = OneLambda.app'
        (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j) (fun l => l.elim0)) w := htEq
    obtain ⟨i, a, hwEq⟩ := conHeaded_o_inv hcw
    rw [hwEq] at htEq
    subst htEq
    have hscoll : collectSpine (replicateSpine (A.ar i) RType.o
        (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) (fun l => l.elim0)) a)
        = some (OneLambdaOp.con i, List.ofFn a) := by
      rw [collectSpine_replicateSpine]
      rfl
    have hcoll : collectSpine (OneLambda.app'
        (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j) (fun l => l.elim0))
        (replicateSpine (A.ar i) RType.o
          (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) (fun l => l.elim0)) a))
        = some (OneLambdaOp.dstr j, [replicateSpine (A.ar i) RType.o
            (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) (fun l => l.elim0)) a]) := by
      rw [collectSpine_app'_o]
      rfl
    have hcontr : iotaContractO (OneLambda.app'
        (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j) (fun l => l.elim0))
        (replicateSpine (A.ar i) RType.o
          (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) (fun l => l.elim0)) a))
        = dstrReduct j (replicateSpine (A.ar i) RType.o
            (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) (fun l => l.elim0)) a) := by
      unfold iotaContractO
      rw [hcoll]
    rw [hcontr]
    rcases Nat.lt_or_ge j.val (A.ar i) with hj | hj
    · have hred : dstrReduct j (replicateSpine (A.ar i) RType.o
          (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) (fun l => l.elim0)) a)
          = a ⟨j.val, hj⟩ := by
        unfold dstrReduct
        simp only [hscoll, List.getElem?_ofFn]
        rw [dif_pos hj]
      rw [hred]
      refine ⟨OneLambdaStep.dstrHit j hj a, ?_, ?_⟩
      · exact lt_trans (size_arg_lt_replicateSpine (A.ar i) RType.o _ a ⟨j.val, hj⟩)
          (size_arg_lt_size_app' _ _)
      · exact le_trans (betaRedexRank_arg_le_replicateSpine (A.ar i) RType.o _ a ⟨j.val, hj⟩)
          (betaRedexRank_arg_le_betaRedexRank_app' _ _)
    · have hred : dstrReduct j (replicateSpine (A.ar i) RType.o
          (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) (fun l => l.elim0)) a)
          = replicateSpine (A.ar i) RType.o
              (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) (fun l => l.elim0)) a := by
        unfold dstrReduct
        simp only [hscoll, List.getElem?_ofFn]
        rw [dif_neg (by omega)]
      rw [hred]
      refine ⟨OneLambdaStep.dstrMiss j hj a, ?_, ?_⟩
      · exact size_arg_lt_size_app' _ _
      · exact betaRedexRank_arg_le_betaRedexRank_app' _ _
  · -- case redex
    have hk : k = 0 := eq_zero_of_o_eq_curried hsB
    subst hk
    have hn : A.numCtors = n := hnk
    subst hn
    replace htEq : t = replicateSpine A.numCtors RType.o
        (OneLambda.app'
          (Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case (fun l => l.elim0)) scrut)
        b := htEq
    obtain ⟨i, a, hscrEq⟩ := conHeaded_o_inv hcs
    obtain ⟨idx, rfl⟩ := exists_ctorAt_eq i
    rw [hscrEq] at htEq
    subst htEq
    have hscoll : collectSpine (replicateSpine (A.ar (ctorAt idx)) RType.o
        (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con (ctorAt idx))
          (fun l => l.elim0)) a)
        = some (OneLambdaOp.con (ctorAt idx), List.ofFn a) := by
      rw [collectSpine_replicateSpine]
      rfl
    have hc1 : collectSpine (OneLambda.app'
        (Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case (fun l => l.elim0))
        (replicateSpine (A.ar (ctorAt idx)) RType.o
          (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con (ctorAt idx))
            (fun l => l.elim0)) a))
        = some (OneLambdaOp.case, [replicateSpine (A.ar (ctorAt idx)) RType.o
            (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con (ctorAt idx))
              (fun l => l.elim0)) a]) := by
      rw [collectSpine_app'_o]
      rfl
    have hc2 : collectSpine (replicateSpine A.numCtors RType.o
        (OneLambda.app'
          (Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case (fun l => l.elim0))
          (replicateSpine (A.ar (ctorAt idx)) RType.o
            (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con (ctorAt idx))
              (fun l => l.elim0)) a))
        b)
        = some (OneLambdaOp.case, replicateSpine (A.ar (ctorAt idx)) RType.o
            (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con (ctorAt idx))
              (fun l => l.elim0)) a :: List.ofFn b) := by
      rw [collectSpine_replicateSpine, hc1]
      rfl
    have hcontr : iotaContractO (replicateSpine A.numCtors RType.o
        (OneLambda.app'
          (Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case (fun l => l.elim0))
          (replicateSpine (A.ar (ctorAt idx)) RType.o
            (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con (ctorAt idx))
              (fun l => l.elim0)) a))
        b)
        = caseReduct (replicateSpine (A.ar (ctorAt idx)) RType.o
            (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con (ctorAt idx))
              (fun l => l.elim0)) a) (List.ofFn b) := by
      unfold iotaContractO
      rw [hc2]
    have hred : caseReduct (replicateSpine (A.ar (ctorAt idx)) RType.o
        (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con (ctorAt idx))
          (fun l => l.elim0)) a) (List.ofFn b) = b idx := by
      unfold caseReduct
      simp only [hscoll, idxOf_ctorAt, List.getElem?_ofFn]
      rw [dif_pos idx.isLt]
    rw [hcontr, hred]
    refine ⟨OneLambdaStep.case idx a b, ?_, ?_⟩
    · exact size_arg_lt_replicateSpine A.numCtors RType.o _ b idx
    · exact betaRedexRank_arg_le_replicateSpine A.numCtors RType.o _ b idx

omit [LinearOrder A.B] in
/-- A term whose sort-gated ι-redex detector `topIota` is set has the base
object sort `o`: the detector's result-sort gate forces the nullary shape,
which determines the sort. -/
theorem eq_o_of_topIota {Γ : Binding.Ctx RType} {s : RType}
    {t : Binding.Tm (oneLambdaSig A) Γ s} (htop : topIota t = true) : s = RType.o := by
  refine eq_o_of_shape_o ?_
  by_contra hcon
  unfold topIota at htop
  rw [if_neg hcon] at htop
  exact Bool.noConfusion htop

/-- The ι-contraction cases at a saturated ι-redex (Leivant III section 4.2,
p. 223): a base-sorted term whose sort-gated ι-redex detector `topIota` is set
is either a destructor redex — a destructor applied to a constructor word —
with `iotaContract` selecting the hit argument (or returning the scrutinee on a
miss), or a saturated case redex with `iotaContract` selecting the branch at
the scrutinee constructor's enumeration position. The shape-and-value
inversion of `iotaContract` consumed by the code-normalizer mirror of the ι
worker; the shape halves re-package `iotaSpine_inv_aux` and `conHeaded_o_inv`,
and the value halves evaluate `iotaContract` on the exposed spine through the
`collectSpine` computation lemmas. -/
theorem iotaContract_cases_of_topIota {Γ : Binding.Ctx RType}
    {t : Binding.Tm (oneLambdaSig A) Γ RType.o} (htop : topIota t = true) :
    (∃ (j : Fin A.maxArity) (i : A.B)
      (a : Fin (A.ar i) → Binding.Tm (oneLambdaSig A) Γ RType.o),
      t = OneLambda.app'
          (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j) (fun l => l.elim0))
          (replicateSpine (A.ar i) RType.o
            (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) (fun l => l.elim0)) a) ∧
      iotaContract t = (if h : j.val < A.ar i then a ⟨j.val, h⟩
        else replicateSpine (A.ar i) RType.o
          (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) (fun l => l.elim0)) a)) ∨
    (∃ (idx : Fin A.numCtors)
      (a : Fin (A.ar (ctorAt idx)) → Binding.Tm (oneLambdaSig A) Γ RType.o)
      (b : Fin A.numCtors → Binding.Tm (oneLambdaSig A) Γ RType.o),
      t = replicateSpine A.numCtors RType.o
          (OneLambda.app'
            (Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case (fun l => l.elim0))
            (replicateSpine (A.ar (ctorAt idx)) RType.o
              (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con (ctorAt idx))
                (fun l => l.elim0)) a)) b ∧
      iotaContract t = b idx) := by
  have hio : iotaSpine t = true := by
    unfold topIota at htop
    rwa [if_pos (show RType.o.shape = RTypeShape.o from rfl)] at htop
  rcases iotaSpine_inv_aux (Tm.size t) t le_rfl hio with
    ⟨j, w, _, hcw, htEq⟩ | ⟨n, k, hnk, hsB, _, scrut, b, hcs, htEq⟩
  · -- destructor redex
    replace htEq : t = OneLambda.app'
        (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j) (fun l => l.elim0)) w := htEq
    obtain ⟨i, a, hwEq⟩ := conHeaded_o_inv hcw
    rw [hwEq] at htEq
    refine Or.inl ⟨j, i, a, htEq, ?_⟩
    subst htEq
    rw [iotaContract_o]
    have hscoll : collectSpine (replicateSpine (A.ar i) RType.o
        (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) (fun l => l.elim0)) a)
        = some (OneLambdaOp.con i, List.ofFn a) := by
      rw [collectSpine_replicateSpine]
      rfl
    have hcoll : collectSpine (OneLambda.app'
        (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j) (fun l => l.elim0))
        (replicateSpine (A.ar i) RType.o
          (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) (fun l => l.elim0)) a))
        = some (OneLambdaOp.dstr j, [replicateSpine (A.ar i) RType.o
            (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) (fun l => l.elim0)) a]) := by
      rw [collectSpine_app'_o]
      rfl
    have hcontr : iotaContractO (OneLambda.app'
        (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j) (fun l => l.elim0))
        (replicateSpine (A.ar i) RType.o
          (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) (fun l => l.elim0)) a))
        = dstrReduct j (replicateSpine (A.ar i) RType.o
            (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) (fun l => l.elim0)) a) := by
      unfold iotaContractO
      rw [hcoll]
    rw [hcontr]
    rcases Nat.lt_or_ge j.val (A.ar i) with hj | hj
    · rw [dif_pos hj]
      unfold dstrReduct
      simp only [hscoll, List.getElem?_ofFn]
      rw [dif_pos hj]
    · rw [dif_neg (by omega)]
      unfold dstrReduct
      simp only [hscoll, List.getElem?_ofFn]
      rw [dif_neg (by omega)]
  · -- case redex
    have hk : k = 0 := eq_zero_of_o_eq_curried hsB
    subst hk
    have hn : A.numCtors = n := hnk
    subst hn
    replace htEq : t = replicateSpine A.numCtors RType.o
        (OneLambda.app'
          (Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case (fun l => l.elim0)) scrut)
        b := htEq
    obtain ⟨i, a, hscrEq⟩ := conHeaded_o_inv hcs
    obtain ⟨idx, rfl⟩ := exists_ctorAt_eq i
    rw [hscrEq] at htEq
    refine Or.inr ⟨idx, a, b, htEq, ?_⟩
    subst htEq
    rw [iotaContract_o]
    have hscoll : collectSpine (replicateSpine (A.ar (ctorAt idx)) RType.o
        (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con (ctorAt idx))
          (fun l => l.elim0)) a)
        = some (OneLambdaOp.con (ctorAt idx), List.ofFn a) := by
      rw [collectSpine_replicateSpine]
      rfl
    have hc1 : collectSpine (OneLambda.app'
        (Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case (fun l => l.elim0))
        (replicateSpine (A.ar (ctorAt idx)) RType.o
          (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con (ctorAt idx))
            (fun l => l.elim0)) a))
        = some (OneLambdaOp.case, [replicateSpine (A.ar (ctorAt idx)) RType.o
            (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con (ctorAt idx))
              (fun l => l.elim0)) a]) := by
      rw [collectSpine_app'_o]
      rfl
    have hc2 : collectSpine (replicateSpine A.numCtors RType.o
        (OneLambda.app'
          (Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case (fun l => l.elim0))
          (replicateSpine (A.ar (ctorAt idx)) RType.o
            (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con (ctorAt idx))
              (fun l => l.elim0)) a))
        b)
        = some (OneLambdaOp.case, replicateSpine (A.ar (ctorAt idx)) RType.o
            (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con (ctorAt idx))
              (fun l => l.elim0)) a :: List.ofFn b) := by
      rw [collectSpine_replicateSpine, hc1]
      rfl
    have hcontr : iotaContractO (replicateSpine A.numCtors RType.o
        (OneLambda.app'
          (Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case (fun l => l.elim0))
          (replicateSpine (A.ar (ctorAt idx)) RType.o
            (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con (ctorAt idx))
              (fun l => l.elim0)) a))
        b)
        = caseReduct (replicateSpine (A.ar (ctorAt idx)) RType.o
            (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con (ctorAt idx))
              (fun l => l.elim0)) a) (List.ofFn b) := by
      unfold iotaContractO
      rw [hc2]
    rw [hcontr]
    unfold caseReduct
    simp only [hscoll, idxOf_ctorAt, List.getElem?_ofFn]
    rw [dif_pos idx.isLt]

/-- The descent induction behind `detIotaStep_sound`, by strong induction on
the term size: at every node carrying an ι-redex, one of the `detIotaStepOp`
guard regimes applies and yields a `OneLambdaStep` onto the worker's image. -/
private theorem detIotaStep_sound_aux :
    (N : ℕ) → ∀ {Γ : Binding.Ctx RType} {s : RType} (t : Binding.Tm (oneLambdaSig A) Γ s),
    Tm.size t ≤ N → hasIota t = true → OneLambdaStep t (detIotaStep t)
  | 0, _, _, t, hN, _ => absurd (Tm.one_le_size t) (by omega)
  | N + 1, Γ, s, t, hN, h => by
      rcases tm_cases t with ⟨x0, ht⟩ | ⟨o, hs0, args, ht⟩
      · subst ht
        rw [hasIota_var] at h
        exact Bool.noConfusion h
      · cases o with
        | app σ τ =>
            have hs1 : τ = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.app σ τ) args :=
              ht
            obtain ⟨f, x, hfx⟩ := op_app_inv args
            rw [hfx] at ht
            subst ht
            rw [size_app'] at hN
            rw [hasIota_app'] at h
            have hf1 := Tm.one_le_size f
            have hx1 := Tm.one_le_size x
            rw [detIotaStep_app']
            split_ifs with hf hx htop
            · exact OneLambdaStep.appL x (detIotaStep_sound_aux N f (by omega) hf)
            · exact OneLambdaStep.appR f (detIotaStep_sound_aux N x (by omega) hx)
            · exact (iotaContract_measures_of_topIota htop).1
            · exfalso
              rw [Bool.or_eq_true, Bool.or_eq_true] at h
              rcases h with (h1 | h2) | h3
              · exact htop h1
              · exact hf h2
              · exact hx h3
        | lam σ τ =>
            have hs1 : RType.arrow σ τ = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.lam σ τ) args :=
              ht
            obtain ⟨b, hb⟩ := op_lam_inv args
            rw [hb] at ht
            subst ht
            rw [size_lam'] at hN
            rw [hasIota_lam'] at h
            rw [detIotaStep_lam', if_pos h]
            exact OneLambdaStep.lamBody (detIotaStep_sound_aux N b (by omega) h)
        | con i =>
            have hs1 : RType.curried (List.replicate (A.ar i) RType.o) RType.o = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) args :=
              ht
            subst ht
            have hfalse : hasIota (Binding.Tm.op (S := oneLambdaSig A) (Γ := Γ)
                (OneLambdaOp.con i) args) = false := by
              rw [hasIota_op]
              simp only [topIota, iotaSpine_op, iotaSpineOp, ite_self, Bool.false_or]
              rfl
            exact Bool.noConfusion (hfalse.symm.trans h)
        | dstr j =>
            have hs1 : RType.arrow RType.o RType.o = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j) args :=
              ht
            subst ht
            have hfalse : hasIota (Binding.Tm.op (S := oneLambdaSig A) (Γ := Γ)
                (OneLambdaOp.dstr j) args) = false := by
              rw [hasIota_op]
              simp only [topIota, iotaSpine_op, iotaSpineOp, ite_self, Bool.false_or]
              rfl
            exact Bool.noConfusion (hfalse.symm.trans h)
        | case =>
            have hs1 : RType.arrow RType.o
                (RType.curried (List.replicate A.numCtors RType.o) RType.o) = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case args := ht
            subst ht
            have hfalse : hasIota (Binding.Tm.op (S := oneLambdaSig A) (Γ := Γ)
                OneLambdaOp.case args) = false := by
              rw [hasIota_op]
              simp only [topIota, iotaSpine_op, iotaSpineOp, ite_self, Bool.false_or]
              rfl
            exact Bool.noConfusion (hfalse.symm.trans h)

/-- The ι worker is sound (spec §8.2): at a term carrying an ι-redex, the
worker `detIotaStep` performs one genuine `OneLambdaStep` — the congruence
regimes lift the descent by `OneLambdaStep.appL`/`appR`/`lamBody`, and the
root-contraction regime is the matching
`OneLambdaStep.dstrHit`/`dstrMiss`/`case` rule. The deterministic
strengthening of Lemma 12's ι-step existence `exists_iota_step_of_hasIota`
(Leivant III section 5, proof paragraph (iii), p. 226). -/
theorem detIotaStep_sound {Γ : Binding.Ctx RType} {s : RType}
    {t : Binding.Tm (oneLambdaSig A) Γ s} (h : hasIota t = true) :
    OneLambdaStep t (detIotaStep t) :=
  detIotaStep_sound_aux (Tm.size t) t le_rfl h

/-- The deterministic step is sound (spec §8.2): at every non-`Normal` term it
performs one genuine `OneLambdaStep` onto its own image — the β worker's step
when the β-rank is positive, the ι worker's step otherwise. Together with
`detStep_normal` this realizes Lemma 12's reduction strategy (Leivant III
section 5, proof paragraphs (ii) and (iii), p. 226) as a stateless function. -/
theorem detStep_sound {Γ s} (t : Binding.Tm (oneLambdaSig A) Γ s)
    (h : ¬ Normal t) : OneLambdaStep t (detStep t) := by
  rw [detStep_eq]
  by_cases hb : 0 < betaRedexRank t
  · rw [if_pos hb]
    exact detStepAt_sound t hb rfl
  · rw [if_neg hb]
    have hi : hasIota t = true := by
      by_contra hcon
      exact h ((normal_iff t).mpr ⟨by omega, by simpa using hcon⟩)
    rw [if_pos hi]
    exact detIotaStep_sound hi

/-! ### Measure of the ι worker

The measure accounting for the ι worker (spec §8.3): on a β-normal term the worker
`detIotaStep` preserves β-normality, and on a β-normal term carrying an ι-redex it
strictly decreases the size. The congruence regimes are inductions over the node
equations; the root-contraction regime consumes `iotaContract_measures_of_topIota`.
The β-normality-preservation content mirrors the `exists_iota_step_of_hasIota`
layer of `Normalization.lean`; the deterministic reduct is bounded by the local
`iotaContract_measures_of_topIota` variant. -/

/-- The combined measure invariant behind `betaRedexRank_detIotaStep` and
`size_detIotaStep_lt`, by strong induction on the term size: on a β-normal term the
ι worker preserves β-normality, keeps the abstraction head where the sort is not
the base object sort, and strictly decreases the size whenever an ι-redex is
present. The head clause feeds the `app'`-congruence β-rank bookkeeping. -/
private theorem detIotaStep_measure_aux :
    (N : ℕ) → ∀ {Γ : Binding.Ctx RType} {s : RType} (t : Binding.Tm (oneLambdaSig A) Γ s),
    Tm.size t ≤ N → betaRedexRank t = 0 →
    betaRedexRank (detIotaStep t) = 0 ∧
      (s.shape ≠ RTypeShape.o → isLam (detIotaStep t) = isLam t) ∧
      (hasIota t = true → Tm.size (detIotaStep t) < Tm.size t)
  | 0, _, _, t, hN, _ => absurd (Tm.one_le_size t) (by omega)
  | N + 1, Γ, s, t, hN, hβ => by
      rcases tm_cases t with ⟨x0, ht⟩ | ⟨o, hs0, args, ht⟩
      · subst ht
        exact ⟨by rw [detIotaStep_var, betaRedexRank_var],
          fun _ => by rw [detIotaStep_var],
          fun h => by rw [hasIota_var] at h; exact absurd h (by simp)⟩
      · cases o with
        | app σ τ =>
            have hs1 : τ = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.app σ τ) args := ht
            obtain ⟨f, x, hfx⟩ := op_app_inv args
            rw [hfx] at ht
            subst ht
            rw [size_app'] at hN
            have hf1 := Tm.one_le_size f
            have hx1 := Tm.one_le_size x
            have hβ2 := hβ
            rw [betaRedexRank_app'] at hβ2
            have hrf : betaRedexRank f = 0 := by omega
            have hrx : betaRedexRank x = 0 := by omega
            have htbf : topBetaRank (app' f x) = 0 := by omega
            have hLf : isLam f = false := by
              cases hh : isLam f with
              | false => rfl
              | true =>
                  rw [topBetaRank_app', hh, if_pos rfl] at htbf
                  have := RType.one_le_ord_arrow σ τ
                  omega
            rw [detIotaStep_app']
            split_ifs with hif hix htop
            · have ihf := detIotaStep_measure_aux N f (by omega) hrf
              have hLf' : isLam (detIotaStep f) = false := (ihf.2.1 (by simp)).trans hLf
              refine ⟨?_, fun _ => rfl, fun _ => ?_⟩
              · have h1 : topBetaRank (app' (detIotaStep f) x) = 0 := by
                  simp [topBetaRank_app', hLf']
                rw [betaRedexRank_app', h1, ihf.1, hrx]; simp
              · rw [size_app', size_app']
                have := ihf.2.2 hif
                omega
            · have ihx := detIotaStep_measure_aux N x (by omega) hrx
              refine ⟨?_, fun _ => rfl, fun _ => ?_⟩
              · have h1 : topBetaRank (app' f (detIotaStep x)) = 0 := by
                  simp [topBetaRank_app', hLf]
                rw [betaRedexRank_app', h1, ihx.1, hrf]; simp
              · rw [size_app', size_app']
                have := ihx.2.2 hix
                omega
            · have hshape : τ.shape = RTypeShape.o := by
                by_contra hc
                unfold topIota at htop
                rw [if_neg hc] at htop
                exact Bool.noConfusion htop
              have hmeas := iotaContract_measures_of_topIota htop
              refine ⟨?_, fun hcon => absurd hshape hcon, fun _ => hmeas.2.1⟩
              have := hmeas.2.2
              rw [hβ] at this
              exact Nat.le_zero.mp this
            · refine ⟨hβ, fun _ => rfl, fun hh => ?_⟩
              rw [hasIota_app', Bool.or_eq_true, Bool.or_eq_true] at hh
              rcases hh with (hh | hh) | hh
              · exact absurd hh htop
              · exact absurd hh hif
              · exact absurd hh hix
        | lam σ τ =>
            have hs1 : RType.arrow σ τ = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.lam σ τ) args := ht
            obtain ⟨b, hb⟩ := op_lam_inv args
            rw [hb] at ht
            subst ht
            rw [size_lam'] at hN
            have hrb : betaRedexRank b = 0 := by rw [betaRedexRank_lam'] at hβ; exact hβ
            rw [detIotaStep_lam']
            split_ifs with hib
            · have ihb := detIotaStep_measure_aux N b (by omega) hrb
              refine ⟨by rw [betaRedexRank_lam']; exact ihb.1, fun _ => rfl, fun _ => ?_⟩
              rw [size_lam', size_lam']
              exact Nat.add_lt_add_left (ihb.2.2 hib) 1
            · refine ⟨by rw [betaRedexRank_lam']; exact hrb, fun _ => rfl, fun hh => ?_⟩
              rw [hasIota_lam'] at hh
              exact absurd hh hib
        | con i =>
            have hs1 : RType.curried (List.replicate (A.ar i) RType.o) RType.o = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) args := ht
            subst ht
            refine ⟨hβ, fun _ => rfl, fun hh => ?_⟩
            have hfalse : hasIota (Binding.Tm.op (S := oneLambdaSig A) (Γ := Γ)
                (OneLambdaOp.con i) args) = false := by
              rw [hasIota_op]
              simp only [topIota, iotaSpine_op, iotaSpineOp, ite_self, Bool.false_or]
              rfl
            exact absurd (hfalse.symm.trans hh) (by simp)
        | dstr j =>
            have hs1 : RType.arrow RType.o RType.o = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j) args := ht
            subst ht
            refine ⟨hβ, fun _ => rfl, fun hh => ?_⟩
            have hfalse : hasIota (Binding.Tm.op (S := oneLambdaSig A) (Γ := Γ)
                (OneLambdaOp.dstr j) args) = false := by
              rw [hasIota_op]
              simp only [topIota, iotaSpine_op, iotaSpineOp, ite_self, Bool.false_or]
              rfl
            exact absurd (hfalse.symm.trans hh) (by simp)
        | case =>
            have hs1 : RType.arrow RType.o
                (RType.curried (List.replicate A.numCtors RType.o) RType.o) = s := hs0
            subst hs1
            replace ht : t = Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case args := ht
            subst ht
            refine ⟨hβ, fun _ => rfl, fun hh => ?_⟩
            have hfalse : hasIota (Binding.Tm.op (S := oneLambdaSig A) (Γ := Γ)
                OneLambdaOp.case args) = false := by
              rw [hasIota_op]
              simp only [topIota, iotaSpine_op, iotaSpineOp, ite_self, Bool.false_or]
              rfl
            exact absurd (hfalse.symm.trans hh) (by simp)

/-- β-normality preservation of the ι worker (spec §8.3): the ι worker
`detIotaStep` keeps a β-normal term (β-rank `0`) β-normal. The congruence regimes
are inductions over the node equations; the root-contraction regime consumes
`iotaContract_measures_of_topIota`. Consumed by `det_cycle`'s ι-phase invariant
(Task 6.4.4). -/
theorem betaRedexRank_detIotaStep {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) (h : betaRedexRank t = 0) :
    betaRedexRank (detIotaStep t) = 0 :=
  (detIotaStep_measure_aux (Tm.size t) t le_rfl h).1

/-- Strict size decrease of the ι worker (spec §8.3): on a β-normal term carrying
an ι-redex, the ι worker `detIotaStep` strictly decreases the size. Each ι reduct
is a proper constituent of its redex (`dstrHit`, `case`) or drops the destructor
node (`dstrMiss`), so the size strictly falls. Consumed by `det_cycle`'s ι-phase
termination (Task 6.4.4). -/
theorem size_detIotaStep_lt {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) (h : betaRedexRank t = 0)
    (hi : hasIota t = true) : Tm.size (detIotaStep t) < Tm.size t :=
  (detIotaStep_measure_aux (Tm.size t) t le_rfl h).2.2 hi

/-! ### The deterministic iteration

The `n`-fold iterate of `detStep` (spec §4.3; plan decision P6): every prefix of
the iteration is a genuine reduction sequence (`detIter_reduces`), a `Normal`
term is a fixpoint (`detIter_normal_stable`), and iterating past a normal point
is absorbed (`detIter_eq_of_normal`). The dispatch bridges expose which worker a
`detStep` application runs: `detStepAt` at positive β-rank, `detIotaStep` at
β-rank `0` with an ι-redex. -/

/-- `n`-fold iteration of `detStep` (spec §4.3; plan decision P6). -/
def detIter (n : ℕ) {Γ s} :
    Binding.Tm (oneLambdaSig A) Γ s → Binding.Tm (oneLambdaSig A) Γ s :=
  detStep^[n]

/-- `detIter` at count `0` is the identity. -/
@[simp]
theorem detIter_zero {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) : detIter 0 t = t := rfl

/-- Peeling the first step of the iteration: `detIter (n + 1)` runs one `detStep`
and then iterates on its image. -/
theorem detIter_succ (n : ℕ) {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) :
    detIter (n + 1) t = detIter n (detStep t) :=
  Function.iterate_succ_apply detStep n t

/-- Peeling the last step of the iteration: `detIter (n + 1)` iterates and then
runs one further `detStep`. -/
theorem detIter_succ' (n : ℕ) {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) :
    detIter (n + 1) t = detStep (detIter n t) :=
  Function.iterate_succ_apply' detStep n t

/-- Splitting the iteration count: `detIter (m + n)` iterates `n` times and then
`m` further times. -/
theorem detIter_add (m n : ℕ) {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) :
    detIter (m + n) t = detIter m (detIter n t) :=
  Function.iterate_add_apply detStep m n t

/-- The deterministic iteration is a reduction sequence (spec §4.3): every term
reduces, under `Relation.ReflTransGen OneLambdaStep`, to its `n`-fold `detStep`
image. Each iteration step either performs a genuine `OneLambdaStep`
(`detStep_sound`) or fixes an already-`Normal` term (`detStep_normal`). -/
theorem detIter_reduces (n : ℕ) {Γ s}
    (t : Binding.Tm (oneLambdaSig A) Γ s) :
    Relation.ReflTransGen OneLambdaStep t (detIter n t) := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
      rw [detIter_succ']
      by_cases h : Normal (detIter n t)
      · rw [detStep_normal h]
        exact ih
      · exact ih.tail (detStep_sound _ h)

/-- A `Normal` term is a fixpoint of the deterministic iteration at every
count. -/
theorem detIter_normal_stable (n : ℕ) {Γ s}
    {t : Binding.Tm (oneLambdaSig A) Γ s} (h : Normal t) : detIter n t = t := by
  induction n with
  | zero => rfl
  | succ n ih => rw [detIter_succ', ih, detStep_normal h]

/-- Overshoot absorption: once the iteration reaches a `Normal` term at count
`k`, every larger count `n` returns the same term. Splits `n = (n - k) + k` by
`detIter_add` and fixes the tail by `detIter_normal_stable`. -/
theorem detIter_eq_of_normal {k n : ℕ} (hkn : k ≤ n) {Γ : Binding.Ctx RType}
    {s : RType} {t : Binding.Tm (oneLambdaSig A) Γ s}
    (h : Normal (detIter k t)) : detIter n t = detIter k t := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
  rw [Nat.add_comm k m, detIter_add]
  exact detIter_normal_stable m h

/-- The β dispatch bridge: at a term of positive β-rank `q`, the deterministic
step is the β worker `detStepAt q`. The dispatch unfolding consumed by
`det_cycle`, connecting the `detIter` orbit to the `detStepAt` iterates of the
Task 6.4.3 chain-decomposition lemmas. -/
theorem detStep_eq_detStepAt {Γ : Binding.Ctx RType} {s : RType}
    {t : Binding.Tm (oneLambdaSig A) Γ s} {q : ℕ} (hq : 0 < q)
    (hrank : betaRedexRank t = q) : detStep t = detStepAt q t := by
  rw [detStep_eq, hrank, if_pos hq]

/-- The ι dispatch bridge: at a β-normal term carrying an ι-redex, the
deterministic step is the ι worker `detIotaStep`. The rank-`0` dispatch
unfolding consumed by `detIter_normal`'s ι phase. -/
theorem detStep_eq_detIotaStep {Γ : Binding.Ctx RType} {s : RType}
    {t : Binding.Tm (oneLambdaSig A) Γ s} (hβ : betaRedexRank t = 0)
    (hι : hasIota t = true) : detStep t = detIotaStep t := by
  rw [detStep_eq, hβ, if_neg (lt_irrefl 0), if_pos hι]

/-! ### The deterministic rank-elimination cycle

The deterministic realization of the 6.3 rank-elimination cycle `beta_cycle`
(spec §4.3, note N1): from a term of β-rank at most `q ≥ 1`, at most `Tm.size t`
iterations of the deterministic step reach a term of β-rank at most `q - 1`,
with `beta_cycle`'s height bound and shape invariant. The interior induction is
structural: the worker's child-priority descent makes the orbit at an operation
node the concatenation of its children's orbits (the Task 6.4.3
iterate-congruence lemmas) followed by at most one root contraction. A
contraction whose reduct is an abstraction can uncover a rank-`q` redex at the
parent node; that firing happens at the parent's own induction level, which is
what the `IsLam` shape clause licenses. -/

omit [LinearOrder A.B] in
/-- The β worker's rank bound along the whole orbit: iterating `detStepAt q` on
a term of β-rank at most `q` never raises the β-rank above `q`. The iterate
closure of `betaRedexRank_detStepAt_le`, bounding every element of the
deterministic orbit at once. -/
theorem betaRedexRank_detStepAt_iterate_le (q n : ℕ) {Γ : Binding.Ctx RType}
    {s : RType} (t : Binding.Tm (oneLambdaSig A) Γ s) (ht : betaRedexRank t ≤ q) :
    betaRedexRank ((detStepAt q)^[n] t) ≤ q := by
  induction n with
  | zero => exact ht
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact betaRedexRank_detStepAt_le q _ ih

omit [LinearOrder A.B] in
/-- The conclusion of one deterministic rank-elimination cycle at rank budget
`q` (note N1): an orbit prefix of at most `Tm.size t` steps of `detStepAt q`
whose proper prefix stays at β-rank exactly `q` and whose endpoint has β-rank
below `q`, height at most `2 ^ Tm.height t`, and the shape invariant — an
abstraction endpoint forces an abstraction start or a sort of order at most
`q`. The rank-exactness of the prefix both feeds the iterate-congruence lemmas
at the parent node and bridges the `detStep` orbit to the `detStepAt q` orbit.
The motive of the `det_cycle` induction, packaged so its per-node case lemmas
share one statement. -/
private def DetCycle (q : ℕ) {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) : Prop :=
  ∃ k, k ≤ Tm.size t ∧
    (∀ j, j < k → betaRedexRank ((detStepAt q)^[j] t) = q) ∧
    betaRedexRank ((detStepAt q)^[k] t) ≤ q - 1 ∧
    Tm.height ((detStepAt q)^[k] t) ≤ 2 ^ Tm.height t ∧
    (IsLam ((detStepAt q)^[k] t) → IsLam t ∨ RType.ord s ≤ q)

omit [LinearOrder A.B] in
/-- The short cycle: a term whose β-rank is already below `q` satisfies the
cycle conclusion with the empty orbit. Discharges the variable and constant
leaves of the `det_cycle` induction and every below-budget node. -/
private theorem detCycle_of_rank_lt {q : ℕ} {Γ : Binding.Ctx RType} {s : RType}
    {t : Binding.Tm (oneLambdaSig A) Γ s} (ht : betaRedexRank t ≤ q - 1) :
    DetCycle q t :=
  ⟨0, Nat.zero_le _, fun j hj => absurd hj (Nat.not_lt_zero j), ht,
    Nat.lt_two_pow_self.le, fun h => Or.inl h⟩

omit [LinearOrder A.B] in
/-- The abstraction case of the deterministic rank-elimination cycle (note N1
item 2): the body's orbit lifts through `detStepAt_iterate_lamBody`, the
abstraction node adding one to the size budget and the height. The endpoint is
an abstraction, but so is the start — the shape invariant's left disjunct. -/
private theorem detCycle_lam' {q : ℕ} {Γ : Binding.Ctx RType} {σ τ : RType}
    {b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ}
    (hb : DetCycle q b) : DetCycle q (OneLambda.lam' b) := by
  obtain ⟨k, hk, hchain, hrank, hheight, -⟩ := hb
  have hiter : ∀ n, n ≤ k → (detStepAt q)^[n] (OneLambda.lam' b)
      = OneLambda.lam' ((detStepAt q)^[n] b) := fun n hn =>
    detStepAt_iterate_lamBody q n b fun i hi => hchain i (lt_of_lt_of_le hi hn)
  refine ⟨k, ?_, ?_, ?_, ?_, ?_⟩
  · rw [size_lam']
    omega
  · intro j hj
    rw [hiter j (le_of_lt hj), betaRedexRank_lam']
    exact hchain j hj
  · rw [hiter k le_rfl, betaRedexRank_lam']
    exact hrank
  · rw [hiter k le_rfl, height_lam', height_lam']
    have h1 : (1 : ℕ) ≤ 2 ^ Tm.height b := Nat.one_le_two_pow
    have h2 : 2 ^ (1 + Tm.height b) = 2 * 2 ^ Tm.height b := by rw [pow_add, pow_one]
    omega
  · intro _
    exact Or.inl (isLam_lam' b)

omit [LinearOrder A.B] in
/-- The application case of the deterministic rank-elimination cycle (note N1
item 2): the function subterm's orbit lifts through `detStepAt_iterate_appL`,
the argument subterm's through `detStepAt_iterate_appR` once the function has
left rank `q`, and the orbit closes with at most one root contraction. When the
reduced function is an abstraction at arrow order exactly `q`, the root β-redex
fires, its contractum bounded by `betaRedexRank_instantiate₁_le` and
`Tm.height_instantiate₁_le` and its sort of order at most `q` — the shape
invariant's right disjunct; otherwise the shape clause of the function's own
cycle bounds the top rank below `q` and the reduced application closes the
cycle. -/
private theorem detCycle_app' {q : ℕ} (hq : 1 ≤ q) {Γ : Binding.Ctx RType}
    {σ τ : RType} {f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ)}
    {x : Binding.Tm (oneLambdaSig A) Γ σ}
    (ht : betaRedexRank (OneLambda.app' f x) ≤ q)
    (hf : DetCycle q f) (hx : DetCycle q x) : DetCycle q (OneLambda.app' f x) := by
  obtain ⟨kf, hkf, hchainf, hrankf, hheightf, hshapef⟩ := hf
  obtain ⟨kx, hkx, hchainx, hrankx, hheightx, -⟩ := hx
  have hfne : betaRedexRank ((detStepAt q)^[kf] f) ≠ q := by omega
  have hxne : betaRedexRank ((detStepAt q)^[kx] x) ≠ q := by omega
  -- the function orbit lifted through the application
  have hiterL : ∀ n, n ≤ kf → (detStepAt q)^[n] (OneLambda.app' f x)
      = OneLambda.app' ((detStepAt q)^[n] f) x := fun n hn =>
    detStepAt_iterate_appL q n f x fun i hi => hchainf i (lt_of_lt_of_le hi hn)
  -- the argument orbit lifted after the function orbit
  have hmid : ∀ n, n ≤ kx → (detStepAt q)^[kf + n] (OneLambda.app' f x)
      = OneLambda.app' ((detStepAt q)^[kf] f) ((detStepAt q)^[n] x) := fun n hn => by
    rw [Nat.add_comm kf n, Function.iterate_add_apply, hiterL kf le_rfl]
    exact detStepAt_iterate_appR q n _ x hfne fun i hi => hchainx i (lt_of_lt_of_le hi hn)
  have hend : (detStepAt q)^[kf + kx] (OneLambda.app' f x)
      = OneLambda.app' ((detStepAt q)^[kf] f) ((detStepAt q)^[kx] x) := hmid kx le_rfl
  -- the whole-orbit rank bound
  have hall : ∀ j, betaRedexRank ((detStepAt q)^[j] (OneLambda.app' f x)) ≤ q :=
    fun j => betaRedexRank_detStepAt_iterate_le q j _ ht
  -- the orbit elements up to the argument-orbit end have rank exactly `q`
  have hprefix : ∀ j, j < kf + kx →
      betaRedexRank ((detStepAt q)^[j] (OneLambda.app' f x)) = q := by
    intro j hj
    refine le_antisymm (hall j) ?_
    rcases Nat.lt_or_ge j kf with hjf | hjf
    · rw [hiterL j (le_of_lt hjf)]
      exact le_trans (le_of_eq (hchainf j hjf).symm)
        (betaRedexRank_le_betaRedexRank_app' _ x)
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hjf
      have hi : i < kx := by omega
      rw [hmid i (le_of_lt hi)]
      exact le_trans (le_of_eq (hchainx i hi).symm)
        (betaRedexRank_arg_le_betaRedexRank_app' _ _)
  by_cases hguard : isLam ((detStepAt q)^[kf] f) = true
      ∧ RType.ord (RType.arrow σ τ) = q
  · -- the root β-redex fires: one further contraction step closes the orbit
    obtain ⟨b, hb⟩ := exists_lam'_of_isLam hguard.1
    have hstep : (detStepAt q)^[kf + kx + 1] (OneLambda.app' f x)
        = Binding.instantiate₁ ((detStepAt q)^[kx] x) b := by
      rw [Function.iterate_succ_apply', hend, detStepAt_app', if_neg hfne, if_neg hxne,
        if_pos hguard, hb, appReduct_lam']
    have hord : RType.ord σ + 1 ≤ q ∧ RType.ord τ ≤ q := by
      have h2 := hguard.2
      rw [RType.ord_arrow] at h2
      omega
    rw [hb, betaRedexRank_lam'] at hrankf
    rw [hb, height_lam'] at hheightf
    refine ⟨kf + kx + 1, ?_, ?_, ?_, ?_, ?_⟩
    · rw [size_app']
      omega
    · intro j hj
      rcases Nat.lt_or_ge j (kf + kx) with hjlt | hjge
      · exact hprefix j hjlt
      · have hje : j = kf + kx := by omega
        subst hje
        refine le_antisymm (hall _) ?_
        rw [hend]
        calc q = topBetaRank (OneLambda.app' ((detStepAt q)^[kf] f)
              ((detStepAt q)^[kx] x)) := by
              rw [topBetaRank_app', if_pos hguard.1, hguard.2]
          _ ≤ _ := by rw [betaRedexRank_app']; exact le_max_left _ _
    · rw [hstep]
      have hN2 := betaRedexRank_instantiate₁_le ((detStepAt q)^[kx] x) b
      omega
    · rw [hstep, height_app']
      have hinst := Tm.height_instantiate₁_le ((detStepAt q)^[kx] x) b
      have hpf : 2 ^ Tm.height f ≤ 2 ^ max (Tm.height f) (Tm.height x) :=
        Nat.pow_le_pow_right (by omega) (le_max_left _ _)
      have hpx : 2 ^ Tm.height x ≤ 2 ^ max (Tm.height f) (Tm.height x) :=
        Nat.pow_le_pow_right (by omega) (le_max_right _ _)
      have htwo : 2 ^ (1 + max (Tm.height f) (Tm.height x))
          = 2 * 2 ^ max (Tm.height f) (Tm.height x) := by rw [pow_add, pow_one]
      omega
    · intro _
      exact Or.inr hord.2
  · -- no root contraction: the orbit ends at the reduced application
    have htop : topBetaRank (OneLambda.app' ((detStepAt q)^[kf] f)
        ((detStepAt q)^[kx] x)) ≤ q - 1 := by
      rw [topBetaRank_app']
      split_ifs with hL
      · have hne : RType.ord (RType.arrow σ τ) ≠ q := fun h => hguard ⟨hL, h⟩
        have hle : RType.ord (RType.arrow σ τ) ≤ q := by
          rcases hshapef hL with hLf | hord
          · have hLf' : isLam f = true := hLf
            have h1 : topBetaRank (OneLambda.app' f x)
                = RType.ord (RType.arrow σ τ) := by
              rw [topBetaRank_app', if_pos hLf']
            have h2 := betaRedexRank_app' f x
            omega
          · exact hord
        omega
      · omega
    refine ⟨kf + kx, ?_, hprefix, ?_, ?_, ?_⟩
    · rw [size_app']
      omega
    · rw [hend, betaRedexRank_app']
      omega
    · rw [hend, height_app', height_app']
      have hpf : 2 ^ Tm.height f ≤ 2 ^ max (Tm.height f) (Tm.height x) :=
        Nat.pow_le_pow_right (by omega) (le_max_left _ _)
      have hpx : 2 ^ Tm.height x ≤ 2 ^ max (Tm.height f) (Tm.height x) :=
        Nat.pow_le_pow_right (by omega) (le_max_right _ _)
      have htwo : 2 ^ (1 + max (Tm.height f) (Tm.height x))
          = 2 * 2 ^ max (Tm.height f) (Tm.height x) := by rw [pow_add, pow_one]
      have hone : (1 : ℕ) ≤ 2 ^ max (Tm.height f) (Tm.height x) := Nat.one_le_two_pow
      omega
    · rw [hend]
      intro habs
      have hfalse : isLam (OneLambda.app' ((detStepAt q)^[kf] f)
          ((detStepAt q)^[kx] x)) = true := habs
      rw [isLam_app'] at hfalse
      exact Bool.noConfusion hfalse

omit [LinearOrder A.B] in
/-- The structural-induction shell of the deterministic rank-elimination cycle
(note N1): strong induction on `Tm.size`, dispatching each head form to its
case lemma — below-budget nodes (including variables and the nullary constants)
to the short cycle, abstractions to the body's cycle, applications to the
orbit-concatenation dispatcher. -/
private theorem det_cycle_aux :
    (N : ℕ) → ∀ {Γ : Binding.Ctx RType} {s : RType} {q : ℕ}, 1 ≤ q →
      ∀ (t : Binding.Tm (oneLambdaSig A) Γ s), Tm.size t ≤ N → betaRedexRank t ≤ q →
      DetCycle q t
  | 0, _, _, _, _, t, hN, _ => absurd (Tm.one_le_size t) (by omega)
  | N + 1, Γ, s, q, hq, t, hN, ht => by
      rcases Nat.lt_or_ge (betaRedexRank t) q with hlt | hge
      · exact detCycle_of_rank_lt (by omega)
      · rcases tm_cases t with ⟨x0, rfl⟩ | ⟨o, hs0, args, ht_eq⟩
        · exact detCycle_of_rank_lt (by rw [betaRedexRank_var]; omega)
        · cases o with
          | app σ τ =>
              have hs1 : τ = s := hs0
              subst hs1
              replace ht_eq : t = Binding.Tm.op (S := oneLambdaSig A)
                (OneLambdaOp.app σ τ) args := ht_eq
              obtain ⟨f, x, hfx⟩ := op_app_inv args
              rw [hfx] at ht_eq
              subst ht_eq
              rw [size_app'] at hN
              have hf1 := Tm.one_le_size f
              have hx1 := Tm.one_le_size x
              exact detCycle_app' hq ht
                (det_cycle_aux N hq f (by omega)
                  (le_trans (betaRedexRank_le_betaRedexRank_app' f x) ht))
                (det_cycle_aux N hq x (by omega)
                  (le_trans (betaRedexRank_arg_le_betaRedexRank_app' f x) ht))
          | lam σ τ =>
              have hs1 : RType.arrow σ τ = s := hs0
              subst hs1
              replace ht_eq : t = Binding.Tm.op (S := oneLambdaSig A)
                (OneLambdaOp.lam σ τ) args := ht_eq
              obtain ⟨b, hb⟩ := op_lam_inv args
              rw [hb] at ht_eq
              subst ht_eq
              rw [size_lam'] at hN
              rw [betaRedexRank_lam'] at ht
              exact detCycle_lam' (det_cycle_aux N hq b (by omega) ht)
          | con i =>
              have hs1 : RType.curried (List.replicate (A.ar i) RType.o) RType.o = s :=
                hs0
              subst hs1
              replace ht_eq : t = Binding.Tm.op (S := oneLambdaSig A)
                (OneLambdaOp.con i) args := ht_eq
              subst ht_eq
              have h0 : betaRedexRank (Binding.Tm.op (S := oneLambdaSig A) (Γ := Γ)
                  (OneLambdaOp.con i) args) = 0 := by
                rw [betaRedexRank_op]
                change max 0 ((Finset.univ : Finset (Fin 0)).sup _) = 0
                simp
              exact detCycle_of_rank_lt (le_trans (le_of_eq h0) (Nat.zero_le _))
          | dstr j =>
              have hs1 : RType.arrow RType.o RType.o = s := hs0
              subst hs1
              replace ht_eq : t = Binding.Tm.op (S := oneLambdaSig A)
                (OneLambdaOp.dstr j) args := ht_eq
              subst ht_eq
              have h0 : betaRedexRank (Binding.Tm.op (S := oneLambdaSig A) (Γ := Γ)
                  (OneLambdaOp.dstr j) args) = 0 := by
                rw [betaRedexRank_op]
                change max 0 ((Finset.univ : Finset (Fin 0)).sup _) = 0
                simp
              exact detCycle_of_rank_lt (le_trans (le_of_eq h0) (Nat.zero_le _))
          | case =>
              have hs1 : RType.arrow RType.o
                  (RType.curried (List.replicate A.numCtors RType.o) RType.o) = s := hs0
              subst hs1
              replace ht_eq : t = Binding.Tm.op (S := oneLambdaSig A)
                OneLambdaOp.case args := ht_eq
              subst ht_eq
              have h0 : betaRedexRank (Binding.Tm.op (S := oneLambdaSig A) (Γ := Γ)
                  OneLambdaOp.case args) = 0 := by
                rw [betaRedexRank_op]
                change max 0 ((Finset.univ : Finset (Fin 0)).sup _) = 0
                simp
              exact detCycle_of_rank_lt (le_trans (le_of_eq h0) (Nat.zero_le _))

/-- The `detStep`-to-`detStepAt` orbit bridge: while every proper prefix of the
`detStepAt q` orbit stays at β-rank exactly `q > 0`, the `detIter` orbit
coincides with it — each prefix step dispatches through
`detStep_eq_detStepAt`. -/
private theorem detIter_eq_iterate_detStepAt {q : ℕ} (hq : 0 < q) :
    (k : ℕ) → ∀ {Γ : Binding.Ctx RType} {s : RType}
      (t : Binding.Tm (oneLambdaSig A) Γ s),
      (∀ j, j < k → betaRedexRank ((detStepAt q)^[j] t) = q) →
      detIter k t = (detStepAt q)^[k] t
  | 0, _, _, _, _ => rfl
  | k + 1, Γ, s, t, hchain => by
      have h0 : betaRedexRank t = q := hchain 0 (Nat.succ_pos k)
      rw [detIter_succ, Function.iterate_succ_apply, detStep_eq_detStepAt hq h0]
      exact detIter_eq_iterate_detStepAt hq k (detStepAt q t) fun j hj => by
        rw [← Function.iterate_succ_apply]
        exact hchain (j + 1) (Nat.succ_lt_succ hj)

/-- One deterministic rank-elimination cycle (Leivant III section 5, proof
paragraph (ii), p. 226, DOI `10.1016/S0168-0072(98)00040-2`; spec §4.3, note
N1): from a term of β-rank at most `q ≥ 1`, at most `Tm.size t` iterations of
the deterministic step reach a term of β-rank at most `q - 1` whose height is
at most `2 ^ Tm.height t`. The final clause is the shape invariant the
uncovering phenomenon requires, mirroring 6.3's `beta_cycle`: an abstraction
endpoint forces an abstraction start or a sort of order at most `q`, licensing
the parent-level firing of an uncovered redex. The deterministic strengthening
of `beta_cycle`, with the existential chain replaced by the `detIter` orbit. -/
theorem det_cycle (q : ℕ) (hq : 1 ≤ q) {Γ s}
    (t : Binding.Tm (oneLambdaSig A) Γ s) (ht : betaRedexRank t ≤ q) :
    ∃ k ≤ Tm.size t,
      betaRedexRank (detIter k t) ≤ q - 1 ∧
      Tm.height (detIter k t) ≤ 2 ^ Tm.height t ∧
      (IsLam (detIter k t) → IsLam t ∨ RType.ord s ≤ q) := by
  obtain ⟨k, hk, hchain, hrank, hheight, hshape⟩ :=
    det_cycle_aux (Tm.size t) hq t le_rfl ht
  have hbridge : detIter k t = (detStepAt q)^[k] t :=
    detIter_eq_iterate_detStepAt hq k t hchain
  refine ⟨k, hk, ?_, ?_, ?_⟩ <;> rw [hbridge]
  · exact hrank
  · exact hheight
  · exact hshape

/-! ### The deterministic clock

The deterministic Lemma 12 clock (spec §4.3): cycles compose downward over the
rank budgets `q, q - 1, …, 1` (the `beta_normalize` shape), the ι phase runs
within the β-normal junction's size ceiling, and overshoot past normality is
absorbed by `detIter_eq_of_normal`, landing the `lemma12_clock` value
`(redexRank t + 1) * tower (redexRank t + 1) (Tm.height t)`. -/

/-- The β phase of the deterministic clock, by downward induction on the rank
budget `q` (the `beta_normalize_aux` shape): a term of β-rank at most `q` and
height at most `H` reaches a β-normal term of height at most `tower q H` within
`q * tower q H` iterations of the deterministic step. At budget `q`, the
current cycle's step count is bounded by the term's size, in turn bounded by
`2 ^ H ≤ tower q H`, and the recursive tail at budget `q - 1` contributes the
remaining `(q - 1) * tower q H`; heights compose through `tower_comp`. -/
private theorem detIter_beta_normalize_aux (q : ℕ) :
    ∀ {Γ : Binding.Ctx RType} {s : RType} (t : Binding.Tm (oneLambdaSig A) Γ s)
      (H : ℕ), betaRedexRank t ≤ q → Tm.height t ≤ H →
      ∃ k, betaRedexRank (detIter k t) = 0 ∧
        Tm.height (detIter k t) ≤ tower q H ∧ k ≤ q * tower q H := by
  induction q with
  | zero =>
      intro Γ s t H ht hH
      exact ⟨0, Nat.le_zero.mp ht, by simpa using hH, by simp⟩
  | succ q ih =>
      intro Γ s t H ht hH
      obtain ⟨k₁, hk₁, hrank₁, hheight₁, -⟩ := det_cycle (q + 1) (by omega) t ht
      have hrank' : betaRedexRank (detIter k₁ t) ≤ q := by omega
      have hheight' : Tm.height (detIter k₁ t) ≤ 2 ^ H :=
        le_trans hheight₁ (Nat.pow_le_pow_right (by omega) hH)
      obtain ⟨k₂, hrank'', hheight'', hk₂⟩ := ih (detIter k₁ t) (2 ^ H) hrank' hheight'
      have htower : tower q (2 ^ H) = tower (q + 1) H := by
        rw [show (2 : ℕ) ^ H = tower 1 H from rfl, tower_comp]
      refine ⟨k₂ + k₁, ?_, ?_, ?_⟩
      · rw [detIter_add]
        exact hrank''
      · rw [detIter_add, ← htower]
        exact hheight''
      · have hk₁' : k₁ ≤ tower (q + 1) H :=
          calc k₁ ≤ Tm.size t := hk₁
            _ ≤ 2 ^ Tm.height t := size_le_two_pow_height t
            _ ≤ 2 ^ H := Nat.pow_le_pow_right (by omega) hH
            _ = tower 1 H := rfl
            _ ≤ tower (q + 1) H := tower_mono_left (by omega) H
        have hk₂' : k₂ ≤ q * tower (q + 1) H := by
          rw [← htower]
          exact hk₂
        calc k₂ + k₁ ≤ q * tower (q + 1) H + tower (q + 1) H :=
              Nat.add_le_add hk₂' hk₁'
          _ = (q + 1) * tower (q + 1) H := (Nat.succ_mul _ _).symm

/-- The ι phase of the deterministic clock, by strong induction on the term
size (the `iota_normalize_aux` shape): a β-normal term reaches a `Normal` term
within `Tm.size t` iterations of the deterministic step. Each iteration
dispatches through `detStep_eq_detIotaStep`; the ι worker's strict size
decrease `size_detIotaStep_lt` drives the induction and its β-normality
preservation `betaRedexRank_detIotaStep` maintains the dispatch guard. -/
private theorem detIter_iota_normalize_aux :
    (N : ℕ) → ∀ {Γ : Binding.Ctx RType} {s : RType}
      (t : Binding.Tm (oneLambdaSig A) Γ s), Tm.size t ≤ N → betaRedexRank t = 0 →
      ∃ k, k ≤ Tm.size t ∧ Normal (detIter k t)
  | 0, _, _, t, hN, _ => absurd (Tm.one_le_size t) (by omega)
  | N + 1, Γ, s, t, hN, hβ => by
      cases hio : hasIota t with
      | false => exact ⟨0, Nat.zero_le _, (normal_iff t).mpr ⟨hβ, hio⟩⟩
      | true =>
          have hsz : Tm.size (detIotaStep t) < Tm.size t := size_detIotaStep_lt t hβ hio
          obtain ⟨k, hk, hnorm⟩ := detIter_iota_normalize_aux N (detIotaStep t)
            (by omega) (betaRedexRank_detIotaStep t hβ)
          refine ⟨k + 1, by omega, ?_⟩
          rw [detIter_succ, detStep_eq_detIotaStep hβ hio]
          exact hnorm

/-- The deterministic Lemma 12 clock (Leivant III section 5, p. 226, DOI
`10.1016/S0168-0072(98)00040-2`; spec §4.3): iterating the deterministic step
`(redexRank t + 1) * tower (redexRank t + 1) (Tm.height t)` times — the
`lemma12_clock` step bound — reaches a `Normal` term. The β phase lands within
`redexRank t * tower (redexRank t + 1) (Tm.height t)` iterations, the ι phase
within the β-normal junction's size `tower (redexRank t + 1) (Tm.height t)`
(via `size_le_two_pow_height`), and the overshoot up to the clock value is
absorbed by `detIter_eq_of_normal`. -/
theorem detIter_normal {Γ s} (t : Binding.Tm (oneLambdaSig A) Γ s) :
    Normal (detIter
      ((redexRank t + 1) * tower (redexRank t + 1) (Tm.height t)) t) := by
  obtain ⟨k₁, hβ₁, hheight₁, hk₁⟩ :=
    detIter_beta_normalize_aux (betaRedexRank t) t (Tm.height t) le_rfl le_rfl
  obtain ⟨k₂, hk₂, hnorm⟩ :=
    detIter_iota_normalize_aux (Tm.size (detIter k₁ t)) (detIter k₁ t) le_rfl hβ₁
  rw [← detIter_add] at hnorm
  have hq₀ : betaRedexRank t ≤ redexRank t := betaRedexRank_le_redexRank t
  have hk₁' : k₁ ≤ redexRank t * tower (redexRank t + 1) (Tm.height t) :=
    calc k₁ ≤ betaRedexRank t * tower (betaRedexRank t) (Tm.height t) := hk₁
      _ ≤ redexRank t * tower (redexRank t + 1) (Tm.height t) :=
          Nat.mul_le_mul hq₀ (tower_mono_left (by omega) _)
  have hk₂' : k₂ ≤ tower (redexRank t + 1) (Tm.height t) :=
    calc k₂ ≤ Tm.size (detIter k₁ t) := hk₂
      _ ≤ 2 ^ Tm.height (detIter k₁ t) := size_le_two_pow_height _
      _ ≤ 2 ^ tower (betaRedexRank t) (Tm.height t) :=
          Nat.pow_le_pow_right (by omega) hheight₁
      _ = tower (betaRedexRank t + 1) (Tm.height t) := rfl
      _ ≤ tower (redexRank t + 1) (Tm.height t) := tower_mono_left (by omega) _
  have hK : k₂ + k₁ ≤ (redexRank t + 1) * tower (redexRank t + 1) (Tm.height t) := by
    calc k₂ + k₁
        ≤ tower (redexRank t + 1) (Tm.height t)
            + redexRank t * tower (redexRank t + 1) (Tm.height t) :=
          Nat.add_le_add hk₂' hk₁'
      _ = (redexRank t + 1) * tower (redexRank t + 1) (Tm.height t) := by
          rw [Nat.succ_mul]
          omega
  rw [detIter_eq_of_normal hK hnorm]
  exact hnorm

end OneLambda

end GebLean.Ramified
