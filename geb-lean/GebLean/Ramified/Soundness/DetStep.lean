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
private theorem op_app_inv {Γ : Binding.Ctx RType} {σ τ : RType}
    (args : ∀ j : Fin (((oneLambdaSig A).args (OneLambdaOp.app σ τ)).length),
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args (OneLambdaOp.app σ τ)).get j).1)
        (((oneLambdaSig A).args (OneLambdaOp.app σ τ)).get j).2) :
    ∃ (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
      (x : Binding.Tm (oneLambdaSig A) Γ σ),
      Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.app σ τ) args = OneLambda.app' f x :=
  ⟨_, _, op_app_eta args⟩

/-- Every abstraction node is a `lam'` of some body at the binder-extended
context: the existential packaging of `op_lam_eta`. -/
private theorem op_lam_inv {Γ : Binding.Ctx RType} {σ τ : RType}
    (args : ∀ j : Fin (((oneLambdaSig A).args (OneLambdaOp.lam σ τ)).length),
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args (OneLambdaOp.lam σ τ)).get j).1)
        (((oneLambdaSig A).args (OneLambdaOp.lam σ τ)).get j).2) :
    ∃ b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ,
      Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.lam σ τ) args = OneLambda.lam' b :=
  ⟨_, op_lam_eta args⟩

/-- The head-form cases of a term of `1λ(A)`: a variable, or an operation node
whose result sort transports to the term's sort. -/
private theorem tm_cases {Γ : Binding.Ctx RType} {s : RType}
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
private theorem exists_lam'_of_isLam {Γ : Binding.Ctx RType} {σ τ : RType}
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
private theorem eq_o_of_shape_o {s : RType} (h : s.shape = RTypeShape.o) : s = RType.o := by
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

/-- The ι-contraction is a genuine `OneLambdaStep` at every saturated ι-redex:
the inversion of `topIota` exposes the destructor- or case-redex shape, on
which `iotaContract` computes the matching
`OneLambdaStep.dstrHit`/`dstrMiss`/`case` reduct. -/
private theorem step_iotaContract_of_topIota {Γ : Binding.Ctx RType} {s : RType}
    {t : Binding.Tm (oneLambdaSig A) Γ s} (htop : topIota t = true) :
    OneLambdaStep t (iotaContract t) := by
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
      exact OneLambdaStep.dstrHit j hj a
    · have hred : dstrReduct j (replicateSpine (A.ar i) RType.o
          (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) (fun l => l.elim0)) a)
          = replicateSpine (A.ar i) RType.o
              (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) (fun l => l.elim0)) a := by
        unfold dstrReduct
        simp only [hscoll, List.getElem?_ofFn]
        rw [dif_neg (by omega)]
      rw [hred]
      exact OneLambdaStep.dstrMiss j hj a
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
    exact OneLambdaStep.case idx a b

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
            · exact step_iotaContract_of_topIota htop
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

end OneLambda

end GebLean.Ramified
