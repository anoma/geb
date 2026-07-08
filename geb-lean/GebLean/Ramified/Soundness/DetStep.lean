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

end OneLambda

end GebLean.Ramified
