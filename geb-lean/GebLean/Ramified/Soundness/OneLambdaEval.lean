import GebLean.Ramified.Soundness.BarRep
import GebLean.Ramified.Soundness.Applicative

/-!
# The standard evaluator of the simply-typed calculus `1λ(A)`

The standard simple-type denotation `oneEval` of the simply-typed calculus
`1λ(A)` (Leivant III section 4.2, DOI `10.1016/S0168-0072(98)00040-2`) over the
standard word algebra `natAlgSig`: an environment-passing fold of a term
`Binding.Tm (oneLambdaSig natAlgSig) Γ s` into a value at
`RType.interp (FreeAlg natAlgSig) s`, together with the renaming- and
substitution-fusion laws that reconcile the syntactic operations `Binding.ren`,
`Binding.sub`, and `Binding.instantiate₁` with the evaluator.

The constant clauses mirror section 4.2's reduction rules (p. 223): `con b`
evaluates to the curried constructor `stdConstructorInterp` at the base object
sort `o`; `dstr j` evaluates to the destructor `dstrRead`, whose hit/miss split
matches `OneLambdaStep.dstrHit`/`dstrMiss`; `case` evaluates to the branch
selector `caseSelect`, whose branch selection matches `OneLambdaStep.case`. The
model is the evident one (novel packaging); it reuses the applicative calculus's
semantic environment infrastructure (`renEnvSem`, `envExtend`, `envCastCtx`,
`childEnv`, and the renaming reconciliations), which is signature-independent.

## Main definitions

* `oneEvalOp` — the per-operation dispatch of the standard denotation.
* `oneEval` — the standard denotation of a `1λ(A)` term over `natAlgSig`.
* `subEnvSemOne` — the semantic substitution environment for `oneEval`.

## Main statements

* `oneEval_var`, `oneEval_app'`, `oneEval_lam'`, `oneEval_con`, `oneEval_dstr`,
  `oneEval_case` — the node computation rules of `oneEval`.
* `oneEval_conc` — the concrete term `conc a` evaluates to the value `a`.
* `oneEval_ren`, `oneEval_sub` — renaming and substitution fusion.
* `oneEval_instantiate₁` — the fusion corollary for single-variable substitution.
* `conc_injective` — injectivity of `conc`, via `oneEval_conc`.
* `oneEval_step` — a `OneLambdaStep`-reduction preserves the denotation.
* `oneEval_reduces` — a `Relation.ReflTransGen`-reduction preserves the
  denotation, the reflexive-transitive lift of `oneEval_step`.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`, section 4.2 (p. 223): the
evaluator, its reduction rules, and their soundness.

## Tags

ramified recurrence, simply-typed lambda calculus, evaluator, denotational
semantics, renaming, substitution
-/

namespace GebLean.Ramified

open GebLean.Binding

/-- The standard-model denotation of an operation node of the simply-typed
calculus `1λ(A)` over `natAlgSig`: given the denotations `ih` of the node's
subterms (each a function of an environment for the ambient context extended by
that subterm's bound sorts), the value of the node as a function of an
environment for the ambient context. The semantic twin of the operation case of
`Binding.traverse` and the `1λ(A)` analogue of `appEvalOp`; the constant clauses
mirror Leivant III section 4.2's reduction rules (p. 223):

* `app` applies the function denotation to the argument denotation, transporting
  the environment across `Γ ++ [] = Γ` (`envCastCtx`);
* `lam` produces the semantic function, extending the environment by the bound
  value (`envExtend`);
* `con b` is the curried constructor `stdConstructorInterp` at the base object
  sort `o` (the constants of `1λ(A)` are nullary, so the subterm family is
  ignored);
* `dstr j` is the destructor `dstrRead` (matching `OneLambdaStep.dstrHit`/
  `dstrMiss`);
* `case` is the branch selector `caseSelect`, curried over its branches; over
  `natAlgSig` (`numCtors = 2`) the case denotation reads exactly two branches, at
  enumeration positions `0` and `1` (matching `OneLambdaStep.case`). -/
def oneEvalOp {Γ : Binding.Ctx RType} (o : OneLambdaOp natAlgSig)
    (ih : ∀ j : Fin ((oneLambdaSig natAlgSig).args o).length,
      (∀ i : Fin (Γ ++ (((oneLambdaSig natAlgSig).args o).get j).1).length,
        RType.interp (FreeAlg natAlgSig)
          ((Γ ++ (((oneLambdaSig natAlgSig).args o).get j).1).get i)) →
        RType.interp (FreeAlg natAlgSig) (((oneLambdaSig natAlgSig).args o).get j).2) :
    (∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) →
      RType.interp (FreeAlg natAlgSig) ((oneLambdaSig natAlgSig).result o) := by
  cases o with
  | app σ τ =>
    have h0 : (0 : Nat) < ((oneLambdaSig natAlgSig).args (OneLambdaOp.app σ τ)).length :=
      Nat.zero_lt_two
    have h1 : (1 : Nat) < ((oneLambdaSig natAlgSig).args (OneLambdaOp.app σ τ)).length :=
      Nat.one_lt_two
    exact fun ρ =>
      (ih ⟨0, h0⟩ (envCastCtx (List.append_nil Γ).symm ρ))
        (ih ⟨1, h1⟩ (envCastCtx (List.append_nil Γ).symm ρ))
  | lam σ τ =>
    have h0 : (0 : Nat) < ((oneLambdaSig natAlgSig).args (OneLambdaOp.lam σ τ)).length :=
      Nat.zero_lt_one
    exact fun ρ v => ih ⟨0, h0⟩ (envExtend ρ v)
  | con b =>
    exact fun _ρ =>
      curryInterp natAlgSig (List.replicate (natAlgSig.ar b) RType.o) RType.o
        (stdConstructorInterp natAlgSig (⟨RType.o, Or.inl rfl⟩, b))
  | dstr j => exact fun _ρ => dstrRead j.val
  | case =>
    exact fun _ρ z =>
      curryInterp natAlgSig (List.replicate natAlgSig.numCtors RType.o) RType.o
        (fun branchEnv =>
          caseSelect z
            (cast (congrArg (RType.interp (FreeAlg natAlgSig))
              (by rw [List.get_eq_getElem, List.getElem_replicate]))
              (branchEnv ⟨0, (by decide : (0:Nat) < 2)⟩))
            (cast (congrArg (RType.interp (FreeAlg natAlgSig))
              (by rw [List.get_eq_getElem, List.getElem_replicate]))
              (branchEnv ⟨1, (by decide : (1:Nat) < 2)⟩)))

/-- The standard-model denotation of a `1λ(A)` term over `natAlgSig`: a function
from a semantic environment at its context to a value at its sort, over the
standard carrier `FreeAlg natAlgSig`. Env-passing fold via `PolyFix.ind`, the
`1λ(A)` analogue of `appEval`. A variable leaf reads the environment at that
variable's position; an operation node dispatches through `oneEvalOp` on the
denotations of its subterms under the binder-extended environment. -/
def oneEval {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    (∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) →
      RType.interp (FreeAlg natAlgSig) s :=
  PolyFix.ind (P := polyTranslate (Binding.varOver (Ty := RType)) (oneLambdaSig natAlgSig).polyEndo)
    (motive := fun {x} _ =>
      (∀ i : Fin x.1.length, RType.interp (FreeAlg natAlgSig) (x.1.get i)) →
        RType.interp (FreeAlg natAlgSig) x.2)
    (fun {_x} i children ih =>
      match i, children, ih with
      | Sum.inl a, _, _ => fun ρ => (leafVar a).2 ▸ ρ (leafVar a).1
      | Sum.inr p, _, ih => fun ρ => p.2 ▸ oneEvalOp p.val (fun j => ih ⟨j⟩) ρ) t

/-- `oneEval` at a variable reads the environment at that variable's position,
transported along the variable's sort proof. The base case of the fold. -/
@[simp] theorem oneEval_var {Γ : Binding.Ctx RType} {s : RType} (x : Binding.Var Γ s)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    oneEval (Binding.Tm.var x) ρ = x.2 ▸ ρ x.1 := by
  obtain ⟨i, hi⟩ := x
  subst hi
  rfl

/-- `oneEval` at an operation node dispatches through `oneEvalOp` on the
denotations of the node's subterms. The operation case of the fold, the
`PolyFix.ind` β-reduction that the node computation lemmas rest on. -/
theorem oneEval_op {Γ : Binding.Ctx RType} (o : OneLambdaOp natAlgSig)
    (args : ∀ j : Fin ((oneLambdaSig natAlgSig).args o).length,
      Binding.Tm (oneLambdaSig natAlgSig) (Γ ++ (((oneLambdaSig natAlgSig).args o).get j).1)
        (((oneLambdaSig natAlgSig).args o).get j).2)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    oneEval (Binding.Tm.op o args) ρ = oneEvalOp o (fun j => oneEval (args j)) ρ := rfl

/-- Transport of `oneEval` across an equality of contexts: evaluating the
context-transported term at the transported environment agrees with evaluating
the original. Discharges the `Γ ++ [] = Γ` mismatch of `app'`. -/
theorem oneEval_congr_ctx {Γ Δ : Binding.Ctx RType} {s : RType} (h : Γ = Δ)
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    oneEval (h ▸ t) (envCastCtx h ρ) = oneEval t ρ := by
  subst h
  rfl

/-- `oneEval` on an application node `app' f x` is the application of the
function denotation to the argument denotation (the β-reduction of the
applicative fragment). -/
@[simp] theorem oneEval_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig natAlgSig) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig natAlgSig) Γ σ)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    oneEval (OneLambda.app' f x) ρ = oneEval f ρ (oneEval x ρ) :=
  congrArg₂ (fun (g : RType.interp (FreeAlg natAlgSig) (RType.arrow σ τ)) y => g y)
    (oneEval_congr_ctx (List.append_nil Γ).symm f ρ)
    (oneEval_congr_ctx (List.append_nil Γ).symm x ρ)

/-- `oneEval` on an abstraction node `lam' b` is the semantic function extending
the environment by the bound value (the denotation of λ-abstraction). -/
@[simp] theorem oneEval_lam' {Γ : Binding.Ctx RType} {σ τ : RType}
    (b : Binding.Tm (oneLambdaSig natAlgSig) (Γ ++ [σ]) τ)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    oneEval (OneLambda.lam' b) ρ = fun v => oneEval b (envExtend ρ v) := rfl

/-- `oneEval` on a constructor constant `con b` is the curried constructor
`stdConstructorInterp` at the base object sort `o`. -/
@[simp] theorem oneEval_con {Γ : Binding.Ctx RType} (b : natAlgSig.B)
    (args : ∀ j : Fin ((oneLambdaSig natAlgSig).args (OneLambdaOp.con b)).length,
      Binding.Tm (oneLambdaSig natAlgSig)
        (Γ ++ (((oneLambdaSig natAlgSig).args (OneLambdaOp.con b)).get j).1)
        (((oneLambdaSig natAlgSig).args (OneLambdaOp.con b)).get j).2)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    oneEval (Binding.Tm.op (OneLambdaOp.con b) args) ρ
      = curryInterp natAlgSig (List.replicate (natAlgSig.ar b) RType.o) RType.o
          (stdConstructorInterp natAlgSig (⟨RType.o, Or.inl rfl⟩, b)) := rfl

/-- `oneEval` on a destructor constant `dstr j` is the destructor `dstrRead`. -/
@[simp] theorem oneEval_dstr {Γ : Binding.Ctx RType} (j : Fin natAlgSig.maxArity)
    (args : ∀ k : Fin ((oneLambdaSig natAlgSig).args (OneLambdaOp.dstr j)).length,
      Binding.Tm (oneLambdaSig natAlgSig)
        (Γ ++ (((oneLambdaSig natAlgSig).args (OneLambdaOp.dstr j)).get k).1)
        (((oneLambdaSig natAlgSig).args (OneLambdaOp.dstr j)).get k).2)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    oneEval (Binding.Tm.op (OneLambdaOp.dstr j) args) ρ = dstrRead j.val := rfl

/-- `oneEval` on a case constant `case` is the branch selector `caseSelect`,
curried over its branches; over `natAlgSig` (`numCtors = 2`) it reads exactly the
two branches at enumeration positions `0` and `1`. -/
@[simp] theorem oneEval_case {Γ : Binding.Ctx RType}
    (args : ∀ j : Fin ((oneLambdaSig natAlgSig).args OneLambdaOp.case).length,
      Binding.Tm (oneLambdaSig natAlgSig)
        (Γ ++ (((oneLambdaSig natAlgSig).args OneLambdaOp.case).get j).1)
        (((oneLambdaSig natAlgSig).args OneLambdaOp.case).get j).2)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    oneEval (Binding.Tm.op OneLambdaOp.case args) ρ
      = fun z => curryInterp natAlgSig (List.replicate natAlgSig.numCtors RType.o) RType.o
          (fun branchEnv =>
            caseSelect z
              (cast (congrArg (RType.interp (FreeAlg natAlgSig))
                (by rw [List.get_eq_getElem, List.getElem_replicate]))
                (branchEnv ⟨0, (by decide : (0:Nat) < 2)⟩))
              (cast (congrArg (RType.interp (FreeAlg natAlgSig))
                (by rw [List.get_eq_getElem, List.getElem_replicate]))
                (branchEnv ⟨1, (by decide : (1:Nat) < 2)⟩))) := rfl

/-- Heterogeneous congruence for `oneEval`: evaluating heterogeneously equal
terms gives heterogeneously equal denotations. -/
theorem oneEval_heq {Γ : Binding.Ctx RType} {s₁ s₂ : RType}
    (t₁ : Binding.Tm (oneLambdaSig natAlgSig) Γ s₁)
    (t₂ : Binding.Tm (oneLambdaSig natAlgSig) Γ s₂)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i))
    (hs : s₁ = s₂) (h : t₁ ≍ t₂) : oneEval t₁ ρ ≍ oneEval t₂ ρ := by
  subst hs
  cases h
  exact HEq.rfl

/-- `oneEval` on an iterated application `appSpine Ts f args` is the semantic
application chain `appChain` of the function denotation to the argument
denotations. The applicative-fragment β-reduction lifted to a whole spine, by
induction on `Ts` from `oneEval_app'`. -/
@[simp] theorem oneEval_appSpine {Γ : Binding.Ctx RType} {result : RType} :
    (Ts : List RType) →
    (f : Binding.Tm (oneLambdaSig natAlgSig) Γ (RType.curried Ts result)) →
    (args : ∀ i : Fin Ts.length, Binding.Tm (oneLambdaSig natAlgSig) Γ (Ts.get i)) →
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) →
    oneEval (OneLambda.appSpine Ts f args) ρ
      = appChain natAlgSig Ts result (oneEval f ρ) (fun i => oneEval (args i) ρ)
  | [], _f, _args, _ρ => rfl
  | _T :: Ts', f, args, ρ => by
    rw [OneLambda.appSpine, oneEval_appSpine Ts', oneEval_app']
    rfl

/-- `oneEval` on a homogeneous application spine `replicateSpine n base head args`
is the semantic application chain of the head denotation to the argument
denotations, reindexed off `List.replicate`. Specializes `oneEval_appSpine` to
`Ts = List.replicate n base`, discharging the `List.getElem_replicate` sort
transport on each argument via `oneEval_heq`. -/
theorem oneEval_replicateSpine {Γ : Binding.Ctx RType} {result : RType} (n : Nat)
    (base : RType)
    (head : Binding.Tm (oneLambdaSig natAlgSig) Γ (RType.curried (List.replicate n base) result))
    (args : Fin n → Binding.Tm (oneLambdaSig natAlgSig) Γ base)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    oneEval (OneLambda.replicateSpine n base head args) ρ
      = appChain natAlgSig (List.replicate n base) result (oneEval head ρ)
          (fun i => cast (congrArg (RType.interp (FreeAlg natAlgSig))
            (show base = (List.replicate n base).get i from by
              rw [List.get_eq_getElem, List.getElem_replicate]))
            (oneEval (args (Fin.cast List.length_replicate i)) ρ)) := by
  rw [OneLambda.replicateSpine, oneEval_appSpine]
  congr 1
  funext i
  apply eq_of_heq
  refine (oneEval_heq _ _ ρ ?_ ?_).trans (cast_heq _ _).symm
  · rw [List.get_eq_getElem, List.getElem_replicate]
  · simp only [eq_mpr_eq_cast]
    exact (cast_heq _ _).trans (cast_heq _ _)

/-- A `con b`-headed homogeneous application spine evaluates to the free-algebra
node `FreeAlg.mk b` on the evaluated arguments (Leivant III section 4.2, p. 223):
the curried constructor `stdConstructorInterp` applied along the spine is folded
back to the node by `oneEval_replicateSpine` and `appChain_stdConstructorInterp`,
the object-sort transports cancelling. The `con`-node computation shared by
`oneEval_conc` and by the `dstr`/`case` redex soundness of `oneEval_step`. -/
theorem oneEval_conSpine {Γ : Binding.Ctx RType} (b : natAlgSig.B)
    (a : Fin (natAlgSig.ar b) → Binding.Tm (oneLambdaSig natAlgSig) Γ RType.o)
    (env : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    oneEval (OneLambda.replicateSpine (natAlgSig.ar b) RType.o
        (Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.con b) (fun k => k.elim0)) a)
        env
      = FreeAlg.mk b (fun k => oneEval (a k) env) := by
  rw [oneEval_replicateSpine]
  apply eq_of_heq
  refine (cast_heq (RType.interp_isObj (FreeAlg natAlgSig) (Or.inl rfl)) _).symm.trans
    (heq_of_eq ?_)
  refine (appChain_stdConstructorInterp natAlgSig b (Or.inl rfl) _).trans ?_
  refine congrArg (FreeAlg.mk (A := natAlgSig) b) ?_
  funext i
  apply eq_of_heq
  exact (cast_heq _ _).trans ((cast_heq _ _).trans HEq.rfl)

/-- The concrete term `conc a` of a free-algebra value evaluates to the value `a`
itself (Leivant III section 4.2): the standard denotation inverts the `con`-node
fold `conc`. By the free-algebra recurrence, each node `c_b(sub)` evaluates its
`con b`-headed spine back to `FreeAlg.mk b sub` (`oneEval_conSpine`), the
recursive results supplied by the induction hypothesis. -/
@[simp] theorem oneEval_conc (a : FreeAlg natAlgSig)
    (env : ∀ i : Fin ([] : Binding.Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([] : Binding.Ctx RType).get i)) :
    oneEval (conc a) env = a := by
  refine PolyFix.ind (P := natAlgSig.polyEndo)
    (motive := fun {_} a => oneEval (conc a) env = a) (fun b children ih => ?_) a
  change oneEval (conc (FreeAlg.mk b children)) env = FreeAlg.mk b children
  rw [conc_mk, oneEval_conSpine]
  exact congrArg (FreeAlg.mk b) (funext ih)

/-- Evaluating the sole suffix variable `boundVar` of `params ++ [ω]` reads the
recurrence argument `envLast`. The `oneEval` counterpart of
`boundVar_appEval_eq_envLast`. -/
theorem oneEval_boundVar_eq_envLast {params : List RType} {ω : RType}
    (ρ : ∀ k : Fin (params ++ [ω]).length,
      RType.interp (FreeAlg natAlgSig) ((params ++ [ω]).get k)) :
    oneEval (Binding.Tm.var (boundVar (Γ := params) (σ := ω))) ρ = envLast params ω ρ := by
  rw [oneEval_var]
  apply eq_of_heq
  refine (eqRec_heq _ _).trans ?_
  simp only [envLast]
  refine HEq.trans ?_ (cast_heq _ _).symm
  have hpos : (boundVar (Γ := params) (σ := ω)).1 = finAppR params [ω] ⟨0, by simp⟩ := by
    apply Fin.ext
    unfold boundVar
    rw [appendRight_val]
    simp [finAppR]
  rw [hpos]

/-- The fresh binder variable reads the extension value: `boundVar` evaluated at
`envExtend ρ v` is `v`. The `oneEval` counterpart of `boundVar_appEval_envExtend`;
the semantic reconciliation the β-redex denotation rests on. -/
theorem oneEval_boundVar_envExtend {Γ : Binding.Ctx RType} {σ : RType}
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i))
    (v : RType.interp (FreeAlg natAlgSig) σ) :
    oneEval (Binding.Tm.var (boundVar (Γ := Γ) (σ := σ))) (envExtend ρ v) = v := by
  rw [oneEval_boundVar_eq_envLast]
  apply eq_of_heq
  simp only [envLast, envExtend]
  refine (cast_heq _ _).trans ?_
  refine (heq_of_eq (childEnv_finAppR ρ (fun _ => v) ⟨0, by simp⟩ Nat.zero_lt_one)).trans ?_
  exact (cast_heq _ _).trans (cast_heq _ _)

/-- Per-operation naturality of `oneEvalOp` under semantic renaming: the `oneEval`
counterpart of `appEvalOp_renEnvSem`. The `app` and `lam` arms use the two
environment reconciliations; the nullary constants ignore both the subterm family
and the environment. The operation case of `oneEval_ren`. -/
theorem oneEvalOp_renEnvSem {Γ Δ : Binding.Ctx RType} (o : OneLambdaOp natAlgSig)
    (θ : Binding.Thinning Γ Δ)
    (g : ∀ j : Fin ((oneLambdaSig natAlgSig).args o).length,
      (∀ i : Fin (Γ ++ (((oneLambdaSig natAlgSig).args o).get j).1).length,
        RType.interp (FreeAlg natAlgSig)
          ((Γ ++ (((oneLambdaSig natAlgSig).args o).get j).1).get i)) →
        RType.interp (FreeAlg natAlgSig) (((oneLambdaSig natAlgSig).args o).get j).2)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i)) :
    oneEvalOp (Γ := Δ) o
        (fun j ρ'' => g j (renEnvSem
          (Binding.Thinning.appendId θ (((oneLambdaSig natAlgSig).args o).get j).1) ρ'')) ρ
      = oneEvalOp (Γ := Γ) o g (renEnvSem θ ρ) := by
  cases o with
  | app σ τ =>
      simp only [oneEvalOp]
      have h0 : renEnvSem (Binding.Thinning.appendId θ
            (((oneLambdaSig natAlgSig).args (OneLambdaOp.app σ τ)).get ⟨0, Nat.zero_lt_two⟩).1)
          (envCastCtx (List.append_nil Δ).symm ρ)
            = envCastCtx (List.append_nil Γ).symm (renEnvSem θ ρ) := renEnvSem_appendId_nil θ ρ
      have h1 : renEnvSem (Binding.Thinning.appendId θ
            (((oneLambdaSig natAlgSig).args (OneLambdaOp.app σ τ)).get ⟨1, Nat.one_lt_two⟩).1)
          (envCastCtx (List.append_nil Δ).symm ρ)
            = envCastCtx (List.append_nil Γ).symm (renEnvSem θ ρ) := renEnvSem_appendId_nil θ ρ
      rw [h0, h1]
      rfl
  | lam σ τ =>
      simp only [oneEvalOp]
      funext v
      have h : renEnvSem (Binding.Thinning.appendId θ
            (((oneLambdaSig natAlgSig).args (OneLambdaOp.lam σ τ)).get ⟨0, Nat.zero_lt_one⟩).1)
          (envExtend ρ v) = envExtend (renEnvSem θ ρ) v := renEnvSem_appendId_extend θ ρ v
      rw [h]
      rfl
  | con b => rfl
  | dstr j => rfl
  | case => rfl

/-- Renaming fusion at a variable leaf: evaluating a renamed variable reads the
thinning through `renEnvSem`. Factored with a free sort variable so the sort proof
can be discharged by substitution. The `oneEval` counterpart of `appEval_ren_var`. -/
theorem oneEval_ren_var {Γ Δ : Binding.Ctx RType} {s : RType} (θ : Binding.Thinning Γ Δ)
    (x : Binding.Var Γ s)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i)) :
    oneEval (Binding.ren θ (Binding.Tm.var x)) ρ
      = oneEval (Binding.Tm.var x) (renEnvSem θ ρ) := by
  rw [Binding.ren, Binding.traverse_var]
  simp only [Binding.varKit, Binding.renEnv]
  rw [oneEval_var, oneEval_var]
  obtain ⟨pos, hsort⟩ := x
  subst hsort
  simp only [renEnvSem]

/-- Renaming fusion for `oneEval` (Leivant III section 4.2): evaluating a renamed term at
an environment equals evaluating the original at the semantically renamed
environment. The base case reads the thinning through `renEnvSem`; the operation
case is `oneEvalOp_renEnvSem` on the binder-weakened subterm denotations. The
`oneEval` counterpart of `appEval_ren`; stated over an arbitrary index so the
induction on the term goes through. -/
@[simp] theorem oneEval_ren : ∀ {y : Binding.Ctx RType × RType}
    (t : PolyFix
      (polyTranslate (Binding.varOver (Ty := RType)) (oneLambdaSig natAlgSig).polyEndo) y)
    {Δ : Binding.Ctx RType} (θ : Binding.Thinning y.1 Δ)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i)),
    oneEval (Binding.ren θ t) ρ = oneEval t (renEnvSem θ ρ) := by
  intro y t
  induction t with
  | mk y idx children ih =>
    intro Δ θ ρ
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children : Binding.Tm (oneLambdaSig natAlgSig) y.1 y.2)
            = Binding.Tm.var (leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      exact oneEval_ren_var θ (leafVar a) ρ
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : (oneLambdaSig natAlgSig).Op // (oneLambdaSig natAlgSig).result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', (oneLambdaSig natAlgSig).result o) (Sum.inr ⟨o, rfl⟩) children
            : Binding.Tm (oneLambdaSig natAlgSig) Γ' ((oneLambdaSig natAlgSig).result o))
            = Binding.Tm.op o (fun j => children ⟨j⟩) from rfl]
      rw [Binding.ren, Binding.traverse_op]
      simp only [Binding.underBinder_renEnv]
      rw [oneEval_op, oneEval_op]
      have hfam : (fun j => oneEval (Binding.traverse (Binding.varKit (oneLambdaSig natAlgSig))
            (Binding.renEnv (Binding.Thinning.appendId θ
              (((oneLambdaSig natAlgSig).args o).get j).1)) (children ⟨j⟩)))
          = (fun (j : Fin ((oneLambdaSig natAlgSig).args o).length) ρ'' =>
              oneEval (children ⟨j⟩) (renEnvSem (Binding.Thinning.appendId θ
                (((oneLambdaSig natAlgSig).args o).get j).1) ρ'')) := by
        funext j ρ''
        exact ih ⟨j⟩ (Binding.Thinning.appendId θ _) ρ''
      rw [hfam]
      exact oneEvalOp_renEnvSem o θ (fun j => oneEval (children ⟨j⟩)) ρ

/-- The semantic substitution environment of a term environment
`σ : Env (Tm (oneLambdaSig natAlgSig)) Γ Δ`: read each `Γ`-position's tautological
variable through `σ` and evaluate the resulting `Δ`-term at `ρ`. The `oneEval`
counterpart of `subEnvSem`, reconciling `Binding.sub σ` with `oneEval` in
`oneEval_sub`. -/
def subEnvSemOne {Γ Δ : Binding.Ctx RType}
    (σ : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) Γ Δ)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i)) :
    ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i) :=
  fun i => oneEval (σ (Γ.get i) ⟨i, rfl⟩) ρ

/-- Evaluating a term environment at two positions of the same underlying index but
possibly distinct sorts gives heterogeneously equal denotations. -/
theorem subEnvSemOne_val_heq {Γ Δ : Binding.Ctx RType}
    (σ : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) Γ Δ)
    {s s' : RType} (hs : s = s') (i : Fin Γ.length)
    (hi : Γ.get i = s) (hi' : Γ.get i = s') :
    σ s ⟨i, hi⟩ ≍ σ s' ⟨i, hi'⟩ := by
  subst hs
  rfl

/-- The semantic substitution environment of an under-binder weakening
`Env.underBinder subKit σ` acting on a recurrence-context gluing
`childEnv Δ σ' n ρ rest` equals the gluing of the substituted prefix environment
`subEnvSemOne σ ρ` with the same suffix values `rest`. The `oneEval` counterpart of
`subEnvSem_underBinder_childEnv`; at prefix positions the binder-weakening
`wk = ren weakAppend` is pushed through `oneEval` by `oneEval_ren` and collapsed by
`renEnvSem_weakAppend_childEnv`; at suffix positions the freshly bound variable
reads `rest` directly. -/
theorem subEnvSemOne_underBinder_childEnv {Γ Δ : Binding.Ctx RType} {σ' : RType} {n : Nat}
    (σ : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) Γ Δ)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i))
    (rest : Fin n → RType.interp (FreeAlg natAlgSig) σ') :
    subEnvSemOne (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig))
        (Ξ := List.replicate n σ') σ) (childEnv Δ σ' n ρ rest)
      = childEnv Γ σ' n (subEnvSemOne σ ρ) rest := by
  funext k
  refine finApp_cases (Γ := Γ) (Δ := List.replicate n σ')
    (motive := fun k =>
      subEnvSemOne (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig))
        (Ξ := List.replicate n σ') σ) (childEnv Δ σ' n ρ rest) k
        = childEnv Γ σ' n (subEnvSemOne σ ρ) rest k)
    (fun i => ?_) (fun j => ?_) k
  · apply eq_of_heq
    have hfin : (finAppL Γ (List.replicate n σ') i).val < Γ.length := i.isLt
    have hvar : Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig))
          (Ξ := List.replicate n σ') σ
          ((Γ ++ List.replicate n σ').get (finAppL Γ (List.replicate n σ') i))
          ⟨finAppL Γ (List.replicate n σ') i, rfl⟩
        = Binding.ren Binding.Thinning.weakAppend
            (σ ((Γ ++ List.replicate n σ').get (finAppL Γ (List.replicate n σ') i))
              ⟨i, (get_finAppL Γ (List.replicate n σ') i).symm⟩) := by
      simp only [Binding.Env.underBinder, Binding.subKit]
      rw [taut_finAppL_eq]
      exact Binding.Var.appendCases_weakAppend _ Γ _ _
    have hLHS : subEnvSemOne (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig))
          (Ξ := List.replicate n σ') σ) (childEnv Δ σ' n ρ rest)
          (finAppL Γ (List.replicate n σ') i) ≍ subEnvSemOne σ ρ i := by
      simp only [subEnvSemOne]
      rw [hvar]
      rw [oneEval_ren (σ ((Γ ++ List.replicate n σ').get (finAppL Γ (List.replicate n σ') i))
            ⟨i, (get_finAppL Γ (List.replicate n σ') i).symm⟩)
          Binding.Thinning.weakAppend (childEnv Δ σ' n ρ rest),
        renEnvSem_weakAppend_childEnv]
      exact oneEval_heq _ _ ρ (get_finAppL Γ (List.replicate n σ') i)
        (subEnvSemOne_val_heq σ (get_finAppL Γ (List.replicate n σ') i) i _ rfl)
    have hRHS : childEnv Γ σ' n (subEnvSemOne σ ρ) rest (finAppL Γ (List.replicate n σ') i)
        ≍ subEnvSemOne σ ρ i :=
      (childEnv_heq_left (subEnvSemOne σ ρ) rest _ hfin).trans (heq_of_eq rfl)
    exact hLHS.trans hRHS.symm
  · apply eq_of_heq
    have hj : j.val < n := lt_of_lt_of_eq j.isLt List.length_replicate
    have hvalR : (finAppR Γ (List.replicate n σ') j).val = Γ.length + j.val := rfl
    have hgeR : ¬ (finAppR Γ (List.replicate n σ') j).val < Γ.length := by rw [hvalR]; omega
    have hbR : (finAppR Γ (List.replicate n σ') j).val - Γ.length < n := by rw [hvalR]; omega
    have hvar : Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig))
          (Ξ := List.replicate n σ') σ
          ((Γ ++ List.replicate n σ').get (finAppR Γ (List.replicate n σ') j))
          ⟨finAppR Γ (List.replicate n σ') j, rfl⟩
        = Binding.Tm.var (Binding.Var.appendRight Δ
            ⟨j, (get_finAppR Γ (List.replicate n σ') j).symm⟩) := by
      simp only [Binding.Env.underBinder, Binding.subKit]
      rw [taut_finAppR_eq]
      exact Binding.Var.appendCases_appendRight _ Γ _ _
    have hLHS : subEnvSemOne (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig))
          (Ξ := List.replicate n σ') σ) (childEnv Δ σ' n ρ rest)
          (finAppR Γ (List.replicate n σ') j) ≍ rest ⟨j.val, hj⟩ := by
      have hposval : (Binding.Var.appendRight Δ
          (⟨j, (get_finAppR Γ (List.replicate n σ') j).symm⟩ :
            Binding.Var (List.replicate n σ') _)).1.val = Δ.length + j.val := by
        rw [appendRight_val]
      have hgeD : ¬ (Binding.Var.appendRight Δ
          (⟨j, (get_finAppR Γ (List.replicate n σ') j).symm⟩ :
            Binding.Var (List.replicate n σ') _)).1.val < Δ.length := by rw [hposval]; omega
      have hbD : (Binding.Var.appendRight Δ
          (⟨j, (get_finAppR Γ (List.replicate n σ') j).symm⟩ :
            Binding.Var (List.replicate n σ') _)).1.val - Δ.length < n := by rw [hposval]; omega
      have hvaleqD : (Binding.Var.appendRight Δ
          (⟨j, (get_finAppR Γ (List.replicate n σ') j).symm⟩ :
            Binding.Var (List.replicate n σ') _)).1.val - Δ.length = j.val := by
        rw [hposval]; omega
      have hposD : (⟨(Binding.Var.appendRight Δ
          (⟨j, (get_finAppR Γ (List.replicate n σ') j).symm⟩ :
            Binding.Var (List.replicate n σ') _)).1.val - Δ.length, hbD⟩ : Fin n)
          = ⟨j.val, hj⟩ := Fin.ext hvaleqD
      simp only [subEnvSemOne]
      rw [hvar, oneEval_var]
      refine (eqRec_heq _ _).trans ((childEnv_heq_right ρ rest _ hgeD hbD).trans ?_)
      exact heq_of_eq (congrArg rest hposD)
    have hvaleqR : (finAppR Γ (List.replicate n σ') j).val - Γ.length = j.val := by
      rw [hvalR]; omega
    have hposR : (⟨(finAppR Γ (List.replicate n σ') j).val - Γ.length, hbR⟩ : Fin n)
        = ⟨j.val, hj⟩ := Fin.ext hvaleqR
    have hRHS : childEnv Γ σ' n (subEnvSemOne σ ρ) rest (finAppR Γ (List.replicate n σ') j)
        ≍ rest ⟨j.val, hj⟩ :=
      (childEnv_heq_right (subEnvSemOne σ ρ) rest _ hgeR hbR).trans
        (heq_of_eq (congrArg rest hposR))
    exact hLHS.trans hRHS.symm

/-- The `app`-node substitution reconciliation (empty binder suffix). The `app`
arm of `oneEvalOp_subEnvSemOne`. -/
theorem subEnvSemOne_underBinder_nil {Γ Δ : Binding.Ctx RType}
    (σ : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) Γ Δ)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i)) :
    subEnvSemOne (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig)) (Ξ := []) σ)
        (envCastCtx (List.append_nil Δ).symm ρ)
      = envCastCtx (List.append_nil Γ).symm (subEnvSemOne σ ρ) := by
  rw [envCastCtx_eq_childEnv_zero RType.o, envCastCtx_eq_childEnv_zero RType.o]
  exact subEnvSemOne_underBinder_childEnv σ ρ finZeroElim

/-- The `lam`-node substitution reconciliation (singleton binder suffix). The `lam`
arm of `oneEvalOp_subEnvSemOne`. -/
theorem subEnvSemOne_underBinder_extend {Γ Δ : Binding.Ctx RType} {σ' : RType}
    (σ : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) Γ Δ)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i))
    (v : RType.interp (FreeAlg natAlgSig) σ') :
    subEnvSemOne (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig)) (Ξ := [σ']) σ)
        (envExtend ρ v)
      = envExtend (subEnvSemOne σ ρ) v :=
  subEnvSemOne_underBinder_childEnv (n := 1) σ ρ (fun _ => v)

/-- Per-operation naturality of `oneEvalOp` under semantic substitution: the
`oneEval` counterpart of `appEvalOp_subEnvSem`. The `app` and `lam` arms use the
two substitution reconciliations; the nullary constants ignore both the subterm
family and the environment. The operation case of `oneEval_sub`. -/
theorem oneEvalOp_subEnvSemOne {Γ Δ : Binding.Ctx RType} (o : OneLambdaOp natAlgSig)
    (σ : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) Γ Δ)
    (g : ∀ j : Fin ((oneLambdaSig natAlgSig).args o).length,
      (∀ i : Fin (Γ ++ (((oneLambdaSig natAlgSig).args o).get j).1).length,
        RType.interp (FreeAlg natAlgSig)
          ((Γ ++ (((oneLambdaSig natAlgSig).args o).get j).1).get i)) →
        RType.interp (FreeAlg natAlgSig) (((oneLambdaSig natAlgSig).args o).get j).2)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i)) :
    oneEvalOp (Γ := Δ) o
        (fun j ρ'' => g j (subEnvSemOne (Binding.Env.underBinder
          (Binding.subKit (oneLambdaSig natAlgSig))
          (Ξ := (((oneLambdaSig natAlgSig).args o).get j).1) σ) ρ'')) ρ
      = oneEvalOp (Γ := Γ) o g (subEnvSemOne σ ρ) := by
  cases o with
  | app σ' τ =>
      simp only [oneEvalOp]
      have h0 : subEnvSemOne (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig))
            (Ξ := (((oneLambdaSig natAlgSig).args
              (OneLambdaOp.app σ' τ)).get ⟨0, Nat.zero_lt_two⟩).1) σ)
          (envCastCtx (List.append_nil Δ).symm ρ)
            = envCastCtx (List.append_nil Γ).symm (subEnvSemOne σ ρ) :=
        subEnvSemOne_underBinder_nil σ ρ
      have h1 : subEnvSemOne (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig))
            (Ξ := (((oneLambdaSig natAlgSig).args
              (OneLambdaOp.app σ' τ)).get ⟨1, Nat.one_lt_two⟩).1) σ)
          (envCastCtx (List.append_nil Δ).symm ρ)
            = envCastCtx (List.append_nil Γ).symm (subEnvSemOne σ ρ) :=
        subEnvSemOne_underBinder_nil σ ρ
      rw [h0, h1]
      rfl
  | lam σ' τ =>
      simp only [oneEvalOp]
      funext v
      have h : subEnvSemOne (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig))
            (Ξ := (((oneLambdaSig natAlgSig).args
              (OneLambdaOp.lam σ' τ)).get ⟨0, Nat.zero_lt_one⟩).1) σ)
          (envExtend ρ v) = envExtend (subEnvSemOne σ ρ) v := subEnvSemOne_underBinder_extend σ ρ v
      rw [h]
      rfl
  | con b => rfl
  | dstr j => rfl
  | case => rfl

/-- Substitution fusion at a variable leaf: substituting a variable reads the
environment through `subEnvSemOne`. The `oneEval` counterpart of `appEval_sub_var`. -/
theorem oneEval_sub_var {Γ Δ : Binding.Ctx RType} {s : RType}
    (σ : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) Γ Δ) (x : Binding.Var Γ s)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i)) :
    oneEval (Binding.sub σ (Binding.Tm.var x)) ρ
      = oneEval (Binding.Tm.var x) (subEnvSemOne σ ρ) := by
  rw [Binding.sub_var, oneEval_var]
  obtain ⟨pos, hsort⟩ := x
  subst hsort
  simp only [subEnvSemOne]

/-- Substitution fusion for `oneEval` (Leivant III section 4.2): evaluating a substituted
term at an environment equals evaluating the original at the semantically
substituted environment. The base case reads the environment through
`subEnvSemOne`; the operation case is `oneEvalOp_subEnvSemOne` on the
binder-weakened subterm denotations. The `oneEval` counterpart of `appEval_sub`,
whose binder-weakening step reuses `oneEval_ren`; stated over an arbitrary index so
the induction on the term goes through. -/
@[simp] theorem oneEval_sub : ∀ {y : Binding.Ctx RType × RType}
    (t : PolyFix
      (polyTranslate (Binding.varOver (Ty := RType)) (oneLambdaSig natAlgSig).polyEndo) y)
    {Δ : Binding.Ctx RType} (σ : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) y.1 Δ)
    (ρ : ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i)),
    oneEval (Binding.sub σ t) ρ = oneEval t (subEnvSemOne σ ρ) := by
  intro y t
  induction t with
  | mk y idx children ih =>
    intro Δ σ ρ
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children : Binding.Tm (oneLambdaSig natAlgSig) y.1 y.2)
            = Binding.Tm.var (leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      exact oneEval_sub_var σ (leafVar a) ρ
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : (oneLambdaSig natAlgSig).Op // (oneLambdaSig natAlgSig).result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', (oneLambdaSig natAlgSig).result o) (Sum.inr ⟨o, rfl⟩) children
            : Binding.Tm (oneLambdaSig natAlgSig) Γ' ((oneLambdaSig natAlgSig).result o))
            = Binding.Tm.op o (fun j => children ⟨j⟩) from rfl]
      rw [Binding.sub, Binding.traverse_op, oneEval_op, oneEval_op]
      have hfam : (fun j => oneEval (Binding.traverse (Binding.subKit (oneLambdaSig natAlgSig))
            (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig)) σ) (children ⟨j⟩)))
          = (fun (j : Fin ((oneLambdaSig natAlgSig).args o).length) ρ'' =>
              oneEval (children ⟨j⟩) (subEnvSemOne (Binding.Env.underBinder
                (Binding.subKit (oneLambdaSig natAlgSig)) σ) ρ'')) := by
        funext j ρ''
        exact ih ⟨j⟩ (Binding.Env.underBinder (Binding.subKit (oneLambdaSig natAlgSig)) σ) ρ''
      rw [hfam]
      exact oneEvalOp_subEnvSemOne o σ (fun j => oneEval (children ⟨j⟩)) ρ

/-- The semantic substitution environment of a single-variable instantiation
`extendEnv idEnv (metaOne N)` is the environment extension by `oneEval N ρ`: prefix
positions read `ρ` (through `idEnv`), the sole suffix position reads `oneEval N ρ`
(through `metaOne N`). The bridge from `oneEval_sub` to `oneEval_instantiate₁`. -/
theorem subEnvSemOne_instantiate₁ {Γ : Binding.Ctx RType} {a : RType}
    (N : Binding.Tm (oneLambdaSig natAlgSig) Γ a)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    subEnvSemOne (Binding.extendEnv Binding.idEnv (Binding.metaOne N)) ρ
      = envExtend ρ (oneEval N ρ) := by
  funext k
  refine finApp_cases (Γ := Γ) (Δ := [a])
    (motive := fun k =>
      subEnvSemOne (Binding.extendEnv Binding.idEnv (Binding.metaOne N)) ρ k
        = envExtend ρ (oneEval N ρ) k)
    (fun i => ?_) (fun j => ?_) k
  · apply eq_of_heq
    have hfin : (finAppL Γ [a] i).val < Γ.length := i.isLt
    have hvar : Binding.extendEnv Binding.idEnv (Binding.metaOne N)
          ((Γ ++ [a]).get (finAppL Γ [a] i)) ⟨finAppL Γ [a] i, rfl⟩
        = Binding.Tm.var (⟨i, (get_finAppL Γ [a] i).symm⟩ :
            Binding.Var Γ ((Γ ++ [a]).get (finAppL Γ [a] i))) := by
      rw [taut_finAppL_eq, Binding.extendEnv_weakAppend]
      rfl
    have hLHS : subEnvSemOne (Binding.extendEnv Binding.idEnv (Binding.metaOne N)) ρ
          (finAppL Γ [a] i) ≍ ρ i := by
      simp only [subEnvSemOne]
      rw [hvar, oneEval_var]
      exact eqRec_heq _ _
    have hRHS : envExtend ρ (oneEval N ρ) (finAppL Γ [a] i) ≍ ρ i := by
      simp only [envExtend]
      exact (childEnv_heq_left ρ (fun _ => oneEval N ρ) _ hfin).trans (heq_of_eq rfl)
    exact hLHS.trans hRHS.symm
  · apply eq_of_heq
    have hj : j.val < 1 := j.isLt
    have hj0 : j = ⟨0, Nat.one_pos⟩ := Fin.ext (Nat.lt_one_iff.mp hj)
    subst hj0
    have hvar : Binding.extendEnv Binding.idEnv (Binding.metaOne N)
          ((Γ ++ [a]).get (finAppR Γ [a] ⟨0, Nat.one_pos⟩))
          ⟨finAppR Γ [a] ⟨0, Nat.one_pos⟩, rfl⟩
        = (get_finAppR Γ [a] ⟨0, Nat.one_pos⟩).symm ▸ N := by
      rw [taut_finAppR_eq, Binding.extendEnv_appendRight]
      rfl
    have hLHS : subEnvSemOne (Binding.extendEnv Binding.idEnv (Binding.metaOne N)) ρ
          (finAppR Γ [a] ⟨0, Nat.one_pos⟩) ≍ oneEval N ρ := by
      simp only [subEnvSemOne]
      rw [hvar]
      exact oneEval_heq _ _ ρ (get_finAppR Γ [a] ⟨0, Nat.one_pos⟩) (eqRec_heq _ _)
    have hbR : (finAppR Γ [a] ⟨0, Nat.one_pos⟩).val - Γ.length < 1 := by
      have hv : (finAppR Γ [a] ⟨0, Nat.one_pos⟩).val = Γ.length + 0 := rfl
      rw [hv]; omega
    have hgeR : ¬ (finAppR Γ [a] ⟨0, Nat.one_pos⟩).val < Γ.length := by
      have hv : (finAppR Γ [a] ⟨0, Nat.one_pos⟩).val = Γ.length + 0 := rfl
      rw [hv]; omega
    have hRHS : envExtend ρ (oneEval N ρ) (finAppR Γ [a] ⟨0, Nat.one_pos⟩) ≍ oneEval N ρ := by
      simp only [envExtend]
      exact (childEnv_heq_right ρ (fun _ => oneEval N ρ) _ hgeR hbR).trans (heq_of_eq rfl)
    exact hLHS.trans hRHS.symm

/-- Single-variable substitution fusion for `oneEval`: evaluating the instantiation
`instantiate₁ N b` equals evaluating `b` at the environment extended by the
denotation of `N`. The denotational form of the β-rule of `1λ(A)` (Leivant III
section 4.2), specializing `oneEval_sub` through `subEnvSemOne_instantiate₁`. -/
theorem oneEval_instantiate₁ {Γ : Binding.Ctx RType} {a s : RType}
    (N : Binding.Tm (oneLambdaSig natAlgSig) Γ a)
    (b : Binding.Tm (oneLambdaSig natAlgSig) (Γ ++ [a]) s)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    oneEval (Binding.instantiate₁ N b) ρ = oneEval b (envExtend ρ (oneEval N ρ)) := by
  rw [Binding.instantiate₁, Binding.instantiate,
    oneEval_sub b (Binding.extendEnv Binding.idEnv (Binding.metaOne N)) ρ,
    subEnvSemOne_instantiate₁]

/-- Injectivity of the concrete term `conc` (Leivant III section 4.2): distinct values
have distinct concrete terms. Evaluate both sides of `conc a = conc b` at the empty
environment through `oneEval_conc`. -/
theorem conc_injective {a b : FreeAlg natAlgSig} (h : conc a = conc b) : a = b := by
  have hval := congrArg
    (fun t : Binding.Tm (oneLambdaSig natAlgSig) [] RType.o => oneEval t finZeroElim) h
  simpa only [oneEval_conc] using hval

/-- The case redex `case z b⃗` (the `replicateSpine` of a `case` head applied to
the recurrence argument `z` and the `numCtors` branches `bs`) evaluates to the
branch selector `caseSelect` on `z`'s denotation and the two branch denotations
(Leivant III section 4.2, p. 223): `oneEval_replicateSpine` exposes the
application chain, the `case` head evaluates to a `curryInterp` (folded back by
`appChain_curryInterp`), and the `List.replicate` sort transports cancel. The
`case`-redex computation of `oneEval_step`; the `oneEval` counterpart of
`appEval_caseRedex`. -/
theorem oneEval_caseSpine {Γ : Binding.Ctx RType}
    (z : Binding.Tm (oneLambdaSig natAlgSig) Γ RType.o)
    (bs : Fin natAlgSig.numCtors → Binding.Tm (oneLambdaSig natAlgSig) Γ RType.o)
    (env : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    oneEval (OneLambda.replicateSpine natAlgSig.numCtors RType.o
        (OneLambda.app' (Binding.Tm.op (S := oneLambdaSig natAlgSig) OneLambdaOp.case
          (fun k => k.elim0)) z) bs) env
      = caseSelect (oneEval z env)
          (oneEval (bs ⟨0, by decide⟩) env) (oneEval (bs ⟨1, by decide⟩) env) := by
  rw [oneEval_replicateSpine]
  simp only [oneEval_app']
  conv_lhs =>
    arg 4
    change curryInterp natAlgSig (List.replicate natAlgSig.numCtors RType.o) RType.o
      (fun be => caseSelect (oneEval z env)
        (cast (congrArg (RType.interp (FreeAlg natAlgSig))
          (by rw [List.get_eq_getElem, List.getElem_replicate])) (be ⟨0, Nat.zero_lt_two⟩))
        (cast (congrArg (RType.interp (FreeAlg natAlgSig))
          (by rw [List.get_eq_getElem, List.getElem_replicate])) (be ⟨1, Nat.one_lt_two⟩)))
  rw [appChain_curryInterp]
  beta_reduce
  refine congrArg₂ (caseSelect (oneEval z env)) ?_ ?_ <;>
    exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))

/-- Applying a destructor constant `dstr j` to an argument evaluates to the
destructor `dstrRead j` on the argument's denotation (Leivant III section 4.2):
the `dstr`-redex computation of `oneEval_step`, folding `oneEval_dstr` through the
application node. Stated as a separate lemma since the destructor clause reduces a
partially-applied node, which `rewrite`/`simp` do not reach under an application. -/
theorem oneEval_dstrApp {Γ : Binding.Ctx RType} (j : Fin natAlgSig.maxArity)
    (x : Binding.Tm (oneLambdaSig natAlgSig) Γ RType.o)
    (env : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    oneEval (OneLambda.app'
        (Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.dstr j) (fun k => k.elim0)) x)
        env
      = dstrRead j.val (oneEval x env) := by
  rw [oneEval_app']
  exact congrFun (oneEval_dstr j (fun k => k.elim0) env) (oneEval x env)

/-- Weakening a term by one fresh binder and evaluating at a one-value extension
reads the original environment: `ren weakAppend` is inverted by `envExtend`. The
`oneEval` counterpart of `appEval_ren_weakAppend_envExtend`; the prefix-embedding
reconciliation the η-rule denotation of `oneEval_step` rests on. -/
theorem oneEval_ren_weakAppend_envExtend {Γ : Binding.Ctx RType} {σ s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i))
    (v : RType.interp (FreeAlg natAlgSig) σ) :
    oneEval (Binding.ren (Binding.Thinning.weakAppend (Ξ := [σ])) t) (envExtend ρ v)
      = oneEval t ρ := by
  rw [oneEval_ren t (Binding.Thinning.weakAppend (Ξ := [σ])) (envExtend ρ v)]
  congr 1
  exact renEnvSem_weakAppend_childEnv ρ (fun _ => v)

/-- Soundness of one-step reduction for the standard evaluator (Leivant III
section 4.2, p. 223): a `OneLambdaStep`-reduction preserves the denotation. The
base redexes match the constant clauses — β by the `instantiate₁` fusion
(`oneEval_instantiate₁`), η by function extensionality with `oneEval_ren`, the
destructor and case redexes by the `con`-spine and `case`-spine computations
(`oneEval_conSpine`, `oneEval_caseSpine`) against `dstrRead`/`caseSelect` — and
the compatibility rules by the induction hypothesis through the node clauses. -/
theorem oneEval_step {Γ : Binding.Ctx RType} {s : RType}
    {t t' : Binding.Tm (oneLambdaSig natAlgSig) Γ s} (h : OneLambdaStep t t')
    (env : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    oneEval t env = oneEval t' env := by
  revert env
  induction h with
  | beta b N =>
    intro env
    rw [oneEval_instantiate₁, oneEval_app', oneEval_lam']
    rfl
  | eta M =>
    intro env
    rw [oneEval_lam']
    funext v
    rw [oneEval_app', oneEval_ren_weakAppend_envExtend]
    exact congrArg (oneEval M env) (oneEval_boundVar_envExtend env v)
  | dstrHit j hlt a =>
    intro env
    rw [oneEval_dstrApp, oneEval_conSpine, dstrRead_mk]
    exact dif_pos hlt
  | dstrMiss j hge a =>
    intro env
    rw [oneEval_dstrApp, oneEval_conSpine, dstrRead_mk, dif_neg (Nat.not_lt.mpr hge)]
  | case idx a b =>
    intro env
    rw [oneEval_caseSpine, oneEval_conSpine]
    exact caseSelect_mk_ctorAt idx (fun k => oneEval (a k) env) (fun k => oneEval (b k) env)
  | appL x _h ih =>
    intro env
    rw [oneEval_app', oneEval_app', ih env]
  | appR f _h ih =>
    intro env
    rw [oneEval_app', oneEval_app']
    exact congrArg (oneEval f env) (ih env)
  | lamBody _h ih =>
    intro env
    rw [oneEval_lam', oneEval_lam']
    funext v
    exact ih (envExtend env v)

/-- Soundness of multi-step reduction for the standard evaluator (Leivant III
section 4.2, p. 223): a `Relation.ReflTransGen`-reduction preserves the
denotation. The reflexive-transitive lift of `oneEval_step`, by induction on the
reduction sequence. -/
theorem oneEval_reduces {Γ : Binding.Ctx RType} {s : RType}
    {t t' : Binding.Tm (oneLambdaSig natAlgSig) Γ s}
    (h : Relation.ReflTransGen OneLambdaStep t t')
    (env : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    oneEval t env = oneEval t' env := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (oneEval_step hstep env)

end GebLean.Ramified
