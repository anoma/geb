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
semantic environment machinery (`renEnvSem`, `envExtend`, `envCastCtx`,
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

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`.

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

/-- The concrete term `conc a` of a free-algebra value evaluates to the value `a`
itself (Leivant III section 4.2): the standard denotation inverts the `con`-node
fold `conc`. By the free-algebra recurrence, each node `c_b(sub)` evaluates its
`con b`-headed spine — the curried constructor applied to the recursively
evaluated subterms — back to `FreeAlg.mk b sub` (`oneEval_replicateSpine`,
`appChain_stdConstructorInterp`). -/
@[simp] theorem oneEval_conc (a : FreeAlg natAlgSig)
    (env : ∀ i : Fin ([] : Binding.Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([] : Binding.Ctx RType).get i)) :
    oneEval (conc a) env = a := by
  refine PolyFix.ind (P := natAlgSig.polyEndo)
    (motive := fun {_} a => oneEval (conc a) env = a) (fun b children ih => ?_) a
  change oneEval (conc (FreeAlg.mk b children)) env = FreeAlg.mk b children
  rw [conc_mk, oneEval_replicateSpine]
  apply eq_of_heq
  refine (cast_heq (RType.interp_isObj (FreeAlg natAlgSig) (Or.inl rfl)) _).symm.trans
    (heq_of_eq ?_)
  refine (appChain_stdConstructorInterp natAlgSig b (Or.inl rfl) _).trans ?_
  refine congrArg (FreeAlg.mk (A := natAlgSig) b) ?_
  funext i
  apply eq_of_heq
  refine (cast_heq _ _).trans ((cast_heq _ _).trans ?_)
  exact (heq_of_eq (ih _)).trans HEq.rfl

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

end GebLean.Ramified
