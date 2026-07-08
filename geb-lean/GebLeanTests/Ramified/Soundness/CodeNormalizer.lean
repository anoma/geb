import GebLean.Ramified.Soundness.CodeNormalizer

/-!
# Ramified-recurrence soundness: code-normalizer tests

Acceptance examples for the code-level substitution `subCode` and its
commutation theorem `subCode_codeTm`: the code-level substitution rewrites the
code of a body into the code of its `Binding.instantiate₁` reduct. The first
example closes the identity β-redex body of task 6.4.1 (a closed substituend, no
weakening) through the node equations alone; the remaining examples are
instances of the commutation theorem `subCode_codeTm`, one on the redex body and
one on a substituend that carries its own binder with a body referencing the
substituted variable underneath a binder — the path on which `subCode` applies
the `shiftCode` weakening under an abstraction node.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`.
-/

namespace GebLean.Ramified.OneLambda

open GebLean.Binding

/-- The substituted variable of the task 6.4.1 identity β-redex body `x`, the sole
bound variable of the singleton suffix `[o]`. -/
private def redexBody : Binding.Tm (oneLambdaSig natAlgSig) ([] ++ [RType.o]) RType.o :=
  Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))

/-- The code-level substitution on the code of the task 6.4.1 redex body equals the
code of its `instantiate₁` reduct: substituting the concrete zero word for the sole
bound variable. The substituend is closed, so no weakening arises. -/
example :
    subCode ([] : Binding.Ctx RType).length (codeTm (conc (natToFreeAlg 0)))
        (codeTm redexBody)
      = codeTm (Binding.instantiate₁ (conc (natToFreeAlg 0)) redexBody) := by
  have hinst : Binding.instantiate₁ (conc (natToFreeAlg 0)) redexBody
      = conc (natToFreeAlg 0) := by
    rw [redexBody, Binding.instantiate₁, Binding.instantiate, Binding.sub_var, boundVar,
      Binding.extendEnv_appendRight]
    rfl
  rw [hinst, redexBody, codeTm_var]
  have hlvl : (boundVar (Γ := ([] : Binding.Ctx RType)) (σ := RType.o)).1.val = 0 := rfl
  rw [hlvl, subCode_var]
  simp

/-- The substituend-weakening acceptance check: a substituend `λ(:o). x` that
carries its own binder, substituted for the variable a body references beneath a
binder, agrees with the genuine `Binding.instantiate₁` numerically. This exercises
the `shiftCode` weakening `subCode` applies under an abstraction node. -/
private def eBinder : Binding.Tm (oneLambdaSig natAlgSig) [] (RType.arrow RType.o RType.o) :=
  OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o)))

/-- The body `λ(:o). y`, in which the substituted variable `y` (level `0`, of the
arrow sort) is referenced beneath a `lam` binder. -/
private def dUnderBinder : Binding.Tm (oneLambdaSig natAlgSig)
    ([] ++ [RType.arrow RType.o RType.o]) (RType.arrow RType.o (RType.arrow RType.o RType.o)) :=
  OneLambda.lam' (Binding.Tm.var
    (⟨⟨0, by decide⟩, rfl⟩ :
      Binding.Var [RType.arrow RType.o RType.o, RType.o] (RType.arrow RType.o RType.o)))

/-- The full substitution, weakening included, matches `instantiate₁` on the
code: the `subCode_codeTm` instance at the binder-carrying substituend, whose
under-binder occurrence exercises the `shiftCode` path. -/
example :
    subCode ([] : Binding.Ctx RType).length (codeTm eBinder) (codeTm dUnderBinder)
      = codeTm (Binding.instantiate₁ eBinder dUnderBinder) :=
  subCode_codeTm eBinder dUnderBinder

/-- The redex-body case is the `subCode_codeTm` instance at the task 6.4.1
identity β-redex body. -/
example :
    subCode ([] : Binding.Ctx RType).length (codeTm (conc (natToFreeAlg 0)))
        (codeTm redexBody)
      = codeTm (Binding.instantiate₁ (conc (natToFreeAlg 0)) redexBody) :=
  subCode_codeTm (conc (natToFreeAlg 0)) redexBody

/-- The β-rank mirror on the closed normal value `conc 0`: reading the β-rank off
the code agrees with the term-level β-rank, through the mirror lemma (no kernel
reduction on the `codeTm` fold). -/
example : betaRankCode (codeTm (conc (natToFreeAlg 0)))
    = betaRedexRank (conc (natToFreeAlg 0)) :=
  betaRankCode_codeTm (conc (natToFreeAlg 0))

/-- The normality mirror on the binder-carrying substituend `λ(:o). x`: the
code-level normality detector agrees with the term-level `Normal` predicate,
through the mirror lemma. -/
example : normalCode (codeTm eBinder) = true ↔ Normal eBinder :=
  normalCode_codeTm eBinder

/-- The task 6.4.1 identity β-redex `(λ(:o). x) 0̄`: the abstraction over the
redex body applied to the concrete zero word. -/
private def idRedex : Binding.Tm (oneLambdaSig natAlgSig) [] RType.o :=
  OneLambda.app' (OneLambda.lam' redexBody) (conc (natToFreeAlg 0))

/-- The deterministic step contracts the identity β-redex to its argument: the
β worker fires the root contraction, whose reduct instantiates the sole bound
variable by the argument. Through the node equations (no kernel reduction). -/
private theorem detStep_idRedex : detStep idRedex = conc (natToFreeAlg 0) := by
  have hb : betaRedexRank redexBody = 0 := betaRedexRank_var _
  have hf : betaRedexRank (OneLambda.lam' redexBody) = 0 := by
    rw [betaRedexRank_lam', hb]
  have hx : betaRedexRank (conc (natToFreeAlg 0)) = 0 := by
    have := (normal_iff (conc (natToFreeAlg 0))).mp (normal_conc _)
    exact this.1
  have htop : topBetaRank idRedex = 1 := by
    rw [idRedex, topBetaRank_app', if_pos (isLam_lam' redexBody)]
    rfl
  have hrank : betaRedexRank idRedex = 1 := by
    rw [idRedex, betaRedexRank_app', ← idRedex, htop, hf, hx]
    omega
  have hstep : detStep idRedex = detStepAt 1 idRedex := detStep_eq_detStepAt one_pos hrank
  rw [hstep, idRedex, detStepAt_app', if_neg (by rw [hf]; omega), if_neg (by rw [hx]; omega),
    if_pos ⟨isLam_lam' redexBody, by simp⟩, appReduct_lam']
  rw [show Binding.instantiate₁ (conc (natToFreeAlg 0)) redexBody = conc (natToFreeAlg 0) from by
    rw [redexBody, Binding.instantiate₁, Binding.instantiate, Binding.sub_var, boundVar,
      Binding.extendEnv_appendRight]
    rfl]

end GebLean.Ramified.OneLambda
