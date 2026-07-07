import GebLean.Ramified.Soundness.Normalization

/-!
# Tests for the Lemma 12 normalization bound

Tests for the type-order measure `RType.ord` (task 6.3.3) and the redex-rank
measure `redexRank`, `Normal`, and the redex detectors (task 6.3.4a).
-/

namespace GebLean.Ramified

open GebLean.Binding GebLean.Ramified.OneLambda

/-- The order of the twice-nested arrow `(o → o) → o` is `2` (Leivant III
section 2.2, p. 213): the outer `arrow` takes the maximum of `1 + ord (o → o)`
and `ord o`, and `ord (o → o) = max (1 + ord o) (ord o) = 1`. -/
example : (RType.arrow (RType.arrow RType.o RType.o) RType.o).ord = 2 := by simp

/-- The concrete term of the zero word has redex rank `0`: a `con`-headed spine
with neither a β-redex nor an ι-redex. -/
example : redexRank (conc (natToFreeAlg 0)) = 0 := by rfl

/-- The concrete term of the zero word is normal (Leivant III section 4.2). Via
`normal_iff`: it has β-rank `0` and no ι-redex. -/
example : Normal (conc (natToFreeAlg 0)) := by
  rw [normal_iff]; exact ⟨rfl, rfl⟩

/-- The identity redex `(λx:o. x) a₀` at sort `o ⟶ o` has redex rank `1`: the
β-rank of the applied abstraction's arrow sort `RType.ord (o ⟶ o) = 1`, with no
ι-redex present. -/
example : redexRank (OneLambda.app'
    (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
    (conc (natToFreeAlg 0))) = 1 := by
  have hN : redexRank (conc (natToFreeAlg 0)) = 0 := rfl
  rw [redexRank_app', topBetaRank_app', topIota_app', hN]
  simp [isLam_lam', headTag_lam', redexRank, betaRedexRank_lam', hasIota_lam',
    betaRedexRank_var, hasIota_var, RType.ord_arrow, RType.ord_o]

/-- A destructor `dstr 0` applied to the `con`-headed zero word is an ι-redex:
its redex rank is `1` (an ι-redex counts rank exactly `1`) and `hasIota` reports
`true`. -/
example :
    redexRank (OneLambda.app' (Binding.Tm.op (S := oneLambdaSig natAlgSig) (Γ := [])
        (OneLambdaOp.dstr ⟨0, by decide⟩) (fun k => k.elim0)) (conc (natToFreeAlg 0))) = 1
      ∧ hasIota (OneLambda.app' (Binding.Tm.op (S := oneLambdaSig natAlgSig) (Γ := [])
        (OneLambdaOp.dstr ⟨0, by decide⟩) (fun k => k.elim0)) (conc (natToFreeAlg 0))) = true := by
  set dnode : Binding.Tm (oneLambdaSig natAlgSig) [] (RType.arrow RType.o RType.o) :=
    Binding.Tm.op (S := oneLambdaSig natAlgSig) (Γ := [])
      (OneLambdaOp.dstr ⟨0, by decide⟩) (fun k => k.elim0) with hdef
  have hN : redexRank (conc (natToFreeAlg 0)) = 0 := rfl
  have hdnode : redexRank dnode = 0 := rfl
  have hil : isLam dnode = false := rfl
  have htop : topIota (OneLambda.app' dnode (conc (natToFreeAlg 0))) = true := rfl
  refine ⟨?_, ?_⟩
  · rw [redexRank_app', topBetaRank_app', htop, hN, hdnode, hil]; simp
  · rw [hasIota_app', htop]; rfl

/-- An unsaturated con-headed case application `case (c₀)` sits at an arrow sort:
`case : o → o^{numCtors} → o` applied only to its scrutinee has result sort
`o^{numCtors} → o`, so it is irreducible under `OneLambdaStep`. The result-sort
saturation guard reports no ι-redex there: `hasIota … = false`, and with no
β-redex the term is `Normal`. Regression for the guard against flagging
arrow-typed partial case applications. -/
example :
    hasIota (OneLambda.app'
        (Binding.Tm.op (S := oneLambdaSig natAlgSig) (Γ := []) OneLambdaOp.case
          (fun k => k.elim0)) (conc (natToFreeAlg 0))) = false
      ∧ Normal (OneLambda.app'
        (Binding.Tm.op (S := oneLambdaSig natAlgSig) (Γ := []) OneLambdaOp.case
          (fun k => k.elim0)) (conc (natToFreeAlg 0))) := by
  refine ⟨rfl, ?_⟩
  rw [normal_iff]; exact ⟨rfl, rfl⟩

/-- A saturated case spine `case (c₀) b₀ b₁` over the con-headed zero word (all
branches the zero word) is a genuine ι-redex at result sort `o`: `hasIota … =
true` and its redex rank is `1`. Confirms the guard preserves detection of the
`OneLambdaStep.case` shape. -/
example :
    redexRank (OneLambda.replicateSpine natAlgSig.numCtors RType.o
        (OneLambda.app'
          (Binding.Tm.op (S := oneLambdaSig natAlgSig) (Γ := []) OneLambdaOp.case
            (fun k => k.elim0)) (conc (natToFreeAlg 0)))
        (fun _ => conc (natToFreeAlg 0))) = 1
      ∧ hasIota (OneLambda.replicateSpine natAlgSig.numCtors RType.o
        (OneLambda.app'
          (Binding.Tm.op (S := oneLambdaSig natAlgSig) (Γ := []) OneLambdaOp.case
            (fun k => k.elim0)) (conc (natToFreeAlg 0)))
        (fun _ => conc (natToFreeAlg 0))) = true :=
  ⟨rfl, rfl⟩

/-- The concrete term of a free-algebra value is normal (task 6.3.4b): the
constructor-headed spine `conc a` carries no redex, for every `a`. -/
example (a : FreeAlg natAlgSig) : Normal (conc a) := normal_conc a

/-- The Berarducci-Böhm representation is normal (task 6.3.4b): the abstraction
`bbRep a σ` over the variable-headed fold carries no redex, for every value `a`
and sort `σ`. -/
example (a : FreeAlg natAlgSig) (σ : RType) : Normal (bbRep a σ) := normal_bbRep a σ

/-- The Church numeral `bbRep (natToFreeAlg 2) (o ⟶ o)` is normal, an acceptance
instance of `normal_bbRep`. -/
example : Normal (bbRep (natToFreeAlg 2) (RType.arrow RType.o RType.o)) :=
  normal_bbRep _ _

/-- Lemma 12's ι-step existence on the saturated destructor redex `dstr 0` over
the con-headed zero word: the flagged β-normal term takes a step that strictly
decreases the size, does not increase the height, and preserves β-normality. -/
example :
    ∃ t', OneLambdaStep (OneLambda.app' (Binding.Tm.op (S := oneLambdaSig natAlgSig) (Γ := [])
          (OneLambdaOp.dstr ⟨0, by decide⟩) (fun k => k.elim0)) (conc (natToFreeAlg 0))) t'
        ∧ Tm.size t' < Tm.size (OneLambda.app' (Binding.Tm.op (S := oneLambdaSig natAlgSig)
          (Γ := []) (OneLambdaOp.dstr ⟨0, by decide⟩) (fun k => k.elim0))
          (conc (natToFreeAlg 0)))
        ∧ Tm.height t' ≤ Tm.height (OneLambda.app' (Binding.Tm.op (S := oneLambdaSig natAlgSig)
          (Γ := []) (OneLambdaOp.dstr ⟨0, by decide⟩) (fun k => k.elim0))
          (conc (natToFreeAlg 0)))
        ∧ betaRedexRank t' = 0 :=
  exists_iota_step_of_hasIota _ (by rw [hasIota_app']; rfl) rfl

end GebLean.Ramified
