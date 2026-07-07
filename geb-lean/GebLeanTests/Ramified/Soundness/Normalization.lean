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

end GebLean.Ramified
