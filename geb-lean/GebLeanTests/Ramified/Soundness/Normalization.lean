import GebLean.Ramified.Soundness.Normalization

/-!
# Tests for the Lemma 12 normalization bound

Tests for the type-order measure `RType.ord` (task 6.3.3) and the redex-rank
measure `redexRank`, `Normal`, and the redex detectors (task 6.3.4a).
-/

namespace GebLean.Ramified

open GebLean.Binding GebLean.Ramified.OneLambda

/-- The tower of twos is strictly monotone in its second argument: a
statement-shape check for `tower_lt_tower_right` at height `2`. -/
example : tower 2 3 < tower 2 4 := tower_lt_tower_right 2 (by decide)

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

/-- One rank-elimination cycle on the identity β-redex `(λx:o. x) c₀` (note
N3): the rank-`1` term of size `4` and height `3` reduces, within the hybrid
ceiling `260 = 4 + 2 ^ (2 ^ 3)`, to a β-normal term. The rank and ceiling side
conditions are discharged by kernel computation on the closed term. -/
example :
    ∃ (t' : Binding.Tm (oneLambdaSig natAlgSig) [] RType.o) (k : ℕ),
      Relation.RelatesInSteps (stepWithin 260)
        (OneLambda.app'
          (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
          (conc (natToFreeAlg 0))) t' k ∧ betaRedexRank t' = 0 := by
  obtain ⟨t', k, hchain, hrank, -, -, -⟩ :=
    beta_cycle (A := natAlgSig) 1 le_rfl
      (OneLambda.app'
        (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
        (conc (natToFreeAlg 0)))
      (by decide) (M := 260) (by decide)
  exact ⟨t', k, hchain, by omega⟩

/-- β-normalization on the identity β-redex `(λx:o. x) c₀` (note N4): the public
`beta_normalize` yields a β-normal reduct of height at most `tower 1 3 = 8`, in at
most `1 * tower 1 3 = 8` steps, within the tower ceiling `tower 2 4`. The concrete
measures (`betaRedexRank = 1`, `Tm.height = 3`) are substituted by kernel
computation on the closed term. -/
example :
    ∃ (t' : Binding.Tm (oneLambdaSig natAlgSig) [] RType.o) (k : ℕ),
      Relation.RelatesInSteps (stepWithin (tower 2 4))
        (OneLambda.app'
          (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
          (conc (natToFreeAlg 0))) t' k ∧
      betaRedexRank t' = 0 ∧ Tm.height t' ≤ 8 ∧ k ≤ 8 := by
  obtain ⟨t', k, hchain, hrank, hheight, hk⟩ := beta_normalize (A := natAlgSig)
    (OneLambda.app'
      (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
      (conc (natToFreeAlg 0)))
  exact ⟨t', k, hchain, hrank, hheight, hk⟩

/-- Note N2 on a small instance: instantiating the identity body `x` (the sole
bound variable) by the zero word `N` yields `N`, whose β-rank `0` is within the
bound `max (betaRedexRank b) (max (betaRedexRank N) (RType.ord o))`. -/
example (b : Binding.Tm (oneLambdaSig natAlgSig) ([] ++ [RType.o]) RType.o) :
    betaRedexRank (Binding.instantiate₁ (conc (natToFreeAlg 0)) b)
      ≤ max (betaRedexRank b)
          (max (betaRedexRank (conc (natToFreeAlg 0))) (RType.ord RType.o)) :=
  betaRedexRank_instantiate₁_le _ _

/-- Lemma 12 on the identity β-redex `(λx:o. x) c₀` (note N7): the rank-`1`,
height-`3` term reduces to a `Normal` form, within the tower ceiling
`tower 2 4`, of height at most `tower 1 3 = 8` and in at most
`1 * tower 1 3 + tower 2 3 = 264` steps. The redex rank and height are reduced
by the node simp equations (`redexRank t₀ = 1`, `Tm.height t₀ = 3`); the
resulting numeric bounds close by arithmetic. The mathematical reduct and step
count are `n = c₀` and `k = 1`, well within the elementary bound. -/
example :
    ∃ (n : Binding.Tm (oneLambdaSig natAlgSig) [] RType.o) (k : ℕ),
      Normal n ∧
      Relation.RelatesInSteps (stepWithin (tower 2 4))
        (OneLambda.app'
          (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
          (conc (natToFreeAlg 0))) n k ∧
      Tm.height n ≤ 8 ∧ k ≤ 264 := by
  obtain ⟨n, k, hnorm, hchain, hheight, hk⟩ := lemma12 (A := natAlgSig)
    (OneLambda.app'
      (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
      (conc (natToFreeAlg 0)))
  have hrank : redexRank (OneLambda.app'
      (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
      (conc (natToFreeAlg 0))) = 1 := by
    have hN : redexRank (conc (natToFreeAlg 0)) = 0 := rfl
    rw [redexRank_app', topBetaRank_app', topIota_app', hN]
    simp [isLam_lam', headTag_lam', redexRank, betaRedexRank_lam', hasIota_lam',
      betaRedexRank_var, hasIota_var, RType.ord_arrow, RType.ord_o]
  have hheq : Tm.height (OneLambda.app'
      (OneLambda.lam' (Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))))
      (conc (natToFreeAlg 0))) = 3 := by
    rw [height_app', height_lam', Binding.Tm.height_var,
      show Tm.height (conc (natToFreeAlg 0)) = 1 from rfl]
    omega
  rw [hrank, hheq] at hchain hheight hk
  have ht13 : (tower 1 3 : ℕ) = 8 := rfl
  have ht23 : (tower (1 + 1) 3 : ℕ) = 256 := rfl
  exact ⟨n, k, hnorm, hchain, by omega, by omega⟩

/-- A closed normal term of the base object sort is a constructor word (task
6.3.10): applied to the concrete term of the zero word, `normal_closed_o_eq_conc`
produces a free-algebra value whose concrete term it equals. A statement-shape
check; the existential witness is opaque. -/
example : ∃ a : FreeAlg natAlgSig, conc (natToFreeAlg 0) = conc a :=
  normal_closed_o_eq_conc (conc (natToFreeAlg 0)) (normal_conc _)

/-- The head-form reading applies to the concrete term of any free-algebra value:
`conc a` is closed, normal, and at sort `o`, so it is some word's concrete term. -/
example (a : FreeAlg natAlgSig) : ∃ b : FreeAlg natAlgSig, conc a = conc b :=
  normal_closed_o_eq_conc (conc a) (normal_conc a)

/-- The source-side constructor word evaluates to the value it encodes (task
6.3.11): `appEval (sourceWord a₀ RType.o) finZeroElim = a₀` at the zero word. -/
example : appEval (sourceWord (natToFreeAlg 0) RType.o) finZeroElim = natToFreeAlg 0 :=
  appEval_sourceWord _ _

end GebLean.Ramified
