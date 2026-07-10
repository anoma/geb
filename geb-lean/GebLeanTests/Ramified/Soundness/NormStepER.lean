import GebLean.Ramified.Soundness.NormStepER

/-!
# Ramified-recurrence soundness: normalizer-step ER-realization tests

Acceptance examples for the elementary-recursive realization of the non-recursive
code reads of `NormStepER.lean`: each read's interpretation, evaluated on a
concrete code of the Task 6.4.1 redex family, computes the structural component
the mirrored ℕ-level function reads. The sort-code reads are exercised on the
arrow type code `o → o`; the operation-node and derived reads on canonical
operation-node codes and a saturated destructor redex, through the `@[simp]`
interpretation lemmas and the code-level node equations (no kernel reduction on
the reads). The β-rank and ι-census folds are exercised on a β-redex (rank `1`) and
an ι-spine redex (census `1`), and on a nullary constant (rank and census `0`),
through the fold interpretation lemmas and the code-level node equations. The ι
worker is exercised on the ι-spine redex, where it contracts the root destructor
miss to the scrutinee, and on the nullary constant, where it is the identity. The
weakening worker is exercised on variable leaves below and at the insertion level,
and its two-fold iterate on a variable leaf bumped twice, through the fold and
bounded-recursion interpretation lemmas and the `shiftCode` node equations. The
substitution fold is exercised on the Task 6.4.1 redex body, restating the
`subCode_codeTm` redex-body instance through `subER_interp`, and on a variable leaf
at the substituted level, where it lands the substituend. The β-worker fold is
exercised on the Task 6.4.1 identity β-redex, which contracts to its argument at
its dispatched rank, and on the nullary constant, where it is the identity. The
closed-term dispatch is exercised on the β-redex, where the positive β-rank routes to
the β worker, on the ι-spine redex, where the zero β-rank and the ι-census route to
the ι worker, and on the nullary constant, where both guards fail and the step is the
identity.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`.
-/

namespace GebLean.Ramified.OneLambda

open GebLean.Binding

/-- The arrow type code `o → o`: the sort of the Task 6.4.1 redex's abstraction. -/
private def arrowCode : ℕ := codeRType (RType.arrow RType.o RType.o)

/-- A canonical application-node code: operation kind bit `0`, payload `4`, child
codes `5` and `6`. -/
private def appNode : ℕ := Nat.pair 1 (Nat.pair (Nat.pair 0 4) (Nat.pair 5 (Nat.pair 6 0)))

/-- A canonical abstraction-node code: operation kind bit `1`. -/
private def lamNode : ℕ := Nat.pair 1 (Nat.pair (Nat.pair 1 0) 7)

/-- A canonical constructor-constant node code: operation kind bit `2`, payload
`3`. -/
private def conNode : ℕ := Nat.pair 1 (Nat.pair (Nat.pair 2 3) 0)

/-- The scrutinee of the destructor redex: an application node (shape `1`, kind
`0`) whose argument child is `9`. -/
private def dstrScrut : ℕ := Nat.pair 1 (Nat.pair (Nat.pair 0 0) (Nat.pair 8 (Nat.pair 9 0)))

/-- A saturated destructor redex: an application node whose function child is a
destructor constant (kind bit `3`) applied to `dstrScrut`. -/
private def dstrRedex : ℕ :=
  Nat.pair 1 (Nat.pair 0
    (Nat.pair (Nat.pair 1 (Nat.pair (Nat.pair 3 0) 0)) (Nat.pair dstrScrut 0)))

/-- The shape-tag read on the arrow type code is the arrow tag `1`. -/
example : shapeER.interp ![arrowCode] = 1 := by
  rw [shapeER_interp, arrowCode]; simp [shapeCode, Nat.unpair_pair]

/-- The argument-code read on the arrow type code is the pair of the domain and
codomain type codes. -/
example : argER.interp ![arrowCode] = Nat.pair (codeRType RType.o) (codeRType RType.o) := by
  rw [argER_interp, arrowCode]; simp [argCode, Nat.unpair_pair]

/-- The domain-code read on the arrow type code is the base sort code. -/
example : domER.interp ![arrowCode] = codeRType RType.o := by
  rw [domER_interp, arrowCode]; simp [domCode, argCode, Nat.unpair_pair]

/-- The codomain-code read on the arrow type code is the base sort code. -/
example : codER.interp ![arrowCode] = codeRType RType.o := by
  rw [codER_interp, arrowCode]; simp [codCode, argCode, Nat.unpair_pair]

/-- The first-child read on the application node is its first child code `5`. -/
example : child0ER.interp ![appNode] = 5 := by
  rw [child0ER_interp, appNode, child0Code_pair]

/-- The second-child read on the application node is its second child code `6`. -/
example : child1ER.interp ![appNode] = 6 := by
  rw [child1ER_interp, appNode, child1Code_pair]

/-- The operation-kind read on the application node is the application kind bit
`0`. -/
example : opKindER.interp ![appNode] = 0 := by
  rw [opKindER_interp, appNode, opKindCode_pair]; simp [Nat.unpair_pair]

/-- The operation-payload read on the application node is its payload `4`. -/
example : opPayloadER.interp ![appNode] = 4 := by
  rw [opPayloadER_interp, appNode, opPayloadCode_pair]; simp [Nat.unpair_pair]

/-- The constructor-label read on the constructor-constant node is its payload
`3`. -/
example : conLabelER.interp ![conNode] = 3 := by
  rw [conLabelER_interp, conNode]; simp [conLabelCode, opKindCode, opPayloadCode, Nat.unpair_pair]

/-- The abstraction detector on the abstraction node reads `1` (Decision Q3). -/
example : isLamER.interp ![lamNode] = 1 := by
  rw [isLamER_interp, lamNode]; simp [isLamCode, Nat.unpair_pair]

/-- The result-sort shape read on the abstraction node is the arrow shape `1`. -/
example : resultShapeER.interp ![lamNode] = 1 := by
  rw [resultShapeER_interp, lamNode, resultShapeCode]; simp [Nat.unpair_pair]

/-- The ι-contraction read on the destructor redex selects the scrutinee's
argument child `9`. -/
example : iotaContractER.interp ![dstrRedex] = 9 := by
  rw [iotaContractER_interp, dstrRedex,
    iotaContractCode_dstr _ _ _ _ (by simp [Nat.unpair_pair]), dstrScrut]
  simp [opKindCode, child1Code, Nat.unpair_pair]

/-- The type-order fold on the base sort code `o` reads order `RType.ord o = 0`,
through `ordCode_codeRType`. -/
example : ordER.interp ![codeRType RType.o] = 0 := by
  rw [ordER_interp, ordCode_codeRType]; simp

/-- The type-order fold on the `Ω o` code reads order `RType.ord (Ω o) = 0`. -/
example : ordER.interp ![codeRType (RType.omega RType.o)] = 0 := by
  rw [ordER_interp, ordCode_codeRType]; simp

/-- The type-order fold on the arrow code `o → o` reads order
`RType.ord (o → o) = 1`. -/
example : ordER.interp ![arrowCode] = 1 := by
  rw [arrowCode, ordER_interp, ordCode_codeRType]; simp

/-- The top-β-rank read on the abstraction node is `0`: an abstraction node is not
an application. -/
example : topBetaRankER.interp ![lamNode] = 0 := by
  rw [topBetaRankER_interp, lamNode,
    topBetaRankCode_op_ne_app _ _ (by simp [Nat.unpair_pair])]

/-- The top-β-rank read on the destructor redex is `0`: the application's function
child is a destructor head, not an abstraction. -/
example : topBetaRankER.interp ![dstrRedex] = 0 := by
  rw [topBetaRankER_interp, dstrRedex,
    topBetaRankCode_app _ _ _ (by decide),
    if_neg (by rw [isLamCode_op]; simp [Nat.unpair_pair])]

/-- An ι-spine redex: an application node (kind `0`) whose function child is a
destructor head (kind `3`) and whose argument child is the constructor node
`conNode`, so the ι-spine bottoms at a `con`-headed argument. -/
private def iotaSpineRedex : ℕ :=
  Nat.pair 1 (Nat.pair (Nat.pair 0 0)
    (Nat.pair (Nat.pair 1 (Nat.pair (Nat.pair 3 0) 0)) (Nat.pair conNode 0)))

/-- The `con`-headedness fold on the constructor-constant node reads `1`: a
constructor node is `con`-headed (Decision Q3). -/
example : conHeadedER.interp ![conNode] = 1 := by
  rw [conHeadedER_interp, conNode, conHeadedCode_con _ _ (by simp [Nat.unpair_pair])]
  rfl

/-- The `con`-headedness fold on the abstraction node reads `0`: an abstraction node
(kind `1`) is neither an application nor a constructor. -/
example : conHeadedER.interp ![lamNode] = 0 := by
  rw [conHeadedER_interp, lamNode,
    conHeadedCode_op_false _ _ (by simp [Nat.unpair_pair]) (by simp [Nat.unpair_pair])]
  rfl

/-- The ι-spine fold on the ι-spine redex reads `1`: the destructor-headed spine
bottoms at the `con`-headed argument `conNode`. -/
example : iotaSpineER.interp ![iotaSpineRedex] = 1 := by
  have hspine : iotaSpineCode iotaSpineRedex = true := by
    rw [iotaSpineRedex, iotaSpineCode_app _ _ _ (by simp [Nat.unpair_pair])]
    simp only [Nat.unpair_pair]
    rw [conNode, conHeadedCode_con _ _ (by simp [Nat.unpair_pair])]
  rw [iotaSpineER_interp, hspine]
  rfl

/-- The ι-spine fold on the abstraction node reads `0`: an abstraction node is not
an application and bottoms no spine. -/
example : iotaSpineER.interp ![lamNode] = 0 := by
  rw [iotaSpineER_interp, lamNode, iotaSpineCode_op_ne_app _ _ (by simp [Nat.unpair_pair])]
  rfl

/-- The sort-gated ι-redex read on the ι-spine redex reads `1`: the result-sort
shape is the base sort and the spine detector holds. -/
example : topIotaER.interp ![iotaSpineRedex] = 1 := by
  have hspine : iotaSpineCode iotaSpineRedex = true := by
    rw [iotaSpineRedex, iotaSpineCode_app _ _ _ (by simp [Nat.unpair_pair])]
    simp only [Nat.unpair_pair]
    rw [conNode, conHeadedCode_con _ _ (by simp [Nat.unpair_pair])]
  have hgate : resultShapeCode iotaSpineRedex = 0 := by
    rw [iotaSpineRedex, resultShapeCode_app _ _ (by simp [Nat.unpair_pair])]
    simp [codCode, argCode, shapeCode, Nat.unpair_pair]
  rw [topIotaER_interp, topIotaCode, if_pos hgate, hspine]
  rfl

/-- The abstraction child of the β-redex: a `lam` node (kind bit `1`) of arrow sort
`o → o` over a variable body. -/
private def betaLamChild : ℕ :=
  Nat.pair 1 (Nat.pair (Nat.pair 1 0) (Nat.pair (Nat.pair 0 0) 0))

/-- A β-redex code: the application (kind bit `0`, arrow-sort payload `o → o`) of the
abstraction `betaLamChild` to a variable argument. The Task 6.4.1 redex-family
instance whose β-rank the fold reads. -/
private def betaRedex : ℕ :=
  Nat.pair 1 (Nat.pair (Nat.pair 0 (Nat.pair (codeRType RType.o) (codeRType RType.o)))
    (Nat.pair betaLamChild (Nat.pair (Nat.pair 0 1) 0)))

/-- The β-rank fold on the β-redex reads rank `1`: the applied abstraction has arrow
sort `o → o` of order `1`, and neither child carries a redex. -/
example : betaRankER.interp ![betaRedex] = 1 := by
  have hlam : isLamCode betaLamChild = true := by
    rw [betaLamChild, isLamCode_op]; simp [Nat.unpair_pair]
  have htop : topBetaRankCode betaRedex = 1 := by
    rw [betaRedex, topBetaRankCode_app _ _ _ (by simp [Nat.unpair_pair]), hlam, if_pos rfl]
    simp only [Nat.unpair_pair]
    rw [show Nat.pair 1 (Nat.pair (codeRType RType.o) (codeRType RType.o))
          = codeRType (RType.arrow RType.o RType.o) from rfl, ordCode_codeRType]
    simp
  have hc0 : betaRankCode betaLamChild = 0 := by
    rw [betaLamChild, betaRankCode_lam _ _ (by simp [Nat.unpair_pair]), betaRankCode_var]
  have hrank : betaRankCode betaRedex = 1 := by
    rw [betaRedex, betaRankCode_app _ _ _ (by simp [Nat.unpair_pair]), ← betaRedex, htop, hc0,
      betaRankCode_var]
    decide
  rw [betaRankER_interp, hrank]

/-- The β-rank fold on the constructor-constant node reads `0`: a nullary constant is
no redex. -/
example : betaRankER.interp ![conNode] = 0 := by
  rw [betaRankER_interp, conNode, betaRankCode_op_ge_two _ _ (by simp [Nat.unpair_pair])]

/-- The ι-census fold on the ι-spine redex reads `1`: the redex is itself a top
ι-redex (Decision Q3). -/
example : hasIotaER.interp ![iotaSpineRedex] = 1 := by
  have hspine : iotaSpineCode iotaSpineRedex = true := by
    rw [iotaSpineRedex, iotaSpineCode_app _ _ _ (by simp [Nat.unpair_pair])]
    simp only [Nat.unpair_pair]
    rw [conNode, conHeadedCode_con _ _ (by simp [Nat.unpair_pair])]
  have hgate : resultShapeCode iotaSpineRedex = 0 := by
    rw [iotaSpineRedex, resultShapeCode_app _ _ (by simp [Nat.unpair_pair])]
    simp [codCode, argCode, shapeCode, Nat.unpair_pair]
  have htop : topIotaCode iotaSpineRedex = true := by
    rw [topIotaCode, if_pos hgate, hspine]
  have hcensus : hasIotaCode iotaSpineRedex = true := by
    conv_lhs => rw [iotaSpineRedex]
    rw [hasIotaCode_app _ _ _ (by simp [Nat.unpair_pair]), ← iotaSpineRedex, htop,
      Bool.true_or, Bool.true_or]
  rw [hasIotaER_interp, hcensus]; rfl

/-- The ι-census fold on the constructor-constant node reads `0`: a nullary constant
carries no ι-redex. -/
example : hasIotaER.interp ![conNode] = 0 := by
  rw [hasIotaER_interp, conNode, hasIotaCode_op_ge_two _ _ (by simp [Nat.unpair_pair])]
  rfl

/-- The ι worker on the ι-spine redex contracts the root destructor miss to the
scrutinee `conNode`: neither child carries an ι-redex, the node is a saturated top
ι-redex, and `iotaContractCode` reads the destructor miss. -/
example : iotaStepER.interp ![iotaSpineRedex] = conNode := by
  have hc0 : hasIotaCode (Nat.pair 1 (Nat.pair (Nat.pair 3 0) 0)) = false :=
    hasIotaCode_op_ge_two _ _ (by simp [Nat.unpair_pair])
  have hc1 : hasIotaCode conNode = false := by
    rw [conNode]; exact hasIotaCode_op_ge_two _ _ (by simp [Nat.unpair_pair])
  have hgate : resultShapeCode iotaSpineRedex = 0 := by
    rw [iotaSpineRedex, resultShapeCode_app _ _ (by simp [Nat.unpair_pair])]
    simp [codCode, argCode, shapeCode, Nat.unpair_pair]
  have hspine : iotaSpineCode iotaSpineRedex = true := by
    rw [iotaSpineRedex, iotaSpineCode_app _ _ _ (by simp [Nat.unpair_pair])]
    simp only [Nat.unpair_pair]
    rw [conNode, conHeadedCode_con _ _ (by simp [Nat.unpair_pair])]
  have htop : topIotaCode iotaSpineRedex = true := by
    rw [topIotaCode, if_pos hgate, hspine]
  have hcontract : iotaContractCode iotaSpineRedex = conNode := by
    rw [iotaSpineRedex, iotaContractCode_dstr _ _ _ _ (by simp [Nat.unpair_pair]),
      if_neg (by rw [conNode]; simp [opKindCode, Nat.unpair_pair])]
  have hstep : iotaStepCode iotaSpineRedex = conNode := by
    conv_lhs => rw [iotaSpineRedex]
    rw [iotaStepCode_app _ _ _ (by simp [Nat.unpair_pair]), ← iotaSpineRedex,
      if_neg (by simp [hc0]), if_neg (by simp [hc1]), if_pos htop, hcontract]
  rw [iotaStepER_interp, hstep]

/-- The ι worker on the constructor-constant node is the identity: a nullary constant
carries no ι-redex to contract. -/
example : iotaStepER.interp ![conNode] = conNode := by
  rw [iotaStepER_interp, conNode, iotaStepCode_const _ _ (by simp [Nat.unpair_pair])]

/-- The weakening worker on a variable leaf below the insertion level is the identity:
a level `2` variable stays fixed under insertion at level `5`. -/
example : shiftER.interp ![Nat.pair 0 2, 5] = Nat.pair 0 2 := by
  rw [shiftER_interp, shiftCode_var, if_pos (by omega)]

/-- The weakening worker on a variable leaf at the insertion level bumps it: a level `5`
variable rises to level `6` under insertion at level `5`. -/
example : shiftER.interp ![Nat.pair 0 5, 5] = Nat.pair 0 6 := by
  rw [shiftER_interp, shiftCode_var, if_neg (by omega)]

/-- The two-fold iterated weakening on a variable leaf bumps its level twice: a level `3`
variable rises to level `5` under two insertions at level `0`. -/
example : shiftIterER.interp ![2, 0, Nat.pair 0 3] = Nat.pair 0 5 := by
  rw [shiftIterER_interp, show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply,
    Function.iterate_one, shiftCode_var, if_neg (by omega), shiftCode_var, if_neg (by omega)]

/-- The substitution fold on a variable leaf at the substituted level lands the
substituend: substituting `conNode` for the level `5` variable at level `5`. -/
example : subER.interp ![Nat.pair 0 5, 5, conNode] = conNode := by
  rw [subER_interp, subCode_var, if_neg (by omega), if_pos rfl]

/-- The substituted variable of the Task 6.4.1 identity β-redex body `x`, the sole
bound variable of the singleton suffix `[o]`. -/
private def redexBody : Binding.Tm (oneLambdaSig natAlgSig) ([] ++ [RType.o]) RType.o :=
  Binding.Tm.var (boundVar (Γ := []) (σ := RType.o))

/-- The substitution fold on the code of the Task 6.4.1 redex body computes the code
of its `Binding.instantiate₁` reduct: the `subCode_codeTm` redex-body instance
restated through `subER_interp`, substituting the concrete zero word for the sole
bound variable of the identity β-redex body. -/
example :
    subER.interp ![codeTm redexBody, ([] : Binding.Ctx RType).length,
        codeTm (conc (natToFreeAlg 0))]
      = codeTm (Binding.instantiate₁ (conc (natToFreeAlg 0)) redexBody) := by
  rw [subER_interp]
  exact subCode_codeTm (conc (natToFreeAlg 0)) redexBody

/-- The β worker on the Task 6.4.1 identity β-redex at its dispatched rank `1`
contracts to the argument: neither child carries a rank-`1` redex, the function
child is an abstraction of arrow sort `o → o` (order `1`), and the contraction
substitutes the level-`1` variable argument for the abstraction's level-`0` body
variable. -/
example : betaStepER.interp ![betaRedex, 1] = Nat.pair 0 1 := by
  have hlam : isLamCode betaLamChild = true := by
    rw [betaLamChild, isLamCode_op]; simp [Nat.unpair_pair]
  have hc0 : betaRankCode betaLamChild = 0 := by
    rw [betaLamChild, betaRankCode_lam _ _ (by simp [Nat.unpair_pair]), betaRankCode_var]
  have hord : ordCode (Nat.pair 1
      (Nat.pair (codeRType RType.o) (codeRType RType.o))) = 1 := by
    rw [show Nat.pair 1 (Nat.pair (codeRType RType.o) (codeRType RType.o))
        = codeRType (RType.arrow RType.o RType.o) from rfl, ordCode_codeRType]
    simp
  have hstep : betaStepCode 1 0 betaRedex = Nat.pair 0 1 := by
    rw [betaRedex, betaStepCode_app _ _ _ _ _ (by simp [Nat.unpair_pair])]
    simp only [Nat.unpair_pair]
    rw [if_neg (by rw [hc0]; omega), if_neg (by rw [betaRankCode_var]; omega),
      if_pos ⟨hlam, hord⟩, betaLamChild]
    simp only [Nat.unpair_pair]
    rw [subCode_var, if_neg (by omega), if_pos rfl]
  rw [betaStepER_interp, hstep]

/-- The β worker on the constructor-constant node is the identity: a nullary
constant carries no β-redex to contract. -/
example : betaStepER.interp ![conNode, 0] = conNode := by
  rw [betaStepER_interp, conNode, betaStepCode_const _ _ _ _ (by simp [Nat.unpair_pair])]

/-- The closed-term dispatch on the Task 6.4.1 identity β-redex routes to the β
worker: the β-rank is positive (`1`), so the step contracts the redex to its
argument. -/
example : stepCodeAtZeroER.interp ![betaRedex] = Nat.pair 0 1 := by
  have hlam : isLamCode betaLamChild = true := by
    rw [betaLamChild, isLamCode_op]; simp [Nat.unpair_pair]
  have htop : topBetaRankCode betaRedex = 1 := by
    rw [betaRedex, topBetaRankCode_app _ _ _ (by simp [Nat.unpair_pair]), hlam, if_pos rfl]
    simp only [Nat.unpair_pair]
    rw [show Nat.pair 1 (Nat.pair (codeRType RType.o) (codeRType RType.o))
          = codeRType (RType.arrow RType.o RType.o) from rfl, ordCode_codeRType]
    simp
  have hc0 : betaRankCode betaLamChild = 0 := by
    rw [betaLamChild, betaRankCode_lam _ _ (by simp [Nat.unpair_pair]), betaRankCode_var]
  have hrank : betaRankCode betaRedex = 1 := by
    rw [betaRedex, betaRankCode_app _ _ _ (by simp [Nat.unpair_pair]), ← betaRedex, htop, hc0,
      betaRankCode_var]
    decide
  have hord : ordCode (Nat.pair 1
      (Nat.pair (codeRType RType.o) (codeRType RType.o))) = 1 := by
    rw [show Nat.pair 1 (Nat.pair (codeRType RType.o) (codeRType RType.o))
        = codeRType (RType.arrow RType.o RType.o) from rfl, ordCode_codeRType]
    simp
  have hstep : betaStepCode 1 0 betaRedex = Nat.pair 0 1 := by
    rw [betaRedex, betaStepCode_app _ _ _ _ _ (by simp [Nat.unpair_pair])]
    simp only [Nat.unpair_pair]
    rw [if_neg (by rw [hc0]; omega), if_neg (by rw [betaRankCode_var]; omega),
      if_pos ⟨hlam, hord⟩, betaLamChild]
    simp only [Nat.unpair_pair]
    rw [subCode_var, if_neg (by omega), if_pos rfl]
  rw [stepCodeAtZeroER_interp, stepCodeAt, hrank, if_pos (by omega), hstep]

/-- The closed-term dispatch on the ι-spine redex routes to the ι worker: the β-rank
is `0` and the ι-census holds, so the step contracts the root destructor miss to the
scrutinee `conNode`. -/
example : stepCodeAtZeroER.interp ![iotaSpineRedex] = conNode := by
  have hrank : betaRankCode iotaSpineRedex = 0 := by
    rw [iotaSpineRedex, betaRankCode_app _ _ _ (by simp [Nat.unpair_pair]),
      topBetaRankCode_app _ _ _ (by simp [Nat.unpair_pair]),
      if_neg (by rw [isLamCode_op]; simp [Nat.unpair_pair]),
      betaRankCode_op_ge_two _ _ (by simp [Nat.unpair_pair]),
      conNode, betaRankCode_op_ge_two _ _ (by simp [Nat.unpair_pair])]
    simp
  have hc0 : hasIotaCode (Nat.pair 1 (Nat.pair (Nat.pair 3 0) 0)) = false :=
    hasIotaCode_op_ge_two _ _ (by simp [Nat.unpair_pair])
  have hc1 : hasIotaCode conNode = false := by
    rw [conNode]; exact hasIotaCode_op_ge_two _ _ (by simp [Nat.unpair_pair])
  have hgate : resultShapeCode iotaSpineRedex = 0 := by
    rw [iotaSpineRedex, resultShapeCode_app _ _ (by simp [Nat.unpair_pair])]
    simp [codCode, argCode, shapeCode, Nat.unpair_pair]
  have hspine : iotaSpineCode iotaSpineRedex = true := by
    rw [iotaSpineRedex, iotaSpineCode_app _ _ _ (by simp [Nat.unpair_pair])]
    simp only [Nat.unpair_pair]
    rw [conNode, conHeadedCode_con _ _ (by simp [Nat.unpair_pair])]
  have htop : topIotaCode iotaSpineRedex = true := by
    rw [topIotaCode, if_pos hgate, hspine]
  have hcensus : hasIotaCode iotaSpineRedex = true := by
    conv_lhs => rw [iotaSpineRedex]
    rw [hasIotaCode_app _ _ _ (by simp [Nat.unpair_pair]), ← iotaSpineRedex, htop,
      Bool.true_or, Bool.true_or]
  have hcontract : iotaContractCode iotaSpineRedex = conNode := by
    rw [iotaSpineRedex, iotaContractCode_dstr _ _ _ _ (by simp [Nat.unpair_pair]),
      if_neg (by rw [conNode]; simp [opKindCode, Nat.unpair_pair])]
  have hstep : iotaStepCode iotaSpineRedex = conNode := by
    conv_lhs => rw [iotaSpineRedex]
    rw [iotaStepCode_app _ _ _ (by simp [Nat.unpair_pair]), ← iotaSpineRedex,
      if_neg (by simp [hc0]), if_neg (by simp [hc1]), if_pos htop, hcontract]
  rw [stepCodeAtZeroER_interp, stepCodeAt, hrank, if_neg (by omega), if_pos hcensus, hstep]

/-- The closed-term dispatch on the nullary constant is the identity: the β-rank is
`0` and the ι-census fails, so both dispatch guards fall through. -/
example : stepCodeAtZeroER.interp ![conNode] = conNode := by
  have hrank : betaRankCode conNode = 0 := by
    rw [conNode, betaRankCode_op_ge_two _ _ (by simp [Nat.unpair_pair])]
  have hcensus : hasIotaCode conNode = false := by
    rw [conNode]; exact hasIotaCode_op_ge_two _ _ (by simp [Nat.unpair_pair])
  rw [stepCodeAtZeroER_interp, stepCodeAt, hrank, if_neg (by omega),
    if_neg (by rw [hcensus]; simp)]

/-- The Task 6.4.1 identity β-redex as a closed term: the identity abstraction
`λx:o. x` applied to the zero constructor `con 0`, a closed term at the base sort
`o`. -/
private def idBetaRedex : Binding.Tm (oneLambdaSig natAlgSig) [] RType.o :=
  app' (lam' redexBody) (conc (natToFreeAlg 0))

/-- The assembled normalizer step on the code of the Task 6.4.1 identity β-redex
computes the code of its deterministic reduct: `normStep_interp` reduces the step to
`stepCode`, and the closed-term commutation `stepCode_codeTm` identifies it with the
`detStep` image. -/
example : normStep.interp ![codeTm idBetaRedex] = codeTm (detStep idBetaRedex) := by
  rw [normStep_interp]
  exact stepCode_codeTm idBetaRedex

/-- The assembled normalizer step fixes a normal code: on the constructor-constant
node `conNode` the closed-term dispatch is the identity (`stepCodeAt 0 conNode =
conNode`) and the clamp is inactive (`conNode ≤ stepBound conNode`), so `normStep`
returns `conNode`. -/
example : normStep.interp ![conNode] = conNode := by
  have hrank : betaRankCode conNode = 0 := by
    rw [conNode, betaRankCode_op_ge_two _ _ (by simp [Nat.unpair_pair])]
  have hcensus : hasIotaCode conNode = false := by
    rw [conNode]; exact hasIotaCode_op_ge_two _ _ (by simp [Nat.unpair_pair])
  have hstep : stepCodeAt 0 conNode = conNode := by
    rw [stepCodeAt, hrank, if_neg (by omega), if_neg (by rw [hcensus]; simp)]
  have hle : conNode ≤ stepBound conNode := by
    rw [stepBound]
    refine le_trans ?_ (self_le_tower 2 _)
    generalize (conNode + 1) ^ 2 = X
    omega
  rw [normStep_interp, stepCode, hstep, min_eq_left hle]

end GebLean.Ramified.OneLambda
