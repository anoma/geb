import GebLean.Ramified.Soundness.NormStepER

/-!
# Ramified-recurrence soundness: code-reads ER-realization tests

Acceptance examples for the elementary-recursive realization of the non-recursive
code reads of `NormStepER.lean`: each read's interpretation, evaluated on a
concrete code of the Task 6.4.1 redex family, computes the structural component
the mirrored ℕ-level function reads. The sort-code reads are exercised on the
arrow type code `o → o`; the operation-node and derived reads on canonical
operation-node codes and a saturated destructor redex, through the `@[simp]`
interpretation lemmas and the code-level node equations (no kernel reduction on
the reads).

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`.
-/

namespace GebLean.Ramified.OneLambda

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

end GebLean.Ramified.OneLambda
