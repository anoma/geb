import GebLean.Ramified.Soundness.CodeNormalizer
import GebLean.Utilities.ERCourseOfValues
import GebLean.LawvereERBoundComputable

/-!
# Ramified recurrence: the deterministic normalizer step as an ER morphism

The elementary-recursive realization layer of the deterministic code normalizer
of the simply-typed calculus `1λ(natAlgSig)` (Leivant III section 4.2,
pp. 223-224). This module realizes the deterministic step of
`GebLean/Ramified/Soundness/CodeNormalizer.lean` as the `ERMor1` morphism
`OneLambda.normStep`, together with every ingredient it composes: the
non-recursive sort-code projections and operation-node structure reads, the
course-of-values folds, the iterated weakening, the gated two-dimensional
substitution and β workers, the closed-term dispatch, and the step majorant. Each
construction's interpretation equals the mirrored ℕ-level function of
`CodeNormalizer.lean`. Each read is a plain composition of the elementary-recursive
Gödel-arithmetic generators (`ERMor1.natUnpairFst`, `ERMor1.natUnpairSnd`,
`ERMor1.natN`, `ERMor1.proj`, `ERMor1.condN`, `ERMor1.boolEqNat`,
`ERMor1.boolAnd`).

The generators compose in dependency order: the type-order fold
`OneLambda.ordER` (the first `ERMor1.cvRec` instantiation) and the top-β-rank read
`OneLambda.topBetaRankER`; the `con`-headedness and ι-spine detector folds
`OneLambda.conHeadedER`, `OneLambda.iotaSpineER` and the sort-gated ι-redex read
`OneLambda.topIotaER`; the β-rank and ι-census folds `OneLambda.betaRankER`,
`OneLambda.hasIotaER`; the ι worker `OneLambda.iotaStepER` (the first fold that
rebuilds nodes under a tower-2 majorant); the weakening worker `OneLambda.shiftER`
and its iterate `OneLambda.shiftIterER`; the code-level substitution
`OneLambda.subER` (the first gated two-dimensional fold `ERMor1.cvRecGated`, keyed by
a weakening depth and a code) and the β worker `OneLambda.betaStepER` (the second,
keyed by a substitution level and a code); the step majorant
`OneLambda.stepBoundER`, the closed-term dispatch `OneLambda.stepCodeAtZeroER`, and
the assembled step `OneLambda.normStep`; and the clocked iteration
`OneLambda.normRun`. Carrying the deterministic step into the
elementary-recursive theory is the formal payment of the machine-model absorption
Leivant III leaves to a footnote (footnote 10, p. 226). Novel realization.

## Main definitions

- `OneLambda.shapeER`, `OneLambda.argER`, `OneLambda.domER`, `OneLambda.codER` —
  the sort-code reads: the shape tag and the child codes of a type code.
- `OneLambda.child0ER`, `OneLambda.child1ER`, `OneLambda.opKindER`,
  `OneLambda.opPayloadER` — the operation-node reads: the two child codes and the
  operation kind bit and payload of an operation node.
- `OneLambda.conLabelER`, `OneLambda.isLamER`, `OneLambda.resultShapeER`,
  `OneLambda.iotaContractER` — the derived reads: the constructor label, the
  abstraction detector, the result-sort shape, and the ι-contraction image.
- `OneLambda.ordER` — the type-order course-of-values fold, `ERMor1.cvRec` at the
  code-valued node `ordNode`; `OneLambda.topBetaRankER` — the top-β-rank read
  composing the top-node reads and `ordER`.
- `OneLambda.conHeadedER`, `OneLambda.iotaSpineER` — the `con`-headedness and
  ι-spine detector folds, `ERMor1.cvRec` at the `Bool.toNat`-valued nodes
  `conHeadedNode`, `iotaSpineNode` with constant value bound `1`; `OneLambda.topIotaER`
  — the non-recursive sort-gated ι-redex read composing `resultShapeER` and
  `iotaSpineER`.
- `OneLambda.betaRankER`, `OneLambda.hasIotaER` — the β-rank and ι-census folds,
  `ERMor1.cvRec` at the nodes `betaRankNode`, `hasIotaNode`; the β-rank fold takes the
  successor of the fold slot as value bound and composes `topBetaRankER`, the ι-census
  fold the constant bound `1` and composes `topIotaER`.
- `OneLambda.iotaStepER` — the ι worker, `ERMor1.cvRec` at the node `iotaStepNode`
  with value bound the `towerER 2` composite over `9 * c + 9`; the node rebuilds
  application and abstraction nodes with `natPair`, composing `hasIotaER`,
  `topIotaER`, `iotaContractER` as full calls and β-reading the child positions for
  the same-function descent.
- `OneLambda.shiftER` — the code-level weakening worker, `ERMor1.cvRec` at `k = 1` with the
  insertion level in the parameter slot and node `shiftNode`; the node bumps a variable leaf
  read against the level via `ltN`/`condN` and rebuilds operation nodes with `natPair`.
- `OneLambda.shiftIterER` — the iterated weakening, `ERMor1.boundedRec` over `shiftER`
  (Decision Q7), one weakening step per depth increment.
- `OneLambda.subER` — the code-level substitution at slots `(c, j, e)`, the first gated
  two-dimensional fold: `ERMor1.cvRecGated` at index `Nat.pair d m` (weakening depth,
  code) with gate `d + m ≤ c`, index bound `Nat.pair c c`, extraction at `Nat.pair 0 c`,
  and value bound the `towerER 2` composite over `27 * c + 9 * e + 18` (Decision Q8);
  the node mirrors the `subCode` arms, composing `shiftIterER` as a full call at the
  variable-hit leaf and absorbing the abstraction descent's substituend shift into the
  depth component of the index.
- `OneLambda.betaStepER` — the β worker at slots `(c, q)`, the second gated
  two-dimensional fold: `ERMor1.cvRecGated` at index `Nat.pair d m` (substitution
  level, code) with gate `d + m ≤ c`, index bound `Nat.pair c c`, extraction at
  `Nat.pair 0 c`, and value bound the `towerER 2` composite over `36 * c + 18`; the
  node mirrors the four guard regimes of the `betaStepCode` application arm, composing
  `betaRankER`, `isLamER`, `ordER`, and `subER` as full calls and absorbing the
  abstraction descent's level increment into the depth component of the index.
- `OneLambda.stepBoundER` — the step majorant, the `towerER 2` composite over the
  quadratic polynomial `6 * (2 * (n + 1) ^ 2 + n + 1)`, realizing `stepBound`.
- `OneLambda.stepCodeAtZeroER` — the closed-term deterministic step, the literal
  `condN` dispatch of `stepCodeAt 0`: the sign of the β-rank read selects the β
  worker at the code's own rank, else the ι-census read selects the ι worker, else the
  identity.
- `OneLambda.normStep` — the assembled deterministic normalizer step, the closed-term
  dispatch `stepCodeAtZeroER` clamped below the step majorant `stepBoundER` by
  `ERMor1.minN`, realizing `stepCode`.
- `OneLambda.normRun` — the clocked iteration of the step, `ERMor1.boundedRec` over
  `normStep` at slots clock, code, budget, with the budget slot as value bound; the
  budget input carries the per-instance trace ceiling, since no elementary function of
  the clock and the code alone dominates every trace.

## Main statements

- `OneLambda.shapeER_interp` through `OneLambda.iotaContractER_interp` — each
  read's interpretation equals the mirrored ℕ-level function of
  `CodeNormalizer.lean`, `Bool.toNat`-valued for the Boolean-valued detector
  `isLamER`.
- `OneLambda.ordER_interp`, `OneLambda.topBetaRankER_interp` — the type-order
  fold and top-β-rank read interpret to `ordCode` and `topBetaRankCode`,
  unconditionally on every code.
- `OneLambda.conHeadedER_interp`, `OneLambda.iotaSpineER_interp`,
  `OneLambda.topIotaER_interp` — the `con`-headedness, ι-spine, and sort-gated
  ι-redex detectors interpret to the `Bool.toNat` of `conHeadedCode`,
  `iotaSpineCode`, `topIotaCode`, unconditionally on every code.
- `OneLambda.betaRankER_interp`, `OneLambda.hasIotaER_interp` — the β-rank and
  ι-census folds interpret to `betaRankCode` and the `Bool.toNat` of `hasIotaCode`,
  unconditionally on every code.
- `OneLambda.iotaStepER_interp` — the ι worker interprets to `iotaStepCode`,
  unconditionally on every code, its fold table bounded by the tower-2 majorant
  `iotaStepCode_le_tower`.
- `OneLambda.shiftER_interp`, `OneLambda.shiftIterER_interp` — the code-level weakening and
  its iterate interpret to `shiftCode j m` and `(shiftCode j)^[d] e`, unconditionally on
  every code, level, depth, and substituend, bounded by the tower-2 majorants
  `shiftCode_le_tower` and `shiftCode_iterate_le_tower`.
- `OneLambda.subER_interp` — the substitution fold interprets to `subCode j e c`,
  unconditionally on every code, level, and substituend, its gated table bounded by the
  tower-2 majorant `subCode_shift_iterate_le_tower` and its determinacy hypothesis
  (Decision Q6) discharged by strong induction on the code component of the index.
- `OneLambda.betaStepER_interp` — the β-worker fold interprets to
  `betaStepCode q 0 c`, unconditionally on every code and rank, its gated table
  bounded by the tower-2 majorant `betaStepCode_le_tower` and its determinacy
  hypothesis (Decision Q6) discharged by strong induction on the code component of
  the index.
- `OneLambda.stepBoundER_interp` — the step majorant interprets to `stepBound n`.
- `OneLambda.stepCodeAtZeroER_interp` — the closed-term dispatch interprets to
  `stepCodeAt 0 c`, unconditionally on every code, splitting on the same guards as
  `stepCodeAt`'s definition.
- `OneLambda.normStep_interp` — the assembled step interprets to `stepCode n`,
  unconditionally on every code, composing `interp_minN` with the closed-term
  dispatch and step-majorant interpretation lemmas.
- `OneLambda.normRun_interp_of_le` — under a budget dominating every trace value up to
  the clock, the clocked iteration interprets to the iterate `stepCode^[k] n`.

## Implementation notes

The Boolean-valued read `isLamER` interprets to `(isLamCode c).toNat`, with `1`
and `0` the dispatch-visible truth values consumed by `condN`. The three reads
that mirror an `if`/`match` on a code (`conLabelER`, `resultShapeER`,
`iotaContractER`) are built from `condEqER`, the composite of `condN` over a
`boolEqNat` read realizing `if a = b then t else f`.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`.

## Tags

ramified recurrence, elementary recursion, Gödel numbering, normalizer
-/

namespace GebLean.Ramified

namespace OneLambda

/-! ### Arithmetic and dispatch helpers -/

/-- A constant `Fin 1 → ℕ` context equals the singleton vector: the identity used
to feed an arity-1 read into a composition. -/
private theorem cons_fin_one (v : ℕ) : (fun _ : Fin 1 => v) = ![v] := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl

/-- The `boolEqNat` arithmetic normal form as a decision value: the product
`(1 - (a - b)) * (1 - (b - a))` is `1` when `a = b` and `0` otherwise. -/
private theorem eqNat_val (a b : ℕ) :
    (1 - (a - b)) * (1 - (b - a)) = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst h; simp
  · rcases Nat.lt_or_ge a b with hlt | hge
    · have h0 : 1 - (b - a) = 0 := by omega
      rw [h0, Nat.mul_zero, if_neg h]
    · have hgt : b < a := by omega
      have h0 : 1 - (a - b) = 0 := by omega
      rw [h0, Nat.zero_mul, if_neg h]

/-- The decision value of an equality equals the `Bool.toNat` of the Boolean
equality: `(if a = b then 1 else 0) = (a == b).toNat`. -/
private theorem ite_eq_beq_toNat (a b : ℕ) :
    (if a = b then (1 : ℕ) else 0) = (a == b).toNat := by
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg h]; simp [beq_eq_false_iff_ne.mpr h]

/-- `Bool.toNat` carries Boolean conjunction to multiplication of the truth
values. -/
private theorem toNat_and (x y : Bool) : (x && y).toNat = x.toNat * y.toNat := by
  cases x <;> cases y <;> rfl

/-- The equality-guarded conditional at arity `n`: `condEqER a b t f` selects `t`
when the reads `a` and `b` agree and `f` otherwise, realized as `condN` over a
`boolEqNat` comparison of `a` and `b`. -/
private def condEqER {n : ℕ} (a b t f : ERMor1 n) : ERMor1 n :=
  ERMor1.comp ERMor1.condN (fun i => match i with
    | ⟨0, _⟩ => ERMor1.comp ERMor1.boolEqNat (fun j => match j with
        | ⟨0, _⟩ => a
        | ⟨1, _⟩ => b)
    | ⟨1, _⟩ => t
    | ⟨2, _⟩ => f)

/-- Interpretation of `condEqER`: the equality-guarded selection of `t` or `f`. -/
@[simp] private theorem condEqER_interp {n : ℕ} (a b t f : ERMor1 n)
    (ctx : Fin n → ℕ) :
    (condEqER a b t f).interp ctx =
      if a.interp ctx = b.interp ctx then t.interp ctx else f.interp ctx := by
  simp only [condEqER, ERMor1.interp_comp, ERMor1.interp_condN, ERMor1.interp_boolEqNat]
  simp only [eqNat_val]
  by_cases h : a.interp ctx = b.interp ctx <;> simp [h]

/-! ### The non-recursive reads -/

/-- The shape-tag read: the leading `Nat.pair` component of a type code, mirroring
`shapeCode`. Novel realization. -/
def shapeER : ERMor1 1 := ERMor1.comp ERMor1.natUnpairFst (fun (_ : Fin 1) => ERMor1.proj 0)

/-- Interpretation of `shapeER`: the shape tag `shapeCode`. -/
@[simp] theorem shapeER_interp (n : ℕ) : shapeER.interp ![n] = shapeCode n := by
  simp only [shapeER, ERMor1.interp_comp, ERMor1.interp_proj, Matrix.cons_val_zero,
    cons_fin_one, ERMor1.interp_natUnpairFst, shapeCode]

/-- The argument-code read: the trailing `Nat.pair` component of a type code,
mirroring `argCode`. Novel realization. -/
def argER : ERMor1 1 := ERMor1.comp ERMor1.natUnpairSnd (fun (_ : Fin 1) => ERMor1.proj 0)

/-- Interpretation of `argER`: the argument code `argCode`. -/
@[simp] theorem argER_interp (n : ℕ) : argER.interp ![n] = argCode n := by
  simp only [argER, ERMor1.interp_comp, ERMor1.interp_proj, Matrix.cons_val_zero,
    cons_fin_one, ERMor1.interp_natUnpairSnd, argCode]

/-- The domain-code read: the first component of the argument code, mirroring
`domCode`. Novel realization. -/
def domER : ERMor1 1 := ERMor1.comp ERMor1.natUnpairFst (fun (_ : Fin 1) => argER)

/-- Interpretation of `domER`: the domain child code `domCode`. -/
@[simp] theorem domER_interp (n : ℕ) : domER.interp ![n] = domCode n := by
  simp only [domER, ERMor1.interp_comp, argER_interp, cons_fin_one,
    ERMor1.interp_natUnpairFst, domCode]

/-- The codomain-code read: the second component of the argument code, mirroring
`codCode`. Novel realization. -/
def codER : ERMor1 1 := ERMor1.comp ERMor1.natUnpairSnd (fun (_ : Fin 1) => argER)

/-- Interpretation of `codER`: the codomain child code `codCode`. -/
@[simp] theorem codER_interp (n : ℕ) : codER.interp ![n] = codCode n := by
  simp only [codER, ERMor1.interp_comp, argER_interp, cons_fin_one,
    ERMor1.interp_natUnpairSnd, codCode]

/-- The first-child read of an operation node, mirroring `child0Code`. Novel
realization. -/
def child0ER : ERMor1 1 :=
  ERMor1.comp ERMor1.natUnpairFst (fun (_ : Fin 1) =>
    ERMor1.comp ERMor1.natUnpairSnd (fun (_ : Fin 1) =>
      ERMor1.comp ERMor1.natUnpairSnd (fun (_ : Fin 1) => ERMor1.proj 0)))

/-- Interpretation of `child0ER`: the first child code `child0Code`. -/
@[simp] theorem child0ER_interp (n : ℕ) : child0ER.interp ![n] = child0Code n := by
  simp only [child0ER, ERMor1.interp_comp, ERMor1.interp_proj, Matrix.cons_val_zero,
    cons_fin_one, ERMor1.interp_natUnpairSnd, ERMor1.interp_natUnpairFst, child0Code]

/-- The second-child read of an operation node, mirroring `child1Code`. Novel
realization. -/
def child1ER : ERMor1 1 :=
  ERMor1.comp ERMor1.natUnpairFst (fun (_ : Fin 1) =>
    ERMor1.comp ERMor1.natUnpairSnd (fun (_ : Fin 1) =>
      ERMor1.comp ERMor1.natUnpairSnd (fun (_ : Fin 1) =>
        ERMor1.comp ERMor1.natUnpairSnd (fun (_ : Fin 1) => ERMor1.proj 0))))

/-- Interpretation of `child1ER`: the second child code `child1Code`. -/
@[simp] theorem child1ER_interp (n : ℕ) : child1ER.interp ![n] = child1Code n := by
  simp only [child1ER, ERMor1.interp_comp, ERMor1.interp_proj, Matrix.cons_val_zero,
    cons_fin_one, ERMor1.interp_natUnpairSnd, ERMor1.interp_natUnpairFst, child1Code]

/-- The operation-kind read: the leading component of the operation tag, mirroring
`opKindCode`. Novel realization. -/
def opKindER : ERMor1 1 :=
  ERMor1.comp ERMor1.natUnpairFst (fun (_ : Fin 1) =>
    ERMor1.comp ERMor1.natUnpairFst (fun (_ : Fin 1) =>
      ERMor1.comp ERMor1.natUnpairSnd (fun (_ : Fin 1) => ERMor1.proj 0)))

/-- Interpretation of `opKindER`: the operation kind bit `opKindCode`. -/
@[simp] theorem opKindER_interp (n : ℕ) : opKindER.interp ![n] = opKindCode n := by
  simp only [opKindER, ERMor1.interp_comp, ERMor1.interp_proj, Matrix.cons_val_zero,
    cons_fin_one, ERMor1.interp_natUnpairSnd, ERMor1.interp_natUnpairFst, opKindCode]

/-- The operation-payload read: the trailing component of the operation tag,
mirroring `opPayloadCode`. Novel realization. -/
def opPayloadER : ERMor1 1 :=
  ERMor1.comp ERMor1.natUnpairSnd (fun (_ : Fin 1) =>
    ERMor1.comp ERMor1.natUnpairFst (fun (_ : Fin 1) =>
      ERMor1.comp ERMor1.natUnpairSnd (fun (_ : Fin 1) => ERMor1.proj 0)))

/-- Interpretation of `opPayloadER`: the operation payload `opPayloadCode`. -/
@[simp] theorem opPayloadER_interp (n : ℕ) : opPayloadER.interp ![n] = opPayloadCode n := by
  simp only [opPayloadER, ERMor1.interp_comp, ERMor1.interp_proj, Matrix.cons_val_zero,
    cons_fin_one, ERMor1.interp_natUnpairSnd, ERMor1.interp_natUnpairFst, opPayloadCode]

/-- The constructor-label read: the operation payload of a constructor-constant
node (kind bit `2`) and of the function child otherwise, mirroring `conLabelCode`.
Novel realization. -/
def conLabelER : ERMor1 1 :=
  condEqER opKindER (ERMor1.natN 1 2) opPayloadER
    (ERMor1.comp opPayloadER (fun (_ : Fin 1) => child0ER))

/-- Interpretation of `conLabelER`: the constructor label `conLabelCode`. -/
@[simp] theorem conLabelER_interp (n : ℕ) : conLabelER.interp ![n] = conLabelCode n := by
  simp only [conLabelER, condEqER_interp, opKindER_interp, ERMor1.interp_natN,
    opPayloadER_interp, ERMor1.interp_comp, child0ER_interp, cons_fin_one, conLabelCode]

/-- The abstraction detector: a node is an abstraction when its shape tag is `1`
and its operation kind bit is `1`, mirroring `isLamCode`. The interpretation is
`Bool.toNat`-valued (Decision Q3). Novel realization. -/
def isLamER : ERMor1 1 :=
  ERMor1.comp ERMor1.boolAnd (fun i => match i with
    | ⟨0, _⟩ => ERMor1.comp ERMor1.boolEqNat (fun j => match j with
        | ⟨0, _⟩ => shapeER
        | ⟨1, _⟩ => ERMor1.natN 1 1)
    | ⟨1, _⟩ => ERMor1.comp ERMor1.boolEqNat (fun j => match j with
        | ⟨0, _⟩ => opKindER
        | ⟨1, _⟩ => ERMor1.natN 1 1))

/-- Interpretation of `isLamER`: the `Bool.toNat` of the abstraction detector
`isLamCode`. -/
@[simp] theorem isLamER_interp (n : ℕ) : isLamER.interp ![n] = (isLamCode n).toNat := by
  simp only [isLamER, ERMor1.interp_comp, ERMor1.interp_boolAnd, ERMor1.interp_boolEqNat,
    shapeER_interp, opKindER_interp, ERMor1.interp_natN]
  simp only [eqNat_val, shapeCode, opKindCode]
  rw [isLamCode, toNat_and, ← ite_eq_beq_toNat, ← ite_eq_beq_toNat]

/-- The result-sort shape of `resultShapeCode` as a nested conditional on the
operation kind bit: an application (kind `0`) reads the shape of the codomain
code; abstractions, destructors, and the case combinator (kinds `1`, `3`, `4`)
have arrow result sorts (shape `1`); every other reading is `0`. -/
private theorem resultShapeCode_eq_ite (c : ℕ) :
    resultShapeCode c = (if opKindCode c = 0 then shapeCode (codCode (domCode c))
      else if opKindCode c = 1 then 1 else if opKindCode c = 3 then 1
      else if opKindCode c = 4 then 1 else 0) := by
  rw [resultShapeCode]
  split <;> rename_i h <;> simp_all [opKindCode, domCode, argCode]

/-- The result-sort shape read: the nested `condEqER` dispatch on the operation
kind bit realizing `resultShapeCode`. Novel realization. -/
def resultShapeER : ERMor1 1 :=
  condEqER opKindER (ERMor1.natN 1 0)
    (ERMor1.comp shapeER (fun (_ : Fin 1) => ERMor1.comp codER (fun (_ : Fin 1) => domER)))
    (condEqER opKindER (ERMor1.natN 1 1) (ERMor1.natN 1 1)
      (condEqER opKindER (ERMor1.natN 1 3) (ERMor1.natN 1 1)
        (condEqER opKindER (ERMor1.natN 1 4) (ERMor1.natN 1 1) (ERMor1.natN 1 0))))

/-- Interpretation of `resultShapeER`: the result-sort shape `resultShapeCode`. -/
@[simp] theorem resultShapeER_interp (n : ℕ) :
    resultShapeER.interp ![n] = resultShapeCode n := by
  simp only [resultShapeER, condEqER_interp, opKindER_interp, ERMor1.interp_natN,
    shapeER_interp, ERMor1.interp_comp, codER_interp, domER_interp, cons_fin_one]
  rw [resultShapeCode_eq_ite]

/-- The ι-contraction of `iotaContractCode` as a de-conjuncted nested conditional
on the shape tags and operation kind bits of the redex code's children: the
destructor branch (function child kind `3`) and the case branch (function child
kind `0`) each dispatch on the scrutinee's shape, and off the ι-redex shapes the
code is unchanged. -/
private theorem iotaContractCode_eq_ite (c : ℕ) :
    iotaContractCode c =
      (if (Nat.unpair (child0Code c)).1 = 1 then
        (if opKindCode (child0Code c) = 3 then
          (if (Nat.unpair (child1Code c)).1 = 1 then
            (if opKindCode (child1Code c) = 0 then child1Code (child1Code c) else child1Code c)
            else child1Code c)
        else if opKindCode (child0Code c) = 0 then
          (if (Nat.unpair (child0Code (child0Code (child0Code c)))).1 = 1 then
            (if opKindCode (child0Code (child0Code (child0Code c))) = 4 then
              (if conLabelCode (child1Code (child0Code (child0Code c))) = 0 then
                child1Code (child0Code c) else child1Code c)
              else c)
            else c)
          else c)
      else c) := by
  rw [iotaContractCode]
  split <;> rename_i h <;> split_ifs <;> simp_all

/-- The ι-contraction read: the nested `condEqER` dispatch on the redex code's
children realizing `iotaContractCode` (Leivant III section 4.2, p. 223). Novel
realization. -/
def iotaContractER : ERMor1 1 :=
  condEqER (ERMor1.comp shapeER (fun (_ : Fin 1) => child0ER)) (ERMor1.natN 1 1)
    (condEqER (ERMor1.comp opKindER (fun (_ : Fin 1) => child0ER)) (ERMor1.natN 1 3)
      (condEqER (ERMor1.comp shapeER (fun (_ : Fin 1) => child1ER)) (ERMor1.natN 1 1)
        (condEqER (ERMor1.comp opKindER (fun (_ : Fin 1) => child1ER)) (ERMor1.natN 1 0)
          (ERMor1.comp child1ER (fun (_ : Fin 1) => child1ER)) child1ER)
        child1ER)
      (condEqER (ERMor1.comp opKindER (fun (_ : Fin 1) => child0ER)) (ERMor1.natN 1 0)
        (condEqER (ERMor1.comp shapeER (fun (_ : Fin 1) =>
              ERMor1.comp child0ER (fun (_ : Fin 1) =>
                ERMor1.comp child0ER (fun (_ : Fin 1) => child0ER)))) (ERMor1.natN 1 1)
          (condEqER (ERMor1.comp opKindER (fun (_ : Fin 1) =>
                ERMor1.comp child0ER (fun (_ : Fin 1) =>
                  ERMor1.comp child0ER (fun (_ : Fin 1) => child0ER)))) (ERMor1.natN 1 4)
            (condEqER (ERMor1.comp conLabelER (fun (_ : Fin 1) =>
                  ERMor1.comp child1ER (fun (_ : Fin 1) =>
                    ERMor1.comp child0ER (fun (_ : Fin 1) => child0ER)))) (ERMor1.natN 1 0)
              (ERMor1.comp child1ER (fun (_ : Fin 1) => child0ER)) child1ER)
            (ERMor1.proj 0))
          (ERMor1.proj 0))
        (ERMor1.proj 0)))
    (ERMor1.proj 0)

/-- Interpretation of `iotaContractER`: the ι-contraction image `iotaContractCode`. -/
@[simp] theorem iotaContractER_interp (n : ℕ) :
    iotaContractER.interp ![n] = iotaContractCode n := by
  simp only [iotaContractER, condEqER_interp, ERMor1.interp_comp, shapeER_interp,
    opKindER_interp, child0ER_interp, child1ER_interp, conLabelER_interp,
    ERMor1.interp_natN, ERMor1.interp_proj, cons_fin_one, Matrix.cons_val_zero]
  rw [iotaContractCode_eq_ite]
  rfl

/-! ### The type-order fold -/

/-- ER-derived maximum of two naturals: `maxN.interp ![a, b] = max a b`. Realized
as `condN` over the `leN` comparison: when `a ≤ b` returns `b`, otherwise `a`. -/
private def maxN : ERMor1 2 :=
  ERMor1.comp ERMor1.condN (fun i => match i with
    | ⟨0, _⟩ => ERMor1.leN
    | ⟨1, _⟩ => ERMor1.proj 1
    | ⟨2, _⟩ => ERMor1.proj 0)

/-- Interpretation of `maxN`: the maximum of the two slots. -/
@[simp] private theorem maxN_interp (ctx : Fin 2 → ℕ) :
    maxN.interp ctx = max (ctx 0) (ctx 1) := by
  rw [maxN, ERMor1.interp_comp, ERMor1.interp_condN]
  change ERMor1.leN.interp ctx * ctx 1 + (1 - ERMor1.leN.interp ctx) * ctx 0
      = max (ctx 0) (ctx 1)
  rw [ERMor1.interp_leN]
  split_ifs <;> omega

/-- The node of the `ordCode` course-of-values fold at slots `(i, cand, code)`:
dispatch on the shape tag of the index `i`. Shape `1` (arrow) reads the two child
orders off the β-table at `domCode i` and `codCode i` and returns
`max (first + 1) second`; shape `2` (`Ω`) reads the single child order at
`argCode i`; every other tag returns `0`. β-reads use `betaOnCandFold` at the
child positions computed from the index. Novel realization. -/
private def ordNode : ERMor1 3 :=
  condEqER (ERMor1.comp shapeER (fun _ : Fin 1 => ERMor1.proj 0)) (ERMor1.natN 3 1)
    (ERMor1.comp maxN (fun i => match i with
      | ⟨0, _⟩ => ERMor1.comp ERMor1.succ (fun _ : Fin 1 =>
          ERMor1.betaOnCandFold (ERMor1.comp domER (fun _ : Fin 1 => ERMor1.proj 0)))
      | ⟨1, _⟩ =>
          ERMor1.betaOnCandFold (ERMor1.comp codER (fun _ : Fin 1 => ERMor1.proj 0))))
    (condEqER (ERMor1.comp shapeER (fun _ : Fin 1 => ERMor1.proj 0)) (ERMor1.natN 3 2)
      (ERMor1.betaOnCandFold (ERMor1.comp argER (fun _ : Fin 1 => ERMor1.proj 0)))
      (ERMor1.natN 3 0))

/-- The node value of `ordNode` at `(i, cand, code)` as a nested conditional on the
shape tag of `i`, with the child orders read off the candidate β-table. -/
private theorem ordNode_interp (i cand code : ℕ) :
    ordNode.interp (Fin.cons i (Fin.cons cand (Fin.cons code (![] : Fin 0 → ℕ)))) =
      if shapeCode i = 1 then
        max (cand.unpair.1 % (1 + (domCode i + 1) * cand.unpair.2) + 1)
          (cand.unpair.1 % (1 + (codCode i + 1) * cand.unpair.2))
      else if shapeCode i = 2 then
        cand.unpair.1 % (1 + (argCode i + 1) * cand.unpair.2)
      else 0 := by
  simp only [ordNode, condEqER_interp, maxN_interp, ERMor1.interp_comp,
    ERMor1.interp_betaOnCandFold, ERMor1.interp_succ, ERMor1.interp_natN,
    ERMor1.interp_proj, Fin.cons_zero, cons_fin_one, shapeER_interp, domER_interp,
    codER_interp, argER_interp, Matrix.cons_val_zero]

/-- The type-order read as an elementary-recursive course-of-values fold: the first
instantiation of `ERMor1.cvRec`, at fold slot the code and node `ordNode`, with
value bound the code itself (`ordCode_le_self`). Realizes the well-founded
recursion of `ordCode` (Leivant III section 2.2, p. 213) as a single bounded
β-witness search. Novel realization. -/
def ordER : ERMor1 1 := ERMor1.cvRec ordNode (ERMor1.proj 0)

/-- Interpretation of `ordER`: the type order `ordCode`, unconditionally on every
code. Discharges the hypotheses of `ERMor1.interp_cvRec_of_bounded` with
`f := ordCode`: the value bound `ordCode_le_self`, its monotonicity immediate from
the fold slot, and node faithfulness from the `ordCode` shape node equations
(`ordCode_shape_one`, `ordCode_shape_two`) with the child codes strictly below the
index (`domCode_lt_of_shape_one`, `codCode_lt_of_shape_one`,
`argCode_lt_of_shape_two`). -/
@[simp] theorem ordER_interp (n : ℕ) : ordER.interp ![n] = ordCode n := by
  refine ERMor1.interp_cvRec_of_bounded ordNode (ERMor1.proj 0) n ![] ordCode
    (fun j _ => ?_) (fun j hj => ?_) (fun i _ cand htrace => ?_)
  · exact ordCode_le_self j
  · exact hj
  · rw [ordNode_interp i cand n]
    by_cases h1 : shapeCode i = 1
    · rw [if_pos h1, htrace (domCode i) (domCode_lt_of_shape_one i h1),
        htrace (codCode i) (codCode_lt_of_shape_one i h1), ordCode_shape_one i h1]
    · rw [if_neg h1]
      by_cases h2 : shapeCode i = 2
      · rw [if_pos h2, htrace (argCode i) (argCode_lt_of_shape_two i h2),
          ordCode_shape_two i h2]
      · rw [if_neg h2]
        symm
        rw [ordCode]
        split <;> simp_all [shapeCode]

/-- The applied arrow-sort code read for the top β-rank: `Nat.pair 1` over the
operation payload of the application tag, mirroring the `ordCode` argument of
`topBetaRankCode`. Novel realization. -/
private def appliedArrowER : ERMor1 1 :=
  ERMor1.comp ERMor1.natPair (fun j => match j with
    | ⟨0, _⟩ => ERMor1.natN 1 1
    | ⟨1, _⟩ => opPayloadER)

/-- Interpretation of `appliedArrowER`: the arrow-sort code `Nat.pair 1
(opPayloadCode c)`. -/
@[simp] private theorem appliedArrowER_interp (c : ℕ) :
    appliedArrowER.interp ![c] = Nat.pair 1 (opPayloadCode c) := by
  have key : appliedArrowER.interp ![c] = ERMor1.natPair.interp ![1, opPayloadCode c] := by
    rw [appliedArrowER]
    simp only [ERMor1.interp_comp]
    congr 1
    funext j
    match j with
    | ⟨0, _⟩ => simp
    | ⟨1, _⟩ => simp [opPayloadER_interp]
  rw [key, ERMor1.interp_natPair]

/-- The top β-rank read of `topBetaRankCode` as a nested conditional on the shape
tag, the operation kind bit, and the abstraction status of the function child:
at an application node (shape `1`, kind `0`) whose function child is a `lam`, the
order read off the applied arrow-sort code; otherwise `0`. -/
private theorem topBetaRankCode_eq_ite (c : ℕ) :
    topBetaRankCode c =
      (if shapeCode c = 1 then
        (if opKindCode c = 0 then
          (if isLamCode (child0Code c) then
            ordCode (Nat.pair 1 (opPayloadCode c)) else 0)
          else 0)
        else 0) := by
  rw [topBetaRankCode]
  split <;> simp_all [shapeCode, opKindCode, child0Code, opPayloadCode]

/-- The top β-rank read: the nested `condEqER` dispatch on the top node realizing
`topBetaRankCode`, composing the reads and `ordER` (no recursion). Novel
realization. -/
def topBetaRankER : ERMor1 1 :=
  condEqER shapeER (ERMor1.natN 1 1)
    (condEqER opKindER (ERMor1.natN 1 0)
      (condEqER (ERMor1.comp isLamER (fun _ : Fin 1 => child0ER)) (ERMor1.natN 1 1)
        (ERMor1.comp ordER (fun _ : Fin 1 => appliedArrowER))
        (ERMor1.natN 1 0))
      (ERMor1.natN 1 0))
    (ERMor1.natN 1 0)

/-- Interpretation of `topBetaRankER`: the top β-rank `topBetaRankCode`. -/
@[simp] theorem topBetaRankER_interp (c : ℕ) :
    topBetaRankER.interp ![c] = topBetaRankCode c := by
  rw [topBetaRankCode_eq_ite]
  simp only [topBetaRankER, condEqER_interp, shapeER_interp, opKindER_interp,
    ERMor1.interp_natN, ERMor1.interp_comp, isLamER_interp, child0ER_interp,
    ordER_interp, appliedArrowER_interp, cons_fin_one]
  by_cases h1 : shapeCode c = 1
  · by_cases h2 : opKindCode c = 0
    · cases hb : isLamCode (child0Code c) <;> simp [h1, h2]
    · simp [h1, h2]
  · simp [h1]

/-! ### The head and spine detector folds -/

/-- The first child code of a shape-`1` code sits strictly below it:
`child0Code n < n`. Two `Nat.unpair` descents below the argument code, itself
strictly below `n` by `argCode_lt_of_shape_one`. Descent input shared by the
`con`-headedness and ι-spine folds. -/
private theorem child0Code_lt_of_shape_one (n : ℕ) (h : shapeCode n = 1) :
    child0Code n < n :=
  Nat.lt_of_le_of_lt
    (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _))
    (argCode_lt_of_shape_one n h)

/-- The second child code of a shape-`1` code sits strictly below it:
`child1Code n < n`. Three `Nat.unpair` descents below the argument code, itself
strictly below `n` by `argCode_lt_of_shape_one`. Descent input shared by the β-rank
and ι-census folds. -/
private theorem child1Code_lt_of_shape_one (n : ℕ) (h : shapeCode n = 1) :
    child1Code n < n :=
  Nat.lt_of_le_of_lt
    (le_trans (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _))
      (Nat.unpair_right_le _))
    (argCode_lt_of_shape_one n h)

/-- The `con`-headedness recursion of `conHeadedCode` as a nested conditional on
the shape tag and operation kind bit of the code: an application node (shape `1`,
kind `0`) descends into the function child code; a constructor node (kind `2`) is
`true`; every other node is `false`. -/
private theorem conHeadedCode_eq_ite (c : ℕ) :
    conHeadedCode c =
      (if shapeCode c = 1 then
        (if opKindCode c = 0 then conHeadedCode (child0Code c)
         else if opKindCode c = 2 then true else false)
      else false) := by
  rw [conHeadedCode]
  split <;> simp_all [shapeCode, opKindCode, child0Code]

/-- The node of the `conHeadedCode` course-of-values fold at slots
`(i, cand, code)`: dispatch on the shape tag and operation kind bit of the index
`i`. At an application node (shape `1`, kind `0`) it reads the child `con`-status
off the β-table at `child0Code i`; a constructor node (kind `2`) returns `1`; every
other node returns `0`. Novel realization. -/
private def conHeadedNode : ERMor1 3 :=
  condEqER (ERMor1.comp shapeER (fun _ : Fin 1 => ERMor1.proj 0)) (ERMor1.natN 3 1)
    (condEqER (ERMor1.comp opKindER (fun _ : Fin 1 => ERMor1.proj 0)) (ERMor1.natN 3 0)
      (ERMor1.betaOnCandFold (ERMor1.comp child0ER (fun _ : Fin 1 => ERMor1.proj 0)))
      (condEqER (ERMor1.comp opKindER (fun _ : Fin 1 => ERMor1.proj 0)) (ERMor1.natN 3 2)
        (ERMor1.natN 3 1) (ERMor1.natN 3 0)))
    (ERMor1.natN 3 0)

/-- The node value of `conHeadedNode` at `(i, cand, code)` as a nested conditional
on the shape tag and operation kind bit of `i`, with the child `con`-status read
off the candidate β-table. -/
private theorem conHeadedNode_interp (i cand code : ℕ) :
    conHeadedNode.interp (Fin.cons i (Fin.cons cand (Fin.cons code (![] : Fin 0 → ℕ)))) =
      if shapeCode i = 1 then
        (if opKindCode i = 0 then cand.unpair.1 % (1 + (child0Code i + 1) * cand.unpair.2)
         else if opKindCode i = 2 then 1 else 0)
      else 0 := by
  simp only [conHeadedNode, condEqER_interp, ERMor1.interp_comp,
    ERMor1.interp_betaOnCandFold, ERMor1.interp_natN, ERMor1.interp_proj, Fin.cons_zero,
    cons_fin_one, shapeER_interp, opKindER_interp, child0ER_interp]

/-- The `con`-headedness detector as an elementary-recursive course-of-values fold:
`ERMor1.cvRec` at fold slot the code and node `conHeadedNode`, with constant value
bound `1` (Decision Q3, `Bool.toNat`-valued). Realizes the strong recursion of
`conHeadedCode` (Leivant III section 4.2, pp. 223-224) as a single bounded
β-witness search. Novel realization. -/
def conHeadedER : ERMor1 1 := ERMor1.cvRec conHeadedNode (ERMor1.oneN 1)

/-- Interpretation of `conHeadedER`: the `Bool.toNat` of the `con`-headedness
detector `conHeadedCode`, unconditionally on every code. Discharges the hypotheses
of `ERMor1.interp_cvRec_of_bounded` with `f := fun j => (conHeadedCode j).toNat`:
the value bound is the constant `1` (`Bool.toNat` is at most `1`), its monotonicity
immediate, and node faithfulness from `conHeadedCode_eq_ite` with the function child
strictly below the index (`child0Code_lt_of_shape_one`). -/
@[simp] theorem conHeadedER_interp (c : ℕ) :
    conHeadedER.interp ![c] = (conHeadedCode c).toNat := by
  refine ERMor1.interp_cvRec_of_bounded conHeadedNode (ERMor1.oneN 1) c ![]
    (fun j => (conHeadedCode j).toNat) (fun j _ => ?_) (fun j _ => ?_)
    (fun i _ cand htrace => ?_)
  · cases h : conHeadedCode j <;> simp [h]
  · simp
  · have htrace' : ∀ p, p < i →
        cand.unpair.1 % (1 + (p + 1) * cand.unpair.2) = (conHeadedCode p).toNat := htrace
    change conHeadedNode.interp _ = (conHeadedCode i).toNat
    rw [conHeadedNode_interp i cand c, conHeadedCode_eq_ite i]
    by_cases h1 : shapeCode i = 1
    · rw [if_pos h1, if_pos h1]
      by_cases h0 : opKindCode i = 0
      · rw [if_pos h0, if_pos h0, htrace' (child0Code i) (child0Code_lt_of_shape_one i h1)]
      · rw [if_neg h0, if_neg h0]
        by_cases h2 : opKindCode i = 2
        · rw [if_pos h2, if_pos h2]; rfl
        · rw [if_neg h2, if_neg h2]; rfl
    · rw [if_neg h1, if_neg h1]; rfl

/-- The ι-spine recursion of `iotaSpineCode` as a nested conditional on the shape
tags and operation kind bits of the code and its function child: at an application
node (shape `1`, kind `0`) whose function child has shape `1`, a destructor head
(kind `3`) or a case head (kind `4`) bottoms the spine at the `con`-headedness of
the argument child; a further application head (kind `0`) descends into the
function child; every other reading is `false`. -/
private theorem iotaSpineCode_eq_ite (c : ℕ) :
    iotaSpineCode c =
      (if shapeCode c = 1 then
        (if opKindCode c = 0 then
          (if shapeCode (child0Code c) = 1 then
            (if opKindCode (child0Code c) = 3 then conHeadedCode (child1Code c)
             else if opKindCode (child0Code c) = 4 then conHeadedCode (child1Code c)
             else if opKindCode (child0Code c) = 0 then iotaSpineCode (child0Code c)
             else false)
          else false)
        else false)
      else false) := by
  rw [iotaSpineCode]
  split <;> simp_all [shapeCode, opKindCode, child0Code, child1Code]

/-- The node of the `iotaSpineCode` course-of-values fold at slots `(i, cand, code)`:
dispatch on the shape tags and operation kind bits of the index `i` and its function
child `child0Code i`. At a destructor or case head the argument child's
`con`-status is read by a full call of `conHeadedER`; at a further application head
the spine descends off the β-table at `child0Code i`. Same-function recursion goes
through the β-table; the `con`-headedness helper is composed as an ordinary full
call. Novel realization. -/
private def iotaSpineNode : ERMor1 3 :=
  condEqER (ERMor1.comp shapeER (fun _ : Fin 1 => ERMor1.proj 0)) (ERMor1.natN 3 1)
    (condEqER (ERMor1.comp opKindER (fun _ : Fin 1 => ERMor1.proj 0)) (ERMor1.natN 3 0)
      (condEqER (ERMor1.comp shapeER (fun _ : Fin 1 =>
            ERMor1.comp child0ER (fun _ : Fin 1 => ERMor1.proj 0))) (ERMor1.natN 3 1)
        (condEqER (ERMor1.comp opKindER (fun _ : Fin 1 =>
              ERMor1.comp child0ER (fun _ : Fin 1 => ERMor1.proj 0))) (ERMor1.natN 3 3)
          (ERMor1.comp conHeadedER (fun _ : Fin 1 =>
            ERMor1.comp child1ER (fun _ : Fin 1 => ERMor1.proj 0)))
          (condEqER (ERMor1.comp opKindER (fun _ : Fin 1 =>
                ERMor1.comp child0ER (fun _ : Fin 1 => ERMor1.proj 0))) (ERMor1.natN 3 4)
            (ERMor1.comp conHeadedER (fun _ : Fin 1 =>
              ERMor1.comp child1ER (fun _ : Fin 1 => ERMor1.proj 0)))
            (condEqER (ERMor1.comp opKindER (fun _ : Fin 1 =>
                  ERMor1.comp child0ER (fun _ : Fin 1 => ERMor1.proj 0))) (ERMor1.natN 3 0)
              (ERMor1.betaOnCandFold (ERMor1.comp child0ER (fun _ : Fin 1 => ERMor1.proj 0)))
              (ERMor1.natN 3 0))))
        (ERMor1.natN 3 0))
      (ERMor1.natN 3 0))
    (ERMor1.natN 3 0)

/-- The node value of `iotaSpineNode` at `(i, cand, code)` as a nested conditional
on the shape tags and operation kind bits of `i` and `child0Code i`, with the
`con`-status by a full `conHeadedCode` call and the spine descent off the candidate
β-table. -/
private theorem iotaSpineNode_interp (i cand code : ℕ) :
    iotaSpineNode.interp (Fin.cons i (Fin.cons cand (Fin.cons code (![] : Fin 0 → ℕ)))) =
      if shapeCode i = 1 then
        (if opKindCode i = 0 then
          (if shapeCode (child0Code i) = 1 then
            (if opKindCode (child0Code i) = 3 then (conHeadedCode (child1Code i)).toNat
             else if opKindCode (child0Code i) = 4 then (conHeadedCode (child1Code i)).toNat
             else if opKindCode (child0Code i) = 0 then
               cand.unpair.1 % (1 + (child0Code i + 1) * cand.unpair.2)
             else 0)
          else 0)
        else 0)
      else 0 := by
  simp only [iotaSpineNode, condEqER_interp, ERMor1.interp_comp,
    ERMor1.interp_betaOnCandFold, ERMor1.interp_natN, ERMor1.interp_proj, Fin.cons_zero,
    cons_fin_one, shapeER_interp, opKindER_interp, child0ER_interp, child1ER_interp,
    conHeadedER_interp]

/-- The ι-spine detector as an elementary-recursive course-of-values fold:
`ERMor1.cvRec` at fold slot the code and node `iotaSpineNode`, with constant value
bound `1` (Decision Q3, `Bool.toNat`-valued). The node composes `conHeadedER` as an
ordinary full call; only the same-function descent goes through the β-table.
Realizes the strong recursion of `iotaSpineCode` (Leivant III section 4.2,
pp. 223-224) as a single bounded β-witness search. Novel realization. -/
def iotaSpineER : ERMor1 1 := ERMor1.cvRec iotaSpineNode (ERMor1.oneN 1)

/-- Interpretation of `iotaSpineER`: the `Bool.toNat` of the ι-spine detector
`iotaSpineCode`, unconditionally on every code. Discharges the hypotheses of
`ERMor1.interp_cvRec_of_bounded` with `f := fun j => (iotaSpineCode j).toNat`: the
constant value bound `1`, its monotonicity, and node faithfulness from
`iotaSpineCode_eq_ite` with the function child strictly below the index
(`child0Code_lt_of_shape_one`). -/
@[simp] theorem iotaSpineER_interp (c : ℕ) :
    iotaSpineER.interp ![c] = (iotaSpineCode c).toNat := by
  refine ERMor1.interp_cvRec_of_bounded iotaSpineNode (ERMor1.oneN 1) c ![]
    (fun j => (iotaSpineCode j).toNat) (fun j _ => ?_) (fun j _ => ?_)
    (fun i _ cand htrace => ?_)
  · cases h : iotaSpineCode j <;> simp [h]
  · simp
  · have htrace' : ∀ p, p < i →
        cand.unpair.1 % (1 + (p + 1) * cand.unpair.2) = (iotaSpineCode p).toNat := htrace
    change iotaSpineNode.interp _ = (iotaSpineCode i).toNat
    rw [iotaSpineNode_interp i cand c, iotaSpineCode_eq_ite i]
    by_cases h1 : shapeCode i = 1
    · rw [if_pos h1, if_pos h1]
      by_cases h0 : opKindCode i = 0
      · rw [if_pos h0, if_pos h0]
        by_cases hs0 : shapeCode (child0Code i) = 1
        · rw [if_pos hs0, if_pos hs0]
          by_cases hk3 : opKindCode (child0Code i) = 3
          · rw [if_pos hk3, if_pos hk3]
          · rw [if_neg hk3, if_neg hk3]
            by_cases hk4 : opKindCode (child0Code i) = 4
            · rw [if_pos hk4, if_pos hk4]
            · rw [if_neg hk4, if_neg hk4]
              by_cases hk0 : opKindCode (child0Code i) = 0
              · rw [if_pos hk0, if_pos hk0,
                  htrace' (child0Code i) (child0Code_lt_of_shape_one i h1)]
              · rw [if_neg hk0, if_neg hk0]; rfl
        · rw [if_neg hs0, if_neg hs0]; rfl
      · rw [if_neg h0, if_neg h0]; rfl
    · rw [if_neg h1, if_neg h1]; rfl

/-- The sort-gated ι-redex detector as an elementary-recursive read: the
equality-guarded selection composing the result-shape read `resultShapeER` and the
ι-spine fold `iotaSpineER`, mirroring `topIotaCode`. Non-recursive; the spine
content is a full call of `iotaSpineER`. Novel realization. -/
def topIotaER : ERMor1 1 :=
  condEqER resultShapeER (ERMor1.natN 1 0) iotaSpineER (ERMor1.natN 1 0)

/-- Interpretation of `topIotaER`: the `Bool.toNat` of the sort-gated ι-redex
detector `topIotaCode`, unconditionally on every code. -/
@[simp] theorem topIotaER_interp (c : ℕ) :
    topIotaER.interp ![c] = (topIotaCode c).toNat := by
  simp only [topIotaER, condEqER_interp, resultShapeER_interp, ERMor1.interp_natN,
    iotaSpineER_interp]
  rw [topIotaCode]
  by_cases h : resultShapeCode c = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]; rfl

/-! ### The rank and iota-census folds -/

/-- `Bool.toNat` carries Boolean disjunction to the maximum of the truth values. -/
private theorem toNat_or (x y : Bool) : (x || y).toNat = max x.toNat y.toNat := by
  cases x <;> cases y <;> rfl

/-- The β-rank recursion of `betaRankCode` as a nested conditional on the shape tag
and operation kind bit of the code: an application node (shape `1`, kind `0`) maxes
the top β-rank with the β-ranks of both children; an abstraction node (kind `1`)
recurses into its body child; every other node is `0`. -/
private theorem betaRankCode_eq_ite (c : ℕ) :
    betaRankCode c =
      (if shapeCode c = 1 then
        (if opKindCode c = 0 then
          max (topBetaRankCode c)
            (max (betaRankCode (child0Code c)) (betaRankCode (child1Code c)))
         else if opKindCode c = 1 then betaRankCode (child0Code c)
         else 0)
      else 0) := by
  rw [betaRankCode]
  split <;> simp_all [shapeCode, opKindCode, child0Code, child1Code]

/-- The node of the `betaRankCode` course-of-values fold at slots `(i, cand, code)`:
dispatch on the shape tag and operation kind bit of the index `i`. At an application
node (shape `1`, kind `0`) it maxes the top β-rank (a full call of `topBetaRankER`)
with the two child β-ranks read off the β-table at `child0Code i` and `child1Code i`;
an abstraction node (kind `1`) reads the single child β-rank; every other node
returns `0`. Same-function recursion goes through the β-table; the top-β-rank helper
is composed as an ordinary full call. Novel realization. -/
private def betaRankNode : ERMor1 3 :=
  condEqER (ERMor1.comp shapeER (fun _ : Fin 1 => ERMor1.proj 0)) (ERMor1.natN 3 1)
    (condEqER (ERMor1.comp opKindER (fun _ : Fin 1 => ERMor1.proj 0)) (ERMor1.natN 3 0)
      (ERMor1.comp maxN (fun i => match i with
        | ⟨0, _⟩ => ERMor1.comp topBetaRankER (fun _ : Fin 1 => ERMor1.proj 0)
        | ⟨1, _⟩ => ERMor1.comp maxN (fun j => match j with
            | ⟨0, _⟩ =>
                ERMor1.betaOnCandFold (ERMor1.comp child0ER (fun _ : Fin 1 => ERMor1.proj 0))
            | ⟨1, _⟩ =>
                ERMor1.betaOnCandFold (ERMor1.comp child1ER (fun _ : Fin 1 => ERMor1.proj 0)))))
      (condEqER (ERMor1.comp opKindER (fun _ : Fin 1 => ERMor1.proj 0)) (ERMor1.natN 3 1)
        (ERMor1.betaOnCandFold (ERMor1.comp child0ER (fun _ : Fin 1 => ERMor1.proj 0)))
        (ERMor1.natN 3 0)))
    (ERMor1.natN 3 0)

/-- The node value of `betaRankNode` at `(i, cand, code)` as a nested conditional on
the shape tag and operation kind bit of `i`, with the top β-rank by a full
`topBetaRankCode` call and the child β-ranks read off the candidate β-table. -/
private theorem betaRankNode_interp (i cand code : ℕ) :
    betaRankNode.interp (Fin.cons i (Fin.cons cand (Fin.cons code (![] : Fin 0 → ℕ)))) =
      if shapeCode i = 1 then
        (if opKindCode i = 0 then
          max (topBetaRankCode i)
            (max (cand.unpair.1 % (1 + (child0Code i + 1) * cand.unpair.2))
              (cand.unpair.1 % (1 + (child1Code i + 1) * cand.unpair.2)))
         else if opKindCode i = 1 then
           cand.unpair.1 % (1 + (child0Code i + 1) * cand.unpair.2)
         else 0)
      else 0 := by
  simp only [betaRankNode, condEqER_interp, maxN_interp, ERMor1.interp_comp,
    ERMor1.interp_betaOnCandFold, ERMor1.interp_natN, ERMor1.interp_proj, Fin.cons_zero,
    cons_fin_one, shapeER_interp, opKindER_interp, child0ER_interp, child1ER_interp,
    topBetaRankER_interp]

/-- The β-rank measure as an elementary-recursive course-of-values fold:
`ERMor1.cvRec` at fold slot the code and node `betaRankNode`, with value bound the
successor of the fold slot (`betaRankCode_le_succ`). The node composes
`topBetaRankER` as an ordinary full call; only the same-function descent goes through
the β-table. Realizes the strong recursion of `betaRankCode` (Leivant III
section 4.2, pp. 223-224) as a single bounded β-witness search. Novel realization. -/
def betaRankER : ERMor1 1 :=
  ERMor1.cvRec betaRankNode (ERMor1.comp ERMor1.succ (fun _ : Fin 1 => ERMor1.proj 0))

/-- Interpretation of `betaRankER`: the β-rank measure `betaRankCode`, unconditionally
on every code. Discharges the hypotheses of `ERMor1.interp_cvRec_of_bounded` with
`f := betaRankCode`: the value bound `betaRankCode_le_succ`, its monotonicity from
`j ≤ code` giving `j + 1 ≤ code + 1`, and node faithfulness from `betaRankCode_eq_ite`
with the two children strictly below the index (`child0Code_lt_of_shape_one`,
`child1Code_lt_of_shape_one`). -/
@[simp] theorem betaRankER_interp (c : ℕ) : betaRankER.interp ![c] = betaRankCode c := by
  refine ERMor1.interp_cvRec_of_bounded betaRankNode
    (ERMor1.comp ERMor1.succ (fun _ : Fin 1 => ERMor1.proj 0)) c ![] betaRankCode
    (fun j _ => ?_) (fun j hj => ?_) (fun i _ cand htrace => ?_)
  · simp only [ERMor1.interp_comp, ERMor1.interp_succ, ERMor1.interp_proj, Fin.cons_zero]
    exact betaRankCode_le_succ j
  · simp only [ERMor1.interp_comp, ERMor1.interp_succ, ERMor1.interp_proj, Fin.cons_zero]
    omega
  · change betaRankNode.interp _ = betaRankCode i
    rw [betaRankNode_interp i cand c, betaRankCode_eq_ite i]
    by_cases h1 : shapeCode i = 1
    · rw [if_pos h1, if_pos h1]
      by_cases h0 : opKindCode i = 0
      · rw [if_pos h0, if_pos h0, htrace (child0Code i) (child0Code_lt_of_shape_one i h1),
          htrace (child1Code i) (child1Code_lt_of_shape_one i h1)]
      · rw [if_neg h0, if_neg h0]
        by_cases h1' : opKindCode i = 1
        · rw [if_pos h1', if_pos h1', htrace (child0Code i) (child0Code_lt_of_shape_one i h1)]
        · rw [if_neg h1', if_neg h1']
    · rw [if_neg h1, if_neg h1]

/-- The ι-census recursion of `hasIotaCode` as a nested conditional on the shape tag
and operation kind bit of the code: an application node (shape `1`, kind `0`) disjoins
the top ι-redex detector with the census of both children; an abstraction node
(kind `1`) recurses into its body child; every other node is `false`. -/
private theorem hasIotaCode_eq_ite (c : ℕ) :
    hasIotaCode c =
      (if shapeCode c = 1 then
        (if opKindCode c = 0 then
          (topIotaCode c || hasIotaCode (child0Code c) || hasIotaCode (child1Code c))
         else if opKindCode c = 1 then hasIotaCode (child0Code c)
         else false)
      else false) := by
  rw [hasIotaCode]
  split <;> simp_all [shapeCode, opKindCode, child0Code, child1Code]

/-- The node of the `hasIotaCode` course-of-values fold at slots `(i, cand, code)`:
dispatch on the shape tag and operation kind bit of the index `i`. At an application
node (shape `1`, kind `0`) it maxes the top ι-redex census (a full call of `topIotaER`)
with the two child censuses read off the β-table at `child0Code i` and `child1Code i`;
an abstraction node (kind `1`) reads the single child census; every other node returns
`0`. Same-function recursion goes through the β-table; the top-ι helper is composed as
an ordinary full call. `Bool` disjunction is the maximum of the `{0, 1}`-valued reads
(`toNat_or`). Novel realization. -/
private def hasIotaNode : ERMor1 3 :=
  condEqER (ERMor1.comp shapeER (fun _ : Fin 1 => ERMor1.proj 0)) (ERMor1.natN 3 1)
    (condEqER (ERMor1.comp opKindER (fun _ : Fin 1 => ERMor1.proj 0)) (ERMor1.natN 3 0)
      (ERMor1.comp maxN (fun i => match i with
        | ⟨0, _⟩ => ERMor1.comp maxN (fun j => match j with
            | ⟨0, _⟩ => ERMor1.comp topIotaER (fun _ : Fin 1 => ERMor1.proj 0)
            | ⟨1, _⟩ =>
                ERMor1.betaOnCandFold (ERMor1.comp child0ER (fun _ : Fin 1 => ERMor1.proj 0)))
        | ⟨1, _⟩ =>
            ERMor1.betaOnCandFold (ERMor1.comp child1ER (fun _ : Fin 1 => ERMor1.proj 0))))
      (condEqER (ERMor1.comp opKindER (fun _ : Fin 1 => ERMor1.proj 0)) (ERMor1.natN 3 1)
        (ERMor1.betaOnCandFold (ERMor1.comp child0ER (fun _ : Fin 1 => ERMor1.proj 0)))
        (ERMor1.natN 3 0)))
    (ERMor1.natN 3 0)

/-- The node value of `hasIotaNode` at `(i, cand, code)` as a nested conditional on the
shape tag and operation kind bit of `i`, with the top census by a full `topIotaCode`
call and the child censuses read off the candidate β-table. -/
private theorem hasIotaNode_interp (i cand code : ℕ) :
    hasIotaNode.interp (Fin.cons i (Fin.cons cand (Fin.cons code (![] : Fin 0 → ℕ)))) =
      if shapeCode i = 1 then
        (if opKindCode i = 0 then
          max (max (topIotaCode i).toNat
            (cand.unpair.1 % (1 + (child0Code i + 1) * cand.unpair.2)))
            (cand.unpair.1 % (1 + (child1Code i + 1) * cand.unpair.2))
         else if opKindCode i = 1 then
           cand.unpair.1 % (1 + (child0Code i + 1) * cand.unpair.2)
         else 0)
      else 0 := by
  simp only [hasIotaNode, condEqER_interp, maxN_interp, ERMor1.interp_comp,
    ERMor1.interp_betaOnCandFold, ERMor1.interp_natN, ERMor1.interp_proj, Fin.cons_zero,
    cons_fin_one, shapeER_interp, opKindER_interp, child0ER_interp, child1ER_interp,
    topIotaER_interp]

/-- The ι-census detector as an elementary-recursive course-of-values fold:
`ERMor1.cvRec` at fold slot the code and node `hasIotaNode`, with constant value bound
`1` (Decision Q3, `Bool.toNat`-valued). The node composes `topIotaER` as an ordinary
full call; only the same-function descent goes through the β-table. Realizes the strong
recursion of `hasIotaCode` (Leivant III section 4.2, pp. 223-224) as a single bounded
β-witness search. Novel realization. -/
def hasIotaER : ERMor1 1 := ERMor1.cvRec hasIotaNode (ERMor1.oneN 1)

/-- Interpretation of `hasIotaER`: the `Bool.toNat` of the ι-census detector
`hasIotaCode`, unconditionally on every code. Discharges the hypotheses of
`ERMor1.interp_cvRec_of_bounded` with `f := fun j => (hasIotaCode j).toNat`: the
constant value bound `1`, its monotonicity, and node faithfulness from
`hasIotaCode_eq_ite` with the two children strictly below the index
(`child0Code_lt_of_shape_one`, `child1Code_lt_of_shape_one`), the `Bool` disjunction
carried to the maximum by `toNat_or`. -/
@[simp] theorem hasIotaER_interp (c : ℕ) : hasIotaER.interp ![c] = (hasIotaCode c).toNat := by
  refine ERMor1.interp_cvRec_of_bounded hasIotaNode (ERMor1.oneN 1) c ![]
    (fun j => (hasIotaCode j).toNat) (fun j _ => ?_) (fun j _ => ?_)
    (fun i _ cand htrace => ?_)
  · cases h : hasIotaCode j <;> simp [h]
  · simp
  · have htrace' : ∀ p, p < i →
        cand.unpair.1 % (1 + (p + 1) * cand.unpair.2) = (hasIotaCode p).toNat := htrace
    change hasIotaNode.interp _ = (hasIotaCode i).toNat
    rw [hasIotaNode_interp i cand c, hasIotaCode_eq_ite i]
    by_cases h1 : shapeCode i = 1
    · rw [if_pos h1, if_pos h1]
      by_cases h0 : opKindCode i = 0
      · rw [if_pos h0, if_pos h0, htrace' (child0Code i) (child0Code_lt_of_shape_one i h1),
          htrace' (child1Code i) (child1Code_lt_of_shape_one i h1), toNat_or, toNat_or]
      · rw [if_neg h0, if_neg h0]
        by_cases h1' : opKindCode i = 1
        · rw [if_pos h1', if_pos h1', htrace' (child0Code i) (child0Code_lt_of_shape_one i h1)]
        · rw [if_neg h1', if_neg h1']; rfl
    · rw [if_neg h1, if_neg h1]; rfl

/-! ### The iota worker -/

/-- Binary Gödel pairing of two reads at arity `n`: `pairER a b` interprets to the
pairing `Nat.pair (a.interp ctx) (b.interp ctx)`, the node-rebuild constructor of
the ι worker. -/
private def pairER {n : ℕ} (a b : ERMor1 n) : ERMor1 n :=
  ERMor1.comp ERMor1.natPair (fun i => match i with
    | ⟨0, _⟩ => a
    | ⟨1, _⟩ => b)

/-- Interpretation of `pairER`: the Gödel pairing of the two reads. -/
@[simp] private theorem pairER_interp {n : ℕ} (a b : ERMor1 n) (ctx : Fin n → ℕ) :
    (pairER a b).interp ctx = Nat.pair (a.interp ctx) (b.interp ctx) := by
  have key : (pairER a b).interp ctx
      = ERMor1.natPair.interp ![a.interp ctx, b.interp ctx] := by
    rw [pairER, ERMor1.interp_comp]
    congr 1
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  rw [key, ERMor1.interp_natPair]

-- ℕ-level sibling beside `iotaStepCode` in `CodeNormalizer.lean`; a private bridge input here.
/-- The operation-tag read on a code: the operation tag of an operation node
`Nat.pair 1 (Nat.pair op pack)`, the pairing of its kind bit and payload. The node
rebuild of the ι worker reuses it unchanged. -/
private def opTagCode (c : ℕ) : ℕ := (Nat.unpair (Nat.unpair c).2).1

-- ℕ-level sibling beside `iotaStepCode` in `CodeNormalizer.lean`; a private bridge input here.
/-- The ι-worker recursion of `iotaStepCode` as a nested conditional on the shape
tag and operation kind bit of the code: an application node (shape `1`, kind `0`)
descends into the function child when it carries an ι-redex, else the argument child,
else contracts a saturated root ι-redex by `iotaContractCode`, else the identity; an
abstraction node (kind `1`) descends into the body child when it carries an ι-redex;
every other node is unchanged. Surviving nodes carry the operation tag unchanged. -/
private theorem iotaStepCode_eq_ite (c : ℕ) :
    iotaStepCode c =
      (if shapeCode c = 1 then
        (if opKindCode c = 0 then
          (if hasIotaCode (child0Code c) = true then
            Nat.pair 1 (Nat.pair (opTagCode c)
              (Nat.pair (iotaStepCode (child0Code c)) (Nat.pair (child1Code c) 0)))
          else if hasIotaCode (child1Code c) = true then
            Nat.pair 1 (Nat.pair (opTagCode c)
              (Nat.pair (child0Code c) (Nat.pair (iotaStepCode (child1Code c)) 0)))
          else if topIotaCode c = true then iotaContractCode c
          else c)
         else if opKindCode c = 1 then
          (if hasIotaCode (child0Code c) = true then
            Nat.pair 1 (Nat.pair (opTagCode c)
              (Nat.pair (iotaStepCode (child0Code c)) 0))
          else c)
         else c)
      else c) := by
  rw [iotaStepCode]
  split <;> simp_all [shapeCode, opKindCode, child0Code, child1Code, opTagCode]

/-- The operation-tag read at arity `3`: the operation tag `opTagCode i` of the fold
slot `i`, two `Nat.unpair` components. The node-rebuild operation tag of the ι
worker. -/
private def opTagER3 : ERMor1 3 :=
  ERMor1.comp ERMor1.natUnpairFst (fun _ : Fin 1 =>
    ERMor1.comp ERMor1.natUnpairSnd (fun _ : Fin 1 => ERMor1.proj 0))

/-- The node value of `opTagER3` at `(i, cand, code)`: the operation tag `opTagCode
i`. -/
private theorem opTagER3_interp (i cand code : ℕ) :
    opTagER3.interp (Fin.cons i (Fin.cons cand (Fin.cons code (![] : Fin 0 → ℕ)))) =
      opTagCode i := by
  simp only [opTagER3, ERMor1.interp_comp, ERMor1.interp_natUnpairFst,
    ERMor1.interp_natUnpairSnd, cons_fin_one, ERMor1.interp_proj, Fin.cons_zero, opTagCode]

/-- The height-2 tower value bound of the ι worker as an `ERMor1 1` term: the
`towerER 2` composite over the polynomial `9 * c + 9`, the elementary-recursive
realization of the majorant `iotaStepCode_le_tower`. -/
private def iotaStepBoundER : ERMor1 1 :=
  ERMor1.comp (ERMor1.towerER 2) (fun _ : Fin 1 =>
    ERMor1.comp ERMor1.addN (fun j => match j with
      | ⟨0, _⟩ => ERMor1.comp ERMor1.mulN (fun k => match k with
          | ⟨0, _⟩ => ERMor1.natN 1 9
          | ⟨1, _⟩ => ERMor1.proj 0)
      | ⟨1, _⟩ => ERMor1.natN 1 9))

/-- Interpretation of `iotaStepBoundER`: the height-2 tower at `9 * c + 9`. -/
@[simp] private theorem iotaStepBoundER_interp (ctx : Fin 1 → ℕ) :
    iotaStepBoundER.interp ctx = tower 2 (9 * ctx 0 + 9) := by
  simp only [iotaStepBoundER, ERMor1.interp_comp, ERMor1.interp_towerER,
    ERMor1.interp_addN, ERMor1.interp_mulN, ERMor1.interp_natN, ERMor1.interp_proj]

/-- The node of the `iotaStepCode` course-of-values fold at slots `(i, cand, code)`:
dispatch on the shape tag and operation kind bit of the index `i`. At an application
node the ι-census of each child is a full call of `hasIotaER` and the top ι-redex a
full call of `topIotaER`; the same-function descent reads the recursed child off the
β-table, the contraction is a full call of `iotaContractER`, and the surviving nodes
are rebuilt by `pairER` with the operation tag `opTagER3`. Novel realization. -/
private def iotaStepNode : ERMor1 3 :=
  condEqER (ERMor1.comp shapeER (fun _ : Fin 1 => ERMor1.proj 0)) (ERMor1.natN 3 1)
    (condEqER (ERMor1.comp opKindER (fun _ : Fin 1 => ERMor1.proj 0)) (ERMor1.natN 3 0)
      (condEqER (ERMor1.comp hasIotaER (fun _ : Fin 1 =>
            ERMor1.comp child0ER (fun _ : Fin 1 => ERMor1.proj 0))) (ERMor1.natN 3 1)
        (pairER (ERMor1.natN 3 1)
          (pairER opTagER3
            (pairER (ERMor1.betaOnCandFold
                (ERMor1.comp child0ER (fun _ : Fin 1 => ERMor1.proj 0)))
              (pairER (ERMor1.comp child1ER (fun _ : Fin 1 => ERMor1.proj 0))
                (ERMor1.natN 3 0)))))
        (condEqER (ERMor1.comp hasIotaER (fun _ : Fin 1 =>
              ERMor1.comp child1ER (fun _ : Fin 1 => ERMor1.proj 0))) (ERMor1.natN 3 1)
          (pairER (ERMor1.natN 3 1)
            (pairER opTagER3
              (pairER (ERMor1.comp child0ER (fun _ : Fin 1 => ERMor1.proj 0))
                (pairER (ERMor1.betaOnCandFold
                    (ERMor1.comp child1ER (fun _ : Fin 1 => ERMor1.proj 0)))
                  (ERMor1.natN 3 0)))))
          (condEqER (ERMor1.comp topIotaER (fun _ : Fin 1 => ERMor1.proj 0))
              (ERMor1.natN 3 1)
            (ERMor1.comp iotaContractER (fun _ : Fin 1 => ERMor1.proj 0))
            (ERMor1.proj 0))))
      (condEqER (ERMor1.comp opKindER (fun _ : Fin 1 => ERMor1.proj 0)) (ERMor1.natN 3 1)
        (condEqER (ERMor1.comp hasIotaER (fun _ : Fin 1 =>
              ERMor1.comp child0ER (fun _ : Fin 1 => ERMor1.proj 0))) (ERMor1.natN 3 1)
          (pairER (ERMor1.natN 3 1)
            (pairER opTagER3
              (pairER (ERMor1.betaOnCandFold
                  (ERMor1.comp child0ER (fun _ : Fin 1 => ERMor1.proj 0)))
                (ERMor1.natN 3 0))))
          (ERMor1.proj 0))
        (ERMor1.proj 0)))
    (ERMor1.proj 0)

/-- The node value of `iotaStepNode` at `(i, cand, code)` as a nested conditional on
the shape tag and operation kind bit of `i`, with the child ι-censuses by full
`hasIotaCode` calls, the top ι-redex by a full `topIotaCode` call, the descent read
off the candidate β-table, and the contraction by a full `iotaContractCode` call. -/
private theorem iotaStepNode_interp (i cand code : ℕ) :
    iotaStepNode.interp (Fin.cons i (Fin.cons cand (Fin.cons code (![] : Fin 0 → ℕ)))) =
      if shapeCode i = 1 then
        (if opKindCode i = 0 then
          (if hasIotaCode (child0Code i) = true then
            Nat.pair 1 (Nat.pair (opTagCode i)
              (Nat.pair (cand.unpair.1 % (1 + (child0Code i + 1) * cand.unpair.2))
                (Nat.pair (child1Code i) 0)))
          else if hasIotaCode (child1Code i) = true then
            Nat.pair 1 (Nat.pair (opTagCode i)
              (Nat.pair (child0Code i)
                (Nat.pair (cand.unpair.1 % (1 + (child1Code i + 1) * cand.unpair.2)) 0)))
          else if topIotaCode i = true then iotaContractCode i
          else i)
         else if opKindCode i = 1 then
          (if hasIotaCode (child0Code i) = true then
            Nat.pair 1 (Nat.pair (opTagCode i)
              (Nat.pair (cand.unpair.1 % (1 + (child0Code i + 1) * cand.unpair.2)) 0))
          else i)
         else i)
      else i := by
  simp only [iotaStepNode, condEqER_interp, opTagER3_interp, pairER_interp,
    ERMor1.interp_comp, ERMor1.interp_betaOnCandFold, ERMor1.interp_natN,
    ERMor1.interp_proj, Fin.cons_zero, cons_fin_one, shapeER_interp, opKindER_interp,
    child0ER_interp, child1ER_interp, hasIotaER_interp, topIotaER_interp,
    iotaContractER_interp, Bool.toNat_eq_one]

/-- The ι worker as an elementary-recursive course-of-values fold: `ERMor1.cvRec` at
fold slot the code and node `iotaStepNode`, with value bound the height-2 tower
composite `iotaStepBoundER` over `9 * c + 9` — the first fold with a tower-2
majorant. The node composes `hasIotaER`, `topIotaER`, `iotaContractER` as ordinary
full calls and rebuilds surviving nodes with `pairER`; only the same-function descent
goes through the β-table. Realizes the strong recursion of `iotaStepCode` (Leivant III
section 4.2, pp. 223-224; the machine-model absorption of footnote 10, p. 226) as a
single bounded β-witness search. Novel realization. -/
def iotaStepER : ERMor1 1 := ERMor1.cvRec iotaStepNode iotaStepBoundER

/-- Interpretation of `iotaStepER`: the ι worker `iotaStepCode`, unconditionally on
every code. Discharges the hypotheses of `ERMor1.interp_cvRec_of_bounded` with
`f := iotaStepCode`: the value bound `iotaStepCode_le_tower`, its monotonicity from
`tower_mono_right` on `9 * j + 9 ≤ 9 * code + 9`, and node faithfulness from
`iotaStepCode_eq_ite` with the recursed children strictly below the index
(`child0Code_lt_of_shape_one`, `child1Code_lt_of_shape_one`). -/
@[simp] theorem iotaStepER_interp (c : ℕ) : iotaStepER.interp ![c] = iotaStepCode c := by
  refine ERMor1.interp_cvRec_of_bounded iotaStepNode iotaStepBoundER c ![] iotaStepCode
    (fun j _ => ?_) (fun j hj => ?_) (fun i _ cand htrace => ?_)
  · simp only [iotaStepBoundER_interp, Fin.cons_zero]
    exact iotaStepCode_le_tower j
  · simp only [iotaStepBoundER_interp, Fin.cons_zero]
    exact tower_mono_right 2 (by omega)
  · change iotaStepNode.interp _ = iotaStepCode i
    rw [iotaStepNode_interp i cand c, iotaStepCode_eq_ite i]
    by_cases h1 : shapeCode i = 1
    · rw [if_pos h1, if_pos h1]
      by_cases h0 : opKindCode i = 0
      · rw [if_pos h0, if_pos h0]
        by_cases hI0 : hasIotaCode (child0Code i) = true
        · rw [if_pos hI0, if_pos hI0,
            htrace (child0Code i) (child0Code_lt_of_shape_one i h1)]
        · rw [if_neg hI0, if_neg hI0]
          by_cases hI1 : hasIotaCode (child1Code i) = true
          · rw [if_pos hI1, if_pos hI1,
              htrace (child1Code i) (child1Code_lt_of_shape_one i h1)]
          · rw [if_neg hI1, if_neg hI1]
      · rw [if_neg h0, if_neg h0]
        by_cases h1k : opKindCode i = 1
        · rw [if_pos h1k, if_pos h1k]
          by_cases hI0 : hasIotaCode (child0Code i) = true
          · rw [if_pos hI0, if_pos hI0,
              htrace (child0Code i) (child0Code_lt_of_shape_one i h1)]
          · rw [if_neg hI0, if_neg hI0]
        · rw [if_neg h1k, if_neg h1k]
    · rw [if_neg h1, if_neg h1]

/-! ### The code shift and its iterate -/

/-- The operation-tag read at arity `1`: the operation tag `opTagCode c` of the fold
slot, two `Nat.unpair` components. The node-rebuild operation tag of the weakening
worker. -/
private def opTagER : ERMor1 1 :=
  ERMor1.comp ERMor1.natUnpairFst (fun _ : Fin 1 =>
    ERMor1.comp ERMor1.natUnpairSnd (fun _ : Fin 1 => ERMor1.proj 0))

/-- Interpretation of `opTagER`: the operation tag `opTagCode c`. -/
@[simp] private theorem opTagER_interp (n : ℕ) : opTagER.interp ![n] = opTagCode n := by
  simp only [opTagER, ERMor1.interp_comp, ERMor1.interp_natUnpairFst,
    ERMor1.interp_natUnpairSnd, cons_fin_one, ERMor1.interp_proj, Matrix.cons_val_zero, opTagCode]

/-- The code-level weakening `shiftCode j` as a nested conditional on the shape tag and
operation kind bit of the code: a variable leaf (shape `0`) bumps its level when it lies
at or beyond the insertion level `j`; an application node (shape `1`, kind `0`) rebuilds
with the two child codes weakened; an abstraction node (kind `1`) rebuilds with the sole
body child weakened; every other node is unchanged. -/
private theorem shiftCode_eq_ite (j c : ℕ) :
    shiftCode j c =
      (if shapeCode c = 0 then
        (if argCode c < j then Nat.pair 0 (argCode c) else Nat.pair 0 (argCode c + 1))
      else if shapeCode c = 1 then
        (if opKindCode c = 0 then
          Nat.pair 1 (Nat.pair (opTagCode c)
            (Nat.pair (shiftCode j (child0Code c)) (Nat.pair (shiftCode j (child1Code c)) 0)))
         else if opKindCode c = 1 then
          Nat.pair 1 (Nat.pair (opTagCode c) (Nat.pair (shiftCode j (child0Code c)) 0))
         else c)
      else c) := by
  rw [shiftCode]
  split <;> simp_all [shapeCode, opKindCode, argCode, opTagCode, child0Code, child1Code]

/-- The context selector `Fin.cons i (Fin.cons cand (Fin.cons code ![jp]))` reads the
insertion level `jp` at slot `3`. -/
private theorem shiftNode_ctx_j (i cand code jp : ℕ) :
    (Fin.cons i (Fin.cons cand (Fin.cons code ![jp])) : Fin 4 → ℕ) 3 = jp := rfl

/-- The node of the `shiftCode j` course-of-values fold at slots `(i, cand, code, j)`:
dispatch on the shape tag and operation kind bit of the index `i`, reading the insertion
level `j` from the parameter slot. A variable leaf compares the level `argCode i` against
`j` via `ltN`/`condN`; an application or abstraction node rebuilds with `natPair`, reading
the weakened children off the β-table; every other node is unchanged. Novel realization. -/
private def shiftNode : ERMor1 4 :=
  condEqER (ERMor1.comp shapeER (fun _ : Fin 1 => ERMor1.proj 0)) (ERMor1.natN 4 0)
    (ERMor1.comp ERMor1.condN (fun t => match t with
      | ⟨0, _⟩ => ERMor1.comp ERMor1.ltN (fun s => match s with
          | ⟨0, _⟩ => ERMor1.comp argER (fun _ : Fin 1 => ERMor1.proj 0)
          | ⟨1, _⟩ => ERMor1.proj 3)
      | ⟨1, _⟩ => pairER (ERMor1.natN 4 0) (ERMor1.comp argER (fun _ : Fin 1 => ERMor1.proj 0))
      | ⟨2, _⟩ => pairER (ERMor1.natN 4 0)
          (ERMor1.comp ERMor1.succ (fun _ : Fin 1 =>
            ERMor1.comp argER (fun _ : Fin 1 => ERMor1.proj 0)))))
    (condEqER (ERMor1.comp shapeER (fun _ : Fin 1 => ERMor1.proj 0)) (ERMor1.natN 4 1)
      (condEqER (ERMor1.comp opKindER (fun _ : Fin 1 => ERMor1.proj 0)) (ERMor1.natN 4 0)
        (pairER (ERMor1.natN 4 1)
          (pairER (ERMor1.comp opTagER (fun _ : Fin 1 => ERMor1.proj 0))
            (pairER (ERMor1.betaOnCandFold (ERMor1.comp child0ER (fun _ : Fin 1 => ERMor1.proj 0)))
              (pairER (ERMor1.betaOnCandFold
                  (ERMor1.comp child1ER (fun _ : Fin 1 => ERMor1.proj 0)))
                (ERMor1.natN 4 0)))))
        (condEqER (ERMor1.comp opKindER (fun _ : Fin 1 => ERMor1.proj 0)) (ERMor1.natN 4 1)
          (pairER (ERMor1.natN 4 1)
            (pairER (ERMor1.comp opTagER (fun _ : Fin 1 => ERMor1.proj 0))
              (pairER (ERMor1.betaOnCandFold
                  (ERMor1.comp child0ER (fun _ : Fin 1 => ERMor1.proj 0)))
                (ERMor1.natN 4 0))))
          (ERMor1.proj 0)))
      (ERMor1.proj 0))

/-- The node value of `shiftNode` at `(i, cand, code, jp)` as a nested conditional on the
shape tag and operation kind bit of `i`, with the weakened children read off the candidate
β-table. -/
private theorem shiftNode_interp (i cand code jp : ℕ) :
    shiftNode.interp (Fin.cons i (Fin.cons cand (Fin.cons code ![jp]))) =
      if shapeCode i = 0 then
        (if argCode i < jp then Nat.pair 0 (argCode i) else Nat.pair 0 (argCode i + 1))
      else if shapeCode i = 1 then
        (if opKindCode i = 0 then
          Nat.pair 1 (Nat.pair (opTagCode i)
            (Nat.pair (cand.unpair.1 % (1 + (child0Code i + 1) * cand.unpair.2))
              (Nat.pair (cand.unpair.1 % (1 + (child1Code i + 1) * cand.unpair.2)) 0)))
         else if opKindCode i = 1 then
          Nat.pair 1 (Nat.pair (opTagCode i)
            (Nat.pair (cand.unpair.1 % (1 + (child0Code i + 1) * cand.unpair.2)) 0))
         else i)
      else i := by
  simp only [shiftNode, condEqER_interp, pairER_interp, ERMor1.interp_comp,
    ERMor1.interp_condN, ERMor1.interp_ltN, ERMor1.interp_betaOnCandFold,
    ERMor1.interp_natN, ERMor1.interp_succ, ERMor1.interp_proj, Fin.cons_zero,
    cons_fin_one, shapeER_interp, argER_interp, opKindER_interp, opTagER_interp,
    child0ER_interp, child1ER_interp, shiftNode_ctx_j, Matrix.cons_val_zero]
  by_cases hv : shapeCode i = 0
  · rw [if_pos hv, if_pos hv]
    by_cases hlt : argCode i < jp <;> simp [hlt]
  · rw [if_neg hv, if_neg hv]

/-- The height-2 tower value bound of the weakening worker as an `ERMor1 2` term: the
`towerER 2` composite over the polynomial `9 * c + 9`, the elementary-recursive
realization of the majorant `shiftCode_le_tower`. -/
private def shiftBoundER : ERMor1 2 :=
  ERMor1.comp (ERMor1.towerER 2) (fun _ : Fin 1 =>
    ERMor1.comp ERMor1.addN (fun j => match j with
      | ⟨0, _⟩ => ERMor1.comp ERMor1.mulN (fun k => match k with
          | ⟨0, _⟩ => ERMor1.natN 2 9
          | ⟨1, _⟩ => ERMor1.proj 0)
      | ⟨1, _⟩ => ERMor1.natN 2 9))

/-- Interpretation of `shiftBoundER`: the height-2 tower at `9 * c + 9`. -/
@[simp] private theorem shiftBoundER_interp (ctx : Fin 2 → ℕ) :
    shiftBoundER.interp ctx = tower 2 (9 * ctx 0 + 9) := by
  simp only [shiftBoundER, ERMor1.interp_comp, ERMor1.interp_towerER,
    ERMor1.interp_addN, ERMor1.interp_mulN, ERMor1.interp_natN, ERMor1.interp_proj]

/-- The code-level weakening as an elementary-recursive course-of-values fold:
`ERMor1.cvRec` at `k = 1` with fold slot the code, parameter slot the insertion level `j`,
and node `shiftNode`, with value bound the height-2 tower composite `shiftBoundER` over
`9 * c + 9`. The node reads the level from the parameter slot and rebuilds application and
abstraction nodes with `natPair`, β-reading the child positions for the same-function
descent. Realizes the strong recursion of `shiftCode` (Leivant III section 4.2, p. 223)
as a single bounded β-witness search. Novel realization. -/
def shiftER : ERMor1 2 := ERMor1.cvRec shiftNode shiftBoundER

/-- Interpretation of `shiftER`: the code-level weakening `shiftCode j m`, unconditionally
on every code and level. Discharges the hypotheses of `ERMor1.interp_cvRec_of_bounded` with
`f := shiftCode j`: the value bound `shiftCode_le_tower`, its monotonicity from
`tower_mono_right` on `9 * i + 9 ≤ 9 * m + 9`, and node faithfulness from `shiftCode_eq_ite`
with the recursed children strictly below the index (`child0Code_lt_of_shape_one`,
`child1Code_lt_of_shape_one`). -/
@[simp] theorem shiftER_interp (m j : ℕ) : shiftER.interp ![m, j] = shiftCode j m := by
  refine ERMor1.interp_cvRec_of_bounded shiftNode shiftBoundER m ![j] (shiftCode j)
    (fun i _ => ?_) (fun i hi => ?_) (fun i _ cand htrace => ?_)
  · simp only [shiftBoundER_interp, Fin.cons_zero]
    exact shiftCode_le_tower j i
  · simp only [shiftBoundER_interp, Fin.cons_zero]
    exact tower_mono_right 2 (by omega)
  · rw [shiftNode_interp i cand m j, shiftCode_eq_ite j i]
    by_cases hv : shapeCode i = 0
    · rw [if_pos hv, if_pos hv]
    · rw [if_neg hv, if_neg hv]
      by_cases hs1 : shapeCode i = 1
      · rw [if_pos hs1, if_pos hs1]
        by_cases hk0 : opKindCode i = 0
        · rw [if_pos hk0, if_pos hk0,
            htrace (child0Code i) (child0Code_lt_of_shape_one i hs1),
            htrace (child1Code i) (child1Code_lt_of_shape_one i hs1)]
        · rw [if_neg hk0, if_neg hk0]
          by_cases hk1 : opKindCode i = 1
          · rw [if_pos hk1, if_pos hk1,
              htrace (child0Code i) (child0Code_lt_of_shape_one i hs1)]
          · rw [if_neg hk1, if_neg hk1]
      · rw [if_neg hs1, if_neg hs1]

/-- The height-2 tower value bound of the iterated weakening as an `ERMor1 3` term: the
`towerER 2` composite over the polynomial `9 * e + 9 * d + 9`, the elementary-recursive
realization of the majorant `shiftCode_iterate_le_tower`. -/
private def shiftIterBoundER : ERMor1 3 :=
  ERMor1.comp (ERMor1.towerER 2) (fun _ : Fin 1 =>
    ERMor1.comp ERMor1.addN (fun i => match i with
      | ⟨0, _⟩ => ERMor1.comp ERMor1.addN (fun j => match j with
          | ⟨0, _⟩ => ERMor1.comp ERMor1.mulN (fun k => match k with
              | ⟨0, _⟩ => ERMor1.natN 3 9
              | ⟨1, _⟩ => ERMor1.proj 2)
          | ⟨1, _⟩ => ERMor1.comp ERMor1.mulN (fun k => match k with
              | ⟨0, _⟩ => ERMor1.natN 3 9
              | ⟨1, _⟩ => ERMor1.proj 0))
      | ⟨1, _⟩ => ERMor1.natN 3 9))

/-- Interpretation of `shiftIterBoundER`: the height-2 tower at `9 * e + 9 * d + 9`, reading
the depth `d` at slot `0` and the substituend `e` at slot `2`. -/
@[simp] private theorem shiftIterBoundER_interp (d j e : ℕ) :
    shiftIterBoundER.interp (Fin.cons d (Fin.cons j (Fin.cons e Fin.elim0)))
      = tower 2 (9 * e + 9 * d + 9) := by
  simp only [shiftIterBoundER, ERMor1.interp_comp, ERMor1.interp_towerER,
    ERMor1.interp_addN, ERMor1.interp_mulN, ERMor1.interp_natN, ERMor1.interp_proj]
  rfl

/-- The step term of the iterated weakening evaluates to a single weakening of the running
value: at slots `(i, prev, j, e)` it computes `shiftCode j prev` by a full call of
`shiftER`. -/
private theorem shiftIter_step_eval (j e i prev : ℕ) :
    (ERMor1.comp shiftER (fun s => match s with
      | ⟨0, _⟩ => ERMor1.proj (k := 4) 1
      | ⟨1, _⟩ => ERMor1.proj (k := 4) 2)).interp
      (Fin.cons i (Fin.cons prev (Fin.cons j (Fin.cons e Fin.elim0)))) = shiftCode j prev := by
  have hg : (fun s : Fin 2 => ((match s with
      | ⟨0, _⟩ => ERMor1.proj (k := 4) 1
      | ⟨1, _⟩ => ERMor1.proj (k := 4) 2) : ERMor1 4).interp
      (Fin.cons i (Fin.cons prev (Fin.cons j (Fin.cons e Fin.elim0))))) = ![prev, j] := by
    funext s
    match s with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  rw [ERMor1.interp_comp, hg, shiftER_interp]

/-- The raw `Nat.rec` trace of the iterated-weakening step at counter `n` equals the
`Function.iterate` of `shiftCode j` on the substituend `e`. -/
private theorem shiftIter_rec_eq (j e n : ℕ) :
    (Nat.rec ((ERMor1.proj (k := 2) 1).interp (Fin.cons j (Fin.cons e Fin.elim0)))
      (fun i prev => (ERMor1.comp shiftER (fun s => match s with
        | ⟨0, _⟩ => ERMor1.proj (k := 4) 1
        | ⟨1, _⟩ => ERMor1.proj (k := 4) 2)).interp
        (Fin.cons i (Fin.cons prev (Fin.cons j (Fin.cons e Fin.elim0))))) n : ℕ)
      = (shiftCode j)^[n] e := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ← ih]
    exact shiftIter_step_eval j e m _

/-- The iterated code-level weakening as an elementary-recursive bounded recursion:
`ERMor1.boundedRec` over `shiftER`, one weakening step per depth increment (Decision Q7),
with base the substituend `e`, step a full call of `shiftER`, and value bound the height-2
tower composite `shiftIterBoundER` over `9 * e + 9 * d + 9`. Realizes the substituend
weakening tower of `subCode`'s abstraction descent (Leivant III section 4.2, pp. 223-224).
Novel realization. -/
def shiftIterER : ERMor1 3 :=
  ERMor1.boundedRec
    (ERMor1.proj (k := 2) 1)
    (ERMor1.comp shiftER (fun s => match s with
      | ⟨0, _⟩ => ERMor1.proj (k := 4) 1
      | ⟨1, _⟩ => ERMor1.proj (k := 4) 2))
    shiftIterBoundER

set_option maxHeartbeats 400000 in
-- `boundedRec_eq_natRec_of_bounded` unification is heavy
/-- Interpretation of `shiftIterER`: the iterate `(shiftCode j)^[d] e`, unconditionally on
every depth, level, and substituend. Discharges the hypotheses of
`ERMor1.boundedRec_eq_natRec_of_bounded`: the trace equals the iterate (`shiftIter_rec_eq`),
the dominance is the iterate majorant `shiftCode_iterate_le_tower`, and the monotonicity is
the linearity of the tower argument in the depth. -/
@[simp] theorem shiftIterER_interp (d j e : ℕ) :
    shiftIterER.interp ![d, j, e] = (shiftCode j)^[d] e := by
  change shiftIterER.interp (Fin.cons d (Fin.cons j (Fin.cons e Fin.elim0)))
      = (shiftCode j)^[d] e
  unfold shiftIterER
  refine (ERMor1.boundedRec_eq_natRec_of_bounded _ _ _ _ _ ?_ ?_).trans ?_
  · intro t _ht
    rw [shiftIter_rec_eq, shiftIterBoundER_interp]
    exact shiftCode_iterate_le_tower j t e
  · intro t ht
    rw [shiftIterBoundER_interp, shiftIterBoundER_interp]
    exact tower_mono_right 2 (by omega)
  · rw [shiftIter_rec_eq]

/-! ### The code substitution -/

/-- The code-level substitution `subCode j e` as a nested conditional on the shape tag
and operation kind bit of the code: a variable leaf (shape `0`) rewrites by the
three-way comparison of its level against the substituted level `j`; an application
node (shape `1`, kind `0`) rebuilds with the two child codes substituted; an
abstraction node (kind `1`) rebuilds with the sole body child substituted against the
substituend weakened by `shiftCode j`; every other node is unchanged. -/
private theorem subCode_eq_ite (j e c : ℕ) :
    subCode j e c =
      if shapeCode c = 0 then
        (if argCode c < j then Nat.pair 0 (argCode c)
         else if argCode c = j then e
         else Nat.pair 0 (argCode c - 1))
      else if shapeCode c = 1 then
        (if opKindCode c = 0 then
          Nat.pair 1 (Nat.pair (opTagCode c)
            (Nat.pair (subCode j e (child0Code c)) (Nat.pair (subCode j e (child1Code c)) 0)))
         else if opKindCode c = 1 then
          Nat.pair 1 (Nat.pair (opTagCode c)
            (Nat.pair (subCode j (shiftCode j e) (child0Code c)) 0))
         else c)
      else c := by
  rw [subCode]
  split <;> simp_all [shapeCode, opKindCode, argCode, opTagCode, child0Code, child1Code]

/-- `Nat.pair` is monotone in both arguments, the ≤-corollary of the mathlib strict
monotonicities `Nat.pair_lt_pair_left` and `Nat.pair_lt_pair_right`. Carries the
gated-index containment of the substitution fold: every gated index `Nat.pair d m`
with `d, m ≤ c` sits at or below the index bound `Nat.pair c c`. -/
private theorem pair_le_pair {a b x y : ℕ} (hax : a ≤ x) (hby : b ≤ y) :
    Nat.pair a b ≤ Nat.pair x y := by
  have h1 : Nat.pair a b ≤ Nat.pair x b := by
    rcases Nat.eq_or_lt_of_le hax with rfl | h
    · exact le_refl _
    · exact le_of_lt (Nat.pair_lt_pair_left b h)
  have h2 : Nat.pair x b ≤ Nat.pair x y := by
    rcases Nat.eq_or_lt_of_le hby with rfl | h
    · exact le_refl _
    · exact le_of_lt (Nat.pair_lt_pair_right x h)
  exact le_trans h1 h2

/-- The depth read of the substitution fold at arity `5`: the leading `Nat.unpair`
component of the index slot, the weakening depth `d` of the 2-D key `Nat.pair d m`
(Decision Q8). -/
private def subIdxDepthER : ERMor1 5 :=
  ERMor1.comp ERMor1.natUnpairFst (fun _ : Fin 1 => ERMor1.proj 0)

/-- Interpretation of `subIdxDepthER`: the depth component of the index. -/
private theorem subIdxDepthER_interp (i cand c j e : ℕ) :
    subIdxDepthER.interp (Fin.cons i (Fin.cons cand (Fin.cons c ![j, e])))
      = (Nat.unpair i).1 := by
  simp only [subIdxDepthER, ERMor1.interp_comp, ERMor1.interp_proj, Fin.cons_zero,
    cons_fin_one, ERMor1.interp_natUnpairFst]

/-- The code read of the substitution fold at arity `5`: the trailing `Nat.unpair`
component of the index slot, the code `m` of the 2-D key `Nat.pair d m`
(Decision Q8). -/
private def subIdxCodeER : ERMor1 5 :=
  ERMor1.comp ERMor1.natUnpairSnd (fun _ : Fin 1 => ERMor1.proj 0)

/-- Interpretation of `subIdxCodeER`: the code component of the index. -/
private theorem subIdxCodeER_interp (i cand c j e : ℕ) :
    subIdxCodeER.interp (Fin.cons i (Fin.cons cand (Fin.cons c ![j, e])))
      = (Nat.unpair i).2 := by
  simp only [subIdxCodeER, ERMor1.interp_comp, ERMor1.interp_proj, Fin.cons_zero,
    cons_fin_one, ERMor1.interp_natUnpairSnd]

/-- The context selector `Fin.cons i (Fin.cons cand (Fin.cons c ![j, e]))` reads the
substituted level `j` at slot `3`. -/
private theorem subNode_ctx_j (i cand c j e : ℕ) :
    (Fin.cons i (Fin.cons cand (Fin.cons c ![j, e])) : Fin 5 → ℕ) 3 = j := rfl

/-- The variable-hit arm of the substitution fold: the iterated weakening
`shiftIterER` composed as an ordinary full call at the depth read of the index and
the level and substituend parameter slots (Decision Q7). -/
private def subHitER : ERMor1 5 :=
  ERMor1.comp shiftIterER (fun s => match s with
    | ⟨0, _⟩ => subIdxDepthER
    | ⟨1, _⟩ => ERMor1.proj 3
    | ⟨2, _⟩ => ERMor1.proj 4)

/-- Interpretation of `subHitER`: the iterated weakening `(shiftCode j)^[d] e` at the
depth component `d` of the index. -/
private theorem subHitER_interp (i cand c j e : ℕ) :
    subHitER.interp (Fin.cons i (Fin.cons cand (Fin.cons c ![j, e])))
      = (shiftCode j)^[(Nat.unpair i).1] e := by
  have harg : (fun s : Fin 3 => ((match s with
      | ⟨0, _⟩ => subIdxDepthER
      | ⟨1, _⟩ => ERMor1.proj 3
      | ⟨2, _⟩ => ERMor1.proj 4) : ERMor1 5).interp
        (Fin.cons i (Fin.cons cand (Fin.cons c ![j, e]))))
      = ![(Nat.unpair i).1, j, e] := by
    funext s
    match s with
    | ⟨0, _⟩ => exact subIdxDepthER_interp i cand c j e
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
  rw [subHitER, ERMor1.interp_comp, harg, shiftIterER_interp]

/-- The gate of the substitution fold at slots `(i, c, j, e)`: the `0/1` indicator of
`d + m ≤ c` for the index `i = Nat.pair d m`, a `leN` composition over the `addN` of
the two `Nat.unpair` reads of the index against the code slot (Decision Q8). -/
private def subSaneER : ERMor1 4 :=
  ERMor1.comp ERMor1.leN (fun s => match s with
    | ⟨0, _⟩ => ERMor1.comp ERMor1.addN (fun t => match t with
        | ⟨0, _⟩ => ERMor1.comp ERMor1.natUnpairFst (fun _ : Fin 1 => ERMor1.proj 0)
        | ⟨1, _⟩ => ERMor1.comp ERMor1.natUnpairSnd (fun _ : Fin 1 => ERMor1.proj 0))
    | ⟨1, _⟩ => ERMor1.proj 1)

/-- Interpretation of `subSaneER`: the `0/1` indicator of the gate `d + m ≤ c`. -/
private theorem subSaneER_interp (i c j e : ℕ) :
    subSaneER.interp (Fin.cons i (Fin.cons c ![j, e]))
      = if (Nat.unpair i).1 + (Nat.unpair i).2 ≤ c then 1 else 0 := by
  -- The plain simp route does not apply: the comp-argument context shape is not simp-normal.
  have hunf : subSaneER.interp (Fin.cons i (Fin.cons c ![j, e]))
      = ERMor1.leN.interp ![(Nat.unpair i).1 + (Nat.unpair i).2, c] := by
    change ERMor1.leN.interp _ = ERMor1.leN.interp _
    congr 1
    funext s
    match s with
    | ⟨0, _⟩ =>
      change ERMor1.addN.interp _ = _
      have harg : (fun t : Fin 2 => ((match t with
          | ⟨0, _⟩ => ERMor1.comp ERMor1.natUnpairFst (fun _ : Fin 1 => ERMor1.proj 0)
          | ⟨1, _⟩ => ERMor1.comp ERMor1.natUnpairSnd
              (fun _ : Fin 1 => ERMor1.proj 0)) : ERMor1 4).interp
            (Fin.cons i (Fin.cons c ![j, e])))
          = ![(Nat.unpair i).1, (Nat.unpair i).2] := by
        funext t
        match t with
        | ⟨0, _⟩ =>
          change ERMor1.natUnpairFst.interp (fun _ : Fin 1 => i) = _
          rw [cons_fin_one, ERMor1.interp_natUnpairFst]
          rfl
        | ⟨1, _⟩ =>
          change ERMor1.natUnpairSnd.interp (fun _ : Fin 1 => i) = _
          rw [cons_fin_one, ERMor1.interp_natUnpairSnd]
          rfl
      rw [harg, ERMor1.interp_addN]
      rfl
    | ⟨1, _⟩ => rfl
  rw [hunf, ERMor1.interp_leN]
  rfl

/-- The index bound of the substitution fold: `Nat.pair c c` over the code slot,
dominating every gated index `Nat.pair d m` with `d + m ≤ c` (Decision Q8). -/
private def subIdxBoundER : ERMor1 3 := pairER (ERMor1.proj 0) (ERMor1.proj 0)

/-- Interpretation of `subIdxBoundER`: the index bound `Nat.pair c c`. -/
private theorem subIdxBoundER_interp (c j e : ℕ) :
    subIdxBoundER.interp (Fin.cons c ![j, e]) = Nat.pair c c := by
  simp only [subIdxBoundER, pairER_interp, ERMor1.interp_proj, Fin.cons_zero]

/-- The extraction position of the substitution fold: `Nat.pair 0 c`, the input code
at weakening depth `0` (Decision Q8). -/
private def subExtractER : ERMor1 3 := pairER (ERMor1.natN 3 0) (ERMor1.proj 0)

/-- Interpretation of `subExtractER`: the extraction position `Nat.pair 0 c`. -/
private theorem subExtractER_interp (c j e : ℕ) :
    subExtractER.interp (Fin.cons c ![j, e]) = Nat.pair 0 c := by
  simp only [subExtractER, pairER_interp, ERMor1.interp_natN, ERMor1.interp_proj,
    Fin.cons_zero]

/-- The height-2 tower value bound of the substitution fold as an `ERMor1 3` term: the
`towerER 2` composite over the polynomial `27 * c + 9 * e + 18`, dominating the gated
table entries through `subCode_shift_iterate_le_tower` (`d, m ≤ c` gives
`18 * m + 9 * d ≤ 27 * c`). -/
private def subBoundER : ERMor1 3 :=
  ERMor1.comp (ERMor1.towerER 2) (fun _ : Fin 1 =>
    ERMor1.comp ERMor1.addN (fun s => match s with
      | ⟨0, _⟩ => ERMor1.comp ERMor1.addN (fun t => match t with
          | ⟨0, _⟩ => ERMor1.comp ERMor1.mulN (fun u => match u with
              | ⟨0, _⟩ => ERMor1.natN 3 27
              | ⟨1, _⟩ => ERMor1.proj 0)
          | ⟨1, _⟩ => ERMor1.comp ERMor1.mulN (fun u => match u with
              | ⟨0, _⟩ => ERMor1.natN 3 9
              | ⟨1, _⟩ => ERMor1.proj 2))
      | ⟨1, _⟩ => ERMor1.natN 3 18))

/-- Interpretation of `subBoundER`: the height-2 tower at `27 * c + 9 * e + 18`. -/
private theorem subBoundER_interp (c j e : ℕ) :
    subBoundER.interp (Fin.cons c ![j, e]) = tower 2 (27 * c + 9 * e + 18) := by
  simp only [subBoundER, ERMor1.interp_comp, ERMor1.interp_towerER, ERMor1.interp_addN,
    ERMor1.interp_mulN, ERMor1.interp_natN, ERMor1.interp_proj]
  rfl

/-- The reference table of the substitution fold at input code `c`, level `j`, and
substituend `e` (Decision Q8): at an index `Nat.pair d m` inside the gate
`d + m ≤ c`, the substitution `subCode j ((shiftCode j)^[d] e) m` against the
`d`-fold weakened substituend; `0` off the gate. -/
private def subTable (c j e i : ℕ) : ℕ :=
  if (Nat.unpair i).1 + (Nat.unpair i).2 ≤ c then
    subCode j ((shiftCode j)^[(Nat.unpair i).1] e) (Nat.unpair i).2
  else 0

/-- The gated entry of `subTable`: at an index `Nat.pair d m` with `d + m ≤ c`, the
table stores `subCode j ((shiftCode j)^[d] e) m`. -/
private theorem subTable_pair_of_le (c j e d m : ℕ) (h : d + m ≤ c) :
    subTable c j e (Nat.pair d m) = subCode j ((shiftCode j)^[d] e) m := by
  unfold subTable
  simp only [Nat.unpair_pair]
  rw [if_pos h]

/-- The node of the substitution fold at slots `(i, cand, c, j, e)`: unpair the index
`i` into the weakening depth `d` and the code `m` and dispatch on the shape tag and
operation kind bit of `m`, mirroring the `subCode` arms. A variable leaf compares its
level against the level slot `j`: below, the leaf is rebuilt; at the level, the
iterated substituend is a full call of `shiftIterER` at depth `d` (the `subHitER`
arm); above, the level drops by one. An application node rebuilds with the two child
codes read off the β-table at `Nat.pair d (child0Code m)` and
`Nat.pair d (child1Code m)`; an abstraction node reads its sole body child at
`Nat.pair (d + 1) (child0Code m)` — the substituend shift of `subCode_lam` is
absorbed into the depth component (Decision Q8); every other node returns the code
component `m` unchanged. Novel realization. -/
private def subNodeER : ERMor1 5 :=
  condEqER (ERMor1.comp shapeER (fun _ : Fin 1 => subIdxCodeER)) (ERMor1.natN 5 0)
    (ERMor1.comp ERMor1.condN (fun t => match t with
      | ⟨0, _⟩ => ERMor1.comp ERMor1.ltN (fun s => match s with
          | ⟨0, _⟩ => ERMor1.comp argER (fun _ : Fin 1 => subIdxCodeER)
          | ⟨1, _⟩ => ERMor1.proj 3)
      | ⟨1, _⟩ => pairER (ERMor1.natN 5 0) (ERMor1.comp argER (fun _ : Fin 1 => subIdxCodeER))
      | ⟨2, _⟩ => condEqER (ERMor1.comp argER (fun _ : Fin 1 => subIdxCodeER))
          (ERMor1.proj 3) subHitER
          (pairER (ERMor1.natN 5 0)
            (ERMor1.comp ERMor1.pred (fun _ : Fin 1 =>
              ERMor1.comp argER (fun _ : Fin 1 => subIdxCodeER))))))
    (condEqER (ERMor1.comp shapeER (fun _ : Fin 1 => subIdxCodeER)) (ERMor1.natN 5 1)
      (condEqER (ERMor1.comp opKindER (fun _ : Fin 1 => subIdxCodeER)) (ERMor1.natN 5 0)
        (pairER (ERMor1.natN 5 1)
          (pairER (ERMor1.comp opTagER (fun _ : Fin 1 => subIdxCodeER))
            (pairER (ERMor1.betaOnCandFold (pairER subIdxDepthER
                (ERMor1.comp child0ER (fun _ : Fin 1 => subIdxCodeER))))
              (pairER (ERMor1.betaOnCandFold (pairER subIdxDepthER
                  (ERMor1.comp child1ER (fun _ : Fin 1 => subIdxCodeER))))
                (ERMor1.natN 5 0)))))
        (condEqER (ERMor1.comp opKindER (fun _ : Fin 1 => subIdxCodeER)) (ERMor1.natN 5 1)
          (pairER (ERMor1.natN 5 1)
            (pairER (ERMor1.comp opTagER (fun _ : Fin 1 => subIdxCodeER))
              (pairER (ERMor1.betaOnCandFold (pairER
                  (ERMor1.comp ERMor1.succ (fun _ : Fin 1 => subIdxDepthER))
                  (ERMor1.comp child0ER (fun _ : Fin 1 => subIdxCodeER))))
                (ERMor1.natN 5 0))))
          subIdxCodeER))
      subIdxCodeER)

/-- The node value of `subNodeER` at index `Nat.pair d m` as a nested conditional on
the shape tag and operation kind bit of the code component `m`, with the iterated
substituend by a full `(shiftCode j)^[d]` call and the substituted children read off
the candidate β-table at the depth-keyed positions. -/
private theorem subNodeER_interp (d m cand c j e : ℕ) :
    subNodeER.interp (Fin.cons (Nat.pair d m) (Fin.cons cand (Fin.cons c ![j, e]))) =
      if shapeCode m = 0 then
        (if argCode m < j then Nat.pair 0 (argCode m)
         else if argCode m = j then (shiftCode j)^[d] e
         else Nat.pair 0 (argCode m - 1))
      else if shapeCode m = 1 then
        (if opKindCode m = 0 then
          Nat.pair 1 (Nat.pair (opTagCode m)
            (Nat.pair (cand.unpair.1 % (1 + (Nat.pair d (child0Code m) + 1) * cand.unpair.2))
              (Nat.pair (cand.unpair.1 % (1 + (Nat.pair d (child1Code m) + 1) * cand.unpair.2))
                0)))
         else if opKindCode m = 1 then
          Nat.pair 1 (Nat.pair (opTagCode m)
            (Nat.pair (cand.unpair.1 %
              (1 + (Nat.pair (d + 1) (child0Code m) + 1) * cand.unpair.2)) 0))
         else m)
      else m := by
  simp only [subNodeER, condEqER_interp, pairER_interp, subHitER_interp,
    subIdxDepthER_interp, subIdxCodeER_interp, ERMor1.interp_comp, ERMor1.interp_condN,
    ERMor1.interp_ltN, ERMor1.interp_betaOnCandFold, ERMor1.interp_natN, ERMor1.interp_succ,
    ERMor1.interp_pred, ERMor1.interp_proj, cons_fin_one, shapeER_interp,
    argER_interp, opKindER_interp, opTagER_interp, child0ER_interp, child1ER_interp,
    subNode_ctx_j, Nat.unpair_pair, Nat.pred_eq_sub_one, Matrix.cons_val_zero]
  by_cases hv : shapeCode m = 0
  · rw [if_pos hv, if_pos hv]
    by_cases hlt : argCode m < j <;> simp [hlt]
  · rw [if_neg hv, if_neg hv]

/-- The node value of the substitution fold equals the reference recursion: at index
`Nat.pair d m`, a candidate whose β-reads agree with the substitution at exactly the
positions the node reads — the two application children at depth `d` and the
abstraction body at depth `d + 1` — makes the node compute
`subCode j ((shiftCode j)^[d] e) m`. The abstraction arm reconciles the depth
increment with the substituend shift of `subCode_lam` through
`Function.iterate_succ_apply'` (Decision Q8). Shared arm-by-arm case analysis of the
node-faithfulness and determinacy inputs of `subER_interp`. -/
private theorem subNode_val_eq_subCode (c j e d m cand : ℕ)
    (h0 : shapeCode m = 1 → opKindCode m = 0 →
      cand.unpair.1 % (1 + (Nat.pair d (child0Code m) + 1) * cand.unpair.2)
          = subCode j ((shiftCode j)^[d] e) (child0Code m)
        ∧ cand.unpair.1 % (1 + (Nat.pair d (child1Code m) + 1) * cand.unpair.2)
          = subCode j ((shiftCode j)^[d] e) (child1Code m))
    (h1 : shapeCode m = 1 → opKindCode m = 1 →
      cand.unpair.1 % (1 + (Nat.pair (d + 1) (child0Code m) + 1) * cand.unpair.2)
        = subCode j ((shiftCode j)^[d + 1] e) (child0Code m)) :
    subNodeER.interp (Fin.cons (Nat.pair d m) (Fin.cons cand (Fin.cons c ![j, e])))
      = subCode j ((shiftCode j)^[d] e) m := by
  rw [subNodeER_interp, subCode_eq_ite j ((shiftCode j)^[d] e) m]
  by_cases hv : shapeCode m = 0
  · rw [if_pos hv, if_pos hv]
  · rw [if_neg hv, if_neg hv]
    by_cases hs : shapeCode m = 1
    · rw [if_pos hs, if_pos hs]
      by_cases hk0 : opKindCode m = 0
      · rw [if_pos hk0, if_pos hk0, (h0 hs hk0).1, (h0 hs hk0).2]
      · rw [if_neg hk0, if_neg hk0]
        by_cases hk1 : opKindCode m = 1
        · rw [if_pos hk1, if_pos hk1, h1 hs hk1,
            Function.iterate_succ_apply' (shiftCode j) d e]
        · rw [if_neg hk1, if_neg hk1]
    · rw [if_neg hs, if_neg hs]

/-- The code-level substitution as a gated elementary-recursive course-of-values
fold: `ERMor1.cvRecGated` at `k = 2` with slots `(c, j, e)` — the code, the
substituted level, and the substituend — and the two-dimensional index
`i = Nat.pair d m` keying the weakening depth and the code (Decision Q8). The gate
`subSaneER` confines the imposed equations to `d + m ≤ c`, the index bound is
`Nat.pair c c`, the extraction reads `Nat.pair 0 c` (the input code at depth `0`),
and the value bound is the height-2 tower composite `subBoundER` over
`27 * c + 9 * e + 18`. The node mirrors the `subCode` arms, composing `shiftIterER`
as an ordinary full call at the variable-hit leaf; only the same-function descent
goes through the β-table. Realizes the parameter-varying strong recursion of
`subCode` (Leivant III section 4.2, pp. 223-224; the machine-model absorption of
footnote 10, p. 226) as a single bounded β-witness search. Novel realization. -/
def subER : ERMor1 3 :=
  ERMor1.cvRecGated subNodeER subSaneER subIdxBoundER subExtractER subBoundER

/-- Interpretation of `subER`: the code-level substitution `subCode j e c`,
unconditionally on every code, level, and substituend. Discharges the hypotheses of
`ERMor1.interp_cvRecGated_eq` against the reference table `subTable` (Decision Q8):
the gate is `0/1`-valued, the gated entries are bounded by the tower-2 majorant
`subCode_shift_iterate_le_tower` (off-gate entries are `0`), node faithfulness holds
at gated indices through `subNode_val_eq_subCode` with every read position gated and
below the index bound (`pair_le_pair`), and determinacy (Decision Q6) is discharged
by strong induction on the code component of the index with the depth universally
quantified — children sit strictly below the code component, and the abstraction
descent pays its depth increment with `child0Code m < m`. The extraction at
`Nat.pair 0 c` is gated and stores the substitution at depth `0`, which is
`subCode j e c` by `Function.iterate_zero_apply`. -/
@[simp] theorem subER_interp (c j e : ℕ) : subER.interp ![c, j, e] = subCode j e c := by
  have h_sane : ∀ i, i ≤ subIdxBoundER.interp (Fin.cons c ![j, e]) →
      subSaneER.interp (Fin.cons i (Fin.cons c ![j, e])) ≤ 1 := by
    intro i _
    rw [subSaneER_interp]
    split
    · exact le_refl 1
    · exact Nat.zero_le 1
  have hval : ∀ i, i ≤ subIdxBoundER.interp (Fin.cons c ![j, e]) →
      subTable c j e i ≤ subBoundER.interp (Fin.cons c ![j, e]) := by
    intro i _
    rw [subBoundER_interp]
    unfold subTable
    split
    · rename_i hgate
      exact le_trans (subCode_shift_iterate_le_tower j (Nat.unpair i).1 e (Nat.unpair i).2)
        (tower_mono_right 2 (by omega))
    · exact Nat.zero_le _
  have h_node : ∀ i, i ≤ subIdxBoundER.interp (Fin.cons c ![j, e]) →
      subSaneER.interp (Fin.cons i (Fin.cons c ![j, e])) = 1 → ∀ cand,
      (∀ p, p ≤ subIdxBoundER.interp (Fin.cons c ![j, e]) →
        cand.unpair.1 % (1 + (p + 1) * cand.unpair.2) = subTable c j e p) →
      subNodeER.interp (Fin.cons i (Fin.cons cand (Fin.cons c ![j, e])))
        = subTable c j e i := by
    intro i _ hSi cand hreads
    obtain ⟨d, m, rfl⟩ : ∃ d m, i = Nat.pair d m :=
      ⟨(Nat.unpair i).1, (Nat.unpair i).2, (Nat.pair_unpair i).symm⟩
    have hdm : d + m ≤ c := by
      rw [subSaneER_interp] at hSi
      simp only [Nat.unpair_pair] at hSi
      by_contra hn
      rw [if_neg hn] at hSi
      omega
    rw [subTable_pair_of_le c j e d m hdm]
    refine subNode_val_eq_subCode c j e d m cand (fun hs hk0 => ?_) (fun hs hk1 => ?_)
    · have hc0 := child0Code_lt_of_shape_one m hs
      have hc1 := child1Code_lt_of_shape_one m hs
      constructor
      · rw [hreads (Nat.pair d (child0Code m))
            (by rw [subIdxBoundER_interp]; exact pair_le_pair (by omega) (by omega)),
          subTable_pair_of_le c j e d (child0Code m) (by omega)]
      · rw [hreads (Nat.pair d (child1Code m))
            (by rw [subIdxBoundER_interp]; exact pair_le_pair (by omega) (by omega)),
          subTable_pair_of_le c j e d (child1Code m) (by omega)]
    · have hc0 := child0Code_lt_of_shape_one m hs
      rw [hreads (Nat.pair (d + 1) (child0Code m))
          (by rw [subIdxBoundER_interp]; exact pair_le_pair (by omega) (by omega)),
        subTable_pair_of_le c j e (d + 1) (child0Code m) (by omega)]
  have h_det : ∀ cand,
      (∀ i, i ≤ subIdxBoundER.interp (Fin.cons c ![j, e]) →
        subSaneER.interp (Fin.cons i (Fin.cons c ![j, e])) = 1 →
        cand.unpair.1 % (1 + (i + 1) * cand.unpair.2) =
          subNodeER.interp (Fin.cons i (Fin.cons cand (Fin.cons c ![j, e])))) →
      cand.unpair.1 %
          (1 + (subExtractER.interp (Fin.cons c ![j, e]) + 1) * cand.unpair.2) =
        subTable c j e (subExtractER.interp (Fin.cons c ![j, e])) := by
    intro cand hcand
    rw [subExtractER_interp, subTable_pair_of_le c j e 0 c (by omega)]
    suffices hmain : ∀ m d, d + m ≤ c →
        cand.unpair.1 % (1 + (Nat.pair d m + 1) * cand.unpair.2)
          = subCode j ((shiftCode j)^[d] e) m from hmain c 0 (by omega)
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro d hdm
      have hle : Nat.pair d m ≤ subIdxBoundER.interp (Fin.cons c ![j, e]) := by
        rw [subIdxBoundER_interp]
        exact pair_le_pair (by omega) (by omega)
      have hS : subSaneER.interp (Fin.cons (Nat.pair d m) (Fin.cons c ![j, e])) = 1 := by
        rw [subSaneER_interp]
        simp only [Nat.unpair_pair]
        rw [if_pos hdm]
      rw [hcand (Nat.pair d m) hle hS]
      refine subNode_val_eq_subCode c j e d m cand (fun hs hk0 => ?_) (fun hs hk1 => ?_)
      · have hc0 := child0Code_lt_of_shape_one m hs
        have hc1 := child1Code_lt_of_shape_one m hs
        exact ⟨ih _ hc0 d (by omega), ih _ hc1 d (by omega)⟩
      · have hc0 := child0Code_lt_of_shape_one m hs
        exact ih _ hc0 (d + 1) (by omega)
  have h_ext : subExtractER.interp (Fin.cons c ![j, e]) ≤
      subIdxBoundER.interp (Fin.cons c ![j, e]) := by
    rw [subExtractER_interp, subIdxBoundER_interp]
    exact pair_le_pair (Nat.zero_le c) (le_refl c)
  have key := ERMor1.interp_cvRecGated_eq subNodeER subSaneER subIdxBoundER subExtractER
    subBoundER c ![j, e] (subTable c j e) h_sane hval h_node h_det h_ext
  rw [subExtractER_interp, subTable_pair_of_le c j e 0 c (by omega),
    Function.iterate_zero_apply] at key
  exact key

/-! ### The beta worker -/

/-- The β worker `betaStepCode q j` as a nested conditional on the shape tag and
operation kind bit of the code, in the four guard regimes of the application arm:
descend into the function child when it carries a rank-`q` redex; else into the
argument child; else contract the rank-`q` root β-redex by `subCode` at the
threaded level; else the identity. An abstraction node descends into its body
child at level `j + 1`; every other node is unchanged. -/
private theorem betaStepCode_eq_ite (q j c : ℕ) :
    betaStepCode q j c =
      if shapeCode c = 1 then
        (if opKindCode c = 0 then
          (if betaRankCode (child0Code c) = q then
            Nat.pair 1 (Nat.pair (opTagCode c)
              (Nat.pair (betaStepCode q j (child0Code c)) (Nat.pair (child1Code c) 0)))
          else if betaRankCode (child1Code c) = q then
            Nat.pair 1 (Nat.pair (opTagCode c)
              (Nat.pair (child0Code c) (Nat.pair (betaStepCode q j (child1Code c)) 0)))
          else if isLamCode (child0Code c) = true
              ∧ ordCode (Nat.pair 1 (opPayloadCode c)) = q then
            subCode j (child1Code c) (child0Code (child0Code c))
          else c)
        else if opKindCode c = 1 then
          (if betaRankCode (child0Code c) = q then
            Nat.pair 1 (Nat.pair (opTagCode c)
              (Nat.pair (betaStepCode q (j + 1) (child0Code c)) 0))
          else c)
        else c)
      else c := by
  rw [betaStepCode]
  split <;>
    simp_all [shapeCode, opKindCode, opTagCode, opPayloadCode, child0Code, child1Code]

/-- The depth read of the β-worker fold at arity `4`: the leading `Nat.unpair`
component of the index slot, the substitution level `d` of the 2-D key
`Nat.pair d m` (Decision Q8). -/
private def betaIdxDepthER : ERMor1 4 :=
  ERMor1.comp ERMor1.natUnpairFst (fun _ : Fin 1 => ERMor1.proj 0)

/-- Interpretation of `betaIdxDepthER`: the depth component of the index. -/
private theorem betaIdxDepthER_interp (i cand c q : ℕ) :
    betaIdxDepthER.interp (Fin.cons i (Fin.cons cand (Fin.cons c ![q])))
      = (Nat.unpair i).1 := by
  simp only [betaIdxDepthER, ERMor1.interp_comp, ERMor1.interp_proj, Fin.cons_zero,
    cons_fin_one, ERMor1.interp_natUnpairFst]

/-- The code read of the β-worker fold at arity `4`: the trailing `Nat.unpair`
component of the index slot, the code `m` of the 2-D key `Nat.pair d m`
(Decision Q8). -/
private def betaIdxCodeER : ERMor1 4 :=
  ERMor1.comp ERMor1.natUnpairSnd (fun _ : Fin 1 => ERMor1.proj 0)

/-- Interpretation of `betaIdxCodeER`: the code component of the index. -/
private theorem betaIdxCodeER_interp (i cand c q : ℕ) :
    betaIdxCodeER.interp (Fin.cons i (Fin.cons cand (Fin.cons c ![q])))
      = (Nat.unpair i).2 := by
  simp only [betaIdxCodeER, ERMor1.interp_comp, ERMor1.interp_proj, Fin.cons_zero,
    cons_fin_one, ERMor1.interp_natUnpairSnd]

/-- The context selector `Fin.cons i (Fin.cons cand (Fin.cons c ![q]))` reads the
dispatched rank `q` at slot `3`. -/
private theorem betaNode_ctx_q (i cand c q : ℕ) :
    (Fin.cons i (Fin.cons cand (Fin.cons c ![q])) : Fin 4 → ℕ) 3 = q := rfl

/-- The contraction arm of the β-worker fold: the substitution `subER` composed as
an ordinary full call at the body of the function child, the depth read of the
index, and the argument child — the rank-`q` root β-redex contraction of
`betaStepCode`. -/
private def betaContractER : ERMor1 4 :=
  ERMor1.comp subER (fun s => match s with
    | ⟨0, _⟩ => ERMor1.comp child0ER (fun _ : Fin 1 =>
        ERMor1.comp child0ER (fun _ : Fin 1 => betaIdxCodeER))
    | ⟨1, _⟩ => betaIdxDepthER
    | ⟨2, _⟩ => ERMor1.comp child1ER (fun _ : Fin 1 => betaIdxCodeER))

/-- Interpretation of `betaContractER`: the contraction
`subCode d (child1Code m) (child0Code (child0Code m))` at the index components
`d` and `m`. -/
private theorem betaContractER_interp (i cand c q : ℕ) :
    betaContractER.interp (Fin.cons i (Fin.cons cand (Fin.cons c ![q])))
      = subCode (Nat.unpair i).1 (child1Code (Nat.unpair i).2)
          (child0Code (child0Code (Nat.unpair i).2)) := by
  have harg : (fun s : Fin 3 => ((match s with
      | ⟨0, _⟩ => ERMor1.comp child0ER (fun _ : Fin 1 =>
          ERMor1.comp child0ER (fun _ : Fin 1 => betaIdxCodeER))
      | ⟨1, _⟩ => betaIdxDepthER
      | ⟨2, _⟩ => ERMor1.comp child1ER (fun _ : Fin 1 => betaIdxCodeER)) : ERMor1 4).interp
        (Fin.cons i (Fin.cons cand (Fin.cons c ![q]))))
      = ![child0Code (child0Code (Nat.unpair i).2), (Nat.unpair i).1,
          child1Code (Nat.unpair i).2] := by
    funext s
    match s with
    | ⟨0, _⟩ =>
      simp only [ERMor1.interp_comp, betaIdxCodeER_interp, cons_fin_one, child0ER_interp]
      rfl
    | ⟨1, _⟩ => exact betaIdxDepthER_interp i cand c q
    | ⟨2, _⟩ =>
      simp only [ERMor1.interp_comp, betaIdxCodeER_interp, cons_fin_one, child1ER_interp]
      rfl
  rw [betaContractER, ERMor1.interp_comp, harg, subER_interp]

/-- The gate of the β-worker fold at slots `(i, c, q)`: the `0/1` indicator of
`d + m ≤ c` for the index `i = Nat.pair d m`, a `leN` composition over the `addN`
of the two `Nat.unpair` reads of the index against the code slot (Decision Q8). -/
private def betaSaneER : ERMor1 3 :=
  ERMor1.comp ERMor1.leN (fun s => match s with
    | ⟨0, _⟩ => ERMor1.comp ERMor1.addN (fun t => match t with
        | ⟨0, _⟩ => ERMor1.comp ERMor1.natUnpairFst (fun _ : Fin 1 => ERMor1.proj 0)
        | ⟨1, _⟩ => ERMor1.comp ERMor1.natUnpairSnd (fun _ : Fin 1 => ERMor1.proj 0))
    | ⟨1, _⟩ => ERMor1.proj 1)

/-- Interpretation of `betaSaneER`: the `0/1` indicator of the gate `d + m ≤ c`. -/
private theorem betaSaneER_interp (i c q : ℕ) :
    betaSaneER.interp (Fin.cons i (Fin.cons c ![q]))
      = if (Nat.unpair i).1 + (Nat.unpair i).2 ≤ c then 1 else 0 := by
  have hunf : betaSaneER.interp (Fin.cons i (Fin.cons c ![q]))
      = ERMor1.leN.interp ![(Nat.unpair i).1 + (Nat.unpair i).2, c] := by
    change ERMor1.leN.interp _ = ERMor1.leN.interp _
    congr 1
    funext s
    match s with
    | ⟨0, _⟩ =>
      change ERMor1.addN.interp _ = _
      have harg : (fun t : Fin 2 => ((match t with
          | ⟨0, _⟩ => ERMor1.comp ERMor1.natUnpairFst (fun _ : Fin 1 => ERMor1.proj 0)
          | ⟨1, _⟩ => ERMor1.comp ERMor1.natUnpairSnd
              (fun _ : Fin 1 => ERMor1.proj 0)) : ERMor1 3).interp
            (Fin.cons i (Fin.cons c ![q])))
          = ![(Nat.unpair i).1, (Nat.unpair i).2] := by
        funext t
        match t with
        | ⟨0, _⟩ =>
          change ERMor1.natUnpairFst.interp (fun _ : Fin 1 => i) = _
          rw [cons_fin_one, ERMor1.interp_natUnpairFst]
          rfl
        | ⟨1, _⟩ =>
          change ERMor1.natUnpairSnd.interp (fun _ : Fin 1 => i) = _
          rw [cons_fin_one, ERMor1.interp_natUnpairSnd]
          rfl
      rw [harg, ERMor1.interp_addN]
      rfl
    | ⟨1, _⟩ => rfl
  rw [hunf, ERMor1.interp_leN]
  rfl

/-- The index bound of the β-worker fold: `Nat.pair c c` over the code slot,
dominating every gated index `Nat.pair d m` with `d + m ≤ c` (Decision Q8). -/
private def betaIdxBoundER : ERMor1 2 := pairER (ERMor1.proj 0) (ERMor1.proj 0)

/-- Interpretation of `betaIdxBoundER`: the index bound `Nat.pair c c`. -/
private theorem betaIdxBoundER_interp (c q : ℕ) :
    betaIdxBoundER.interp (Fin.cons c ![q]) = Nat.pair c c := by
  simp only [betaIdxBoundER, pairER_interp, ERMor1.interp_proj, Fin.cons_zero]

/-- The extraction position of the β-worker fold: `Nat.pair 0 c`, the input code
at substitution level `0` — the closed-term level of the `stepCodeAt 0`
consumer (Decision Q8). -/
private def betaExtractER : ERMor1 2 := pairER (ERMor1.natN 2 0) (ERMor1.proj 0)

/-- Interpretation of `betaExtractER`: the extraction position `Nat.pair 0 c`. -/
private theorem betaExtractER_interp (c q : ℕ) :
    betaExtractER.interp (Fin.cons c ![q]) = Nat.pair 0 c := by
  simp only [betaExtractER, pairER_interp, ERMor1.interp_natN, ERMor1.interp_proj,
    Fin.cons_zero]

/-- The height-2 tower value bound of the β-worker fold as an `ERMor1 2` term: the
`towerER 2` composite over the polynomial `36 * c + 18`, dominating the gated
table entries through `betaStepCode_le_tower` (`d, m ≤ c` gives
`27 * m + 9 * d ≤ 36 * c`). -/
private def betaStepBoundER : ERMor1 2 :=
  ERMor1.comp (ERMor1.towerER 2) (fun _ : Fin 1 =>
    ERMor1.comp ERMor1.addN (fun s => match s with
      | ⟨0, _⟩ => ERMor1.comp ERMor1.mulN (fun u => match u with
          | ⟨0, _⟩ => ERMor1.natN 2 36
          | ⟨1, _⟩ => ERMor1.proj 0)
      | ⟨1, _⟩ => ERMor1.natN 2 18))

/-- Interpretation of `betaStepBoundER`: the height-2 tower at `36 * c + 18`. -/
private theorem betaStepBoundER_interp (c q : ℕ) :
    betaStepBoundER.interp (Fin.cons c ![q]) = tower 2 (36 * c + 18) := by
  simp only [betaStepBoundER, ERMor1.interp_comp, ERMor1.interp_towerER,
    ERMor1.interp_addN, ERMor1.interp_mulN, ERMor1.interp_natN, ERMor1.interp_proj]
  rfl

/-- The reference table of the β-worker fold at input code `c` and rank `q`
(Decision Q8): at an index `Nat.pair d m` inside the gate `d + m ≤ c`, the β
worker `betaStepCode q d m` at substitution level `d`; `0` off the gate. -/
private def betaTable (c q i : ℕ) : ℕ :=
  if (Nat.unpair i).1 + (Nat.unpair i).2 ≤ c then
    betaStepCode q (Nat.unpair i).1 (Nat.unpair i).2
  else 0

/-- The gated entry of `betaTable`: at an index `Nat.pair d m` with `d + m ≤ c`,
the table stores `betaStepCode q d m`. -/
private theorem betaTable_pair_of_le (c q d m : ℕ) (h : d + m ≤ c) :
    betaTable c q (Nat.pair d m) = betaStepCode q d m := by
  unfold betaTable
  simp only [Nat.unpair_pair]
  rw [if_pos h]

/-- The node of the β-worker fold at slots `(i, cand, c, q)`: unpair the index `i`
into the substitution level `d` and the code `m` and dispatch on the shape tag and
operation kind bit of `m`, mirroring the four guard regimes of the `betaStepCode`
application arm. The child β-ranks are full calls of `betaRankER`; a rank-`q`
function or argument child is read substituted off the β-table at
`Nat.pair d (child0Code m)` or `Nat.pair d (child1Code m)` and the node rebuilt;
the root-contraction guard composes `isLamER` on the function child and `ordER` on
the applied arrow-sort code (full calls), and its arm is the full `subER` call
`betaContractER`; an abstraction node reads its body child at
`Nat.pair (d + 1) (child0Code m)` — the level increment of `betaStepCode_lam`
absorbed into the depth component (Decision Q8); every other node returns the code
component `m` unchanged. Novel realization. -/
private def betaStepNodeER : ERMor1 4 :=
  condEqER (ERMor1.comp shapeER (fun _ : Fin 1 => betaIdxCodeER)) (ERMor1.natN 4 1)
    (condEqER (ERMor1.comp opKindER (fun _ : Fin 1 => betaIdxCodeER)) (ERMor1.natN 4 0)
      (condEqER (ERMor1.comp betaRankER (fun _ : Fin 1 =>
            ERMor1.comp child0ER (fun _ : Fin 1 => betaIdxCodeER))) (ERMor1.proj 3)
        (pairER (ERMor1.natN 4 1)
          (pairER (ERMor1.comp opTagER (fun _ : Fin 1 => betaIdxCodeER))
            (pairER (ERMor1.betaOnCandFold (pairER betaIdxDepthER
                (ERMor1.comp child0ER (fun _ : Fin 1 => betaIdxCodeER))))
              (pairER (ERMor1.comp child1ER (fun _ : Fin 1 => betaIdxCodeER))
                (ERMor1.natN 4 0)))))
        (condEqER (ERMor1.comp betaRankER (fun _ : Fin 1 =>
              ERMor1.comp child1ER (fun _ : Fin 1 => betaIdxCodeER))) (ERMor1.proj 3)
          (pairER (ERMor1.natN 4 1)
            (pairER (ERMor1.comp opTagER (fun _ : Fin 1 => betaIdxCodeER))
              (pairER (ERMor1.comp child0ER (fun _ : Fin 1 => betaIdxCodeER))
                (pairER (ERMor1.betaOnCandFold (pairER betaIdxDepthER
                    (ERMor1.comp child1ER (fun _ : Fin 1 => betaIdxCodeER))))
                  (ERMor1.natN 4 0)))))
          (condEqER (ERMor1.comp isLamER (fun _ : Fin 1 =>
                ERMor1.comp child0ER (fun _ : Fin 1 => betaIdxCodeER))) (ERMor1.natN 4 1)
            (condEqER (ERMor1.comp ordER (fun _ : Fin 1 =>
                  ERMor1.comp appliedArrowER (fun _ : Fin 1 => betaIdxCodeER)))
                (ERMor1.proj 3)
              betaContractER
              betaIdxCodeER)
            betaIdxCodeER)))
      (condEqER (ERMor1.comp opKindER (fun _ : Fin 1 => betaIdxCodeER)) (ERMor1.natN 4 1)
        (condEqER (ERMor1.comp betaRankER (fun _ : Fin 1 =>
              ERMor1.comp child0ER (fun _ : Fin 1 => betaIdxCodeER))) (ERMor1.proj 3)
          (pairER (ERMor1.natN 4 1)
            (pairER (ERMor1.comp opTagER (fun _ : Fin 1 => betaIdxCodeER))
              (pairER (ERMor1.betaOnCandFold (pairER
                  (ERMor1.comp ERMor1.succ (fun _ : Fin 1 => betaIdxDepthER))
                  (ERMor1.comp child0ER (fun _ : Fin 1 => betaIdxCodeER))))
                (ERMor1.natN 4 0))))
          betaIdxCodeER)
        betaIdxCodeER))
    betaIdxCodeER

/-- The node value of `betaStepNodeER` at index `Nat.pair d m` as a nested
conditional on the shape tag and operation kind bit of the code component `m`, with
the child β-ranks by full `betaRankCode` calls, the substituted children read off
the candidate β-table at the depth-keyed positions, the contraction guard by full
`isLamCode` and `ordCode` calls, and the contraction by a full `subCode` call. -/
private theorem betaStepNodeER_interp (d m cand c q : ℕ) :
    betaStepNodeER.interp (Fin.cons (Nat.pair d m) (Fin.cons cand (Fin.cons c ![q]))) =
      if shapeCode m = 1 then
        (if opKindCode m = 0 then
          (if betaRankCode (child0Code m) = q then
            Nat.pair 1 (Nat.pair (opTagCode m)
              (Nat.pair (cand.unpair.1 % (1 + (Nat.pair d (child0Code m) + 1) * cand.unpair.2))
                (Nat.pair (child1Code m) 0)))
          else if betaRankCode (child1Code m) = q then
            Nat.pair 1 (Nat.pair (opTagCode m)
              (Nat.pair (child0Code m)
                (Nat.pair (cand.unpair.1 % (1 + (Nat.pair d (child1Code m) + 1) * cand.unpair.2))
                  0)))
          else if isLamCode (child0Code m) = true then
            (if ordCode (Nat.pair 1 (opPayloadCode m)) = q then
              subCode d (child1Code m) (child0Code (child0Code m))
            else m)
          else m)
        else if opKindCode m = 1 then
          (if betaRankCode (child0Code m) = q then
            Nat.pair 1 (Nat.pair (opTagCode m)
              (Nat.pair (cand.unpair.1 %
                (1 + (Nat.pair (d + 1) (child0Code m) + 1) * cand.unpair.2)) 0))
          else m)
        else m)
      else m := by
  simp only [betaStepNodeER, condEqER_interp, pairER_interp, betaContractER_interp,
    betaIdxDepthER_interp, betaIdxCodeER_interp, ERMor1.interp_comp,
    ERMor1.interp_betaOnCandFold, ERMor1.interp_natN, ERMor1.interp_succ,
    ERMor1.interp_proj, cons_fin_one, shapeER_interp, opKindER_interp, opTagER_interp,
    child0ER_interp, child1ER_interp, betaRankER_interp, isLamER_interp, ordER_interp,
    appliedArrowER_interp, betaNode_ctx_q, Nat.unpair_pair, Bool.toNat_eq_one,
    Matrix.cons_val_zero]

/-- The node value of the β-worker fold equals the reference recursion: at index
`Nat.pair d m`, a candidate whose β-reads agree with the β worker at exactly the
positions the node reads — the two application children at depth `d` and the
abstraction body at depth `d + 1` — makes the node compute `betaStepCode q d m`.
The contraction arm needs no read: `subER` is complete, so the full call computes
the contraction outright. Shared arm-by-arm case analysis of the node-faithfulness
and determinacy inputs of `betaStepER_interp`. -/
private theorem betaStepNode_val_eq_betaStepCode (c q d m cand : ℕ)
    (h0 : shapeCode m = 1 → opKindCode m = 0 →
      cand.unpair.1 % (1 + (Nat.pair d (child0Code m) + 1) * cand.unpair.2)
          = betaStepCode q d (child0Code m)
        ∧ cand.unpair.1 % (1 + (Nat.pair d (child1Code m) + 1) * cand.unpair.2)
          = betaStepCode q d (child1Code m))
    (h1 : shapeCode m = 1 → opKindCode m = 1 →
      cand.unpair.1 % (1 + (Nat.pair (d + 1) (child0Code m) + 1) * cand.unpair.2)
        = betaStepCode q (d + 1) (child0Code m)) :
    betaStepNodeER.interp (Fin.cons (Nat.pair d m) (Fin.cons cand (Fin.cons c ![q])))
      = betaStepCode q d m := by
  rw [betaStepNodeER_interp, betaStepCode_eq_ite q d m]
  by_cases hs : shapeCode m = 1
  · rw [if_pos hs, if_pos hs]
    by_cases hk0 : opKindCode m = 0
    · rw [if_pos hk0, if_pos hk0]
      by_cases hr0 : betaRankCode (child0Code m) = q
      · rw [if_pos hr0, if_pos hr0, (h0 hs hk0).1]
      · rw [if_neg hr0, if_neg hr0]
        by_cases hr1 : betaRankCode (child1Code m) = q
        · rw [if_pos hr1, if_pos hr1, (h0 hs hk0).2]
        · rw [if_neg hr1, if_neg hr1]
          by_cases hL : isLamCode (child0Code m) = true
          · rw [if_pos hL]
            by_cases hOrd : ordCode (Nat.pair 1 (opPayloadCode m)) = q
            · rw [if_pos hOrd, if_pos ⟨hL, hOrd⟩]
            · rw [if_neg hOrd, if_neg (fun h => hOrd h.2)]
          · rw [if_neg hL, if_neg (fun h => hL h.1)]
    · rw [if_neg hk0, if_neg hk0]
      by_cases hk1 : opKindCode m = 1
      · rw [if_pos hk1, if_pos hk1]
        by_cases hr0 : betaRankCode (child0Code m) = q
        · rw [if_pos hr0, if_pos hr0, h1 hs hk1]
        · rw [if_neg hr0, if_neg hr0]
      · rw [if_neg hk1, if_neg hk1]
  · rw [if_neg hs, if_neg hs]

/-- The β worker as a gated elementary-recursive course-of-values fold:
`ERMor1.cvRecGated` at `k = 1` with slots `(c, q)` — the code and the dispatched
rank — and the two-dimensional index `i = Nat.pair d m` keying the substitution
level and the code (Decision Q8). The gate `betaSaneER` confines the imposed
equations to `d + m ≤ c`, the index bound is `Nat.pair c c`, the extraction reads
`Nat.pair 0 c` (the input code at the closed-term level `0`), and the value bound
is the height-2 tower composite `betaStepBoundER` over `36 * c + 18`. The node
mirrors the `betaStepCode` arms, composing `betaRankER`, `isLamER`, `ordER`, and
`subER` as ordinary full calls; only the same-function descent goes through the
β-table. Realizes the parameter-varying strong recursion of `betaStepCode`
(Leivant III section 4.2, p. 224; the machine-model absorption of footnote 10,
p. 226) as a single bounded β-witness search. Novel realization. -/
def betaStepER : ERMor1 2 :=
  ERMor1.cvRecGated betaStepNodeER betaSaneER betaIdxBoundER betaExtractER betaStepBoundER

/-- Interpretation of `betaStepER`: the β worker `betaStepCode q 0 c` at the
closed-term level, unconditionally on every code and rank. Discharges the
hypotheses of `ERMor1.interp_cvRecGated_eq` against the reference table
`betaTable` (Decision Q8): the gate is `0/1`-valued, the gated entries are bounded
by the tower-2 majorant `betaStepCode_le_tower` (off-gate entries are `0`), node
faithfulness holds at gated indices through `betaStepNode_val_eq_betaStepCode`
with every read position gated and below the index bound (`pair_le_pair`), and
determinacy (Decision Q6) is discharged by strong induction on the code component
of the index with the depth universally quantified — children sit strictly below
the code component, and the abstraction descent pays its depth increment with
`child0Code m < m`. The extraction at `Nat.pair 0 c` is gated and stores
`betaStepCode q 0 c` directly. -/
@[simp] theorem betaStepER_interp (c q : ℕ) :
    betaStepER.interp ![c, q] = betaStepCode q 0 c := by
  have h_sane : ∀ i, i ≤ betaIdxBoundER.interp (Fin.cons c ![q]) →
      betaSaneER.interp (Fin.cons i (Fin.cons c ![q])) ≤ 1 := by
    intro i _
    rw [betaSaneER_interp]
    split
    · exact le_refl 1
    · exact Nat.zero_le 1
  have hval : ∀ i, i ≤ betaIdxBoundER.interp (Fin.cons c ![q]) →
      betaTable c q i ≤ betaStepBoundER.interp (Fin.cons c ![q]) := by
    intro i _
    rw [betaStepBoundER_interp]
    unfold betaTable
    split
    · rename_i hgate
      exact le_trans (betaStepCode_le_tower q (Nat.unpair i).1 (Nat.unpair i).2)
        (tower_mono_right 2 (by omega))
    · exact Nat.zero_le _
  have h_node : ∀ i, i ≤ betaIdxBoundER.interp (Fin.cons c ![q]) →
      betaSaneER.interp (Fin.cons i (Fin.cons c ![q])) = 1 → ∀ cand,
      (∀ p, p ≤ betaIdxBoundER.interp (Fin.cons c ![q]) →
        cand.unpair.1 % (1 + (p + 1) * cand.unpair.2) = betaTable c q p) →
      betaStepNodeER.interp (Fin.cons i (Fin.cons cand (Fin.cons c ![q])))
        = betaTable c q i := by
    intro i _ hSi cand hreads
    obtain ⟨d, m, rfl⟩ : ∃ d m, i = Nat.pair d m :=
      ⟨(Nat.unpair i).1, (Nat.unpair i).2, (Nat.pair_unpair i).symm⟩
    have hdm : d + m ≤ c := by
      rw [betaSaneER_interp] at hSi
      simp only [Nat.unpair_pair] at hSi
      by_contra hn
      rw [if_neg hn] at hSi
      omega
    rw [betaTable_pair_of_le c q d m hdm]
    refine betaStepNode_val_eq_betaStepCode c q d m cand (fun hs hk0 => ?_)
      (fun hs hk1 => ?_)
    · have hc0 := child0Code_lt_of_shape_one m hs
      have hc1 := child1Code_lt_of_shape_one m hs
      constructor
      · rw [hreads (Nat.pair d (child0Code m))
            (by rw [betaIdxBoundER_interp]; exact pair_le_pair (by omega) (by omega)),
          betaTable_pair_of_le c q d (child0Code m) (by omega)]
      · rw [hreads (Nat.pair d (child1Code m))
            (by rw [betaIdxBoundER_interp]; exact pair_le_pair (by omega) (by omega)),
          betaTable_pair_of_le c q d (child1Code m) (by omega)]
    · have hc0 := child0Code_lt_of_shape_one m hs
      rw [hreads (Nat.pair (d + 1) (child0Code m))
          (by rw [betaIdxBoundER_interp]; exact pair_le_pair (by omega) (by omega)),
        betaTable_pair_of_le c q (d + 1) (child0Code m) (by omega)]
  have h_det : ∀ cand,
      (∀ i, i ≤ betaIdxBoundER.interp (Fin.cons c ![q]) →
        betaSaneER.interp (Fin.cons i (Fin.cons c ![q])) = 1 →
        cand.unpair.1 % (1 + (i + 1) * cand.unpair.2) =
          betaStepNodeER.interp (Fin.cons i (Fin.cons cand (Fin.cons c ![q])))) →
      cand.unpair.1 %
          (1 + (betaExtractER.interp (Fin.cons c ![q]) + 1) * cand.unpair.2) =
        betaTable c q (betaExtractER.interp (Fin.cons c ![q])) := by
    intro cand hcand
    rw [betaExtractER_interp, betaTable_pair_of_le c q 0 c (by omega)]
    suffices hmain : ∀ m d, d + m ≤ c →
        cand.unpair.1 % (1 + (Nat.pair d m + 1) * cand.unpair.2)
          = betaStepCode q d m from hmain c 0 (by omega)
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro d hdm
      have hle : Nat.pair d m ≤ betaIdxBoundER.interp (Fin.cons c ![q]) := by
        rw [betaIdxBoundER_interp]
        exact pair_le_pair (by omega) (by omega)
      have hS : betaSaneER.interp (Fin.cons (Nat.pair d m) (Fin.cons c ![q])) = 1 := by
        rw [betaSaneER_interp]
        simp only [Nat.unpair_pair]
        rw [if_pos hdm]
      rw [hcand (Nat.pair d m) hle hS]
      refine betaStepNode_val_eq_betaStepCode c q d m cand (fun hs hk0 => ?_)
        (fun hs hk1 => ?_)
      · have hc0 := child0Code_lt_of_shape_one m hs
        have hc1 := child1Code_lt_of_shape_one m hs
        exact ⟨ih _ hc0 d (by omega), ih _ hc1 d (by omega)⟩
      · have hc0 := child0Code_lt_of_shape_one m hs
        exact ih _ hc0 (d + 1) (by omega)
  have h_ext : betaExtractER.interp (Fin.cons c ![q]) ≤
      betaIdxBoundER.interp (Fin.cons c ![q]) := by
    rw [betaExtractER_interp, betaIdxBoundER_interp]
    exact pair_le_pair (Nat.zero_le c) (le_refl c)
  have key := ERMor1.interp_cvRecGated_eq betaStepNodeER betaSaneER betaIdxBoundER
    betaExtractER betaStepBoundER c ![q] (betaTable c q) h_sane hval h_node h_det h_ext
  rw [betaExtractER_interp, betaTable_pair_of_le c q 0 c (by omega)] at key
  exact key

/-! ### The step dispatch and majorant -/

/-- The step majorant as an `ERMor1 1` term: the `towerER 2` composite over the
quadratic polynomial `6 * (2 * (n + 1) ^ 2 + n + 1)`, the elementary-recursive
realization of the reference majorant `stepBound` (spec §6.1). The square is a `powN`
read at exponent `2`. Novel realization. -/
def stepBoundER : ERMor1 1 :=
  ERMor1.comp (ERMor1.towerER 2) (fun _ : Fin 1 =>
    ERMor1.comp ERMor1.mulN (fun s => match s with
      | ⟨0, _⟩ => ERMor1.natN 1 6
      | ⟨1, _⟩ => ERMor1.comp ERMor1.addN (fun t => match t with
          | ⟨0, _⟩ => ERMor1.comp ERMor1.addN (fun u => match u with
              | ⟨0, _⟩ => ERMor1.comp ERMor1.mulN (fun v => match v with
                  | ⟨0, _⟩ => ERMor1.natN 1 2
                  | ⟨1, _⟩ => ERMor1.comp ERMor1.powN (fun w => match w with
                      | ⟨0, _⟩ => ERMor1.comp ERMor1.addN (fun x => match x with
                          | ⟨0, _⟩ => ERMor1.proj 0
                          | ⟨1, _⟩ => ERMor1.natN 1 1)
                      | ⟨1, _⟩ => ERMor1.natN 1 2))
              | ⟨1, _⟩ => ERMor1.proj 0)
          | ⟨1, _⟩ => ERMor1.natN 1 1)))

/-- Interpretation of `stepBoundER`: the step majorant `stepBound n`. -/
@[simp] theorem stepBoundER_interp (n : ℕ) : stepBoundER.interp ![n] = stepBound n := by
  simp only [stepBoundER, ERMor1.interp_comp, ERMor1.interp_towerER, ERMor1.interp_mulN,
    ERMor1.interp_addN, ERMor1.interp_powN, ERMor1.interp_natN, ERMor1.interp_proj,
    Matrix.cons_val_zero, stepBound]

/-- The β-dispatch arm of the closed-term step: the β worker `betaStepER` composed as
an ordinary full call at the input code and its own β-rank `betaRankER`, mirroring the
`betaStepCode (betaRankCode c) 0 c` arm of `stepCodeAt 0`. -/
private def betaDispatchER : ERMor1 1 :=
  ERMor1.comp betaStepER (fun s => match s with
    | ⟨0, _⟩ => ERMor1.proj 0
    | ⟨1, _⟩ => betaRankER)

/-- Interpretation of `betaDispatchER`: the β worker at the code's own β-rank,
`betaStepCode (betaRankCode c) 0 c`. -/
private theorem betaDispatchER_interp (c : ℕ) :
    betaDispatchER.interp ![c] = betaStepCode (betaRankCode c) 0 c := by
  have harg : (fun s : Fin 2 => ((match s with
      | ⟨0, _⟩ => ERMor1.proj 0
      | ⟨1, _⟩ => betaRankER) : ERMor1 1).interp ![c]) = ![c, betaRankCode c] := by
    funext s
    match s with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => exact betaRankER_interp c
  rw [betaDispatchER, ERMor1.interp_comp, harg, betaStepER_interp]

/-- The closed-term deterministic step as the literal `condN` dispatch of
`stepCodeAt 0` (spec §6.1; M6): the sign of the β-rank read `signN (betaRankER c)`
selects the β-dispatch arm `betaDispatchER`; else the ι-census read `hasIotaER c`
selects the ι worker `iotaStepER`; else the identity `proj 0`. Novel realization. -/
def stepCodeAtZeroER : ERMor1 1 :=
  ERMor1.comp ERMor1.condN (fun s => match s with
    | ⟨0, _⟩ => ERMor1.comp ERMor1.signN (fun _ : Fin 1 => betaRankER)
    | ⟨1, _⟩ => betaDispatchER
    | ⟨2, _⟩ => ERMor1.comp ERMor1.condN (fun t => match t with
        | ⟨0, _⟩ => hasIotaER
        | ⟨1, _⟩ => iotaStepER
        | ⟨2, _⟩ => ERMor1.proj 0))

/-- Interpretation of `stepCodeAtZeroER`: the closed-term deterministic step
`stepCodeAt 0 c`, unconditionally on every code. Splits on the same guards as
`stepCodeAt`'s definition — the positivity of `betaRankCode c` and the ι-census — the
sign read `1 - (1 - betaRankCode c)` matching the positivity guard and the
`Bool.toNat` census read matching the ι guard, each arm closed by the landed worker
interpretation lemmas. -/
theorem stepCodeAtZeroER_interp (c : ℕ) :
    stepCodeAtZeroER.interp ![c] = stepCodeAt 0 c := by
  simp only [stepCodeAtZeroER, ERMor1.interp_comp, ERMor1.interp_condN,
    ERMor1.interp_signN, betaRankER_interp, betaDispatchER_interp, hasIotaER_interp,
    iotaStepER_interp, ERMor1.interp_proj, Matrix.cons_val_zero]
  rw [stepCodeAt]
  by_cases h1 : 0 < betaRankCode c
  · rw [if_pos h1]
    have hg0 : 1 - (1 - betaRankCode c) = 1 := by omega
    rw [hg0]
    simp only [one_mul, Nat.sub_self, zero_mul, add_zero]
  · rw [if_neg h1]
    have hg0 : 1 - (1 - betaRankCode c) = 0 := by omega
    rw [hg0]
    simp only [zero_mul, Nat.sub_zero, one_mul, zero_add]
    by_cases h2 : hasIotaCode c = true
    · rw [if_pos h2]
      have hg2 : (hasIotaCode c).toNat = 1 := by rw [h2]; rfl
      rw [hg2]
      simp only [one_mul, Nat.sub_self, zero_mul, add_zero]
    · rw [if_neg h2]
      have hg2 : (hasIotaCode c).toNat = 0 := by
        rw [Bool.not_eq_true] at h2
        rw [h2]; rfl
      rw [hg2]
      simp only [zero_mul, Nat.sub_zero, one_mul, zero_add]

/-! ### The assembled step -/

/-- The deterministic normalizer step as an elementary-recursive morphism (spec
§6.1; M6): the closed-term dispatch `stepCodeAtZeroER` clamped below the step
majorant `stepBoundER` by `ERMor1.minN`, the literal realization of `stepCode`.
The clamp bounds no fold table — every worker interpretation is unconditional — and
is reproduced solely because `stepCode`'s definition carries it (Decision Q4).
Carrying the deterministic step into the elementary-recursive theory is the formal
payment of the machine-model absorption Leivant III leaves to a footnote (section
4.2, p. 224; footnote 10, p. 226). Novel realization. -/
def normStep : ERMor1 1 :=
  ERMor1.comp ERMor1.minN (fun i => match i with
    | ⟨0, _⟩ => stepCodeAtZeroER
    | ⟨1, _⟩ => stepBoundER)

/-- Interpretation of `normStep`: the reference deterministic step `stepCode n`,
unconditionally on every code. Composes `ERMor1.interp_minN` with the closed-term
dispatch lemma `stepCodeAtZeroER_interp` and the step majorant lemma
`stepBoundER_interp` through the two `minN` slots, matching the `min` of
`stepCodeAt 0` and `stepBound` in `stepCode`'s definition. -/
theorem normStep_interp (n : ℕ) : normStep.interp ![n] = stepCode n := by
  have harg : (fun i : Fin 2 => ((match i with
      | ⟨0, _⟩ => stepCodeAtZeroER
      | ⟨1, _⟩ => stepBoundER) : ERMor1 1).interp ![n])
      = ![stepCodeAt 0 n, stepBound n] := by
    funext i
    match i with
    | ⟨0, _⟩ => exact stepCodeAtZeroER_interp n
    | ⟨1, _⟩ => exact stepBoundER_interp n
  rw [normStep, ERMor1.interp_comp, harg, ERMor1.interp_minN]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, stepCode]

/-! ### The clocked iteration -/

/-- The budget read of the clocked iteration evaluates to the budget slot: at slots
`(j, n, b)` the value bound is `b`, constant in the recursion counter. -/
private theorem normRun_bound_eval (j n b : ℕ) :
    (ERMor1.proj (k := 3) 2).interp (Fin.cons j (Fin.cons n (Fin.cons b Fin.elim0))) = b := by
  rw [ERMor1.interp_proj]
  rfl

/-- The step term of the clocked iteration evaluates to a single deterministic step of the
running value: at slots `(i, prev, n, b)` it computes `stepCode prev` by a full call of
`normStep`. -/
private theorem normRun_step_eval (n b i prev : ℕ) :
    (ERMor1.comp normStep (fun _ : Fin 1 => ERMor1.proj (k := 4) 1)).interp
      (Fin.cons i (Fin.cons prev (Fin.cons n (Fin.cons b Fin.elim0)))) = stepCode prev := by
  have hg : (fun _ : Fin 1 => (ERMor1.proj (k := 4) 1).interp
      (Fin.cons i (Fin.cons prev (Fin.cons n (Fin.cons b Fin.elim0))))) = ![prev] := by
    funext s
    match s with
    | ⟨0, _⟩ => rfl
  rw [ERMor1.interp_comp, hg, normStep_interp]

/-- The raw `Nat.rec` trace of the clocked-iteration step at counter `k` equals the
`Function.iterate` of `stepCode` on the code `n`. -/
private theorem normRun_rec_eq (n b k : ℕ) :
    (Nat.rec ((ERMor1.proj (k := 2) 0).interp (Fin.cons n (Fin.cons b Fin.elim0)))
      (fun i prev => (ERMor1.comp normStep (fun _ : Fin 1 => ERMor1.proj (k := 4) 1)).interp
        (Fin.cons i (Fin.cons prev (Fin.cons n (Fin.cons b Fin.elim0))))) k : ℕ)
      = stepCode^[k] n := by
  induction k with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ← ih]
    exact normRun_step_eval n b m _

/-- The clocked iteration of the deterministic normalizer step as an elementary-recursive
morphism (spec §6.2; plan decision P6): `ERMor1.boundedRec` over `normStep` at slots
`(k, n, b)` — clock, code, budget — with base the code, step a full call of `normStep` on
the running value, and value bound the budget slot. The budget is a genuine input:
`stepCode` raises the magnitude of an arbitrary code by a fixed-height tower, so no
elementary function of the clock and the code alone dominates every trace — uniform
elementary iteration is impossible at unbounded redex rank, matching the per-fixed-`F`
framing of Leivant III Proposition 13 (section 5, p. 226), where the normalization clock
and its elementary majorant are constants of the fixed term. The budget slot carries the
per-instance ceiling (`codeCeil` at a closed term's code), under which the iteration is
exact (Lemma 12, section 5, p. 226; the machine-model absorption of footnote 10, p. 226).
Novel realization. -/
def normRun : ERMor1 3 :=
  ERMor1.boundedRec
    (ERMor1.proj (k := 2) 0)
    (ERMor1.comp normStep (fun _ : Fin 1 => ERMor1.proj (k := 4) 1))
    (ERMor1.proj (k := 3) 2)

/-- Interpretation of `normRun` under a trace budget: when the budget `b` dominates every
value of the iterate up to the clock `k`, the clocked iteration computes the `k`-fold
iterate of the reference step, `stepCode^[k] n`. Discharges the hypotheses of
`ERMor1.boundedRec_eq_natRec_of_bounded`: the trace equals the iterate
(`normRun_rec_eq`), the dominance is the budget hypothesis, and the monotonicity is the
budget's constancy in the counter. -/
theorem normRun_interp_of_le (k n b : ℕ)
    (hb : ∀ j, j ≤ k → stepCode^[j] n ≤ b) :
    normRun.interp ![k, n, b] = stepCode^[k] n := by
  change normRun.interp (Fin.cons k (Fin.cons n (Fin.cons b Fin.elim0))) = stepCode^[k] n
  unfold normRun
  refine (ERMor1.boundedRec_eq_natRec_of_bounded _ _ _ _ _ ?_ ?_).trans ?_
  · intro j hj
    rw [normRun_rec_eq, normRun_bound_eval]
    exact hb j hj
  · intro j _hj
    rw [normRun_bound_eval, normRun_bound_eval]
  · rw [normRun_rec_eq]

end OneLambda

end GebLean.Ramified
