import GebLean.Ramified.Soundness.CodeNormalizer
import GebLean.Utilities.ERCourseOfValues
import GebLean.LawvereERBoundComputable
import GebLean.LawvereERKSim.ErToKFunctor

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
- `OneLambda.decodeWordER` — the word decoder, `ERMor1.cvRec` at the node
  `decodeWordNode` with the code itself as value bound; the node reads the successor
  of the argument-child β-read at an application node and `0` elsewhere.
- `OneLambda.codeBbRepER` — the argument code of the Berarducci-Böhm numeral
  representation: the fixed abstraction wrapper `codeLamWrapER` (a meta-level fold
  over the constructor step types) around the spine fold `codeBbInnerER`, an
  `ERMor1.boundedRec` under the Task 6.4.8 envelope tower.
- `OneLambda.buildCode` — the code of the applied bar-image term of Proposition 13
  (plan decision P4): the `pairER` rebuild of the `app` node over the closed
  constants of the fixed function term and the argument code `codeBbRepER`.
- `OneLambda.rankCeil`, `OneLambda.heightCeil`, `OneLambda.sizeCeil`,
  `OneLambda.payloadCeil` — the per-`F` constants: the uniform rank, height, size,
  and sort-payload ceilings of the applied bar-image term.
- `OneLambda.clockER` — the in-system clock: the Lemma 12 clock at the per-`F`
  ceilings, a `(rankCeil F + 1)`-height `ERMor1.towerER` composite over the input
  numeral times the constant coefficient.
- `OneLambda.budgetER` — the in-system budget: the chain-ceiling shape `codeCeil`
  at the per-`F` ceilings, a `towerER 2` composite whose exponent is the in-system
  clock, feeding the budget slot of `normRun`.
- `OneLambda.collapseER` — the atomic collapse morphism (spec §6.4; plan decision
  P4): decode ∘ clocked normalization ∘ build, the `ERMorN 1 1` composite feeding
  `normRun` at the in-system clock, the applied-term code, and the in-system
  budget, read off by the word decoder.
- `OneLambda.sourceApps` — the `a`-fold source-level application spine: the
  `sourceApp` iterate applying a closed function term at the curried arrow sort
  over the shifted input sorts to one closed argument per input position.
- `OneLambda.collapseERN` — the `a`-ary collapse morphism (spec §6.4): the
  `ERMorN a 1` composite of the same decode ∘ clocked normalization ∘ build shape,
  with the applied-spine code, the per-`F` ceilings over the staggered input sum
  in the in-system clock and budget.

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
- `OneLambda.normRun_codeTm` — at closed terms the iteration at budget `codeCeil t`
  computes the code of the deterministic iterate, `codeTm (detIter k t)`.
- `OneLambda.normRun_normal` — the normalizer clock: at the Lemma 12 clock value the
  deterministic iterate of a closed term is normal and the ER iteration lands its code.
- `OneLambda.decodeWordER_interp` — the word decoder interprets to `decodeWord`,
  unconditionally on every code, its value bound `decodeWord_le_self`.
- `OneLambda.codeBbRepER_interp` — the argument-code composite interprets to
  `codeBbRep`, unconditionally on every numeral, its spine trace bounded by the
  envelope tower `codeBbInner_le_tower`.
- `OneLambda.buildCode_interp` — the code builder interprets to the code of the
  applied bar-image term, `codeTm (app' (barTm F) (bbRep (natToFreeAlg n)
  (barTy τ)))`, unconditionally on every numeral.
- `OneLambda.redexRank_applied_le`, `OneLambda.height_applied_le`,
  `OneLambda.size_applied_le`, `OneLambda.sortPayload_applied_le` — the per-`F`
  ceilings dominate the applied term's measures, the rank and payload uniformly
  and the height and size up to the input numeral.
- `OneLambda.clockER_dominates` — the in-system clock dominates the deterministic
  Lemma 12 clock of the applied bar-image term at every input numeral.
- `OneLambda.budgetER_dominates` — the in-system budget dominates the chain
  ceiling `codeCeil` of the applied bar-image term at every input numeral, so
  `normRun`'s budget slot can be fed in-system.
- `OneLambda.collapseER_interp` — adequacy of the collapse morphism against the
  denotational anchor: at every input the collapse computes the numeric reading
  of the standard denotation of Proposition 13's applied term.
- `OneLambda.collapseERN_interp` — adequacy of the `a`-ary collapse morphism: at
  every input tuple the collapse computes the numeric reading of the standard
  denotation of the source-side application spine of the fixed term over the
  constructor words of the inputs.

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

open GebLean.Binding

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

/-- The clocked-iteration commutation at closed terms (spec §6.2): at budget `codeCeil t`
the ER iteration on the code of a closed term computes the code of the deterministic
iterate, `codeTm (detIter k t)`. The budget hypothesis of `normRun_interp_of_le` is
discharged by the iterated closed-term commutation `stepCode_iterate_codeTm` and the
chain ceiling `codeTm_detIter_le_codeCeil`. -/
theorem normRun_codeTm (k : ℕ) {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) [] s) :
    normRun.interp ![k, codeTm t, codeCeil t] = codeTm (detIter k t) := by
  have hb : ∀ j, j ≤ k → stepCode^[j] (codeTm t) ≤ codeCeil t := by
    intro j _hj
    rw [stepCode_iterate_codeTm j t]
    exact codeTm_detIter_le_codeCeil j t
  rw [normRun_interp_of_le k (codeTm t) (codeCeil t) hb, stepCode_iterate_codeTm k t]

/-- The normalizer clock in ER (spec §3; plan decision P6): at the Lemma 12 clock value
`(redexRank t + 1) * tower (redexRank t + 1) (Tm.height t)` (Leivant III section 5,
p. 226) the deterministic iterate of a closed term is normal, and the ER iteration at
budget `codeCeil t` lands its code. Conjoins the deterministic clock `detIter_normal`
with the closed-term commutation `normRun_codeTm` at the clock value. -/
theorem normRun_normal {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) [] s) :
    Normal (detIter ((redexRank t + 1) * tower (redexRank t + 1) (Tm.height t)) t) ∧
      normRun.interp ![(redexRank t + 1) * tower (redexRank t + 1) (Tm.height t), codeTm t,
          codeCeil t]
        = codeTm (detIter ((redexRank t + 1) * tower (redexRank t + 1) (Tm.height t)) t) :=
  ⟨detIter_normal t, normRun_codeTm _ t⟩

/-! ### The word decode and argument-code folds -/

/-- The dispatch of `decodeWord` as a nested conditional on the shape tag and the
operation kind bit: at an application node (shape `1`, kind `0`) one more than the
decoding of the argument child `child1Code`; every other reading is `0`. -/
private theorem decodeWord_eq_ite (c : ℕ) :
    decodeWord c
      = if shapeCode c = 1 then
          (if opKindCode c = 0 then decodeWord (child1Code c) + 1 else 0)
        else 0 := by
  rw [decodeWord]
  split <;> rename_i h <;>
    simp_all [shapeCode, opKindCode, child1Code]

/-- The argument child of an operation node sits strictly below the node: the
pairing bounds `Nat.unpair_left_le`/`Nat.unpair_right_le` through the pack and the
strict step `self_lt_pair_one` past the kind bit `1`. Local re-derivation of the
recursion guard of `decodeWord` at the code reads. -/
private theorem child1Code_lt_of_shape (c : ℕ) (h : shapeCode c = 1) :
    child1Code c < c := by
  have hsnd : (Nat.unpair c).2 < c := by
    conv_rhs => rw [← Nat.pair_unpair c, show (Nat.unpair c).1 = 1 from h]
    exact self_lt_pair_one _
  exact Nat.lt_of_le_of_lt
    (le_trans (Nat.unpair_left_le _)
      (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _))) hsnd

/-- The node of the `decodeWord` course-of-values fold at slots `(i, cand, code)`:
at an application node (shape tag `1`, operation kind bit `0`) the successor of the
β-read at the argument child `child1Code i`; every other reading is `0`. Novel
realization. -/
private def decodeWordNode : ERMor1 3 :=
  condEqER (ERMor1.comp shapeER (fun _ : Fin 1 => ERMor1.proj 0)) (ERMor1.natN 3 1)
    (condEqER (ERMor1.comp opKindER (fun _ : Fin 1 => ERMor1.proj 0)) (ERMor1.natN 3 0)
      (ERMor1.comp ERMor1.succ (fun _ : Fin 1 =>
        ERMor1.betaOnCandFold (ERMor1.comp child1ER (fun _ : Fin 1 => ERMor1.proj 0))))
      (ERMor1.natN 3 0))
    (ERMor1.natN 3 0)

/-- The node value of `decodeWordNode` at `(i, cand, code)` as a nested conditional
on the shape tag and the operation kind bit of `i`, with the argument-child decoding
read off the candidate β-table. -/
private theorem decodeWordNode_interp (i cand code : ℕ) :
    decodeWordNode.interp (Fin.cons i (Fin.cons cand (Fin.cons code (![] : Fin 0 → ℕ)))) =
      if shapeCode i = 1 then
        (if opKindCode i = 0 then
          cand.unpair.1 % (1 + (child1Code i + 1) * cand.unpair.2) + 1
        else 0)
      else 0 := by
  simp only [decodeWordNode, condEqER_interp, ERMor1.interp_comp,
    ERMor1.interp_betaOnCandFold, ERMor1.interp_succ, ERMor1.interp_natN,
    ERMor1.interp_proj, Fin.cons_zero, cons_fin_one, shapeER_interp, opKindER_interp,
    child1ER_interp, Matrix.cons_val_zero, Nat.succ_eq_add_one]

/-- The word decoder as an elementary-recursive course-of-values fold:
`ERMor1.cvRec` at fold slot the code and node `decodeWordNode`, with value bound
the code itself (`decodeWord_le_self`). Realizes the well-founded recursion of
`decodeWord` (Leivant III section 4.2) as a single bounded β-witness search.
Novel realization. -/
def decodeWordER : ERMor1 1 := ERMor1.cvRec decodeWordNode (ERMor1.proj 0)

/-- Interpretation of `decodeWordER`: the word decoding `decodeWord`,
unconditionally on every code. Discharges the hypotheses of
`ERMor1.interp_cvRec_of_bounded` with `f := decodeWord`: the value bound
`decodeWord_le_self`, its monotonicity immediate from the fold slot, and node
faithfulness from the dispatch unfolding `decodeWord_eq_ite` with the argument
child strictly below the index (`child1Code_lt_of_shape`). -/
@[simp] theorem decodeWordER_interp (n : ℕ) : decodeWordER.interp ![n] = decodeWord n := by
  refine ERMor1.interp_cvRec_of_bounded decodeWordNode (ERMor1.proj 0) n ![] decodeWord
    (fun j _ => ?_) (fun j hj => ?_) (fun i _ cand htrace => ?_)
  · exact decodeWord_le_self j
  · exact hj
  · rw [decodeWordNode_interp i cand n]
    by_cases h1 : shapeCode i = 1
    · rw [if_pos h1]
      by_cases h2 : opKindCode i = 0
      · rw [if_pos h2, htrace (child1Code i) (child1Code_lt_of_shape i h1)]
        symm
        rw [decodeWord_eq_ite i, if_pos h1, if_pos h2]
      · rw [if_neg h2]
        symm
        rw [decodeWord_eq_ite i, if_pos h1, if_neg h2]
    · rw [if_neg h1]
      symm
      rw [decodeWord_eq_ite i, if_neg h1]

/-- The step term of the `codeBbInner` recursion at slots `(i, prev)`: one
`app`-of-constructor-variable node layer over the running spine code, the `pairER`
rebuild of `codeBbInner`'s successor arm. Novel realization. -/
private def codeBbInnerStepER (τ : RType) : ERMor1 2 :=
  pairER (ERMor1.natN 2 1)
    (pairER (ERMor1.natN 2 (codeOp (OneLambdaOp.app (barTy τ) (barTy τ))))
      (pairER (ERMor1.natN 2 (Nat.pair 0 (ctorIdx true).val))
        (pairER (ERMor1.proj 1) (ERMor1.natN 2 0))))

/-- The step term of the `codeBbInner` recursion evaluates to the successor arm of
`codeBbInner` on the running value. -/
private theorem codeBbInnerStepER_eval (τ : RType) (i prev : ℕ) :
    (codeBbInnerStepER τ).interp (Fin.cons i (Fin.cons prev (![] : Fin 0 → ℕ)))
      = Nat.pair 1 (Nat.pair (codeOp (OneLambdaOp.app (barTy τ) (barTy τ)))
          (Nat.pair (Nat.pair 0 (ctorIdx true).val) (Nat.pair prev 0))) := by
  simp only [codeBbInnerStepER, pairER_interp, ERMor1.interp_natN, ERMor1.interp_proj,
    Fin.cons_zero, Fin.cons_one]

/-- The value bound of the `codeBbInner` recursion: the `towerER 2` composite over
the linear polynomial of `codeBbInner_le_tower`, with the application-tag payload
and the constructor-context length as per-`τ` constants. Novel realization. -/
private def bbInnerBoundER (τ : RType) : ERMor1 1 :=
  ERMor1.comp (ERMor1.towerER 2) (fun _ : Fin 1 =>
    ERMor1.comp ERMor1.mulN (fun s => match s with
      | ⟨0, _⟩ => ERMor1.natN 1 6
      | ⟨1, _⟩ => ERMor1.comp ERMor1.addN (fun t => match t with
          | ⟨0, _⟩ => ERMor1.comp ERMor1.mulN (fun u => match u with
              | ⟨0, _⟩ => ERMor1.natN 1 4
              | ⟨1, _⟩ => ERMor1.proj 0)
          | ⟨1, _⟩ => ERMor1.natN 1 (opPayload (OneLambdaOp.app (barTy τ) (barTy τ))
              + (stepTypes natAlgSig (barTy τ) (barTy τ)).length + 3))))

/-- The value bound of the `codeBbInner` recursion evaluates to the tower of
`codeBbInner_le_tower` at the counter slot. -/
private theorem bbInnerBoundER_eval (τ : RType) (j : ℕ) :
    (bbInnerBoundER τ).interp (Fin.cons j (![] : Fin 0 → ℕ))
      = tower 2 (6 * (4 * j + (opPayload (OneLambdaOp.app (barTy τ) (barTy τ))
          + (stepTypes natAlgSig (barTy τ) (barTy τ)).length + 3))) := by
  simp only [bbInnerBoundER, ERMor1.interp_comp, ERMor1.interp_towerER,
    ERMor1.interp_mulN, ERMor1.interp_addN, ERMor1.interp_natN, ERMor1.interp_proj,
    Fin.cons_zero]

/-- The Gödel code of the variable-headed numeral spine as an elementary-recursive
morphism: `ERMor1.boundedRec` at base the constructor-variable leaf code, step
`codeBbInnerStepER`, and value bound the envelope tower `bbInnerBoundER` (N6: one
bounded recursion under the Task 6.4.8 envelope). Realizes `codeBbInner`. Novel
realization. -/
private def codeBbInnerER (τ : RType) : ERMor1 1 :=
  ERMor1.boundedRec (ERMor1.natN 0 (Nat.pair 0 (ctorIdx false).val))
    (codeBbInnerStepER τ) (bbInnerBoundER τ)

/-- The raw `Nat.rec` trace of the `codeBbInner` recursion at counter `k` equals
the numeric fold `codeBbInner τ k`. -/
private theorem codeBbInnerER_rec_eq (τ : RType) (k : ℕ) :
    (Nat.rec ((ERMor1.natN 0 (Nat.pair 0 (ctorIdx false).val)).interp (![] : Fin 0 → ℕ))
      (fun i prev => (codeBbInnerStepER τ).interp
        (Fin.cons i (Fin.cons prev (![] : Fin 0 → ℕ)))) k : ℕ)
      = codeBbInner τ k := by
  induction k with
  | zero =>
    rw [show (Nat.rec ((ERMor1.natN 0 (Nat.pair 0 (ctorIdx false).val)).interp
        (![] : Fin 0 → ℕ)) _ 0 : ℕ)
      = (ERMor1.natN 0 (Nat.pair 0 (ctorIdx false).val)).interp (![] : Fin 0 → ℕ) from rfl,
      ERMor1.interp_natN]
    rfl
  | succ m ih =>
    change (codeBbInnerStepER τ).interp (Fin.cons m (Fin.cons _ (![] : Fin 0 → ℕ)))
      = codeBbInner τ (m + 1)
    rw [ih, codeBbInnerStepER_eval]
    rfl

/-- Interpretation of `codeBbInnerER`: the numeric spine fold `codeBbInner`,
unconditionally on every numeral. Discharges the hypotheses of
`ERMor1.boundedRec_eq_natRec_of_bounded`: the trace equals the fold
(`codeBbInnerER_rec_eq`), the dominance is the envelope tower
`codeBbInner_le_tower`, and the monotonicity is `tower_mono_right` at the linear
polynomial. -/
private theorem codeBbInnerER_interp (τ : RType) (n : ℕ) :
    (codeBbInnerER τ).interp ![n] = codeBbInner τ n := by
  change (codeBbInnerER τ).interp (Fin.cons n (![] : Fin 0 → ℕ)) = codeBbInner τ n
  unfold codeBbInnerER
  refine (ERMor1.boundedRec_eq_natRec_of_bounded _ _ _ _ _ ?_ ?_).trans ?_
  · intro j _hj
    rw [codeBbInnerER_rec_eq, bbInnerBoundER_eval]
    exact codeBbInner_le_tower τ j
  · intro j hj
    rw [bbInnerBoundER_eval, bbInnerBoundER_eval]
    exact tower_mono_right 2 (by omega)
  · exact codeBbInnerER_rec_eq τ n

/-- The numeric abstraction wrapper `codeLamWrap` as an elementary-recursive
composite: a meta-level fold over the binder suffix layering one `pairER` rebuild
of a `lam` node per context sort around an inner read. Novel realization. -/
private def codeLamWrapER (result : RType) : List RType → ERMor1 1 → ERMor1 1
  | [], e => e
  | ξ :: Δ', e =>
      pairER (ERMor1.natN 1 1)
        (pairER (ERMor1.natN 1 (codeOp (OneLambdaOp.lam ξ (RType.curried Δ' result))))
          (pairER (codeLamWrapER result Δ' e) (ERMor1.natN 1 0)))

/-- Interpretation of `codeLamWrapER`: the numeric wrapper `codeLamWrap` applied to
the inner read's value, by induction on the binder suffix. -/
private theorem codeLamWrapER_interp (result : RType) (Δ : List RType) (e : ERMor1 1)
    (ctx : Fin 1 → ℕ) :
    (codeLamWrapER result Δ e).interp ctx = codeLamWrap result Δ (e.interp ctx) := by
  induction Δ with
  | nil => rfl
  | cons ξ Δ' ih =>
    simp only [codeLamWrapER, pairER_interp, ERMor1.interp_natN, ih, codeLamWrap]

/-- The Gödel code of the Berarducci-Böhm representation of a numeral as an
elementary-recursive morphism (spec §6.3; N6): the fixed abstraction wrapper
`codeLamWrapER` over the constructor step types around the numeral-recursive spine
fold `codeBbInnerER`, mirroring the factorization of `codeBbRep` (Leivant III
section 4.2). Novel realization. -/
def codeBbRepER (τ : RType) : ERMor1 1 :=
  codeLamWrapER (barTy τ) (stepTypes natAlgSig (barTy τ) (barTy τ)) (codeBbInnerER τ)

/-- Interpretation of `codeBbRepER`: the numeric fold `codeBbRep`, unconditionally
on every numeral, composing the wrapper interpretation `codeLamWrapER_interp` with
the spine interpretation `codeBbInnerER_interp`. -/
@[simp] theorem codeBbRepER_interp (τ : RType) (n : ℕ) :
    (codeBbRepER τ).interp ![n] = codeBbRep τ n := by
  unfold codeBbRepER
  rw [codeLamWrapER_interp, codeBbInnerER_interp]
  rfl

/-! ### The applied-term code builder -/

/-- The code of the applied bar-image term as an elementary-recursive morphism
(spec §6.3; N6; plan decision P4): the `pairER` rebuild of the `app` node of
`codeTm_app'` over the closed constants `codeTm (barTm F)` and the application
operation code — closed naturals of the fixed function term `F` — and the
numeral-recursive argument code `codeBbRepER τ`. The applied term is the shape of
Proposition 13 (Leivant III section 5, p. 226): the bar image `barTm F` applied to
the Berarducci-Böhm representation of the input numeral. Novel realization. -/
def buildCode {τ : RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) [] (RType.arrow (RType.omega τ) RType.o)) :
    ERMor1 1 :=
  pairER (ERMor1.natN 1 1)
    (pairER (ERMor1.natN 1 (codeOp (OneLambdaOp.app (barTy (RType.omega τ)) RType.o)))
      (pairER (ERMor1.natN 1 (codeTm (barTm F)))
        (pairER (codeBbRepER τ) (ERMor1.natN 1 0))))

/-- Interpretation of `buildCode`: the code of the applied bar-image term,
`codeTm (app' (barTm F) (bbRep (natToFreeAlg n) (barTy τ)))`, unconditionally on
every numeral. The argument slot lands `codeBbRep` (`codeBbRepER_interp`), the
numeric fold agrees with the argument's term code (`codeBbRep_codeTm`), and the
node equation `codeTm_app'` reassembles the application code. -/
theorem buildCode_interp {τ : RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) [] (RType.arrow (RType.omega τ) RType.o))
    (n : ℕ) :
    (buildCode F).interp ![n]
      = codeTm (OneLambda.app' (barTm F) (bbRep (natToFreeAlg n) (barTy τ))) := by
  unfold buildCode
  simp only [pairER_interp, ERMor1.interp_natN, codeBbRepER_interp]
  rw [codeBbRep_codeTm]
  exact (codeTm_app' (barTm F) (bbRep (natToFreeAlg n) (barTy τ))).symm

/-! ### The in-system clock and budget -/

/-- The aggregate redex rank of an application node is bounded by the ranks of
its subterms together with the order of the function's arrow sort: the top
β-detector contributes at most `RType.ord (RType.arrow σ τ)` and the top
ι-detector at most `1`. Local re-derivation of the rank-uniformity bound of
Proposition 13 (Leivant III section 5, p. 226). -/
private theorem redexRank_app'_le {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig natAlgSig) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig natAlgSig) Γ σ) :
    redexRank (app' f x)
      ≤ max (redexRank f) (max (redexRank x) (max 1 (RType.ord (RType.arrow σ τ)))) := by
  rw [redexRank_app', topBetaRank_app']
  split_ifs <;> omega

/-- The uniform rank ceiling of the fixed function term `F` (Proposition 13's
`qF`, Leivant III section 5, p. 226): the redex rank of the bar image together
with the order of the applied arrow sort, a constant of `F`. Applied to a normal
argument, the rank of the application never exceeds it. -/
def rankCeil {τ : RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) [] (RType.arrow (RType.omega τ) RType.o)) : ℕ :=
  max (redexRank (barTm F))
    (max 1 (RType.ord (RType.arrow (barTy (RType.omega τ)) RType.o)))

/-- The rank ceiling dominates the redex rank of the applied bar-image term,
uniformly in the argument word: the argument's rank vanishes (`normal_bbRep`),
leaving the rank of `barTm F` and the sort data (`redexRank_app'_le`). -/
theorem redexRank_applied_le {τ : RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) [] (RType.arrow (RType.omega τ) RType.o))
    (a : FreeAlg natAlgSig) :
    redexRank (OneLambda.app' (barTm F) (bbRep a (barTy τ))) ≤ rankCeil F := by
  have happ : redexRank (OneLambda.app' (barTm F) (bbRep a (barTy τ)))
      ≤ max (redexRank (barTm F)) (max (redexRank (bbRep a (barTy τ)))
          (max 1 (RType.ord (RType.arrow (barTy (RType.omega τ)) RType.o)))) :=
    redexRank_app'_le (barTm F) (bbRep a (barTy τ))
  have h0 : redexRank (bbRep a (barTy τ)) = 0 := normal_bbRep a (barTy τ)
  rw [h0] at happ
  unfold rankCeil
  omega

/-- The height ceiling of the fixed function term `F`: the height of the bar
image plus the constructor-context length plus two, a constant of `F`. Applied
to the representation of the numeral `n`, the height of the application never
exceeds `heightCeil F + n`. -/
def heightCeil {τ : RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) [] (RType.arrow (RType.omega τ) RType.o)) : ℕ :=
  Tm.height (barTm F) + ((stepTypes natAlgSig (barTy τ) (barTy τ)).length + 2)

/-- The height ceiling dominates the height of the applied bar-image term up to
the input numeral: `height_app'` splits the application, and the `bbRep` spine
adds one level per constructor over the fixed abstraction prefix
(`height_bbRep_le`). -/
theorem height_applied_le {τ : RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) [] (RType.arrow (RType.omega τ) RType.o))
    (n : ℕ) :
    Tm.height (OneLambda.app' (barTm F) (bbRep (natToFreeAlg n) (barTy τ)))
      ≤ heightCeil F + n := by
  have happ : Tm.height (OneLambda.app' (barTm F) (bbRep (natToFreeAlg n) (barTy τ)))
      = 1 + max (Tm.height (barTm F)) (Tm.height (bbRep (natToFreeAlg n) (barTy τ))) :=
    height_app' (barTm F) (bbRep (natToFreeAlg n) (barTy τ))
  have hb := height_bbRep_le τ n
  unfold heightCeil
  omega

/-- The size ceiling of the fixed function term `F`: the size of the bar image
plus the constructor-context length plus two, a constant of `F`. Applied to the
representation of the numeral `n`, the size of the application never exceeds
`sizeCeil F + 2 * n`. -/
def sizeCeil {τ : RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) [] (RType.arrow (RType.omega τ) RType.o)) : ℕ :=
  Tm.size (barTm F) + ((stepTypes natAlgSig (barTy τ) (barTy τ)).length + 2)

/-- The size ceiling dominates the size of the applied bar-image term up to
twice the input numeral: `size_app'` splits the application, and the `bbRep`
spine adds two nodes per constructor over the fixed abstraction prefix
(`size_bbRep_le`). -/
theorem size_applied_le {τ : RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) [] (RType.arrow (RType.omega τ) RType.o))
    (n : ℕ) :
    Tm.size (OneLambda.app' (barTm F) (bbRep (natToFreeAlg n) (barTy τ)))
      ≤ sizeCeil F + 2 * n := by
  have happ : Tm.size (OneLambda.app' (barTm F) (bbRep (natToFreeAlg n) (barTy τ)))
      = 1 + Tm.size (barTm F) + Tm.size (bbRep (natToFreeAlg n) (barTy τ)) :=
    size_app' (barTm F) (bbRep (natToFreeAlg n) (barTy τ))
  have hb := size_bbRep_le τ n
  unfold sizeCeil
  omega

/-- The sort-payload ceiling of the fixed function term `F`: the payload of the
applied `app` tag, the payload of the bar image, and the payload wrapper of the
argument representation, a constant of `F`. -/
def payloadCeil {τ : RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) [] (RType.arrow (RType.omega τ) RType.o)) : ℕ :=
  max (opPayload (OneLambdaOp.app (barTy (RType.omega τ)) RType.o))
    (max (sortPayload (barTm F))
      (lamWrapPayload (barTy τ) (stepTypes natAlgSig (barTy τ) (barTy τ))
        (opPayload (OneLambdaOp.app (barTy τ) (barTy τ)))))

/-- The payload ceiling dominates the sort payload of the applied bar-image term,
uniformly in the input numeral: `sortPayload_app'` splits the application, and
the argument representation's payload is a function of `τ` alone
(`sortPayload_bbRep_le`). -/
theorem sortPayload_applied_le {τ : RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) [] (RType.arrow (RType.omega τ) RType.o))
    (n : ℕ) :
    sortPayload (OneLambda.app' (barTm F) (bbRep (natToFreeAlg n) (barTy τ)))
      ≤ payloadCeil F := by
  have happ : sortPayload (OneLambda.app' (barTm F) (bbRep (natToFreeAlg n) (barTy τ)))
      = max (opPayload (OneLambdaOp.app (barTy (RType.omega τ)) RType.o))
          (max (sortPayload (barTm F))
            (sortPayload (bbRep (natToFreeAlg n) (barTy τ)))) :=
    sortPayload_app' (barTm F) (bbRep (natToFreeAlg n) (barTy τ))
  have hb := sortPayload_bbRep_le τ n
  unfold payloadCeil
  omega

/-- The in-system clock of the fixed function term `F` (spec §6.3; N6): the
elementary-recursive composite computing
`(rankCeil F + 1) * tower (rankCeil F + 1) (heightCeil F + n)`, the Lemma 12
clock at the per-`F` rank and height ceilings — a `(rankCeil F + 1)`-height
`ERMor1.towerER` over the successor-and-addition atoms, times the constant
(Leivant III section 5, p. 226: the clock of Proposition 13 is a constant of
the fixed term over the input's representation height). Novel realization. -/
def clockER {τ : RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) [] (RType.arrow (RType.omega τ) RType.o)) :
    ERMor1 1 :=
  ERMor1.comp ERMor1.mulN (fun i => match i with
    | ⟨0, _⟩ => ERMor1.natN 1 (rankCeil F + 1)
    | ⟨1, _⟩ => ERMor1.comp (ERMor1.towerER (rankCeil F + 1)) (fun _ : Fin 1 =>
        ERMor1.comp ERMor1.addN (fun j => match j with
          | ⟨0, _⟩ => ERMor1.natN 1 (heightCeil F)
          | ⟨1, _⟩ => ERMor1.proj 0)))

/-- Interpretation of `clockER`: the Lemma 12 clock at the per-`F` ceilings,
`(rankCeil F + 1) * tower (rankCeil F + 1) (heightCeil F + n)`. -/
@[simp] theorem clockER_interp {τ : RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) [] (RType.arrow (RType.omega τ) RType.o))
    (n : ℕ) :
    (clockER F).interp ![n]
      = (rankCeil F + 1) * tower (rankCeil F + 1) (heightCeil F + n) := by
  simp only [clockER, ERMor1.interp_comp, ERMor1.interp_mulN, ERMor1.interp_towerER,
    ERMor1.interp_addN, ERMor1.interp_natN, ERMor1.interp_proj, Matrix.cons_val_zero]

/-- The deterministic clock of the applied bar-image term is dominated by the
Lemma 12 clock at the per-`F` ceilings: the rank ceiling enters both the
coefficient and the tower height (`tower_mono_left`), and the height ceiling
the tower argument (`tower_mono_right`). -/
theorem detClock_applied_le {τ : RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) [] (RType.arrow (RType.omega τ) RType.o))
    (n : ℕ) :
    (redexRank (OneLambda.app' (barTm F) (bbRep (natToFreeAlg n) (barTy τ))) + 1)
      * tower (redexRank (OneLambda.app' (barTm F) (bbRep (natToFreeAlg n) (barTy τ))) + 1)
        (Tm.height (OneLambda.app' (barTm F) (bbRep (natToFreeAlg n) (barTy τ))))
      ≤ (rankCeil F + 1) * tower (rankCeil F + 1) (heightCeil F + n) := by
  have hr := redexRank_applied_le F (natToFreeAlg n)
  have hh := height_applied_le F n
  exact Nat.mul_le_mul (Nat.add_le_add_right hr 1)
    (le_trans (tower_mono_left (Nat.add_le_add_right hr 1) _) (tower_mono_right _ hh))

/-- The in-system clock dominates the deterministic Lemma 12 clock of the applied
bar-image term (spec §6.3; the binding inequality of the clock deliverable): at
every input numeral `n`, the `detClock` value of Proposition 13's applied term is
at most `clockER F` evaluated at `n`. -/
theorem clockER_dominates {τ : RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) [] (RType.arrow (RType.omega τ) RType.o))
    (n : ℕ) :
    (redexRank (OneLambda.app' (barTm F) (bbRep (natToFreeAlg n) (barTy τ))) + 1)
      * tower (redexRank (OneLambda.app' (barTm F) (bbRep (natToFreeAlg n) (barTy τ))) + 1)
        (Tm.height (OneLambda.app' (barTm F) (bbRep (natToFreeAlg n) (barTy τ))))
      ≤ (clockER F).interp ![n] := by
  rw [clockER_interp]
  exact detClock_applied_le F n

/-- The in-system budget of the fixed function term `F` (ratified correction to
Task 6.4.14: the budget slot of `normRun` is a genuine input): the
elementary-recursive composite computing the chain ceiling `codeCeil` at the
per-`F` size, payload, rank, and height ceilings — a `towerER 2` composite over
a polynomial-and-exponential expression in `n` whose exponent is the in-system
clock `clockER F`. Novel realization. -/
def budgetER {τ : RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) [] (RType.arrow (RType.omega τ) RType.o)) :
    ERMor1 1 :=
  ERMor1.comp (ERMor1.towerER 2) (fun _ : Fin 1 =>
    ERMor1.comp ERMor1.mulN (fun s => match s with
      | ⟨0, _⟩ => ERMor1.natN 1 6
      | ⟨1, _⟩ => ERMor1.comp ERMor1.addN (fun t => match t with
          | ⟨0, _⟩ => ERMor1.comp ERMor1.addN (fun u => match u with
              | ⟨0, _⟩ => ERMor1.comp ERMor1.mulN (fun v => match v with
                  | ⟨0, _⟩ => ERMor1.natN 1 2
                  | ⟨1, _⟩ => ERMor1.comp ERMor1.powN (fun w => match w with
                      | ⟨0, _⟩ => ERMor1.comp ERMor1.addN (fun x => match x with
                          | ⟨0, _⟩ => ERMor1.natN 1 (sizeCeil F)
                          | ⟨1, _⟩ => ERMor1.comp ERMor1.mulN (fun y => match y with
                              | ⟨0, _⟩ => ERMor1.natN 1 2
                              | ⟨1, _⟩ => ERMor1.proj 0))
                      | ⟨1, _⟩ => ERMor1.comp ERMor1.powN (fun z => match z with
                          | ⟨0, _⟩ => ERMor1.natN 1 2
                          | ⟨1, _⟩ => clockER F)))
              | ⟨1, _⟩ => ERMor1.natN 1 (payloadCeil F))
          | ⟨1, _⟩ => ERMor1.natN 1 1)))

/-- Interpretation of `budgetER`: the chain ceiling shape at the per-`F`
ceilings, a height-`2` tower over
`6 * (2 * (sizeCeil F + 2 * n) ^ 2 ^ clock + payloadCeil F + 1)` with `clock`
the Lemma 12 clock of `clockER_interp`. -/
@[simp] theorem budgetER_interp {τ : RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) [] (RType.arrow (RType.omega τ) RType.o))
    (n : ℕ) :
    (budgetER F).interp ![n]
      = tower 2 (6 * (2 * (sizeCeil F + 2 * n)
          ^ 2 ^ ((rankCeil F + 1) * tower (rankCeil F + 1) (heightCeil F + n))
          + payloadCeil F + 1)) := by
  simp only [budgetER, ERMor1.interp_comp, ERMor1.interp_towerER, ERMor1.interp_mulN,
    ERMor1.interp_addN, ERMor1.interp_powN, ERMor1.interp_natN, ERMor1.interp_proj,
    clockER_interp, Matrix.cons_val_zero]

/-- The in-system budget dominates the deterministic chain ceiling of the applied
bar-image term (ratified correction to Task 6.4.14; the binding inequality of the
budget deliverable): at every input numeral `n`, `codeCeil` of Proposition 13's
applied term is at most `budgetER F` evaluated at `n`, so the budget slot of
`normRun` can be fed in-system. Chains the per-`F` measure ceilings with
`tower_mono_right` and power monotonicity, the exponent bounded by
`detClock_applied_le`. -/
theorem budgetER_dominates {τ : RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) [] (RType.arrow (RType.omega τ) RType.o))
    (n : ℕ) :
    codeCeil (OneLambda.app' (barTm F) (bbRep (natToFreeAlg n) (barTy τ)))
      ≤ (budgetER F).interp ![n] := by
  rw [budgetER_interp]
  unfold codeCeil detClock
  refine tower_mono_right 2 ?_
  have hs := size_applied_le F n
  have hp := sortPayload_applied_le F n
  have hD := detClock_applied_le F n
  have hpow : Tm.size (OneLambda.app' (barTm F) (bbRep (natToFreeAlg n) (barTy τ)))
        ^ 2 ^ ((redexRank (OneLambda.app' (barTm F) (bbRep (natToFreeAlg n) (barTy τ))) + 1)
          * tower (redexRank (OneLambda.app' (barTm F) (bbRep (natToFreeAlg n) (barTy τ))) + 1)
            (Tm.height (OneLambda.app' (barTm F) (bbRep (natToFreeAlg n) (barTy τ)))))
      ≤ (sizeCeil F + 2 * n)
        ^ 2 ^ ((rankCeil F + 1) * tower (rankCeil F + 1) (heightCeil F + n)) := by
    refine le_trans (Nat.pow_le_pow_left hs _) (Nat.pow_le_pow_right ?_ ?_)
    · unfold sizeCeil
      have := Tm.one_le_size (barTm F)
      omega
    · exact Nat.pow_le_pow_right (by omega) hD
  rw [show (List.map barTy ([] : Binding.Ctx RType)).length = 0 from rfl]
  omega

/-! ### The atomic collapse morphism -/

/-- Interpretation of a composition over a single fed slot: the fed morphism evaluates
once and enters as the singleton context. -/
private theorem interp_comp_singleton {k : ℕ} (e : ERMor1 1) (g : ERMor1 k)
    (ctx : Fin k → ℕ) :
    (ERMor1.comp e fun _ => g).interp ctx = e.interp ![g.interp ctx] := by
  rw [ERMor1.interp_comp]
  exact congrArg e.interp (cons_fin_one (g.interp ctx))

/-- Interpretation of a composition over three fed slots: each fed morphism evaluates
pointwise and enters positionally. -/
private theorem interp_comp_three {k : ℕ} (e : ERMor1 3) (g₀ g₁ g₂ : ERMor1 k)
    (ctx : Fin k → ℕ) :
    (ERMor1.comp e ![g₀, g₁, g₂]).interp ctx
      = e.interp ![g₀.interp ctx, g₁.interp ctx, g₂.interp ctx] := by
  rw [ERMor1.interp_comp]
  refine congrArg e.interp (funext fun j => ?_)
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

/-- The atomic collapse morphism for a single codomain-`o` source (spec §6.4; plan
decision P4): decode ∘ clocked normalization ∘ build. The composite feeds the clocked
iteration `normRun` at the in-system clock `clockER F`, the applied-term code
`buildCode F`, and the in-system budget `budgetER F`, and reads the word decoder
`decodeWordER` off the resulting normal code — per fixed `F`, the whole of
Proposition 13's normalization pipeline (Leivant III section 5, p. 226, DOI
`10.1016/S0168-0072(98)00040-2`) as one elementary-recursive morphism, anchored
denotationally by `collapseER_interp`. Novel realization. -/
def collapseER {τ : RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) []
      (RType.arrow (RType.omega τ) RType.o)) : ERMorN 1 1 :=
  fun _ => ERMor1.comp decodeWordER fun _ =>
    ERMor1.comp normRun ![clockER F, buildCode F, budgetER F]

/-- Adequacy of the collapse morphism against the denotational anchor (spec §6.4; plan
decision P4): at every input the collapse computes the numeric reading of the standard
denotation of Proposition 13's applied term (Leivant III section 5, p. 226) —
`freeAlgToNat` of `appEval` at the source-side application of `F` to the constructor
word of the input. The fed code slot reduces by `buildCode_interp`; the budget
dominance (`codeTm_detIter_le_codeCeil` chained through `budgetER_dominates`)
discharges `normRun_interp_of_le`, landing the iterate's code by
`stepCode_iterate_codeTm`; the clock dominance (`clockER_dominates`) absorbs the
overshoot past the Lemma 12 normal form (`detIter_normal`, `detIter_eq_of_normal`);
the normal reduct is identified with the value word by the Proposition 13
identification chain (`normal_closed_o_eq_conc`, `oneEval_reduces`, `oneEval_conc`
against `prop11_represents` through `represents_arrow` and `lemma9_omega`); and the
word decoder reads the value off its code (`decodeWord_codeTm_conc`). -/
theorem collapseER_interp {τ : RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) []
      (RType.arrow (RType.omega τ) RType.o)) (v : Fin 1 → ℕ) :
    (collapseER F).interp v = fun _ =>
      freeAlgToNat (appEval
        (sourceApp F (sourceWord (natToFreeAlg (v 0)) τ)) finZeroElim) := by
  obtain ⟨n, rfl⟩ : ∃ n, v = ![n] :=
    ⟨v 0, funext fun i => match i with | ⟨0, _⟩ => rfl⟩
  funext i
  simp only [Matrix.cons_val_zero]
  set a : FreeAlg natAlgSig := natToFreeAlg n
  set W : Binding.Tm (oneLambdaSig natAlgSig) [] RType.o :=
    app' (barTm F) (bbRep a (barTy τ))
  set L : ℕ := (redexRank W + 1) * tower (redexRank W + 1) (Tm.height W)
  -- The fed slots: the code slot is the applied term's code, the clock slot dominates
  -- the Lemma 12 clock, and the budget slot dominates every trace value.
  have hcode : (buildCode F).interp ![n] = codeTm W := buildCode_interp F n
  have hclk : L ≤ (clockER F).interp ![n] := clockER_dominates F n
  have hbud : ∀ j, j ≤ (clockER F).interp ![n] →
      stepCode^[j] (codeTm W) ≤ (budgetER F).interp ![n] := by
    intro j _hj
    rw [stepCode_iterate_codeTm j W]
    exact le_trans (codeTm_detIter_le_codeCeil j W) (budgetER_dominates F n)
  have hnorm : Normal (detIter L W) := detIter_normal W
  -- The identification chain of Proposition 13: the normal reduct is the value word.
  obtain ⟨b, hb⟩ := normal_closed_o_eq_conc (detIter L W) hnorm
  have h9 : Represents (RType.omega τ) (sourceWord a τ) (bbRep a (barTy τ)) := by
    have h := lemma9_omega τ (sourceWord a τ)
    rwa [appEval_sourceWord] at h
  have hrep : Represents RType.o (sourceApp F (sourceWord a τ)) W :=
    (represents_arrow F (barTm F)).mp (prop11_represents F) (sourceWord a τ)
      (bbRep a (barTy τ)) h9
  have hred : Relation.ReflTransGen OneLambdaStep W
      (conc (appEval (sourceApp F (sourceWord a τ)) finZeroElim)) := hrep
  have hval : b = appEval (sourceApp F (sourceWord a τ)) finZeroElim := by
    have h1 := oneEval_reduces (detIter_reduces L W) finZeroElim
    have h2 := oneEval_reduces hred finZeroElim
    rw [hb, oneEval_conc] at h1
    rw [oneEval_conc] at h2
    exact h1.symm.trans h2
  -- The composite unfolds to the decode of the clocked run at the fed slots.
  simp only [collapseER, ERMorN.interp]
  rw [interp_comp_singleton, interp_comp_three, decodeWordER_interp, hcode,
    normRun_interp_of_le _ _ _ hbud, stepCode_iterate_codeTm _ W,
    detIter_eq_of_normal hclk hnorm, hb, decodeWord_codeTm_conc, hval]

/-! ### The a-ary collapse morphism -/

/-- The curried arrow sort `Ω τ₀ → ⋯ → Ω τ_{a-1} → o` of an indexed family of shifted
input sorts, in structural-recursion form: the `Fin`-indexed counterpart of
`RType.curried (List.ofFn fun i => RType.omega (τs i)) RType.o`
(`omegaCurried_eq_curried`), exposing the head sort and the tail family
definitionally to the spine recursions below. -/
private def omegaCurried : {a : ℕ} → (Fin a → RType) → RType
  | 0, _ => RType.o
  | _ + 1, τs => RType.arrow (RType.omega (τs 0)) (omegaCurried fun i => τs i.succ)

/-- The structural curried sort agrees with the list-curried spelling over
`List.ofFn`: `omegaCurried τs = RType.curried (List.ofFn fun i => RType.omega (τs i))
RType.o`, by induction on the arity through `List.ofFn_succ`. -/
private theorem omegaCurried_eq_curried : ∀ {a : ℕ} (τs : Fin a → RType),
    omegaCurried τs = RType.curried (List.ofFn fun i => RType.omega (τs i)) RType.o
  | 0, _ => rfl
  | _ + 1, τs => by
      rw [List.ofFn_succ, RType.curried_cons]
      exact congrArg (RType.arrow (RType.omega (τs 0)))
        (omegaCurried_eq_curried fun i => τs i.succ)

/-- The source-level application spine over a structurally-curried head: iterate
`sourceApp` over the argument tuple, peeling the head sort of `omegaCurried`
definitionally. The recursion core of `sourceApps`. -/
private def sourceSpine : {a : ℕ} → (τs : Fin a → RType) →
    Binding.Tm (rlmrOSig natAlgSig) [] (omegaCurried τs) →
    (∀ i : Fin a, Binding.Tm (rlmrOSig natAlgSig) [] (RType.omega (τs i))) →
    Binding.Tm (rlmrOSig natAlgSig) [] RType.o
  | 0, _, H, _ => H
  | _ + 1, τs, H, ws =>
      sourceSpine (fun i => τs i.succ) (sourceApp H (ws 0)) fun i => ws i.succ

/-- The `a`-fold source-level application spine (spec §6.4): the `sourceApp` iterate,
applying a closed function term at the curried arrow sort over the shifted input
sorts `Ω (τs i)` to one closed argument term per input position — the source-side
application shape of the `a`-ary hypothesis of Proposition 13 (Leivant III
section 5, p. 226, DOI `10.1016/S0168-0072(98)00040-2`). The `Fin`-indexed
counterpart of the list-indexed `Ramified.appSpine`; the head is carried across
`omegaCurried_eq_curried` once and the iteration is structural. -/
def sourceApps {a : ℕ} {τs : Fin a → RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) []
      (RType.curried (List.ofFn fun i => RType.omega (τs i)) RType.o))
    (ws : ∀ i : Fin a, Binding.Tm (rlmrOSig natAlgSig) [] (RType.omega (τs i))) :
    Binding.Tm (rlmrOSig natAlgSig) [] RType.o :=
  sourceSpine τs ((omegaCurried_eq_curried τs).symm ▸ F) ws

/-- The bar-side application spine at numeric inputs: iterate `OneLambda.app'` over
the Berarducci-Böhm representations of the input numerals, peeling the head sort of
`omegaCurried` through `barTy` definitionally. The `a`-ary applied bar-image term of
Proposition 13 (Leivant III section 5, p. 226) over a generic head. -/
private def barSpine : {a : ℕ} → (τs : Fin a → RType) →
    Binding.Tm (oneLambdaSig natAlgSig) [] (barTy (omegaCurried τs)) →
    (Fin a → ℕ) → Binding.Tm (oneLambdaSig natAlgSig) [] RType.o
  | 0, _, H, _ => H
  | _ + 1, τs, H, v =>
      barSpine (fun i => τs i.succ)
        (OneLambda.app' H (bbRep (natToFreeAlg (v 0)) (barTy (τs 0)))) fun i => v i.succ

/-- The bar image of the fixed `a`-ary function term at the structural head sort:
`barTm F` carried across `omegaCurried_eq_curried`. The head of the applied
bar-image spine `barSpine` and the closed head constant of the code builder. -/
private def barHead {a : ℕ} {τs : Fin a → RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) []
      (RType.curried (List.ofFn fun i => RType.omega (τs i)) RType.o)) :
    Binding.Tm (oneLambdaSig natAlgSig) [] (barTy (omegaCurried τs)) :=
  (congrArg barTy (omegaCurried_eq_curried τs)).symm ▸ barTm F

/-- Transport of the representation relation along a sort equality: representation
at `τ` carries to representation of the transported terms at `τ'`. -/
private theorem represents_cast {τ τ' : RType} (e : τ = τ')
    (F : Binding.Tm (rlmrOSig natAlgSig) [] τ)
    (Fhat : Binding.Tm (oneLambdaSig natAlgSig) [] (barTy τ))
    (h : Represents τ F Fhat) :
    Represents τ' (e ▸ F) ((congrArg barTy e) ▸ Fhat) := by
  subst e
  exact h

/-- The fixed `a`-ary function term is represented by its bar image at the
structural head sort: Proposition 11 (`prop11_represents`) carried across
`omegaCurried_eq_curried`. -/
private theorem represents_head {a : ℕ} {τs : Fin a → RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) []
      (RType.curried (List.ofFn fun i => RType.omega (τs i)) RType.o)) :
    Represents (omegaCurried τs) ((omegaCurried_eq_curried τs).symm ▸ F) (barHead F) :=
  represents_cast (omegaCurried_eq_curried τs).symm F (barTm F) (prop11_represents F)

/-- The source spine at the constructor words of the input numerals is represented
by the bar spine at the same numerals (Leivant III sections 4.2 and 5): fold the
arrow clause of `Represents` over the argument positions, each argument represented
by its Berarducci-Böhm form through `lemma9_omega` and `appEval_sourceWord`. -/
private theorem represents_barSpine : ∀ {a : ℕ} (τs : Fin a → RType)
    (H : Binding.Tm (rlmrOSig natAlgSig) [] (omegaCurried τs))
    (Hhat : Binding.Tm (oneLambdaSig natAlgSig) [] (barTy (omegaCurried τs))),
    Represents (omegaCurried τs) H Hhat → ∀ v : Fin a → ℕ,
    Represents RType.o
      (sourceSpine τs H fun i => sourceWord (natToFreeAlg (v i)) (τs i))
      (barSpine τs Hhat v)
  | 0, _, _, _, h, _ => h
  | _ + 1, τs, H, Hhat, h, v => by
      have h9 : Represents (RType.omega (τs 0))
          (sourceWord (natToFreeAlg (v 0)) (τs 0))
          (bbRep (natToFreeAlg (v 0)) (barTy (τs 0))) := by
        have h' := lemma9_omega (τs 0) (sourceWord (natToFreeAlg (v 0)) (τs 0))
        rwa [appEval_sourceWord] at h'
      exact represents_barSpine (fun i => τs i.succ)
        (sourceApp H (sourceWord (natToFreeAlg (v 0)) (τs 0)))
        (OneLambda.app' Hhat (bbRep (natToFreeAlg (v 0)) (barTy (τs 0))))
        ((represents_arrow H Hhat).mp h _ _ h9) fun i => v i.succ

/-- The per-position height-and-size offset of the bar spine: one application node
and the argument representation's fixed abstraction prefix per input position — the
constructor-context length plus two, summed over the positions. -/
private def spineOffset : {a : ℕ} → (Fin a → RType) → ℕ
  | 0, _ => 0
  | _ + 1, τs =>
      ((stepTypes natAlgSig (barTy (τs 0)) (barTy (τs 0))).length + 2)
        + spineOffset fun i => τs i.succ

/-- The per-position sort-payload offset of the bar spine: the payload of the `app`
tag at each application step and the payload wrapper of each argument
representation, summed over the input positions. -/
private def spinePayload : {a : ℕ} → (Fin a → RType) → ℕ
  | 0, _ => 0
  | _ + 1, τs =>
      opPayload (OneLambdaOp.app (barTy (RType.omega (τs 0)))
          (barTy (omegaCurried fun i => τs i.succ)))
        + lamWrapPayload (barTy (τs 0)) (stepTypes natAlgSig (barTy (τs 0)) (barTy (τs 0)))
            (opPayload (OneLambdaOp.app (barTy (τs 0)) (barTy (τs 0))))
        + spinePayload fun i => τs i.succ

/-- The redex rank of the bar spine is bounded by the head rank together with the
order of the head's arrow sort, uniformly in the input numerals: each argument's
rank vanishes (`normal_bbRep`), and the order of every suffix arrow sort is
dominated by the order of the full arrow sort. The `a`-ary rank-uniformity bound of
Proposition 13 (Leivant III section 5, p. 226). -/
private theorem redexRank_barSpine_le : ∀ {a : ℕ} (τs : Fin a → RType)
    (H : Binding.Tm (oneLambdaSig natAlgSig) [] (barTy (omegaCurried τs)))
    (v : Fin a → ℕ),
    redexRank (barSpine τs H v)
      ≤ max (redexRank H) (max 1 (RType.ord (barTy (omegaCurried τs))))
  | 0, _, _, _ => le_max_left _ _
  | _ + 1, τs, H, v => by
      set W0 : Binding.Tm (oneLambdaSig natAlgSig) []
          (barTy (omegaCurried fun i => τs i.succ)) :=
        OneLambda.app' H (bbRep (natToFreeAlg (v 0)) (barTy (τs 0)))
      have hrec := redexRank_barSpine_le (fun i => τs i.succ) W0 fun i => v i.succ
      have happ : redexRank W0
          ≤ max (redexRank H)
              (max (redexRank (bbRep (natToFreeAlg (v 0)) (barTy (τs 0))))
                (max 1 (RType.ord (RType.arrow (barTy (RType.omega (τs 0)))
                  (barTy (omegaCurried fun i => τs i.succ)))))) :=
        redexRank_app'_le H _
      have h0 : redexRank (bbRep (natToFreeAlg (v 0)) (barTy (τs 0))) = 0 :=
        normal_bbRep (natToFreeAlg (v 0)) (barTy (τs 0))
      have harr : RType.ord (RType.arrow (barTy (RType.omega (τs 0)))
            (barTy (omegaCurried fun i => τs i.succ)))
          = max (RType.ord (barTy (RType.omega (τs 0))) + 1)
              (RType.ord (barTy (omegaCurried fun i => τs i.succ))) := rfl
      have hord : RType.ord (barTy (omegaCurried τs))
          = max (RType.ord (barTy (RType.omega (τs 0))) + 1)
              (RType.ord (barTy (omegaCurried fun i => τs i.succ))) := rfl
      have hunfold : redexRank (barSpine τs H v)
          = redexRank (barSpine (fun i => τs i.succ) W0 fun i => v i.succ) := rfl
      rw [hunfold]
      omega

/-- The height of the bar spine is bounded by the head height plus the spine offset
plus the sum of the input numerals: each application step contributes one level over
the argument representation's height (`height_bbRep_le`). -/
private theorem height_barSpine_le : ∀ {a : ℕ} (τs : Fin a → RType)
    (H : Binding.Tm (oneLambdaSig natAlgSig) [] (barTy (omegaCurried τs)))
    (v : Fin a → ℕ),
    Tm.height (barSpine τs H v) ≤ Tm.height H + spineOffset τs + ∑ i, v i
  | 0, τs, H, v => by
      have hsum : ∑ i, v i = 0 := by simp
      have hunfold : Tm.height (barSpine τs H v) = Tm.height H := rfl
      have hoff : spineOffset τs = 0 := rfl
      rw [hunfold, hoff, hsum]
      omega
  | _ + 1, τs, H, v => by
      set W0 : Binding.Tm (oneLambdaSig natAlgSig) []
          (barTy (omegaCurried fun i => τs i.succ)) :=
        OneLambda.app' H (bbRep (natToFreeAlg (v 0)) (barTy (τs 0)))
      have hrec := height_barSpine_le (fun i => τs i.succ) W0 fun i => v i.succ
      have happ : Tm.height W0
          = 1 + max (Tm.height H) (Tm.height (bbRep (natToFreeAlg (v 0)) (barTy (τs 0)))) :=
        height_app' H _
      have hb := height_bbRep_le (τs 0) (v 0)
      have hsum : ∑ i, v i = v 0 + ∑ i : Fin _, v i.succ := Fin.sum_univ_succ v
      have hunfold : Tm.height (barSpine τs H v)
          = Tm.height (barSpine (fun i => τs i.succ) W0 fun i => v i.succ) := rfl
      have hoff : spineOffset τs
          = ((stepTypes natAlgSig (barTy (τs 0)) (barTy (τs 0))).length + 2)
            + spineOffset fun i => τs i.succ := rfl
      rw [hunfold, hoff]
      omega

/-- The size of the bar spine is bounded by the head size plus the spine offset plus
twice the sum of the input numerals: each application step contributes one node over
the argument representation's size (`size_bbRep_le`). -/
private theorem size_barSpine_le : ∀ {a : ℕ} (τs : Fin a → RType)
    (H : Binding.Tm (oneLambdaSig natAlgSig) [] (barTy (omegaCurried τs)))
    (v : Fin a → ℕ),
    Tm.size (barSpine τs H v) ≤ Tm.size H + spineOffset τs + 2 * ∑ i, v i
  | 0, τs, H, v => by
      have hsum : ∑ i, v i = 0 := by simp
      have hunfold : Tm.size (barSpine τs H v) = Tm.size H := rfl
      have hoff : spineOffset τs = 0 := rfl
      rw [hunfold, hoff, hsum]
      omega
  | _ + 1, τs, H, v => by
      set W0 : Binding.Tm (oneLambdaSig natAlgSig) []
          (barTy (omegaCurried fun i => τs i.succ)) :=
        OneLambda.app' H (bbRep (natToFreeAlg (v 0)) (barTy (τs 0)))
      have hrec := size_barSpine_le (fun i => τs i.succ) W0 fun i => v i.succ
      have happ : Tm.size W0
          = 1 + Tm.size H + Tm.size (bbRep (natToFreeAlg (v 0)) (barTy (τs 0))) :=
        size_app' H _
      have hb := size_bbRep_le (τs 0) (v 0)
      have hsum : ∑ i, v i = v 0 + ∑ i : Fin _, v i.succ := Fin.sum_univ_succ v
      have hunfold : Tm.size (barSpine τs H v)
          = Tm.size (barSpine (fun i => τs i.succ) W0 fun i => v i.succ) := rfl
      have hoff : spineOffset τs
          = ((stepTypes natAlgSig (barTy (τs 0)) (barTy (τs 0))).length + 2)
            + spineOffset fun i => τs i.succ := rfl
      rw [hunfold, hoff]
      omega

/-- The sort payload of the bar spine is bounded by the head payload plus the spine
payload, uniformly in the input numerals: each argument representation's payload is
a function of its sort alone (`sortPayload_bbRep_le`). -/
private theorem sortPayload_barSpine_le : ∀ {a : ℕ} (τs : Fin a → RType)
    (H : Binding.Tm (oneLambdaSig natAlgSig) [] (barTy (omegaCurried τs)))
    (v : Fin a → ℕ),
    sortPayload (barSpine τs H v) ≤ sortPayload H + spinePayload τs
  | 0, τs, H, v => by
      have hunfold : sortPayload (barSpine τs H v) = sortPayload H := rfl
      have hoff : spinePayload τs = 0 := rfl
      rw [hunfold, hoff]
      omega
  | _ + 1, τs, H, v => by
      set W0 : Binding.Tm (oneLambdaSig natAlgSig) []
          (barTy (omegaCurried fun i => τs i.succ)) :=
        OneLambda.app' H (bbRep (natToFreeAlg (v 0)) (barTy (τs 0)))
      have hrec := sortPayload_barSpine_le (fun i => τs i.succ) W0 fun i => v i.succ
      have happ : sortPayload W0
          = max (opPayload (OneLambdaOp.app (barTy (RType.omega (τs 0)))
              (barTy (omegaCurried fun i => τs i.succ))))
            (max (sortPayload H)
              (sortPayload (bbRep (natToFreeAlg (v 0)) (barTy (τs 0))))) :=
        sortPayload_app' H _
      have hb := sortPayload_bbRep_le (τs 0) (v 0)
      have hunfold : sortPayload (barSpine τs H v)
          = sortPayload (barSpine (fun i => τs i.succ) W0 fun i => v i.succ) := rfl
      have hoff : spinePayload τs
          = opPayload (OneLambdaOp.app (barTy (RType.omega (τs 0)))
              (barTy (omegaCurried fun i => τs i.succ)))
            + lamWrapPayload (barTy (τs 0))
                (stepTypes natAlgSig (barTy (τs 0)) (barTy (τs 0)))
                (opPayload (OneLambdaOp.app (barTy (τs 0)) (barTy (τs 0))))
            + spinePayload fun i => τs i.succ := rfl
      rw [hunfold, hoff]
      omega

/-- The per-step head-code rebuild of the spine code: at slots `(hd, v₀, …)` the
`pairER` rebuild of one `app` node applying the running head code `hd` to the
argument code `codeBbRepER σ` read at the first input slot, tagged with the `app`
operation at the step's sorts. Novel realization. -/
private def spineHeadER (a : ℕ) (σ ρ : RType) : ERMor1 (a + 2) :=
  pairER (ERMor1.natN (a + 2) 1)
    (pairER (ERMor1.natN (a + 2)
        (codeOp (OneLambdaOp.app (barTy (RType.omega σ)) (barTy ρ))))
      (pairER (ERMor1.proj 0)
        (pairER (ERMor1.comp (codeBbRepER σ) fun _ : Fin 1 => ERMor1.proj (Fin.succ 0))
          (ERMor1.natN (a + 2) 0))))

/-- The head-code rebuild evaluates to the `app`-node pack of the head slot and the
argument code `codeBbRep σ` at the first input slot. -/
private theorem spineHeadER_interp (a : ℕ) (σ ρ : RType) (h : ℕ) (v : Fin (a + 1) → ℕ) :
    (spineHeadER a σ ρ).interp (Fin.cons h v)
      = Nat.pair 1 (Nat.pair (codeOp (OneLambdaOp.app (barTy (RType.omega σ)) (barTy ρ)))
          (Nat.pair h (Nat.pair (codeBbRep σ (v 0)) 0))) := by
  simp only [spineHeadER, pairER_interp, ERMor1.interp_natN, ERMor1.interp_comp,
    ERMor1.interp_proj, cons_fin_one, codeBbRepER_interp, Fin.cons_zero, Fin.cons_succ]

/-- The spine-code fold: `ERMor1 (a + 1)` at slots `(hd, v₀, …, v_{a-1})` rebuilding
the code of the `a`-fold left-associated application of the head coded in the first
slot to the argument codes `codeBbRepER (τs i)` at the input slots — one
`spineHeadER` layer per input position, by meta-level recursion on the arity
(spec §6.4; N6). Novel realization. -/
private def spineCodeER : {a : ℕ} → (Fin a → RType) → ERMor1 (a + 1)
  | 0, _ => ERMor1.proj 0
  | a + 1, τs =>
      ERMor1.comp (spineCodeER fun i => τs i.succ)
        (Fin.cons (spineHeadER a (τs 0) (omegaCurried fun i => τs i.succ))
          fun j : Fin a => ERMor1.proj j.succ.succ)

/-- The spine-code fold at a head code computes the code of the bar spine:
`spineCodeER` evaluated at `(codeTm H, v)` is `codeTm (barSpine τs H v)`, each layer
reassembled by `codeTm_app'` through `codeBbRep_codeTm`. -/
private theorem spineCodeER_codeTm : ∀ {a : ℕ} (τs : Fin a → RType)
    (H : Binding.Tm (oneLambdaSig natAlgSig) [] (barTy (omegaCurried τs)))
    (v : Fin a → ℕ),
    (spineCodeER τs).interp (Fin.cons (codeTm H) v) = codeTm (barSpine τs H v)
  | 0, _, _, _ => rfl
  | a + 1, τs, H, v => by
      change (spineCodeER fun i => τs i.succ).interp
          (fun j => ((Fin.cons (spineHeadER a (τs 0) (omegaCurried fun i => τs i.succ))
              (fun j : Fin a => ERMor1.proj j.succ.succ) :
                Fin (a + 1) → ERMor1 (a + 2)) j).interp
            (Fin.cons (codeTm H) v))
        = codeTm (barSpine τs H v)
      have hctx : (fun j => ((Fin.cons
              (spineHeadER a (τs 0) (omegaCurried fun i => τs i.succ))
              (fun j : Fin a => ERMor1.proj j.succ.succ) :
                Fin (a + 1) → ERMor1 (a + 2)) j).interp
            (Fin.cons (codeTm H) v))
          = Fin.cons
              (codeTm (OneLambda.app' H (bbRep (natToFreeAlg (v 0)) (barTy (τs 0)))))
              (fun i => v i.succ) := by
        funext j
        refine Fin.cases ?_ (fun k => ?_) j
        · simp only [Fin.cons_zero]
          rw [spineHeadER_interp, codeBbRep_codeTm]
          exact (codeTm_app' H _).symm
        · simp only [Fin.cons_succ, ERMor1.interp_proj]
      rw [hctx]
      exact spineCodeER_codeTm (fun i => τs i.succ)
        (OneLambda.app' H (bbRep (natToFreeAlg (v 0)) (barTy (τs 0)))) fun i => v i.succ

/-- The code of the `a`-ary applied bar-image term as an elementary-recursive
morphism (spec §6.4; N6; plan decision P4): the spine-code fold `spineCodeER` fed
the closed head constant `codeTm (barHead F)` and the input slots. Novel
realization. -/
private def buildCodeN {a : ℕ} {τs : Fin a → RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) []
      (RType.curried (List.ofFn fun i => RType.omega (τs i)) RType.o)) :
    ERMor1 a :=
  ERMor1.comp (spineCodeER τs)
    (Fin.cons (ERMor1.natN a (codeTm (barHead F))) fun i : Fin a => ERMor1.proj i)

/-- Interpretation of `buildCodeN`: the code of the `a`-ary applied bar-image term,
`codeTm (barSpine τs (barHead F) v)`, unconditionally on every input tuple. -/
private theorem buildCodeN_interp {a : ℕ} {τs : Fin a → RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) []
      (RType.curried (List.ofFn fun i => RType.omega (τs i)) RType.o))
    (v : Fin a → ℕ) :
    (buildCodeN F).interp v = codeTm (barSpine τs (barHead F) v) := by
  unfold buildCodeN
  rw [ERMor1.interp_comp]
  have hctx : (fun j : Fin (a + 1) =>
        ((Fin.cons (ERMor1.natN a (codeTm (barHead F)))
            (fun i : Fin a => ERMor1.proj i) : Fin (a + 1) → ERMor1 a) j).interp v)
      = Fin.cons (codeTm (barHead F)) v := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [Fin.cons_zero, ERMor1.interp_natN]
    · simp only [Fin.cons_succ, ERMor1.interp_proj]
  rw [hctx, spineCodeER_codeTm]

/-- The uniform rank ceiling of the fixed `a`-ary function term (Proposition 13's
`qF` at `a` inputs, Leivant III section 5, p. 226): the redex rank of the bar-image
head together with the order of the head's arrow sort, a constant of `F`. -/
private def rankCeilN {a : ℕ} {τs : Fin a → RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) []
      (RType.curried (List.ofFn fun i => RType.omega (τs i)) RType.o)) : ℕ :=
  max (redexRank (barHead F)) (max 1 (RType.ord (barTy (omegaCurried τs))))

/-- The height ceiling of the fixed `a`-ary function term: the head height plus the
spine offset, a constant of `F`. At input tuple `v` the spine height never exceeds
`heightCeilN F + ∑ i, v i`. -/
private def heightCeilN {a : ℕ} {τs : Fin a → RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) []
      (RType.curried (List.ofFn fun i => RType.omega (τs i)) RType.o)) : ℕ :=
  Tm.height (barHead F) + spineOffset τs

/-- The size ceiling of the fixed `a`-ary function term: the head size plus the
spine offset, a constant of `F`. At input tuple `v` the spine size never exceeds
`sizeCeilN F + 2 * ∑ i, v i`. -/
private def sizeCeilN {a : ℕ} {τs : Fin a → RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) []
      (RType.curried (List.ofFn fun i => RType.omega (τs i)) RType.o)) : ℕ :=
  Tm.size (barHead F) + spineOffset τs

/-- The sort-payload ceiling of the fixed `a`-ary function term: the head payload
plus the spine payload, a constant of `F` dominating the spine payload uniformly in
the input tuple. -/
private def payloadCeilN {a : ℕ} {τs : Fin a → RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) []
      (RType.curried (List.ofFn fun i => RType.omega (τs i)) RType.o)) : ℕ :=
  sortPayload (barHead F) + spinePayload τs

/-- The deterministic Lemma 12 clock of the `a`-ary bar spine is dominated by the
Lemma 12 clock at the per-`F` ceilings, with the input sum in the tower argument
(spec §6.3, the common-clock sum domination): the rank ceiling enters the
coefficient and the tower height, the height ceiling and the input sum the tower
argument. -/
private theorem detClock_barSpine_le {a : ℕ} {τs : Fin a → RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) []
      (RType.curried (List.ofFn fun i => RType.omega (τs i)) RType.o))
    (v : Fin a → ℕ) :
    (redexRank (barSpine τs (barHead F) v) + 1)
      * tower (redexRank (barSpine τs (barHead F) v) + 1)
        (Tm.height (barSpine τs (barHead F) v))
      ≤ (rankCeilN F + 1) * tower (rankCeilN F + 1) (heightCeilN F + ∑ i, v i) := by
  have hr : redexRank (barSpine τs (barHead F) v) ≤ rankCeilN F :=
    redexRank_barSpine_le τs (barHead F) v
  have hh : Tm.height (barSpine τs (barHead F) v) ≤ heightCeilN F + ∑ i, v i := by
    have := height_barSpine_le τs (barHead F) v
    unfold heightCeilN
    omega
  exact Nat.mul_le_mul (Nat.add_le_add_right hr 1)
    (le_trans (tower_mono_left (Nat.add_le_add_right hr 1) _) (tower_mono_right _ hh))

/-- The in-system clock of the fixed `a`-ary function term (spec §6.3; N6): the
elementary-recursive composite computing
`(rankCeilN F + 1) * tower (rankCeilN F + 1) (heightCeilN F + ∑ i, v i)`, the
Lemma 12 clock at the per-`F` ceilings over the staggered input sum
(`ERMor1.sumCtxER`, the sum-domination form of spec §6.3). Novel realization. -/
private def clockERN {a : ℕ} {τs : Fin a → RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) []
      (RType.curried (List.ofFn fun i => RType.omega (τs i)) RType.o)) :
    ERMor1 a :=
  ERMor1.comp ERMor1.mulN (fun i => match i with
    | ⟨0, _⟩ => ERMor1.natN a (rankCeilN F + 1)
    | ⟨1, _⟩ => ERMor1.comp (ERMor1.towerER (rankCeilN F + 1)) (fun _ : Fin 1 =>
        ERMor1.comp ERMor1.addN (fun j => match j with
          | ⟨0, _⟩ => ERMor1.natN a (heightCeilN F)
          | ⟨1, _⟩ => ERMor1.sumCtxER a)))

/-- Interpretation of `clockERN`: the Lemma 12 clock at the per-`F` ceilings over
the input sum, `(rankCeilN F + 1) * tower (rankCeilN F + 1) (heightCeilN F + ∑ i, v i)`. -/
private theorem clockERN_interp {a : ℕ} {τs : Fin a → RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) []
      (RType.curried (List.ofFn fun i => RType.omega (τs i)) RType.o))
    (v : Fin a → ℕ) :
    (clockERN F).interp v
      = (rankCeilN F + 1) * tower (rankCeilN F + 1) (heightCeilN F + ∑ i, v i) := by
  simp only [clockERN, ERMor1.interp_comp, ERMor1.interp_mulN, ERMor1.interp_towerER,
    ERMor1.interp_addN, ERMor1.interp_natN, ERMor1.interp_sumCtxER]

/-- The in-system budget of the fixed `a`-ary function term (spec §6.3; ratified
correction to Task 6.4.14: the budget slot of `normRun` is a genuine input): the
elementary-recursive composite computing the chain ceiling `codeCeil` at the
per-`F` size, payload, rank, and height ceilings over the input sum — a `towerER 2`
composite whose exponent is the in-system clock `clockERN F`. Novel realization. -/
private def budgetERN {a : ℕ} {τs : Fin a → RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) []
      (RType.curried (List.ofFn fun i => RType.omega (τs i)) RType.o)) :
    ERMor1 a :=
  ERMor1.comp (ERMor1.towerER 2) (fun _ : Fin 1 =>
    ERMor1.comp ERMor1.mulN (fun s => match s with
      | ⟨0, _⟩ => ERMor1.natN a 6
      | ⟨1, _⟩ => ERMor1.comp ERMor1.addN (fun t => match t with
          | ⟨0, _⟩ => ERMor1.comp ERMor1.addN (fun u => match u with
              | ⟨0, _⟩ => ERMor1.comp ERMor1.mulN (fun w => match w with
                  | ⟨0, _⟩ => ERMor1.natN a 2
                  | ⟨1, _⟩ => ERMor1.comp ERMor1.powN (fun x => match x with
                      | ⟨0, _⟩ => ERMor1.comp ERMor1.addN (fun y => match y with
                          | ⟨0, _⟩ => ERMor1.natN a (sizeCeilN F)
                          | ⟨1, _⟩ => ERMor1.comp ERMor1.mulN (fun z => match z with
                              | ⟨0, _⟩ => ERMor1.natN a 2
                              | ⟨1, _⟩ => ERMor1.sumCtxER a))
                      | ⟨1, _⟩ => ERMor1.comp ERMor1.powN (fun p => match p with
                          | ⟨0, _⟩ => ERMor1.natN a 2
                          | ⟨1, _⟩ => clockERN F)))
              | ⟨1, _⟩ => ERMor1.natN a (payloadCeilN F))
          | ⟨1, _⟩ => ERMor1.natN a 1)))

/-- Interpretation of `budgetERN`: the chain-ceiling shape at the per-`F` ceilings
over the input sum, a height-`2` tower over
`6 * (2 * (sizeCeilN F + 2 * ∑ i, v i) ^ 2 ^ clock + payloadCeilN F + 1)` with
`clock` the Lemma 12 clock of `clockERN_interp`. -/
private theorem budgetERN_interp {a : ℕ} {τs : Fin a → RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) []
      (RType.curried (List.ofFn fun i => RType.omega (τs i)) RType.o))
    (v : Fin a → ℕ) :
    (budgetERN F).interp v
      = tower 2 (6 * (2 * (sizeCeilN F + 2 * ∑ i, v i)
          ^ 2 ^ ((rankCeilN F + 1) * tower (rankCeilN F + 1) (heightCeilN F + ∑ i, v i))
          + payloadCeilN F + 1)) := by
  simp only [budgetERN, ERMor1.interp_comp, ERMor1.interp_towerER, ERMor1.interp_mulN,
    ERMor1.interp_addN, ERMor1.interp_powN, ERMor1.interp_natN, ERMor1.interp_sumCtxER,
    clockERN_interp]

/-- The in-system budget dominates the deterministic chain ceiling of the `a`-ary
bar spine: at every input tuple `v`, `codeCeil` of the applied spine is at most
`budgetERN F` evaluated at `v`, so the budget slot of `normRun` can be fed
in-system. Chains the per-`F` spine ceilings with `tower_mono_right` and power
monotonicity, the exponent bounded by `detClock_barSpine_le`. -/
private theorem budgetERN_dominates {a : ℕ} {τs : Fin a → RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) []
      (RType.curried (List.ofFn fun i => RType.omega (τs i)) RType.o))
    (v : Fin a → ℕ) :
    codeCeil (barSpine τs (barHead F) v) ≤ (budgetERN F).interp v := by
  rw [budgetERN_interp]
  unfold codeCeil detClock
  refine tower_mono_right 2 ?_
  have hs : Tm.size (barSpine τs (barHead F) v) ≤ sizeCeilN F + 2 * ∑ i, v i := by
    have := size_barSpine_le τs (barHead F) v
    unfold sizeCeilN
    omega
  have hp : sortPayload (barSpine τs (barHead F) v) ≤ payloadCeilN F := by
    have := sortPayload_barSpine_le τs (barHead F) v
    unfold payloadCeilN
    omega
  have hD := detClock_barSpine_le F v
  have hpow : Tm.size (barSpine τs (barHead F) v)
        ^ 2 ^ ((redexRank (barSpine τs (barHead F) v) + 1)
          * tower (redexRank (barSpine τs (barHead F) v) + 1)
            (Tm.height (barSpine τs (barHead F) v)))
      ≤ (sizeCeilN F + 2 * ∑ i, v i)
        ^ 2 ^ ((rankCeilN F + 1) * tower (rankCeilN F + 1) (heightCeilN F + ∑ i, v i)) := by
    refine le_trans (Nat.pow_le_pow_left hs _) (Nat.pow_le_pow_right ?_ ?_)
    · unfold sizeCeilN
      have := Tm.one_le_size (barHead F)
      omega
    · exact Nat.pow_le_pow_right (by omega) hD
  rw [show ([] : Binding.Ctx RType).length = 0 from rfl]
  omega

/-- The atomic collapse morphism at `a` shifted inputs (spec §6.4; plan decision
P4): decode ∘ clocked normalization ∘ build. The composite feeds the clocked
iteration `normRun` at the in-system clock `clockERN F`, the `a`-ary applied-term
code `buildCodeN F`, and the in-system budget `budgetERN F`, and reads the word
decoder `decodeWordER` off the resulting normal code — per fixed `F`, the whole of
Proposition 13's normalization pipeline at `a` inputs (Leivant III section 5,
p. 226, DOI `10.1016/S0168-0072(98)00040-2`) as one elementary-recursive morphism,
anchored denotationally by `collapseERN_interp`. The atomic builder for a single
codomain-`o` source morphism; per-component tupling into `ERMorN` morphism maps is
downstream scope (spec §6.4). Novel realization. -/
def collapseERN {a : ℕ} {τs : Fin a → RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) []
      (RType.curried (List.ofFn fun i => RType.omega (τs i)) RType.o)) :
    ERMorN a 1 :=
  fun _ => ERMor1.comp decodeWordER fun _ =>
    ERMor1.comp normRun ![clockERN F, buildCodeN F, budgetERN F]

/-- Adequacy of the `a`-ary collapse morphism against the denotational anchor
(spec §6.4; plan decision P4): at every input tuple the collapse computes the
numeric reading of the standard denotation of Proposition 13's `a`-ary applied term
(Leivant III section 5, p. 226) — `freeAlgToNat` of `appEval` at the source-side
application spine of `F` over the constructor words of the inputs. The fed code
slot reduces by `buildCodeN_interp`; the budget dominance
(`codeTm_detIter_le_codeCeil` chained through `budgetERN_dominates`) discharges
`normRun_interp_of_le`, landing the iterate's code by `stepCode_iterate_codeTm`;
the clock dominance (`detClock_barSpine_le`) absorbs the overshoot past the
Lemma 12 normal form (`detIter_normal`, `detIter_eq_of_normal`); the normal reduct
is identified with the value word by the Proposition 13 identification chain
(`normal_closed_o_eq_conc`, `oneEval_reduces`, `oneEval_conc` against the folded
arrow clause of `prop11_represents` through `represents_arrow` and `lemma9_omega`);
and the word decoder reads the value off its code (`decodeWord_codeTm_conc`). -/
theorem collapseERN_interp {a : ℕ} {τs : Fin a → RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) []
      (RType.curried (List.ofFn fun i => RType.omega (τs i)) RType.o))
    (v : Fin a → ℕ) :
    (collapseERN F).interp v = fun _ =>
      freeAlgToNat (appEval
        (sourceApps F (fun i => sourceWord (natToFreeAlg (v i)) (τs i)))
        finZeroElim) := by
  funext i
  set W : Binding.Tm (oneLambdaSig natAlgSig) [] RType.o :=
    barSpine τs (barHead F) v
  set L : ℕ := (redexRank W + 1) * tower (redexRank W + 1) (Tm.height W)
  -- The fed slots: the code slot is the applied spine's code, the clock slot
  -- dominates the Lemma 12 clock, and the budget slot dominates every trace value.
  have hcode : (buildCodeN F).interp v = codeTm W := buildCodeN_interp F v
  have hclk : L ≤ (clockERN F).interp v := by
    rw [clockERN_interp]
    exact detClock_barSpine_le F v
  have hbud : ∀ j, j ≤ (clockERN F).interp v →
      stepCode^[j] (codeTm W) ≤ (budgetERN F).interp v := by
    intro j _hj
    rw [stepCode_iterate_codeTm j W]
    exact le_trans (codeTm_detIter_le_codeCeil j W) (budgetERN_dominates F v)
  have hnorm : Normal (detIter L W) := detIter_normal W
  -- The identification chain of Proposition 13: the normal reduct is the value word.
  obtain ⟨b, hb⟩ := normal_closed_o_eq_conc (detIter L W) hnorm
  have hrep : Represents RType.o
      (sourceSpine τs ((omegaCurried_eq_curried τs).symm ▸ F)
        fun i => sourceWord (natToFreeAlg (v i)) (τs i)) W :=
    represents_barSpine τs _ (barHead F) (represents_head F) v
  have hred : Relation.ReflTransGen OneLambdaStep W
      (conc (appEval (sourceApps F fun i => sourceWord (natToFreeAlg (v i)) (τs i))
        finZeroElim)) := hrep
  have hval : b = appEval
      (sourceApps F fun i => sourceWord (natToFreeAlg (v i)) (τs i)) finZeroElim := by
    have h1 := oneEval_reduces (detIter_reduces L W) finZeroElim
    have h2 := oneEval_reduces hred finZeroElim
    rw [hb, oneEval_conc] at h1
    rw [oneEval_conc] at h2
    exact h1.symm.trans h2
  -- The composite unfolds to the decode of the clocked run at the fed slots.
  simp only [collapseERN, ERMorN.interp]
  rw [interp_comp_singleton, interp_comp_three, decodeWordER_interp, hcode,
    normRun_interp_of_le _ _ _ hbud, stepCode_iterate_codeTm _ W,
    detIter_eq_of_normal hclk hnorm, hb, decodeWord_codeTm_conc, hval]

/-! ### The K^sim landing corollary -/

/-- The K^sim landing of the collapse morphism (spec §6.5; plan decision D3): the
`ERMorN 1 1` collapse morphism `collapseER F` is realized by a multi-output K^sim
morphism, exhibited as the slotwise `erToK`-translation `erToKN (collapseER F)` and
interp-faithful on every input by `erToKN_interp`. This states the ⊇ direction of
the ER-to-K^sim bridge (Tourlakis 2018 §0.1.0.44, at the normalizer's output) as a
corollary through `erToK`, rather than shipping a `KMor1` normalizer definition
(spec §1.1 non-goal). Novel realization. -/
theorem collapseER_ksim_definable {τ : RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) []
      (RType.arrow (RType.omega τ) RType.o)) :
    ∃ g : KMorN 1 1, ∀ v, KMorN.interp g v = (collapseER F).interp v :=
  ⟨erToKN (collapseER F), fun v => funext fun i => erToKN_interp (collapseER F) v i⟩

end OneLambda

end GebLean.Ramified
