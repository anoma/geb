import GebLean.Ramified.Soundness.CodeNormalizer
import GebLean.Utilities.ERCourseOfValues
import GebLean.LawvereERBoundComputable

/-!
# Ramified recurrence: the code reads as ER morphisms

The elementary-recursive realization layer of the deterministic code normalizer
of the simply-typed calculus `1λ(natAlgSig)` (Leivant III section 4.2,
pp. 223-224). This module realizes the non-recursive reads of
`GebLean/Ramified/Soundness/CodeNormalizer.lean` — the sort-code projections and
the operation-node structure reads — as `ERMor1` morphisms whose interpretation
equals the mirrored ℕ-level function. Each read is a plain composition of the
elementary-recursive Gödel-arithmetic generators (`ERMor1.natUnpairFst`,
`ERMor1.natUnpairSnd`, `ERMor1.condN`, `ERMor1.boolEqNat`, `ERMor1.boolAnd`). The
type-order fold `OneLambda.ordER` — the first `ERMor1.cvRec` instantiation — and
the non-recursive top-β-rank read `OneLambda.topBetaRankER` composed from it are
realized here, together with the `con`-headedness and ι-spine detector folds
`OneLambda.conHeadedER`, `OneLambda.iotaSpineER`, the non-recursive sort-gated
ι-redex read `OneLambda.topIotaER`, the β-rank and ι-census folds
`OneLambda.betaRankER`, `OneLambda.hasIotaER`, and the ι worker
`OneLambda.iotaStepER` — the first fold that rebuilds nodes and carries a tower-2
majorant — are realized here; the remaining folds, the iterate, the
dispatch, and the assembled `normStep` are realized in later commits. Carrying the code reads
into the
elementary-recursive theory is
the formal payment of the machine-model absorption Leivant III leaves to a
footnote (footnote 10, p. 226). Novel realization.

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
    (fun j _ => ?_) (fun j hj => ?_) (fun i hi cand htrace => ?_)
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

/-- The operation-tag read on a code: the operation tag of an operation node
`Nat.pair 1 (Nat.pair op pack)`, the pairing of its kind bit and payload. The node
rebuild of the ι worker reuses it unchanged. -/
private def opTagCode (c : ℕ) : ℕ := (Nat.unpair (Nat.unpair c).2).1

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

end OneLambda

end GebLean.Ramified
