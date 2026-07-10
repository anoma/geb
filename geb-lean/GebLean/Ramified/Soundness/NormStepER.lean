import GebLean.Ramified.Soundness.CodeNormalizer
import GebLean.Utilities.ERCourseOfValues

/-!
# Ramified recurrence: the code reads as ER morphisms

The elementary-recursive realization layer of the deterministic code normalizer
of the simply-typed calculus `1λ(natAlgSig)` (Leivant III section 4.2,
pp. 223-224). This module realizes the non-recursive reads of
`GebLean/Ramified/Soundness/CodeNormalizer.lean` — the sort-code projections and
the operation-node structure reads — as `ERMor1` morphisms whose interpretation
equals the mirrored ℕ-level function. Each read is a plain composition of the
elementary-recursive Gödel-arithmetic generators (`ERMor1.natUnpairFst`,
`ERMor1.natUnpairSnd`, `ERMor1.condN`, `ERMor1.boolEqNat`, `ERMor1.boolAnd`); the
folds, the iterate, the dispatch, and the assembled `normStep` are realized in
later commits. Carrying the code reads into the elementary-recursive theory is
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

## Main statements

- `OneLambda.shapeER_interp` through `OneLambda.iotaContractER_interp` — each
  read's interpretation equals the mirrored ℕ-level function of
  `CodeNormalizer.lean`, `Bool.toNat`-valued for the Boolean-valued detector
  `isLamER`.

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

end OneLambda

end GebLean.Ramified
