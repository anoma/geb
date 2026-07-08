import GebLean.Ramified.Soundness.DetStep
import GebLean.Utilities.ComputationalComplexity
import Mathlib.Data.Nat.Pairing

/-!
# Ramified recurrence: sort and term codes

The Gödel coding of the ramified types (Leivant III section 2.3) as natural
numbers, opening the coding layer of the deterministic normalizer. `codeRType`
folds an r-type to a `Nat.pair`-nested numeral tagged by its top shape, and
`ordCode` reads the type order `RType.ord` directly off that numeral by strong
recursion on the code value, mirroring `RType.ord` without decoding.

`codeRType` is a three-shape fold: the base sort `o` codes to `Nat.pair 0 0`, an
arrow `σ → τ` to `Nat.pair 1 (Nat.pair (codeRType σ) (codeRType τ))`, and an
`Ω τ` to `Nat.pair 2 (codeRType τ)`. The leading `Nat.pair` component is the
shape tag, read back by `shapeCode`; the trailing components carry the child
codes, read back by `argCode` (the single child of an `Ω` code), and by
`domCode` and `codCode` (the domain and codomain codes of an arrow code).

`ordCode` recurses on the code by well-founded recursion: it dispatches on the
shape tag and recurses into the child codes, which the pairing inequalities
`OneLambda.self_lt_pair_one` and `OneLambda.self_lt_pair_two` place strictly
below the composite code. The mirror theorem `ordCode_codeRType` proves the two
routes agree: reading the order off the code equals computing it on the type.

The term layer codes the terms of the simply-typed calculus `1λ(natAlgSig)`
(Leivant III section 4.2). `codeOp` codes an operation as a kind bit `0`-`4`
paired with its payload (the domain and codomain sort codes of an `app` or
`lam`, the `Bool` label of a `con`, the position index of a `dstr`, or `0` for
`case`). `codeTm` folds a term to a `Nat.pair` numeral: a variable leaf codes to
`Nat.pair 0 x.1.val` (the de Bruijn index; the sort proof is not encoded) and an
operation node to `Nat.pair 1 (Nat.pair (codeOp o) childrenPack)`. The children
pack by `List.foldr Nat.pair 0` over `List.ofFn`, closed by a trailing `0`, so a
node's child codes are recoverable position-by-position by iterated
`Nat.unpair`. Each child code sits strictly below its node code: the child links
are the non-strict pairing bounds `Nat.left_le_pair`/`Nat.right_le_pair` through
the pack, and the strict step is `self_lt_pair_one` at the kind bit `1`. This is
the termination measure for the strong recursions on codes of the downstream
normalizer tasks.

## Main definitions

* `OneLambda.codeRType` — the Gödel code of an r-type: a shape-tagged
  `Nat.pair` numeral.
* `OneLambda.shapeCode` — the top shape tag of a code (`0` for `o`, `1` for an
  arrow, `2` for an `Ω`).
* `OneLambda.argCode` — the child code of an `Ω` code (the payload after the
  tag).
* `OneLambda.domCode`, `OneLambda.codCode` — the domain and codomain child codes
  of an arrow code.
* `OneLambda.ordCode` — the type order read off a code by strong recursion,
  mirroring `RType.ord`.
* `OneLambda.codeOp` — the Gödel code of an operation of `1λ(natAlgSig)`: a kind
  bit paired with the operation's payload.
* `OneLambda.codeTm` — the Gödel code of a term of `1λ(natAlgSig)`: a `Nat.pair`
  fold tagging variables by de Bruijn index and operation nodes by `codeOp` with
  the packed child codes.
* `OneLambda.codeConc` — the Gödel code of the concrete `o`-term of a numeral: a
  `Nat.rec` fold shadowing `codeTm ∘ conc ∘ natToFreeAlg`.
* `OneLambda.decodeWord` — the decoder reading a natural number back off the code
  of a constructor word by strong recursion on the code value.
* `OneLambda.codeLamWrap` — the numeric abstraction wrapper of
  `OneLambda.lamSpine`: a fold over the binder suffix layering `lam` nodes.
* `OneLambda.codeBbInner` — the Gödel code of the variable-headed spine of the
  Berarducci-Böhm representation of a numeral: a `Nat.rec` fold.
* `OneLambda.codeBbRep` — the Gödel code of the Berarducci-Böhm representation of a
  numeral: the fixed `codeLamWrap` prefix over `codeBbInner`.
* `OneLambda.tmOpMax` — the signature-generic maximal operation weight of a term
  under a per-operation weight `w`.
* `OneLambda.opPayload` — the sort-code payload of a single operation: an
  `app`/`lam` node's `max (codeRType σ) (codeRType τ)`, and `0` otherwise.
* `OneLambda.sortPayload` — the maximal sort-code payload in a term's op tags:
  `tmOpMax opPayload`.
* `OneLambda.detClock` — the deterministic Lemma-12 clock, the iteration count at
  which `detIter` reaches a `Normal` term.
* `OneLambda.codeCeil` — the deterministic-chain ceiling, a monotone tower
  expression in `Tm.size t`, `Tm.height t`, `sortPayload t`, and `Γ.length`.

## Main statements

* `OneLambda.codeRType_o`, `OneLambda.codeRType_arrow`,
  `OneLambda.codeRType_omega` — the node equations of the code fold.
* `OneLambda.shapeCode_codeRType_o`, `OneLambda.shapeCode_codeRType_arrow`,
  `OneLambda.shapeCode_codeRType_omega` — the shape tag on each code shape.
* `OneLambda.argCode_codeRType_omega`, `OneLambda.domCode_codeRType_arrow`,
  `OneLambda.codCode_codeRType_arrow` — the child-code reads on each code shape.
* `OneLambda.self_lt_pair_one`, `OneLambda.self_lt_pair_two` — the strict
  pairing steps `p < Nat.pair 1 p` and `p < Nat.pair 2 p` that bound the
  recursion of `ordCode`.
* `OneLambda.ordCode_pair_zero`, `OneLambda.ordCode_pair_one`,
  `OneLambda.ordCode_pair_two` — the dispatch unfoldings of `ordCode` at each
  code shape.
* `OneLambda.ordCode_codeRType` — the mirror theorem: `ordCode (codeRType σ) =
  RType.ord σ`.
* `OneLambda.codeTm_var`, `OneLambda.codeTm_op` — the leaf and generic
  operation-node equations of the code fold.
* `OneLambda.codeTm_app'`, `OneLambda.codeTm_lam'`, `OneLambda.codeTm_con`,
  `OneLambda.codeTm_dstr`, `OneLambda.codeTm_case` — the operation-node equations
  through the `1λ(natAlgSig)` combinators and constant formers.
* `OneLambda.codeTm_child_lt_app'_left`, `OneLambda.codeTm_child_lt_app'_right`,
  `OneLambda.codeTm_child_lt_lam'` — the strictness cluster: each subterm's code
  is strictly below its node's code, the termination measure for the strong
  recursions on codes of the downstream normalizer tasks.
* `OneLambda.codeConc_codeTm` — the numeric fold `codeConc` agrees with the code
  of the concrete term: `codeConc n = codeTm (conc (natToFreeAlg n))`.
* `OneLambda.decodeWord_codeTm_conc`, `OneLambda.decodeWord_codeConc` — the
  decoder inverts the constructor-word code: `decodeWord (codeTm (conc a)) =
  freeAlgToNat a` and `decodeWord (codeConc n) = n`.
* `OneLambda.codeTm_lamSpine` — the code of an iterated abstraction is
  `codeLamWrap` applied to the body code.
* `OneLambda.codeBbInner_codeTm`, `OneLambda.codeBbRep_codeTm` — the numeric folds
  agree with the codes: `codeBbInner τ n = codeTm (bbSpine (barTy τ) (natToFreeAlg
  n))` and `codeBbRep τ n = codeTm (bbRep (natToFreeAlg n) (barTy τ))`.
* `OneLambda.sortPayload_instantiate₁_le` — instantiation raises the sort payload
  by at most the substituted term's: `sortPayload (instantiate₁ e d) ≤
  max (sortPayload e) (sortPayload d)`.
* `OneLambda.sortPayload_detStep_le` — the deterministic step does not increase
  the sort payload: `sortPayload (detStep t) ≤ sortPayload t`.
* `OneLambda.codeOp_le_tower`, `OneLambda.pair_le_tower_two` — the operation-code
  and pairing bounds feeding the envelope.
* `OneLambda.codeTm_le_envelope` — the tower envelope: `codeTm t ≤
  tower 2 (6 * (2 * Tm.size t + sortPayload t + Γ.length + 1))`.
* `OneLambda.size_step_le`, `OneLambda.size_detIter_le_ceil` — the per-step size
  squaring and the `k`-uniform chain size ceiling.
* `OneLambda.codeTm_detIter_le_codeCeil` — the chain ceiling: `codeTm
  (detIter k t) ≤ codeCeil t`.

## Implementation notes

`codeRType` follows the measure-fold house pattern of `RType.ord`
(`GebLean/Ramified/Soundness/Normalization.lean`): the dependent eliminator
`PolyFix.ind` over `rTypeSig.polyEndo` (decision 8), with the three node
equations holding definitionally. `ordCode` is a well-founded recursion on the
code value; its child recursions are guarded by `self_lt_pair_one` and
`self_lt_pair_two`, which reconstruct the code as `Nat.pair tag payload`
(`Nat.pair_unpair`) and step strictly past the payload. This project's coding
layer pins the algebra signature at `natAlgSig`.

`codeTm` folds over the variable-augmented endofunctor
`polyTranslate varOver (oneLambdaSig natAlgSig).polyEndo`, following the
`PolyFix.ind` fold pattern of `Tm.size` (`GebLean/Binding/Measures.lean`). The
`childrenPack` convention is `List.foldr Nat.pair 0` over `List.ofFn` of the
child codes, one recorded realization of the brief's nullary-`0`, unary-`Nat.pair
c₀ 0`, binary-`Nat.pair c₀ (Nat.pair c₁ 0)` scheme: the trailing `0` terminator
makes every arity a right-nested `Nat.pair` list, so `codeTm_op`'s generic pack
specializes to each operation's node equation definitionally. The subterm
combinators `app'`/`lam'` transport their arguments across `Γ ++ [] = Γ`; the
node equations discharge that transport by `codeTm_appendNil`, the
single-transport specialization of `codeTm_cast`, matching the house pattern of
the `Normalization.lean` detector folds.

The word codes `codeConc`, `codeBbInner`, and `codeBbRep` are numeric `Nat.rec`
folds on the numeral, each proved to agree with its term code by induction on the
numeral through the landed node equations rather than by kernel reduction of the
`PolyFix` folds. `codeConc` and `codeBbInner` recurse on the numeral directly.
`codeBbRep` factors as the fixed abstraction wrapper `codeLamWrap` (a fold over
the constructor step types, depending on `τ` alone) over the numeral-recursive
spine code `codeBbInner`: the `lamSpine` prefix of `bbRep` is constant across the
numeral, so the recursion lives entirely in the variable-headed spine core, and
`codeTm_lamSpine` bridges the wrapper to `codeTm`. `decodeWord` is the strong
recursion inverting the constructor-word code, terminating by the same pairing
bounds and strict step `self_lt_pair_one` that guard `ordCode`.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher
type recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`, section 2.2 (p. 213): the
order of a simple type; section 2.3: the ramified types; section 4.2 (p. 223):
the operations and terms of the simply-typed calculus `1λ(A)`. The Gödel coding
of the r-types and the terms as `Nat.pair` numerals and the order read `ordCode`
are a novel realization; the underlying type and term conventions transcribe
Leivant III sections 2.3 and 4.2.

## Tags

ramified recurrence, ramified type, Gödel numbering, pairing function, type
order, well-founded recursion, term code
-/

namespace GebLean.Ramified

open GebLean.Binding

namespace OneLambda

/-- The Gödel code of an r-type (Leivant III section 2.3): the base sort `o`
codes to `Nat.pair 0 0`, an arrow `σ → τ` to `Nat.pair 1 (Nat.pair (codeRType
σ) (codeRType τ))`, and an `Ω τ` to `Nat.pair 2 (codeRType τ)`. The leading
`Nat.pair` component is the shape tag; the trailing components carry the child
codes. Realized by the dependent eliminator `PolyFix.ind` (decision 8),
following `RType.ord`'s fold pattern. Novel realization. -/
def codeRType (τ : RType) : ℕ :=
  PolyFix.ind (P := rTypeSig.polyEndo) (motive := fun {_} _ => ℕ)
    (fun i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ => Nat.pair 0 0
      | RTypeShape.arrow, _, ih =>
        Nat.pair 1
          (Nat.pair (ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)))
            (ih (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow))))
      | RTypeShape.omega, _, ih =>
        Nat.pair 2 (ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.omega)))) τ

@[simp] theorem codeRType_o : codeRType RType.o = Nat.pair 0 0 := rfl

@[simp] theorem codeRType_arrow (σ τ : RType) :
    codeRType (RType.arrow σ τ)
      = Nat.pair 1 (Nat.pair (codeRType σ) (codeRType τ)) := rfl

@[simp] theorem codeRType_omega (τ : RType) :
    codeRType (RType.omega τ) = Nat.pair 2 (codeRType τ) := rfl

/-- The top shape tag of a code: the leading `Nat.pair` component. On a
`codeRType` image it is `0` for `o`, `1` for an arrow, and `2` for an `Ω`. -/
def shapeCode (n : ℕ) : ℕ := (Nat.unpair n).1

/-- The child code carried after the shape tag: the trailing `Nat.pair`
component. On an `Ω` code it is the code of the child; on an arrow code it is
the pair of the domain and codomain codes. -/
def argCode (n : ℕ) : ℕ := (Nat.unpair n).2

/-- The domain child code of an arrow code: the first component of `argCode`. -/
def domCode (n : ℕ) : ℕ := (Nat.unpair (argCode n)).1

/-- The codomain child code of an arrow code: the second component of
`argCode`. -/
def codCode (n : ℕ) : ℕ := (Nat.unpair (argCode n)).2

theorem shapeCode_codeRType_o : shapeCode (codeRType RType.o) = 0 := by
  simp [shapeCode, Nat.unpair_pair]

theorem shapeCode_codeRType_arrow (σ τ : RType) :
    shapeCode (codeRType (RType.arrow σ τ)) = 1 := by
  simp [shapeCode, Nat.unpair_pair]

theorem shapeCode_codeRType_omega (τ : RType) :
    shapeCode (codeRType (RType.omega τ)) = 2 := by
  simp [shapeCode, Nat.unpair_pair]

theorem argCode_codeRType_omega (τ : RType) :
    argCode (codeRType (RType.omega τ)) = codeRType τ := by
  simp [argCode, Nat.unpair_pair]

theorem domCode_codeRType_arrow (σ τ : RType) :
    domCode (codeRType (RType.arrow σ τ)) = codeRType σ := by
  simp [domCode, argCode, Nat.unpair_pair]

theorem codCode_codeRType_arrow (σ τ : RType) :
    codCode (codeRType (RType.arrow σ τ)) = codeRType τ := by
  simp [codCode, argCode, Nat.unpair_pair]

/-- The strict pairing step past the shape tag `1`: `p < Nat.pair 1 p`. On the
`p ≤ 1` branch `Nat.pair 1 p = p + 2`; on the `1 < p` branch `Nat.pair 1 p =
p * p + 1 > p`. Bounds the arrow recursion of `ordCode`. -/
theorem self_lt_pair_one (p : ℕ) : p < Nat.pair 1 p := by
  rw [Nat.pair]
  split_ifs with h
  · have hp : p ≤ p * p := Nat.le_mul_of_pos_left p (by omega)
    omega
  · omega

/-- The strict pairing step past the shape tag `2`: `p < Nat.pair 2 p`. On the
`p ≤ 2` branch `Nat.pair 2 p = p + 6`; on the `2 < p` branch `Nat.pair 2 p =
p * p + 2 > p`. Bounds the `Ω` recursion of `ordCode`. -/
theorem self_lt_pair_two (p : ℕ) : p < Nat.pair 2 p := by
  rw [Nat.pair]
  split_ifs with h
  · have hp : p ≤ p * p := Nat.le_mul_of_pos_left p (by omega)
    omega
  · omega

/-- The type order read off a code (Leivant III section 2.2, p. 213): dispatch on
the shape tag `shapeCode n` and recurse into the child codes, mirroring
`RType.ord`. Shape `1` (arrow) reads `max (ordCode (domCode n) + 1) (ordCode
(codCode n))`; shape `2` (`Ω`) reads `ordCode (argCode n)`; every other tag reads
`0`. Well-founded on the code value: `self_lt_pair_one` and `self_lt_pair_two`
place the child codes strictly below the composite. Novel realization. -/
def ordCode (n : ℕ) : ℕ :=
  match h : (Nat.unpair n).1 with
  | 1 =>
    max (ordCode (Nat.unpair (Nat.unpair n).2).1 + 1)
      (ordCode (Nat.unpair (Nat.unpair n).2).2)
  | 2 => ordCode (Nat.unpair n).2
  | _ => 0
  termination_by n
  decreasing_by
    · have hlt : (Nat.unpair n).2 < n := by
        conv_rhs => rw [← Nat.pair_unpair n, h]
        exact self_lt_pair_one _
      exact Nat.lt_of_le_of_lt (Nat.unpair_left_le _) hlt
    · have hlt : (Nat.unpair n).2 < n := by
        conv_rhs => rw [← Nat.pair_unpair n, h]
        exact self_lt_pair_one _
      exact Nat.lt_of_le_of_lt (Nat.unpair_right_le _) hlt
    · conv_rhs => rw [← Nat.pair_unpair n, h]
      exact self_lt_pair_two _

/-- The dispatch unfolding of `ordCode` at a base-sort code `Nat.pair 0 0`. -/
theorem ordCode_pair_zero : ordCode (Nat.pair 0 0) = 0 := by
  rw [ordCode]
  split <;> simp_all [Nat.unpair_pair]

/-- The dispatch unfolding of `ordCode` at an arrow code `Nat.pair 1 (Nat.pair a
b)`: the shape-`1` branch reads the two child orders. -/
theorem ordCode_pair_one (a b : ℕ) :
    ordCode (Nat.pair 1 (Nat.pair a b)) = max (ordCode a + 1) (ordCode b) := by
  rw [ordCode]
  split <;> simp_all [Nat.unpair_pair]

/-- The dispatch unfolding of `ordCode` at an `Ω` code `Nat.pair 2 a`: the
shape-`2` branch reads the single child order. -/
theorem ordCode_pair_two (a : ℕ) : ordCode (Nat.pair 2 a) = ordCode a := by
  rw [ordCode]
  split <;> simp_all [Nat.unpair_pair]

/-- The mirror theorem (Leivant III section 2.2, p. 213): reading the type order
off a code agrees with computing it on the type, `ordCode (codeRType σ) =
RType.ord σ`. By structural induction on the r-type via `PolyFix.ind`, the node
equations of `codeRType` and `RType.ord` feeding the `ordCode` dispatch
unfoldings. Novel realization. -/
theorem ordCode_codeRType (σ : RType) : ordCode (codeRType σ) = RType.ord σ :=
  PolyFix.ind (P := rTypeSig.polyEndo)
    (motive := fun {_} t => ordCode (codeRType t) = RType.ord t)
    (fun i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ => ordCode_pair_zero
      | RTypeShape.arrow, childx, ih => by
        change ordCode (Nat.pair 1
            (Nat.pair (codeRType (childx (⟨0, by decide⟩ : Fin (rTypeSig.ar
                RTypeShape.arrow))))
              (codeRType (childx (⟨1, by decide⟩ : Fin (rTypeSig.ar
                RTypeShape.arrow)))))) = _
        rw [ordCode_pair_one,
          ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)),
          ih (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow))]
        rfl
      | RTypeShape.omega, childx, ih => by
        change ordCode (Nat.pair 2 (codeRType (childx (⟨0, by decide⟩ :
            Fin (rTypeSig.ar RTypeShape.omega))))) = _
        rw [ordCode_pair_two,
          ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.omega))]
        rfl) σ

/-- The Gödel code of an operation of `1λ(natAlgSig)` (Leivant III section 4.2):
a kind bit `0`-`4` paired with the operation's payload. An application `app σ τ`
codes to `Nat.pair 0 (Nat.pair (codeRType σ) (codeRType τ))` and an abstraction
`lam σ τ` to `Nat.pair 1 (Nat.pair (codeRType σ) (codeRType τ))`, carrying the
domain and codomain sort codes; a constructor constant `con b` codes to
`Nat.pair 2 (cond b 1 0)` (the `natAlgSig` label type is `Bool`); a destructor
`dstr j` to `Nat.pair 3 j.val` (the enumeration index of the destructed
position); and the case combinator to `Nat.pair 4 0`. `OneLambdaOp natAlgSig` is
a finite native enumeration, so a plain `match` suffices. Novel realization. -/
def codeOp : OneLambdaOp natAlgSig → ℕ
  | .app σ τ => Nat.pair 0 (Nat.pair (codeRType σ) (codeRType τ))
  | .lam σ τ => Nat.pair 1 (Nat.pair (codeRType σ) (codeRType τ))
  | .con b => Nat.pair 2 (cond b 1 0)
  | .dstr j => Nat.pair 3 j.val
  | .case => Nat.pair 4 0

/-- The Gödel code of a term of `1λ(natAlgSig)` (Leivant III section 4.2): a
variable leaf `x` codes to `Nat.pair 0 x.1.val`, tagging kind bit `0` with the de
Bruijn index (the variable's sort proof is not encoded); an operation node codes
to `Nat.pair 1 (Nat.pair (codeOp o) childrenPack)`, tagging kind bit `1` with the
operation code and the packed child codes. The children pack by
`List.foldr Nat.pair 0` over `List.ofFn`, so a nullary node packs to `0`, a unary
node with child code `c₀` to `Nat.pair c₀ 0`, and a binary node with child codes
`c₀, c₁` to `Nat.pair c₀ (Nat.pair c₁ 0)`. Realized by the dependent eliminator
`PolyFix.ind` (decision 8) over the variable-augmented endofunctor
`polyTranslate varOver (oneLambdaSig natAlgSig).polyEndo`, following the fold
pattern of `Tm.size` (`GebLean/Binding/Measures.lean`). Novel realization. -/
def codeTm {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) : ℕ :=
  PolyFix.ind (P := polyTranslate Binding.varOver (oneLambdaSig natAlgSig).polyEndo)
    (motive := fun {_} _ => ℕ)
    (fun i children ih =>
      match i, children, ih with
      | Sum.inl a, _, _ => Nat.pair 0 (Binding.leafVar a).1.val
      | Sum.inr p, _, ih =>
        Nat.pair 1 (Nat.pair (codeOp p.val)
          (List.foldr Nat.pair 0
            (List.ofFn (fun j : Fin ((oneLambdaSig natAlgSig).args p.val).length => ih ⟨j⟩))))) t

/-- The code of a variable term is the kind bit `0` paired with the de Bruijn
index. -/
@[simp] theorem codeTm_var {Γ : Binding.Ctx RType} {s : RType} (x : Binding.Var Γ s) :
    codeTm (Binding.Tm.var x) = Nat.pair 0 x.1.val := by
  obtain ⟨i, hi⟩ := x; subst hi; rfl

/-- The code of an operation node is the kind bit `1` paired with the operation
code and the children pack `List.foldr Nat.pair 0` over the fold's child codes.
The generic node equation the per-operation combinator equations specialize. -/
theorem codeTm_op {Γ : Binding.Ctx RType} (o : OneLambdaOp natAlgSig)
    (args : ∀ j : Fin ((oneLambdaSig natAlgSig).args o).length,
      Binding.Tm (oneLambdaSig natAlgSig) (Γ ++ (((oneLambdaSig natAlgSig).args o).get j).1)
        (((oneLambdaSig natAlgSig).args o).get j).2) :
    codeTm (Binding.Tm.op o args)
      = Nat.pair 1 (Nat.pair (codeOp o)
          (List.foldr Nat.pair 0 (List.ofFn (fun j => codeTm (args j))))) := rfl

/-- The code is invariant under transport of the context and sort indices. -/
theorem codeTm_cast {Γ Γ' : Binding.Ctx RType} {s s' : RType}
    (hΓ : Γ = Γ') (hs : s = s') (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    codeTm (hs ▸ hΓ ▸ t) = codeTm t := by subst hΓ; subst hs; rfl

/-- The code ignores the `Γ ++ [] = Γ` transport that `app'` applies to its
subterms. -/
private theorem codeTm_appendNil {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    codeTm ((List.append_nil Γ).symm ▸ t) = codeTm t :=
  codeTm_cast (List.append_nil Γ).symm rfl t

/-- The code of an application node `app' f x`: the kind bit `1`, the `app`
operation code, and the two child codes packed binary (`codeTm f` then
`codeTm x`), discharging the `Γ ++ [] = Γ` transports of `app'` by
`codeTm_appendNil`. -/
@[simp] theorem codeTm_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig natAlgSig) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig natAlgSig) Γ σ) :
    codeTm (app' f x)
      = Nat.pair 1 (Nat.pair (codeOp (OneLambdaOp.app σ τ))
          (Nat.pair (codeTm f) (Nat.pair (codeTm x) 0))) := by
  refine (codeTm_op (Γ := Γ) (OneLambdaOp.app σ τ)
    (fun j => Fin.cases ((List.append_nil Γ).symm ▸ f)
      (fun k => Fin.cases ((List.append_nil Γ).symm ▸ x) (fun l => l.elim0) k) j)).trans ?_
  change Nat.pair 1 (Nat.pair (codeOp (OneLambdaOp.app σ τ))
    (Nat.pair (codeTm ((List.append_nil Γ).symm ▸ f))
      (Nat.pair (codeTm ((List.append_nil Γ).symm ▸ x)) 0))) = _
  rw [codeTm_appendNil, codeTm_appendNil]

/-- The code of an abstraction node `lam' b`: the kind bit `1`, the `lam`
operation code, and the sole body child code packed unary (`codeTm b`). The
body lives in `Γ ++ [σ]`, so no transport is required. -/
@[simp] theorem codeTm_lam' {Γ : Binding.Ctx RType} {σ τ : RType}
    (b : Binding.Tm (oneLambdaSig natAlgSig) (Γ ++ [σ]) τ) :
    codeTm (lam' b)
      = Nat.pair 1 (Nat.pair (codeOp (OneLambdaOp.lam σ τ)) (Nat.pair (codeTm b) 0)) := by
  refine (codeTm_op (Γ := Γ) (OneLambdaOp.lam σ τ)
    (fun j => Fin.cases b (fun k => k.elim0) j)).trans ?_
  rfl

/-- The code of a constructor constant `con b`: the kind bit `1`, the `con`
operation code, and the nullary children pack `0`. -/
@[simp] theorem codeTm_con {Γ : Binding.Ctx RType} (b : Bool) :
    codeTm (Binding.Tm.op (S := oneLambdaSig natAlgSig) (Γ := Γ) (OneLambdaOp.con b)
        (fun k => k.elim0))
      = Nat.pair 1 (Nat.pair (codeOp (OneLambdaOp.con b)) 0) := rfl

/-- The code of a destructor `dstr j`: the kind bit `1`, the `dstr` operation
code, and the nullary children pack `0`. -/
@[simp] theorem codeTm_dstr {Γ : Binding.Ctx RType} (j : Fin natAlgSig.maxArity) :
    codeTm (Binding.Tm.op (S := oneLambdaSig natAlgSig) (Γ := Γ) (OneLambdaOp.dstr j)
        (fun k => k.elim0))
      = Nat.pair 1 (Nat.pair (codeOp (OneLambdaOp.dstr j)) 0) := rfl

/-- The code of the case combinator: the kind bit `1`, the `case` operation
code, and the nullary children pack `0`. -/
@[simp] theorem codeTm_case {Γ : Binding.Ctx RType} :
    codeTm (Binding.Tm.op (S := oneLambdaSig natAlgSig) (Γ := Γ) OneLambdaOp.case
        (fun k => k.elim0))
      = Nat.pair 1 (Nat.pair (codeOp OneLambdaOp.case) 0) := rfl

/-- The function child code sits strictly below the application-node code:
`codeTm f < codeTm (app' f x)`. The child links are the non-strict pairing
bounds `Nat.left_le_pair`/`Nat.right_le_pair` through the pack, and the strict
step is `self_lt_pair_one` at the kind bit `1`. The termination measure for a
strong recursion on codes descending into an application's function subterm. -/
theorem codeTm_child_lt_app'_left {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig natAlgSig) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig natAlgSig) Γ σ) :
    codeTm f < codeTm (app' f x) := by
  rw [codeTm_app']
  refine lt_of_le_of_lt (Nat.left_le_pair (codeTm f) (Nat.pair (codeTm x) 0)) ?_
  refine lt_of_le_of_lt (Nat.right_le_pair (codeOp (OneLambdaOp.app σ τ)) _) ?_
  exact self_lt_pair_one _

/-- The argument child code sits strictly below the application-node code:
`codeTm x < codeTm (app' f x)`. The termination measure for a strong recursion
on codes descending into an application's argument subterm. -/
theorem codeTm_child_lt_app'_right {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig natAlgSig) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig natAlgSig) Γ σ) :
    codeTm x < codeTm (app' f x) := by
  rw [codeTm_app']
  refine lt_of_le_of_lt (Nat.left_le_pair (codeTm x) 0) ?_
  refine lt_of_le_of_lt (Nat.right_le_pair (codeTm f) (Nat.pair (codeTm x) 0)) ?_
  refine lt_of_le_of_lt (Nat.right_le_pair (codeOp (OneLambdaOp.app σ τ)) _) ?_
  exact self_lt_pair_one _

/-- The body child code sits strictly below the abstraction-node code:
`codeTm b < codeTm (lam' b)`. The termination measure for a strong recursion on
codes descending into an abstraction's body subterm. -/
theorem codeTm_child_lt_lam' {Γ : Binding.Ctx RType} {σ τ : RType}
    (b : Binding.Tm (oneLambdaSig natAlgSig) (Γ ++ [σ]) τ) :
    codeTm b < codeTm (lam' b) := by
  rw [codeTm_lam']
  refine lt_of_le_of_lt (Nat.left_le_pair (codeTm b) 0) ?_
  refine lt_of_le_of_lt (Nat.right_le_pair (codeOp (OneLambdaOp.lam σ τ)) _) ?_
  exact self_lt_pair_one _

/-- The concrete `o`-term of the zero numeral is the nullary constructor constant
`con false`: `natToFreeAlg 0` is the `false`-node, whose concrete fold is the
constant with an empty spine. Holds definitionally through `conc_mk` and the
`replicateSpine` at arity `0`. -/
theorem conc_natToFreeAlg_zero :
    conc (natToFreeAlg 0)
      = Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.con false)
          (fun k => k.elim0) := rfl

/-- The concrete `o`-term of the successor numeral wraps the predecessor's
concrete term in one application of the unary constructor constant `con true`:
`natToFreeAlg (n + 1)` is the `true`-node over `natToFreeAlg n`, whose concrete
fold applies `con true` along the arity-`1` spine. Holds definitionally through
`conc_mk` and the `replicateSpine` at arity `1`. -/
theorem conc_natToFreeAlg_succ (n : ℕ) :
    conc (natToFreeAlg (n + 1))
      = app'
          (Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.con true)
            (fun k => k.elim0))
          (conc (natToFreeAlg n)) := rfl

/-- The Gödel code of the concrete `o`-term of a numeral (Leivant III section 4.2):
a plain `Nat.rec` fold on `n` mirroring the constructor-word structure of
`conc (natToFreeAlg n)`. The zero numeral codes to the `con false` node
`Nat.pair 1 (Nat.pair (codeOp (con false)) 0)`; the successor numeral codes to
one `app`-of-`con true` layer over the predecessor code, matching `codeTm_app'`
and `codeTm_con`. The numeric shadow of `codeTm ∘ conc ∘ natToFreeAlg`. Novel
realization. -/
def codeConc : ℕ → ℕ
  | 0 => Nat.pair 1 (Nat.pair (codeOp (OneLambdaOp.con false)) 0)
  | n + 1 =>
      Nat.pair 1 (Nat.pair (codeOp (OneLambdaOp.app RType.o RType.o))
        (Nat.pair (Nat.pair 1 (Nat.pair (codeOp (OneLambdaOp.con true)) 0))
          (Nat.pair (codeConc n) 0)))

/-- The numeric fold `codeConc` agrees with the code of the concrete term
(Leivant III section 4.2): `codeConc n = codeTm (conc (natToFreeAlg n))`. By
induction on `n`, the constructor-word reductions `conc_natToFreeAlg_zero` and
`conc_natToFreeAlg_succ` feeding the node equations `codeTm_con` and
`codeTm_app'`. Novel realization. -/
theorem codeConc_codeTm (n : ℕ) : codeConc n = codeTm (conc (natToFreeAlg n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := codeTm_app' (Γ := [])
      (Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.con true) (fun k => k.elim0))
      (conc (natToFreeAlg n))
    rw [← ih] at h
    exact h.symm

/-- Reading a natural number back off the code of a constructor word (Leivant III
section 4.2): strong recursion on the code value. A code `Nat.pair 1 (Nat.pair op
pack)` is an operation node; when `op` codes an application (`(Nat.unpair op).1 =
0`) the word is a successor and the recursion reads the argument child, the second
entry of the binary pack, adding one; every other operation head — in a
well-formed constructor word, the nullary `con false` — is the zero word.
Don't-care on non-word codes. Well-founded on the code value: the argument child
sits strictly below the node through the pairing bounds
`Nat.unpair_left_le`/`Nat.unpair_right_le` and the strict step `self_lt_pair_one`
past the outer kind bit. Novel realization. -/
def decodeWord (n : ℕ) : ℕ :=
  match h : (Nat.unpair n).1, (Nat.unpair (Nat.unpair (Nat.unpair n).2).1).1 with
  | 1, 0 => decodeWord (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair n).2).2).2).1 + 1
  | _, _ => 0
  termination_by n
  decreasing_by
    have hlt : (Nat.unpair n).2 < n := by
      conv_rhs => rw [← Nat.pair_unpair n, h]
      exact self_lt_pair_one _
    exact Nat.lt_of_le_of_lt
      (le_trans (Nat.unpair_left_le _)
        (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _))) hlt

/-- The dispatch unfolding of `decodeWord` at an operation node whose operation
head is not an application (`(Nat.unpair op).1 ≠ 0`): the zero word. Covers the
`con`-headed node of a constructor word. -/
theorem decodeWord_nonApp (op pack : ℕ) (hop : (Nat.unpair op).1 ≠ 0) :
    decodeWord (Nat.pair 1 (Nat.pair op pack)) = 0 := by
  rw [decodeWord]; split <;> simp_all [Nat.unpair_pair]

/-- The dispatch unfolding of `decodeWord` at an application node
(`(Nat.unpair op).1 = 0`): one more than the decoding of the argument child, the
second entry of the binary children pack. -/
theorem decodeWord_app (op head child : ℕ) (hop : (Nat.unpair op).1 = 0) :
    decodeWord (Nat.pair 1 (Nat.pair op (Nat.pair head (Nat.pair child 0))))
      = decodeWord child + 1 := by
  rw [decodeWord]; split <;> simp_all [Nat.unpair_pair]

/-- The decoder inverts the code of the concrete term (Leivant III section 4.2):
`decodeWord (codeTm (conc a)) = freeAlgToNat a`. By recurrence-structural
induction on `a` via `PolyFix.ind`: at a `false` node the concrete term is the
nullary `con false`, decoded to `0`; at a `true` node it is `con true` applied to
the predecessor's concrete term, decoded to one more than the child's decoding
(the induction hypothesis), matching `freeAlgToNat`'s node reductions. Novel
realization. -/
theorem decodeWord_codeTm_conc (a : FreeAlg natAlgSig) :
    decodeWord (codeTm (conc a)) = freeAlgToNat a := by
  refine PolyFix.ind (P := natAlgSig.polyEndo)
    (motive := fun {_} a => decodeWord (codeTm (conc a)) = freeAlgToNat a)
    (fun b children ih => ?_) a
  change decodeWord (codeTm (conc (FreeAlg.mk b children)))
    = freeAlgToNat (FreeAlg.mk b children)
  cases b with
  | false =>
    exact decodeWord_nonApp (codeOp (OneLambdaOp.con false)) 0
      (by simp [codeOp, Nat.unpair_pair])
  | true =>
    have h := codeTm_app' (Γ := [])
      (Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.con true) (fun k => k.elim0))
      (conc (children ⟨0, Nat.zero_lt_one⟩))
    have hcode : codeTm (conc (FreeAlg.mk (A := natAlgSig) true children))
        = codeTm (app'
            (Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.con true)
              (fun k => k.elim0))
            (conc (children ⟨0, Nat.zero_lt_one⟩))) := rfl
    rw [hcode, h, decodeWord_app _ _ _ (by simp [codeOp, Nat.unpair_pair]),
      ih ⟨0, Nat.zero_lt_one⟩]
    rfl

/-- The decoder inverts the numeric fold `codeConc`: `decodeWord (codeConc n) =
n`. By induction on `n`, the zero code decoded through `decodeWord_nonApp` and the
successor code through `decodeWord_app`, the child being the predecessor code
resolved by the induction hypothesis. Novel realization. -/
theorem decodeWord_codeConc (n : ℕ) : decodeWord (codeConc n) = n := by
  induction n with
  | zero =>
    exact decodeWord_nonApp (codeOp (OneLambdaOp.con false)) 0
      (by simp [codeOp, Nat.unpair_pair])
  | succ n ih =>
    change decodeWord (Nat.pair 1 (Nat.pair (codeOp (OneLambdaOp.app RType.o RType.o))
        (Nat.pair (Nat.pair 1 (Nat.pair (codeOp (OneLambdaOp.con true)) 0))
          (Nat.pair (codeConc n) 0)))) = n + 1
    rw [decodeWord_app _ _ _ (by simp [codeOp, Nat.unpair_pair]), ih]

/-- The code is invariant under a context transport realized as `cast` of a
`congrArg` on the term type, the form the iterated abstraction `lamSpine` emits.
The `cast`-shaped counterpart of `codeTm_cast`. -/
private theorem codeTm_castCtx {Γ Γ' : Binding.Ctx RType} {τ : RType} (h : Γ = Γ')
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ τ) :
    codeTm (cast (congrArg (fun c => Binding.Tm (oneLambdaSig natAlgSig) c τ) h) t)
      = codeTm t := by
  cases h; rfl

/-- The Gödel code of an iterated abstraction over a binder suffix `Δ` at result
sort `result`, as a fold over `Δ` wrapping the code of a body: each context sort
`ξ` contributes one `lam`-node layer `Nat.pair 1 (Nat.pair (codeOp (lam ξ (curried
Δ' result))) (Nat.pair · 0))`, the empty suffix passing the body code through. The
numeric wrapper of `OneLambda.lamSpine`, computed by `codeTm_lamSpine`. -/
def codeLamWrap (result : RType) : List RType → ℕ → ℕ
  | [], c => c
  | ξ :: Δ', c =>
      Nat.pair 1 (Nat.pair (codeOp (OneLambdaOp.lam ξ (RType.curried Δ' result)))
        (Nat.pair (codeLamWrap result Δ' c) 0))

/-- The code of an iterated abstraction is the wrapper `codeLamWrap` applied to the
code of the body: `codeTm (lamSpine Δ body) = codeLamWrap result Δ (codeTm body)`.
By induction on the binder suffix `Δ`, peeling one `lam'` layer at a time
(`codeTm_lam'`) and discharging the binder-associativity transports by
`codeTm_castCtx`. -/
theorem codeTm_lamSpine :
    {Γ : Binding.Ctx RType} → {result : RType} → (Δ : List RType) →
    (body : Binding.Tm (oneLambdaSig natAlgSig) (Γ ++ Δ) result) →
    codeTm (OneLambda.lamSpine Δ body) = codeLamWrap result Δ (codeTm body)
  | Γ, _result, [], body => by
      rw [OneLambda.lamSpine]; exact codeTm_castCtx (List.append_nil Γ) body
  | Γ, result, ξ :: Δ', body => by
      refine (codeTm_lam' (Γ := Γ) (σ := ξ) (τ := RType.curried Δ' result) _).trans ?_
      rw [codeTm_lamSpine Δ', codeTm_castCtx (List.append_assoc Γ [ξ] Δ').symm body]; rfl

/-- The variable-headed application spine inside the Berarducci-Böhm
representation (Leivant III section 4.2): the free-algebra fold of `bbRep` at sort
`σ` before the outer `lamSpine`, replacing each constructor node by the bound
constructor variable `ctorVar b` saturated along the arity spine. Definitionally
the body that `bbRep a σ` abstracts. -/
private def bbSpine (σ : RType) (a : FreeAlg natAlgSig) :
    Binding.Tm (oneLambdaSig natAlgSig) (stepTypes natAlgSig σ σ) σ :=
  FreeAlg.recurse (A := natAlgSig) (P := Unit)
    (C := Binding.Tm (oneLambdaSig natAlgSig) (stepTypes natAlgSig σ σ) σ)
    (fun b _ _sub rec =>
      OneLambda.replicateSpine (natAlgSig.ar b) σ (Binding.Tm.var (ctorVar b)) rec) () a

/-- The Gödel code of the variable-headed spine `bbSpine (barTy τ)` of a numeral: a
`Nat.rec` fold shadowing `codeTm ∘ bbSpine (barTy τ) ∘ natToFreeAlg`. The zero
numeral codes to the bound constructor variable `ctorVar false`
(`Nat.pair 0 (ctorIdx false).val`); the successor numeral codes to one
`app`-of-`ctorVar true` layer over the predecessor code, matching `codeTm_app'`
and `codeTm_var`. Novel realization. -/
def codeBbInner (τ : RType) : ℕ → ℕ
  | 0 => Nat.pair 0 (ctorIdx false).val
  | m + 1 =>
      Nat.pair 1 (Nat.pair (codeOp (OneLambdaOp.app (barTy τ) (barTy τ)))
        (Nat.pair (Nat.pair 0 (ctorIdx true).val) (Nat.pair (codeBbInner τ m) 0)))

/-- The numeric fold `codeBbInner` agrees with the code of the variable-headed
spine: `codeBbInner τ n = codeTm (bbSpine (barTy τ) (natToFreeAlg n))`. By
induction on `n`, the `bbSpine` reductions feeding `codeTm_var` at the base and
`codeTm_app'` at the successor. Novel realization. -/
theorem codeBbInner_codeTm (τ : RType) (n : ℕ) :
    codeBbInner τ n = codeTm (bbSpine (barTy τ) (natToFreeAlg n)) := by
  induction n with
  | zero =>
    change codeBbInner τ 0 = codeTm (Binding.Tm.var (ctorVar (σ := barTy τ) false))
    rw [codeTm_var]; rfl
  | succ m ih =>
    have h := codeTm_app' (Γ := stepTypes natAlgSig (barTy τ) (barTy τ))
      (Binding.Tm.var (ctorVar (σ := barTy τ) true))
      (bbSpine (barTy τ) (natToFreeAlg m))
    rw [codeTm_var, ← ih] at h
    exact h.symm

/-- The Gödel code of the Berarducci-Böhm representation of a numeral at the barred
sort `barTy τ` (Leivant III section 4.2): the fixed abstraction wrapper
`codeLamWrap` over the constructor step types applied to the numeric spine code
`codeBbInner τ n`. The lambda-spine prefix is a function of `τ` alone, so the
recursion in `n` lives entirely in the variable-headed spine core. Novel
realization. -/
def codeBbRep (τ : RType) (n : ℕ) : ℕ :=
  codeLamWrap (barTy τ) (stepTypes natAlgSig (barTy τ) (barTy τ)) (codeBbInner τ n)

/-- The numeric fold `codeBbRep` agrees with the code of the Berarducci-Böhm
representation (Leivant III section 4.2): `codeBbRep τ n = codeTm (bbRep
(natToFreeAlg n) (barTy τ))`. The spine agreement `codeBbInner_codeTm` supplies the
body code, which `codeTm_lamSpine` wraps through the constructor abstraction of
`bbRep`. Novel realization. -/
theorem codeBbRep_codeTm (τ : RType) (n : ℕ) :
    codeBbRep τ n = codeTm (bbRep (natToFreeAlg n) (barTy τ)) := by
  rw [codeBbRep, codeBbInner_codeTm]
  exact (codeTm_lamSpine (Γ := []) (stepTypes natAlgSig (barTy τ) (barTy τ))
    (bbSpine (barTy τ) (natToFreeAlg n))).symm

/-! ### Sort-code payloads

The maximal `codeRType` payload carried by a term's operation tags, and its
stability along instantiation and the deterministic reduction step. The term
code `codeTm` embeds each `app`/`lam` node's domain and codomain sort codes;
`sortPayload` records the largest such code, so that the envelope bound
`codeTm_le_envelope` reads the sort contribution off a single measure. -/

/-- The maximal operation weight occurring in a term's operation tags, for an
arbitrary per-operation weight `w`: a variable leaf contributes `0`, and an
operation node contributes the maximum of its own weight `w o` and the weights of
its subterms. A signature-generic fold by the dependent eliminator `PolyFix.ind`
following the `max`-over-children pattern of `Tm.height`. -/
def tmOpMax {Ty : Type} {S : Binding.BinderSig Ty} (w : S.Op → ℕ) {Γ : Binding.Ctx Ty}
    {s : Ty} (t : Binding.Tm S Γ s) : ℕ :=
  PolyFix.ind (P := polyTranslate Binding.varOver S.polyEndo) (motive := fun {_} _ => ℕ)
    (fun i children ih =>
      match i, children, ih with
      | Sum.inl _, _, _ => 0
      | Sum.inr p, _, ih =>
        max (w p.val) (Finset.univ.sup fun j : Fin (S.args p.val).length => ih ⟨j⟩)) t

/-- The weight-max of a variable term is `0`. -/
@[simp] theorem tmOpMax_var {Ty : Type} {S : Binding.BinderSig Ty} (w : S.Op → ℕ)
    {Γ : Binding.Ctx Ty} {s : Ty} (x : Binding.Var Γ s) :
    tmOpMax w (Binding.Tm.var x) = 0 := by
  obtain ⟨i, hi⟩ := x; subst hi; rfl

/-- The weight-max of an operation node is the maximum of its own weight and the
weight-maxes of its subterms. -/
theorem tmOpMax_op {Ty : Type} {S : Binding.BinderSig Ty} (w : S.Op → ℕ) {Γ : Binding.Ctx Ty}
    (o : S.Op)
    (args : ∀ j : Fin (S.args o).length,
      Binding.Tm S (Γ ++ ((S.args o).get j).1) ((S.args o).get j).2) :
    tmOpMax w (Binding.Tm.op o args)
      = max (w o) (Finset.univ.sup fun j => tmOpMax w (args j)) := rfl

/-- The weight-max is invariant under transport of the context and sort
indices. -/
theorem tmOpMax_cast {Ty : Type} {S : Binding.BinderSig Ty} (w : S.Op → ℕ)
    {Γ Γ' : Binding.Ctx Ty} {s s' : Ty} (hΓ : Γ = Γ') (hs : s = s') (t : Binding.Tm S Γ s) :
    tmOpMax w (hs ▸ hΓ ▸ t) = tmOpMax w t := by subst hΓ; subst hs; rfl

/-- Renaming preserves the weight-max: a renaming is structure-preserving on the
operation tree. Signature-generic, following the `Tm.size_ren` induction. -/
@[simp] theorem tmOpMax_ren {Ty : Type} {S : Binding.BinderSig Ty} (w : S.Op → ℕ)
    {Γ Δ : Binding.Ctx Ty} {s : Ty} (ρ : Binding.Thinning Γ Δ) (t : Binding.Tm S Γ s) :
    tmOpMax w (Binding.ren ρ t) = tmOpMax w t := by
  suffices h : ∀ {y : Binding.Ctx Ty × Ty}
      (t : PolyFix (polyTranslate Binding.varOver S.polyEndo) y)
      {Δ : Binding.Ctx Ty} (ρ : Binding.Thinning y.1 Δ),
      tmOpMax w (Γ := Δ) (Binding.traverse (Binding.varKit S) (Binding.renEnv ρ) t)
        = tmOpMax w (Γ := y.1) (s := y.2) t from h t ρ
  intro y t
  induction t with
  | mk y idx children ih =>
    intro Δ ρ
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children : Binding.Tm S y.1 y.2)
            = Binding.Tm.var (Binding.leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      simp only [Binding.traverse_var, Binding.varKit, Binding.renEnv, tmOpMax_var]
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : S.Op // S.result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', S.result o) (Sum.inr ⟨o, rfl⟩) children
            : Binding.Tm S Γ' (S.result o))
            = Binding.Tm.op o (fun j => children ⟨j⟩) from rfl]
      rw [Binding.traverse_op, tmOpMax_op, tmOpMax_op]
      congr 1
      refine Finset.sup_congr rfl fun j _ => ?_
      rw [Binding.underBinder_renEnv]
      exact ih ⟨j⟩ (Binding.Thinning.appendId ρ _)

/-- The substitution bound on the weight-max: substituting along an environment
`σ` whose images all have weight-max at most `P` bounds it by `max (tmOpMax w t) P`.
Signature-generic, following the `Tm.size_sub_le` induction; the binder case's
fresh images are variables (weight-max `0`) and old images are renamings
(weight-max preserved). -/
theorem tmOpMax_sub_le {Ty : Type} {S : Binding.BinderSig Ty} (w : S.Op → ℕ)
    {Γ Δ : Binding.Ctx Ty} {s : Ty} (σ : Binding.Env (Binding.Tm S) Γ Δ) (t : Binding.Tm S Γ s)
    {P : ℕ} (hσ : ∀ u (x : Binding.Var Γ u), tmOpMax w (σ u x) ≤ P) :
    tmOpMax w (Binding.sub σ t) ≤ max (tmOpMax w t) P := by
  suffices h : ∀ {y : Binding.Ctx Ty × Ty}
      (t : PolyFix (polyTranslate Binding.varOver S.polyEndo) y)
      {Δ : Binding.Ctx Ty} (σ : Binding.Env (Binding.Tm S) y.1 Δ),
      (∀ u (x : Binding.Var y.1 u), tmOpMax w (σ u x) ≤ P) →
      tmOpMax w (Γ := Δ) (Binding.traverse (Binding.subKit S) σ t)
        ≤ max (tmOpMax w (Γ := y.1) (s := y.2) t) P from h t σ hσ
  intro y t
  induction t with
  | mk y idx children ih =>
    intro Δ σ hσ
    cases idx with
    | inl a =>
      rw [show (PolyFix.mk y (Sum.inl a) children : Binding.Tm S y.1 y.2)
            = Binding.Tm.var (Binding.leafVar a) from by
              obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
              congr 1
              funext e
              exact e.elim]
      rw [Binding.traverse_var, tmOpMax_var]
      simp only [Binding.subKit, id]
      exact le_trans (hσ y.2 (Binding.leafVar a)) (le_max_right _ _)
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : S.Op // S.result o = s' } at p
      revert children ih
      obtain ⟨o, rfl⟩ := p
      intro children ih
      rw [show (PolyFix.mk (Γ', S.result o) (Sum.inr ⟨o, rfl⟩) children
            : Binding.Tm S Γ' (S.result o))
            = Binding.Tm.op o (fun j => children ⟨j⟩) from rfl]
      simp only [Binding.traverse_op, tmOpMax_op]
      have hbound : ∀ j : Fin (S.args o).length,
          tmOpMax w (Binding.traverse (Binding.subKit S)
              (Binding.Env.underBinder (Binding.subKit S) σ) (children ⟨j⟩))
            ≤ max (tmOpMax w (children ⟨j⟩)) P := by
        intro j
        apply ih ⟨j⟩
        intro u x
        simp only [Binding.Env.underBinder, Binding.subKit]
        rw [Binding.Var.appendCases_natural (tmOpMax w)]
        apply Binding.Var.appendCases_le
        · intro y; rw [tmOpMax_var]; exact Nat.zero_le P
        · intro v; rw [tmOpMax_ren]; exact hσ u v
      refine max_le (le_max_of_le_left (le_max_left _ _)) (Finset.sup_le fun j _ => ?_)
      exact le_trans (hbound j)
        (max_le_max (le_trans
          (Finset.le_sup (f := fun k => tmOpMax w (children ⟨k⟩)) (Finset.mem_univ j))
          (le_max_right _ _)) (le_refl P))

/-- The sort-code payload of a single operation of `1λ(natAlgSig)`: an
application `app σ τ` or abstraction `lam σ τ` contributes the larger of its
domain and codomain sort codes `max (codeRType σ) (codeRType τ)`; the constructor
constants, destructors, and the case combinator carry no `codeRType` in their
tags and contribute `0`. -/
def opPayload : OneLambdaOp natAlgSig → ℕ
  | .app σ τ => max (codeRType σ) (codeRType τ)
  | .lam σ τ => max (codeRType σ) (codeRType τ)
  | _ => 0

/-- The maximal sort-code payload occurring in a term's operation tags: the
weight-max `tmOpMax` at the operation payload `opPayload`. A variable leaf
contributes `0`, and an operation node the maximum of its `opPayload` and the
payloads of its subterms. Novel realization. -/
def sortPayload {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) : ℕ :=
  tmOpMax opPayload t

/-- The sort payload of a variable term is `0`. -/
@[simp] theorem sortPayload_var {Γ : Binding.Ctx RType} {s : RType} (x : Binding.Var Γ s) :
    sortPayload (Binding.Tm.var x) = 0 := tmOpMax_var _ _

/-- The sort payload of an operation node is the maximum of its own `opPayload`
and the payloads of its subterms. -/
theorem sortPayload_op {Γ : Binding.Ctx RType} (o : OneLambdaOp natAlgSig)
    (args : ∀ j : Fin ((oneLambdaSig natAlgSig).args o).length,
      Binding.Tm (oneLambdaSig natAlgSig) (Γ ++ (((oneLambdaSig natAlgSig).args o).get j).1)
        (((oneLambdaSig natAlgSig).args o).get j).2) :
    sortPayload (Binding.Tm.op o args)
      = max (opPayload o) (Finset.univ.sup fun j => sortPayload (args j)) := rfl

/-- The sort payload is invariant under transport of the context and sort
indices. -/
theorem sortPayload_cast {Γ Γ' : Binding.Ctx RType} {s s' : RType}
    (hΓ : Γ = Γ') (hs : s = s') (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    sortPayload (hs ▸ hΓ ▸ t) = sortPayload t := tmOpMax_cast _ hΓ hs t

/-- The sort payload ignores the `Γ ++ [] = Γ` transport that `app'` applies to
its subterms. -/
private theorem sortPayload_appendNil {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    sortPayload ((List.append_nil Γ).symm ▸ t) = sortPayload t :=
  sortPayload_cast (List.append_nil Γ).symm rfl t

/-- The sort payload of an application node: the maximum of the `app` operation
payload and the payloads of the function and argument subterms. -/
@[simp] theorem sortPayload_app' {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig natAlgSig) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig natAlgSig) Γ σ) :
    sortPayload (app' f x)
      = max (opPayload (OneLambdaOp.app σ τ)) (max (sortPayload f) (sortPayload x)) := by
  refine (sortPayload_op (Γ := Γ) (OneLambdaOp.app σ τ)
    (fun j => Fin.cases ((List.append_nil Γ).symm ▸ f)
      (fun k => Fin.cases ((List.append_nil Γ).symm ▸ x) (fun l => l.elim0) k) j)).trans ?_
  change max (opPayload (OneLambdaOp.app σ τ)) ((Finset.univ : Finset (Fin 2)).sup _) = _
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from rfl, Finset.sup_insert,
    Finset.sup_singleton]
  change max (opPayload (OneLambdaOp.app σ τ))
    (sortPayload ((List.append_nil Γ).symm ▸ f) ⊔ sortPayload ((List.append_nil Γ).symm ▸ x)) = _
  rw [sortPayload_appendNil, sortPayload_appendNil]

/-- The sort payload of an abstraction node: the maximum of the `lam` operation
payload and the body subterm's payload. -/
@[simp] theorem sortPayload_lam' {Γ : Binding.Ctx RType} {σ τ : RType}
    (b : Binding.Tm (oneLambdaSig natAlgSig) (Γ ++ [σ]) τ) :
    sortPayload (lam' b) = max (opPayload (OneLambdaOp.lam σ τ)) (sortPayload b) := by
  refine (sortPayload_op (Γ := Γ) (OneLambdaOp.lam σ τ)
    (fun j => Fin.cases b (fun k => k.elim0) j)).trans ?_
  change max (opPayload (OneLambdaOp.lam σ τ)) ((Finset.univ : Finset (Fin 1)).sup _) = _
  rw [show (Finset.univ : Finset (Fin 1)) = {0} from rfl, Finset.sup_singleton]
  rfl

/-- The function subterm's payload is bounded by the application node's
payload. -/
theorem sortPayload_le_app'_left {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig natAlgSig) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig natAlgSig) Γ σ) :
    sortPayload f ≤ sortPayload (app' f x) := by
  rw [sortPayload_app']; exact le_max_of_le_right (le_max_left _ _)

/-- The argument subterm's payload is bounded by the application node's
payload. -/
theorem sortPayload_le_app'_right {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig natAlgSig) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig natAlgSig) Γ σ) :
    sortPayload x ≤ sortPayload (app' f x) := by
  rw [sortPayload_app']; exact le_max_of_le_right (le_max_right _ _)

/-- The body subterm's payload is bounded by the abstraction node's payload. -/
theorem sortPayload_le_lam' {Γ : Binding.Ctx RType} {σ τ : RType}
    (b : Binding.Tm (oneLambdaSig natAlgSig) (Γ ++ [σ]) τ) :
    sortPayload b ≤ sortPayload (lam' b) := by
  rw [sortPayload_lam']; exact le_max_right _ _

/-- Renaming along a thinning preserves the sort payload: a renaming is
structure-preserving on the operation tree, and `codeRType` reads only the sort
tags, not the variables. The `tmOpMax_ren` specialization at `opPayload`. -/
@[simp] theorem sortPayload_ren {Γ Δ : Binding.Ctx RType} {s : RType}
    (ρ : Binding.Thinning Γ Δ) (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    sortPayload (Binding.ren ρ t) = sortPayload t := tmOpMax_ren _ ρ t

/-- The substitution bound on the sort payload: substituting along an environment
`σ` whose images all have payload at most `P` bounds the payload by
`max (sortPayload t) P`. The `tmOpMax_sub_le` specialization at `opPayload`. -/
theorem sortPayload_sub_le {Γ Δ : Binding.Ctx RType} {s : RType}
    (σ : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) Γ Δ)
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) {P : ℕ}
    (hσ : ∀ u (x : Binding.Var Γ u), sortPayload (σ u x) ≤ P) :
    sortPayload (Binding.sub σ t) ≤ max (sortPayload t) P := tmOpMax_sub_le _ σ t hσ

/-- The single-variable substitution bound on the sort payload: instantiating the
sole bound variable of a body `d` by a term `e` bounds the payload by
`max (sortPayload e) (sortPayload d)`. The corollary of `sortPayload_sub_le` at
the instantiating environment, whose new image is `e` (payload `sortPayload e`)
and whose old images are variables (payload `0`). -/
theorem sortPayload_instantiate₁_le {Γ : Binding.Ctx RType} {a s : RType}
    (e : Binding.Tm (oneLambdaSig natAlgSig) Γ a)
    (d : Binding.Tm (oneLambdaSig natAlgSig) (Γ ++ [a]) s) :
    sortPayload (Binding.instantiate₁ e d) ≤ max (sortPayload e) (sortPayload d) := by
  unfold Binding.instantiate₁ Binding.instantiate
  refine le_trans (sortPayload_sub_le _ d (P := sortPayload e) ?_)
    (le_of_eq (max_comm (sortPayload d) (sortPayload e)))
  intro u x
  rw [Binding.extendEnv_apply, Binding.Var.appendCases_natural sortPayload]
  apply Binding.Var.appendCases_le
  · intro w
    obtain ⟨i, hi⟩ := w
    cases i using Fin.cases with
    | zero => exact le_of_eq (sortPayload_cast rfl hi e)
    | succ j => exact j.elim0
  · intro v
    simp only [Binding.idEnv, sortPayload_var]
    exact Nat.zero_le _

/-- Peeling the first argument of a homogeneous spine, the definitional
successor equation `replicateSpine (n + 1) = replicateSpine n` over the head
applied to the first argument. -/
private theorem replicateSpineCons {Γ : Binding.Ctx RType} {result : RType} (n : ℕ)
    (base : RType)
    (head : Binding.Tm (oneLambdaSig natAlgSig) Γ
      (RType.curried (List.replicate (n + 1) base) result))
    (a : Fin (n + 1) → Binding.Tm (oneLambdaSig natAlgSig) Γ base) :
    replicateSpine (n + 1) base head a
      = replicateSpine n base
          (app' (σ := base) (τ := RType.curried (List.replicate n base) result) head
            (a ⟨0, n.succ_pos⟩))
          (fun i => a i.succ) := rfl

/-- The head of a homogeneous spine has payload bounded by the spine's. -/
private theorem sortPayload_head_le_replicateSpine {Γ : Binding.Ctx RType} {result : RType} :
    (n : ℕ) → (base : RType) →
    (head : Binding.Tm (oneLambdaSig natAlgSig) Γ (RType.curried (List.replicate n base) result)) →
    (a : Fin n → Binding.Tm (oneLambdaSig natAlgSig) Γ base) →
    sortPayload head ≤ sortPayload (replicateSpine n base head a)
  | 0, _base, _head, _a => le_refl _
  | n + 1, base, head, a => by
      rw [replicateSpineCons]
      exact le_trans (sortPayload_le_app'_left head (a ⟨0, n.succ_pos⟩))
        (sortPayload_head_le_replicateSpine n base _ _)

/-- Every argument of a homogeneous spine has payload bounded by the spine's. -/
private theorem sortPayload_arg_le_replicateSpine {Γ : Binding.Ctx RType} {result : RType} :
    (n : ℕ) → (base : RType) →
    (head : Binding.Tm (oneLambdaSig natAlgSig) Γ (RType.curried (List.replicate n base) result)) →
    (a : Fin n → Binding.Tm (oneLambdaSig natAlgSig) Γ base) → (i : Fin n) →
    sortPayload (a i) ≤ sortPayload (replicateSpine n base head a)
  | n + 1, base, head, a, ⟨0, _⟩ => by
      rw [replicateSpineCons]
      exact le_trans (sortPayload_le_app'_right head (a ⟨0, n.succ_pos⟩))
        (sortPayload_head_le_replicateSpine n base _ _)
  | n + 1, base, head, a, ⟨iv + 1, hi⟩ => by
      rw [replicateSpineCons]
      exact sortPayload_arg_le_replicateSpine n base _ (fun i => a i.succ)
        ⟨iv, Nat.lt_of_succ_lt_succ hi⟩

/-- A single reduction step does not increase the sort payload: every
`OneLambdaStep` reduct's tags are drawn from the redex's subterms, whose payloads
are bounded by the redex's. By induction on the step; the β case reduces to
`sortPayload_instantiate₁_le`, the ι cases to spine subterm monotonicity, and the
congruence cases to the inductive hypothesis. -/
theorem sortPayload_step_le {Γ : Binding.Ctx RType} {s : RType}
    {t t' : Binding.Tm (oneLambdaSig natAlgSig) Γ s} (h : OneLambdaStep t t') :
    sortPayload t' ≤ sortPayload t := by
  induction h with
  | beta b N =>
      exact le_trans (sortPayload_instantiate₁_le N b)
        (max_le (sortPayload_le_app'_right _ _)
          (le_trans (sortPayload_le_lam' b) (sortPayload_le_app'_left _ _)))
  | eta M =>
      calc sortPayload M
          = sortPayload (Binding.ren (Binding.Thinning.weakAppend (Ξ := [_])) M) :=
            (sortPayload_ren _ _).symm
        _ ≤ sortPayload (app' (Binding.ren (Binding.Thinning.weakAppend (Ξ := [_])) M)
              (Binding.Tm.var boundVar)) := sortPayload_le_app'_left _ _
        _ ≤ sortPayload (lam' _) := sortPayload_le_lam' _
  | dstrHit j hh a =>
      exact le_trans (sortPayload_arg_le_replicateSpine _ _ _ _ _)
        (sortPayload_le_app'_right _ _)
  | dstrMiss j hh a => exact sortPayload_le_app'_right _ _
  | case idx a b => exact sortPayload_arg_le_replicateSpine _ _ _ _ _
  | appL x h ih =>
      rw [sortPayload_app', sortPayload_app']
      exact max_le_max (le_refl _) (max_le_max ih (le_refl _))
  | appR f h ih =>
      rw [sortPayload_app', sortPayload_app']
      exact max_le_max (le_refl _) (max_le_max (le_refl _) ih)
  | lamBody h ih =>
      rw [sortPayload_lam', sortPayload_lam']
      exact max_le_max (le_refl _) ih

/-- The deterministic step does not increase the sort payload: on a non-normal
term it performs a genuine `OneLambdaStep` (`detStep_sound`), bounded by
`sortPayload_step_le`; on a normal term it is the identity (`detStep_normal`). -/
theorem sortPayload_detStep_le {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    sortPayload (detStep t) ≤ sortPayload t := by
  by_cases h : Normal t
  · rw [detStep_normal h]
  · exact sortPayload_step_le (detStep_sound t h)

/-! ### The tower envelope

A single tower-of-height-2 bound on the term code, read off the term's size, its
sort payload, and its context length. The de Bruijn index of a variable leaf is
bounded by its context length (`Var Γ s = {i : Fin Γ.length // …}`), so the
context length `Γ.length` enters the envelope alongside `Tm.size` and
`sortPayload`; on a closed term (`Γ = []`) it contributes `0`. The proof nests
`Nat.pair_le_sq` up the tree: each pairing squares the payload sum, and squaring
telescopes into the height-2 tower through the exact identity
`(tower 2 y) ^ (2 ^ k) = tower 2 (y + k)`. -/

/-- Squaring a height-2 tower raises its argument by one:
`(tower 2 y) ^ 2 = tower 2 (y + 1)`, since `(2 ^ 2 ^ y) ^ 2 = 2 ^ (2 · 2 ^ y) =
2 ^ 2 ^ (y + 1)`. -/
theorem tower_two_sq (y : ℕ) : (tower 2 y) ^ 2 = tower 2 (y + 1) := by
  simp only [tower_succ, tower_zero]
  rw [← pow_mul, pow_succ]

/-- Raising a height-2 tower to the fourth power raises its argument by two:
`(tower 2 y) ^ 4 = tower 2 (y + 2)`. -/
theorem tower_two_pow_four (y : ℕ) : (tower 2 y) ^ 4 = tower 2 (y + 2) := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, tower_two_sq, tower_two_sq]

/-- A square is bounded by a height-2 tower one above its base: `n ^ 2 ≤
tower 2 (n + 1)`, since `n ^ 2 ≤ (2 ^ n) ^ 2 = 2 ^ (n · 2) ≤ 2 ^ 2 ^ (n + 1)`. -/
theorem sq_le_tower_two (n : ℕ) : n ^ 2 ≤ tower 2 (n + 1) := by
  have hexp : n * 2 ≤ 2 ^ (n + 1) := by
    rw [pow_succ]
    have := le_two_pow_self n
    omega
  calc n ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left (le_two_pow_self n) 2
    _ = 2 ^ (n * 2) := by rw [← pow_mul]
    _ ≤ 2 ^ (2 ^ (n + 1)) := Nat.pow_le_pow_right (by decide) hexp
    _ = tower 2 (n + 1) := by simp only [tower_succ, tower_zero]

/-- A pairing of two values under a common height-2 tower bound is bounded by the
tower two above: `Nat.pair a b ≤ tower 2 (y + 2)` when `a, b ≤ tower 2 y` and
`1 ≤ y`. From `Nat.pair_le_sq` and `tower_two_pow_four`, using
`3 ≤ tower 2 y`. -/
theorem pair_le_tower_two {y a b : ℕ} (hy : 1 ≤ y) (ha : a ≤ tower 2 y)
    (hb : b ≤ tower 2 y) : Nat.pair a b ≤ tower 2 (y + 2) := by
  set T := tower 2 y with hT
  have hT3 : 3 ≤ T := by
    calc (3 : ℕ) ≤ 4 := by decide
      _ = tower 2 1 := by decide
      _ ≤ T := tower_mono_right 2 hy
  have hT9 : 9 ≤ T ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul hT3 hT3
  calc Nat.pair a b ≤ (a + b + 1) ^ 2 := Nat.pair_le_sq a b
    _ ≤ (T + T + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    _ ≤ (3 * T) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    _ = 3 ^ 2 * T ^ 2 := Nat.mul_pow 3 T 2
    _ ≤ T ^ 2 * T ^ 2 := Nat.mul_le_mul hT9 (le_refl _)
    _ = T ^ 4 := by rw [← pow_add]
    _ = tower 2 (y + 2) := tower_two_pow_four y

/-- The operation code is bounded by a height-2 tower five above its sort
payload: `codeOp o ≤ tower 2 (opPayload o + 5)`. For `app`/`lam` the two
`codeRType` children pass through two `pair_le_tower_two` layers; the nullary
constants code to fixed values below `tower 2 4`. -/
theorem codeOp_le_tower (o : OneLambdaOp natAlgSig) : codeOp o ≤ tower 2 (opPayload o + 5) := by
  have hnat_maxArity : natAlgSig.maxArity = 1 := by decide
  cases o with
  | app σ τ =>
    simp only [codeOp, opPayload]
    set P := max (codeRType σ) (codeRType τ) with hP
    have hσ : codeRType σ ≤ tower 2 (P + 1) :=
      le_trans (le_max_left _ _) (le_trans (self_le_tower 2 P) (tower_mono_right 2 (by omega)))
    have hτ : codeRType τ ≤ tower 2 (P + 1) :=
      le_trans (le_max_right _ _) (le_trans (self_le_tower 2 P) (tower_mono_right 2 (by omega)))
    have h1 : Nat.pair (codeRType σ) (codeRType τ) ≤ tower 2 (P + 3) :=
      pair_le_tower_two (by omega) hσ hτ
    apply pair_le_tower_two (y := P + 3) (a := 0) (by omega) (Nat.zero_le _) h1
  | lam σ τ =>
    simp only [codeOp, opPayload]
    set P := max (codeRType σ) (codeRType τ) with hP
    have hσ : codeRType σ ≤ tower 2 (P + 1) :=
      le_trans (le_max_left _ _) (le_trans (self_le_tower 2 P) (tower_mono_right 2 (by omega)))
    have hτ : codeRType τ ≤ tower 2 (P + 1) :=
      le_trans (le_max_right _ _) (le_trans (self_le_tower 2 P) (tower_mono_right 2 (by omega)))
    have h1 : Nat.pair (codeRType σ) (codeRType τ) ≤ tower 2 (P + 3) :=
      pair_le_tower_two (by omega) hσ hτ
    apply pair_le_tower_two (y := P + 3) (a := 1) (by omega)
      (one_le_tower_of_one_le 2 (P + 3) (by omega)) h1
  | con b =>
    simp only [codeOp, opPayload]
    have h : Nat.pair 2 (cond b 1 0) ≤ 16 := by cases b <;> decide
    exact le_trans h (le_trans (by decide : (16 : ℕ) ≤ tower 2 4)
      (tower_mono_right 2 (by omega)))
  | dstr j =>
    simp only [codeOp, opPayload]
    have hj : j.val = 0 := by have := j.2; omega
    rw [hj]
    exact le_trans (by decide : Nat.pair 3 0 ≤ tower 2 4) (tower_mono_right 2 (by omega))
  | case =>
    simp only [codeOp, opPayload]
    exact le_trans (by decide : Nat.pair 4 0 ≤ tower 2 4) (tower_mono_right 2 (by omega))

/-- A two-deep right-nested pairing terminated by `0` is bounded by the tower four
above the common bound: one `pair_le_tower_two` layer per pairing. -/
theorem pair2_le_tower {z c0 c1 : ℕ} (hz : 1 ≤ z) (h0 : c0 ≤ tower 2 z)
    (h1 : c1 ≤ tower 2 z) : Nat.pair c0 (Nat.pair c1 0) ≤ tower 2 (z + 4) := by
  have p1 : Nat.pair c1 0 ≤ tower 2 (z + 2) := pair_le_tower_two hz h1 (Nat.zero_le _)
  exact pair_le_tower_two (by omega) (le_trans h0 (tower_mono_right 2 (by omega))) p1

/-- A three-deep right-nested pairing terminated by `0` is bounded by the tower
six above the common bound. -/
theorem pair3_le_tower {z c0 c1 c2 : ℕ} (hz : 1 ≤ z) (h0 : c0 ≤ tower 2 z)
    (h1 : c1 ≤ tower 2 z) (h2 : c2 ≤ tower 2 z) :
    Nat.pair c0 (Nat.pair c1 (Nat.pair c2 0)) ≤ tower 2 (z + 6) := by
  have p2 : Nat.pair c1 (Nat.pair c2 0) ≤ tower 2 (z + 4) := pair2_le_tower hz h1 h2
  exact pair_le_tower_two (by omega) (le_trans h0 (tower_mono_right 2 (by omega))) p2

/-- A four-deep right-nested pairing terminated by `0` is bounded by the tower
eight above the common bound. -/
theorem pair4_le_tower {z c0 c1 c2 c3 : ℕ} (hz : 1 ≤ z) (h0 : c0 ≤ tower 2 z)
    (h1 : c1 ≤ tower 2 z) (h2 : c2 ≤ tower 2 z) (h3 : c3 ≤ tower 2 z) :
    Nat.pair c0 (Nat.pair c1 (Nat.pair c2 (Nat.pair c3 0))) ≤ tower 2 (z + 8) := by
  have p3 : Nat.pair c1 (Nat.pair c2 (Nat.pair c3 0)) ≤ tower 2 (z + 6) :=
    pair3_le_tower hz h1 h2 h3
  exact pair_le_tower_two (by omega) (le_trans h0 (tower_mono_right 2 (by omega))) p3

/-! Head-form inversions (local re-derivations of the private `Normalization`/
`DetStep` case principle), used by the envelope induction to expose the
`app'`/`lam'`/nullary node structure. -/

/-- Transporting a term along a context equality and back is the identity. -/
private theorem env_eqRec_symm {A : AlgSig} [Fintype A.B] {Γ Γ' : Binding.Ctx RType}
    {s : RType} (h : Γ = Γ') (t : Binding.Tm (oneLambdaSig A) Γ s) :
    h.symm ▸ (h ▸ t : Binding.Tm (oneLambdaSig A) Γ' s) = t := by cases h; rfl

/-- Every application node is an `app'` of a function and argument. -/
private theorem env_op_app_inv {A : AlgSig} [Fintype A.B] {Γ : Binding.Ctx RType} {σ τ : RType}
    (args : ∀ j : Fin (((oneLambdaSig A).args (OneLambdaOp.app σ τ)).length),
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args (OneLambdaOp.app σ τ)).get j).1)
        (((oneLambdaSig A).args (OneLambdaOp.app σ τ)).get j).2) :
    ∃ (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
      (x : Binding.Tm (oneLambdaSig A) Γ σ),
      Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.app σ τ) args = OneLambda.app' f x := by
  refine ⟨List.append_nil Γ ▸ (args ⟨0, Nat.succ_pos 1⟩ :
      Binding.Tm (oneLambdaSig A) (Γ ++ []) (RType.arrow σ τ)),
    List.append_nil Γ ▸ (args ⟨1, Nat.one_lt_two⟩ :
      Binding.Tm (oneLambdaSig A) (Γ ++ []) σ), ?_⟩
  unfold OneLambda.app'
  congr 1
  funext j
  match j with
  | ⟨0, _⟩ => exact (env_eqRec_symm (List.append_nil Γ) _).symm
  | ⟨1, _⟩ => exact (env_eqRec_symm (List.append_nil Γ) _).symm

/-- Every abstraction node is a `lam'` of a body. -/
private theorem env_op_lam_inv {A : AlgSig} [Fintype A.B] {Γ : Binding.Ctx RType} {σ τ : RType}
    (args : ∀ j : Fin (((oneLambdaSig A).args (OneLambdaOp.lam σ τ)).length),
      Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args (OneLambdaOp.lam σ τ)).get j).1)
        (((oneLambdaSig A).args (OneLambdaOp.lam σ τ)).get j).2) :
    ∃ b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ,
      Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.lam σ τ) args = OneLambda.lam' b := by
  refine ⟨args ⟨0, Nat.one_pos⟩, ?_⟩
  unfold OneLambda.lam'
  congr 1
  funext j
  match j with
  | ⟨0, _⟩ => rfl

/-- The head-form cases of a term: a variable, or an operation node whose result
sort transports to the term's sort. -/
private theorem env_tm_cases {A : AlgSig} [Fintype A.B] {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig A) Γ s) :
    (∃ x : Binding.Var Γ s, t = Binding.Tm.var x) ∨
    ∃ (o : OneLambdaOp A) (hs : (oneLambdaSig A).result o = s)
      (args : ∀ j : Fin (((oneLambdaSig A).args o).length),
        Binding.Tm (oneLambdaSig A) (Γ ++ (((oneLambdaSig A).args o).get j).1)
          (((oneLambdaSig A).args o).get j).2),
      t = (hs ▸ Binding.Tm.op (S := oneLambdaSig A) o args
            : Binding.Tm (oneLambdaSig A) Γ s) := by
  suffices haux : ∀ {y : Binding.Ctx RType × RType}
      (t : PolyFix (polyTranslate Binding.varOver (oneLambdaSig A).polyEndo) y),
      (∃ x : Binding.Var y.1 y.2,
        t = (Binding.Tm.var x : Binding.Tm (oneLambdaSig A) y.1 y.2)) ∨
      ∃ (o : OneLambdaOp A) (hs : (oneLambdaSig A).result o = y.2)
        (args : ∀ j : Fin (((oneLambdaSig A).args o).length),
          Binding.Tm (oneLambdaSig A) (y.1 ++ (((oneLambdaSig A).args o).get j).1)
            (((oneLambdaSig A).args o).get j).2),
        t = (hs ▸ Binding.Tm.op (S := oneLambdaSig A) o args
              : Binding.Tm (oneLambdaSig A) y.1 y.2) from haux t
  intro y t
  cases t with
  | mk y idx children =>
    cases idx with
    | inl a =>
      refine Or.inl ⟨Binding.leafVar a, ?_⟩
      obtain ⟨⟨Γ', i'⟩, rfl⟩ := a
      congr 1
      funext e
      exact e.elim
    | inr p =>
      obtain ⟨Γ', s'⟩ := y
      change { o : OneLambdaOp A // (oneLambdaSig A).result o = s' } at p
      revert children
      obtain ⟨o, rfl⟩ := p
      intro children
      exact Or.inr ⟨o, rfl, fun j => children ⟨j⟩, rfl⟩

/-- The code of a nullary operation node is bounded by the tower-9 of `0`,
independent of the node: two pairing layers over `codeOp_le_tower` at payload
`0`. -/
private theorem codeTm_nullary_le {o : OneLambdaOp natAlgSig} {Γ : Binding.Ctx RType}
    (hpay : opPayload o = 0)
    (args : ∀ j : Fin ((oneLambdaSig natAlgSig).args o).length,
      Binding.Tm (oneLambdaSig natAlgSig) (Γ ++ (((oneLambdaSig natAlgSig).args o).get j).1)
        (((oneLambdaSig natAlgSig).args o).get j).2)
    (hlen : ((oneLambdaSig natAlgSig).args o).length = 0) :
    codeTm (Binding.Tm.op (S := oneLambdaSig natAlgSig) o args) ≤ tower 2 9 := by
  rw [codeTm_op]
  have hofn : List.ofFn (fun j => codeTm (args j)) = [] := by
    rw [List.ofFn_eq_nil_iff]; exact hlen
  rw [hofn, List.foldr_nil]
  have hco : codeOp o ≤ tower 2 5 := by
    have h := codeOp_le_tower o; rw [hpay] at h; exact h
  exact pair2_le_tower (z := 5) (by omega) (one_le_tower_of_one_le 2 5 (by omega)) hco

/-- The strong-induction shell of the tower envelope: on a term of size at most
`N`, the code is bounded by the height-2 tower of `6 · (2 · size + payload +
Γ.length + 1)`. -/
private theorem codeTm_le_envelope_aux :
    (N : ℕ) → ∀ {Γ : Binding.Ctx RType} {s : RType}
      (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s), Tm.size t ≤ N →
      codeTm t ≤ tower 2 (6 * (2 * Tm.size t + sortPayload t + Γ.length + 1))
  | 0, _, _, t, hN => absurd (Tm.one_le_size t) (by omega)
  | N + 1, Γ, s, t, hN => by
    rcases env_tm_cases t with ⟨x, rfl⟩ | ⟨o, hs, args, ht⟩
    · rw [codeTm_var, Tm.size_var, sortPayload_var]
      have hidx : x.1.val < Γ.length := x.1.2
      calc Nat.pair 0 x.1.val ≤ (0 + x.1.val + 1) ^ 2 := Nat.pair_le_sq 0 x.1.val
        _ = (x.1.val + 1) ^ 2 := by rw [Nat.zero_add]
        _ ≤ Γ.length ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ ≤ tower 2 (Γ.length + 1) := sq_le_tower_two _
        _ ≤ tower 2 (6 * (2 * 1 + 0 + Γ.length + 1)) := tower_mono_right 2 (by omega)
    · cases o with
      | app σ τ =>
        have hs1 : τ = s := hs
        subst hs1
        replace ht : t = Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.app σ τ) args :=
          ht
        obtain ⟨f, x, hfx⟩ := env_op_app_inv args
        rw [hfx] at ht
        subst ht
        rw [size_app'] at hN
        have hf1 := Tm.one_le_size f
        have hx1 := Tm.one_le_size x
        have ihf := codeTm_le_envelope_aux N f (by omega)
        have ihx := codeTm_le_envelope_aux N x (by omega)
        rw [codeTm_app']
        set z := max (max (6 * (2 * Tm.size f + sortPayload f + Γ.length + 1))
          (6 * (2 * Tm.size x + sortPayload x + Γ.length + 1)))
          (sortPayload (app' f x) + 5) with hz_def
        have hz1 : 1 ≤ z := by rw [hz_def]; omega
        have hple : opPayload (OneLambdaOp.app σ τ) ≤ sortPayload (app' f x) := by
          rw [sortPayload_app']; exact le_max_left _ _
        have hco : codeOp (OneLambdaOp.app σ τ) ≤ tower 2 z :=
          le_trans (codeOp_le_tower _) (tower_mono_right 2 (by rw [hz_def]; omega))
        have hf : codeTm f ≤ tower 2 z :=
          le_trans ihf (tower_mono_right 2 (le_max_of_le_left (le_max_left _ _)))
        have hx : codeTm x ≤ tower 2 z :=
          le_trans ihx (tower_mono_right 2 (le_max_of_le_left (le_max_right _ _)))
        refine le_trans (pair4_le_tower hz1 (one_le_tower_of_one_le 2 z hz1) hco hf hx)
          (tower_mono_right 2 ?_)
        rw [hz_def, size_app', sortPayload_app']
        omega
      | lam σ τ =>
        have hs1 : RType.arrow σ τ = s := hs
        subst hs1
        replace ht : t = Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.lam σ τ) args :=
          ht
        obtain ⟨b, hb⟩ := env_op_lam_inv args
        rw [hb] at ht
        subst ht
        rw [size_lam'] at hN
        have hb1 := Tm.one_le_size b
        have ihb := codeTm_le_envelope_aux N b (by omega)
        have hlb : (Γ ++ [σ]).length = Γ.length + 1 := by simp
        rw [hlb] at ihb
        rw [codeTm_lam']
        set z := max (6 * (2 * Tm.size b + sortPayload b + (Γ.length + 1) + 1))
          (sortPayload (lam' b) + 5) with hz_def
        have hz1 : 1 ≤ z := by rw [hz_def]; omega
        have hple : opPayload (OneLambdaOp.lam σ τ) ≤ sortPayload (lam' b) := by
          rw [sortPayload_lam']; exact le_max_left _ _
        have hco : codeOp (OneLambdaOp.lam σ τ) ≤ tower 2 z :=
          le_trans (codeOp_le_tower _) (tower_mono_right 2 (by rw [hz_def]; omega))
        have hcb : codeTm b ≤ tower 2 z :=
          le_trans ihb (tower_mono_right 2 (le_max_left _ _))
        refine le_trans (pair3_le_tower hz1 (one_le_tower_of_one_le 2 z hz1) hco hcb)
          (tower_mono_right 2 ?_)
        rw [hz_def, size_lam', sortPayload_lam']
        omega
      | con i =>
        have hs1 : RType.curried (List.replicate (natAlgSig.ar i) RType.o) RType.o = s := hs
        subst hs1
        replace ht : t = Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.con i) args := ht
        have hone : 1 ≤ Tm.size t := Tm.one_le_size t
        refine le_trans ?_ (tower_mono_right 2
          (show (9 : ℕ) ≤ 6 * (2 * Tm.size t + sortPayload t + Γ.length + 1) from by omega))
        rw [ht]
        exact codeTm_nullary_le rfl args rfl
      | dstr j =>
        have hs1 : RType.arrow RType.o RType.o = s := hs
        subst hs1
        replace ht : t = Binding.Tm.op (S := oneLambdaSig natAlgSig) (OneLambdaOp.dstr j) args := ht
        have hone : 1 ≤ Tm.size t := Tm.one_le_size t
        refine le_trans ?_ (tower_mono_right 2
          (show (9 : ℕ) ≤ 6 * (2 * Tm.size t + sortPayload t + Γ.length + 1) from by omega))
        rw [ht]
        exact codeTm_nullary_le rfl args rfl
      | case =>
        have hs1 : RType.arrow RType.o
            (RType.curried (List.replicate natAlgSig.numCtors RType.o) RType.o) = s := hs
        subst hs1
        replace ht : t = Binding.Tm.op (S := oneLambdaSig natAlgSig) OneLambdaOp.case args := ht
        have hone : 1 ≤ Tm.size t := Tm.one_le_size t
        refine le_trans ?_ (tower_mono_right 2
          (show (9 : ℕ) ≤ 6 * (2 * Tm.size t + sortPayload t + Γ.length + 1) from by omega))
        rw [ht]
        exact codeTm_nullary_le rfl args rfl

/-- The tower envelope (spec §5.4): the term code sits below a single height-2
tower whose argument is linear in the term's size, its sort payload, and its
context length, `codeTm t ≤ tower 2 (6 · (2 · Tm.size t + sortPayload t +
Γ.length + 1))`. The `Γ.length` term bounds the de Bruijn index of a variable
leaf, which the term's size and payload do not; it vanishes on a closed term.
The concrete constant `6`, the `2 · Tm.size` weight, and the `Γ.length` summand
are fixed by the proof; the height-2 tower shape is the interface. Nesting
`Nat.pair_le_sq` up the tree telescopes into the tower through
`(tower 2 y) ^ (2 ^ k) = tower 2 (y + k)`. -/
theorem codeTm_le_envelope {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    codeTm t ≤ tower 2 (6 * (2 * Tm.size t + sortPayload t + Γ.length + 1)) :=
  codeTm_le_envelope_aux (Tm.size t) t le_rfl

/-! ### The deterministic chain ceiling

Every code on the deterministic chain from `t` is below a single monotone
tower-shaped ceiling `codeCeil t`. The sort payload is stable along the chain
(`sortPayload_detStep_le`); the size is bounded by iterating the per-step
squaring `size_detStep_sq` and absorbing overshoot past the deterministic clock;
`codeCeil` instantiates the envelope at those two ceilings. -/

/-- `n ≤ n ^ 2`. -/
private theorem self_le_sq (n : ℕ) : n ≤ n ^ 2 := by
  rw [pow_two]
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · exact Nat.le_mul_of_pos_left n h

/-- `x ^ 2 + b ≤ (x + b) ^ 2`. -/
private theorem sq_add_le (x b : ℕ) : x ^ 2 + b ≤ (x + b) ^ 2 := by
  rw [pow_two, pow_two]
  have h1 : x * x ≤ (x + b) * x := Nat.mul_le_mul_right x (Nat.le_add_right x b)
  have h2 : b ≤ (x + b) * b := by
    rcases Nat.eq_zero_or_pos b with hb | hb
    · simp [hb]
    · calc b = 1 * b := (Nat.one_mul b).symm
        _ ≤ (x + b) * b := Nat.mul_le_mul_right b (by omega)
  calc x * x + b ≤ (x + b) * x + (x + b) * b := by omega
    _ = (x + b) * (x + b) := by rw [← Nat.mul_add]

/-- `c + d ^ 2 ≤ (c + d) ^ 2`. -/
private theorem add_sq_le (c d : ℕ) : c + d ^ 2 ≤ (c + d) ^ 2 := by
  rw [pow_two, pow_two]
  have h1 : c ≤ (c + d) * c := by
    rcases Nat.eq_zero_or_pos c with hc | hc
    · simp [hc]
    · calc c = 1 * c := (Nat.one_mul c).symm
        _ ≤ (c + d) * c := Nat.mul_le_mul_right c (by omega)
  have h2 : d * d ≤ (c + d) * d := Nat.mul_le_mul_right d (Nat.le_add_left d c)
  calc c + d * d ≤ (c + d) * c + (c + d) * d := by omega
    _ = (c + d) * (c + d) := by rw [← Nat.mul_add]

/-- `1 + a ^ 2 ≤ (1 + a) ^ 2`. -/
private theorem one_add_sq_le (a : ℕ) : 1 + a ^ 2 ≤ (1 + a) ^ 2 := by
  rw [Nat.add_comm 1 a, Nat.add_comm 1 (a ^ 2)]; exact sq_add_le a 1

/-- `1 + a ^ 2 + b ≤ (1 + a + b) ^ 2`. -/
private theorem one_add_sq_add_le (a b : ℕ) : 1 + a ^ 2 + b ≤ (1 + a + b) ^ 2 :=
  le_trans (by have := one_add_sq_le a; omega) (sq_add_le (1 + a) b)

/-- `a * b ≤ (a + b) ^ 2`. -/
private theorem mul_le_add_sq (a b : ℕ) : a * b ≤ (a + b) ^ 2 := by
  rw [pow_two]
  exact Nat.mul_le_mul (Nat.le_add_right a b) (Nat.le_add_left b a)

/-- The function subterm's size is at most the application node's. -/
private theorem size_le_app'_left {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig natAlgSig) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig natAlgSig) Γ σ) : Tm.size f ≤ Tm.size (app' f x) := by
  rw [size_app']; omega

/-- The argument subterm's size is at most the application node's. -/
private theorem size_le_app'_right {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig natAlgSig) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig natAlgSig) Γ σ) : Tm.size x ≤ Tm.size (app' f x) := by
  rw [size_app']; omega

/-- The head of a homogeneous spine has size at most the spine's. -/
private theorem size_head_le_replicateSpine {Γ : Binding.Ctx RType} {result : RType} :
    (n : ℕ) → (base : RType) →
    (head : Binding.Tm (oneLambdaSig natAlgSig) Γ (RType.curried (List.replicate n base) result)) →
    (a : Fin n → Binding.Tm (oneLambdaSig natAlgSig) Γ base) →
    Tm.size head ≤ Tm.size (replicateSpine n base head a)
  | 0, _base, _head, _a => le_refl _
  | n + 1, base, head, a => by
      rw [replicateSpineCons]
      exact le_trans (size_le_app'_left head (a ⟨0, n.succ_pos⟩))
        (size_head_le_replicateSpine n base _ _)

/-- Every argument of a homogeneous spine has size at most the spine's. -/
private theorem size_arg_le_replicateSpine {Γ : Binding.Ctx RType} {result : RType} :
    (n : ℕ) → (base : RType) →
    (head : Binding.Tm (oneLambdaSig natAlgSig) Γ (RType.curried (List.replicate n base) result)) →
    (a : Fin n → Binding.Tm (oneLambdaSig natAlgSig) Γ base) → (i : Fin n) →
    Tm.size (a i) ≤ Tm.size (replicateSpine n base head a)
  | n + 1, base, head, a, ⟨0, _⟩ => by
      rw [replicateSpineCons]
      exact le_trans (size_le_app'_right head (a ⟨0, n.succ_pos⟩))
        (size_head_le_replicateSpine n base _ _)
  | n + 1, base, head, a, ⟨iv + 1, hi⟩ => by
      rw [replicateSpineCons]
      exact size_arg_le_replicateSpine n base _ (fun i => a i.succ)
        ⟨iv, Nat.lt_of_succ_lt_succ hi⟩

/-- A single reduction step at most squares the size: substitution multiplies the
size, and every other reduct is a subterm. By induction on the step; the β case
uses `Tm.size_instantiate₁_le`, the ι cases spine subterm monotonicity, and the
congruence cases the inductive hypothesis with the square-completion lemmas. -/
theorem size_step_le {Γ : Binding.Ctx RType} {s : RType}
    {t t' : Binding.Tm (oneLambdaSig natAlgSig) Γ s} (h : OneLambdaStep t t') :
    Tm.size t' ≤ Tm.size t ^ 2 := by
  induction h with
  | beta b N =>
      rw [size_app', size_lam']
      refine le_trans (Tm.size_instantiate₁_le N b) (le_trans (mul_le_add_sq _ _) ?_)
      exact Nat.pow_le_pow_left (by omega) 2
  | eta M =>
      refine le_trans ?_ (self_le_sq _)
      rw [size_lam', size_app', Tm.size_ren, Tm.size_var]; omega
  | dstrHit j hh a =>
      refine le_trans ?_ (self_le_sq _)
      exact le_trans (size_arg_le_replicateSpine _ _ _ _ ⟨j.val, hh⟩)
        (size_le_app'_right _ _)
  | dstrMiss j hh a =>
      exact le_trans (size_le_app'_right _ _) (self_le_sq _)
  | case idx a b =>
      refine le_trans ?_ (self_le_sq _)
      exact size_arg_le_replicateSpine _ _ _ _ idx
  | appL x h ih =>
      rw [size_app', size_app']
      exact le_trans (Nat.add_le_add_right (Nat.add_le_add_left ih 1) (Tm.size x))
        (one_add_sq_add_le _ _)
  | appR f h ih =>
      rw [size_app', size_app']
      exact le_trans (Nat.add_le_add_left ih (1 + Tm.size f))
        (add_sq_le (1 + Tm.size f) (Tm.size _))
  | lamBody h ih =>
      rw [size_lam', size_lam']
      exact le_trans (Nat.add_le_add_left ih 1) (one_add_sq_le _)

/-- The deterministic step at most squares the size: on a non-normal term it
performs a genuine `OneLambdaStep` (`size_step_le`); on a normal term it is the
identity. -/
theorem size_detStep_sq {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) : Tm.size (detStep t) ≤ Tm.size t ^ 2 := by
  by_cases h : Normal t
  · rw [detStep_normal h]; exact self_le_sq _
  · exact size_step_le (detStep_sound t h)

/-- The size of a deterministic iterate is bounded by the size raised to a
`k`-fold squaring: `Tm.size (detIter k t) ≤ Tm.size t ^ (2 ^ k)`. By induction on
`k`, each step squaring by `size_detStep_sq`. -/
theorem size_detIter_le_pow (k : ℕ) {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    Tm.size (detIter k t) ≤ Tm.size t ^ (2 ^ k) := by
  induction k with
  | zero => rw [detIter_zero, show (2 : ℕ) ^ 0 = 1 from rfl, pow_one]
  | succ k ih =>
    rw [detIter_succ']
    calc Tm.size (detStep (detIter k t))
        ≤ Tm.size (detIter k t) ^ 2 := size_detStep_sq _
      _ ≤ (Tm.size t ^ (2 ^ k)) ^ 2 := Nat.pow_le_pow_left ih 2
      _ = Tm.size t ^ (2 ^ (k + 1)) := by rw [← pow_mul, ← pow_succ]

/-- The sort payload of a deterministic iterate is bounded by the sort payload of
`t`: iterating `sortPayload_detStep_le`. -/
theorem sortPayload_detIter_le (k : ℕ) {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    sortPayload (detIter k t) ≤ sortPayload t := by
  induction k with
  | zero => exact (congrArg sortPayload (detIter_zero t)).le
  | succ k ih => rw [detIter_succ']; exact le_trans (sortPayload_detStep_le _) ih

/-- The deterministic clock (Leivant III Lemma 12): the iteration count at which
`detIter` reaches a `Normal` term, `(redexRank t + 1) · 2_(redexRank t + 1)
(Tm.height t)`. -/
def detClock {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) : ℕ :=
  (redexRank t + 1) * tower (redexRank t + 1) (Tm.height t)

/-- A `k`-uniform size ceiling for the deterministic chain: every iterate's size
is bounded by `Tm.size t` raised to `2 ^ detClock t`. Below the clock the iterate
squaring bound applies directly; past the clock the term is `Normal`
(`detIter_normal`) and overshoot is absorbed (`detIter_eq_of_normal`). -/
theorem size_detIter_le_ceil (k : ℕ) {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    Tm.size (detIter k t) ≤ Tm.size t ^ (2 ^ detClock t) := by
  rcases Nat.lt_or_ge k (detClock t) with hk | hk
  · refine le_trans (size_detIter_le_pow k t)
      (Nat.pow_le_pow_right (Tm.one_le_size t) (Nat.pow_le_pow_right (by omega) (le_of_lt hk)))
  · rw [detIter_eq_of_normal hk (detIter_normal t)]
    exact size_detIter_le_pow (detClock t) t

/-- The deterministic chain ceiling (spec §5.4; consumed by Tasks 6.4.12-6.4.13):
a single monotone tower-shaped bound on every code of the deterministic chain,
`codeCeil t = tower 2 (6 · (2 · Tm.size t ^ (2 ^ detClock t) + sortPayload t +
Γ.length + 1))`. Instantiates the envelope at the chain's uniform size ceiling
`size_detIter_le_ceil`, the stable sort payload `sortPayload_detIter_le`, and the
context length preserved along the chain. Novel realization. -/
def codeCeil {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) : ℕ :=
  tower 2 (6 * (2 * Tm.size t ^ (2 ^ detClock t) + sortPayload t + Γ.length + 1))

/-- Every code on the deterministic chain from `t` sits below the monotone
ceiling `codeCeil t`: `codeTm (detIter k t) ≤ codeCeil t`. The envelope at
`detIter k t` composes with the uniform size ceiling and the stable sort payload,
the context length being preserved by `detStep`. -/
theorem codeTm_detIter_le_codeCeil (k : ℕ) {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (oneLambdaSig natAlgSig) Γ s) :
    codeTm (detIter k t) ≤ codeCeil t := by
  refine le_trans (codeTm_le_envelope (detIter k t)) ?_
  unfold codeCeil
  apply tower_mono_right
  have hs := size_detIter_le_ceil k t
  have hp := sortPayload_detIter_le k t
  omega

end OneLambda

end GebLean.Ramified
