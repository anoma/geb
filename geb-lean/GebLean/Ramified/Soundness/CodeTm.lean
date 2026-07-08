import GebLean.Ramified.Soundness.DetStep
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

end OneLambda

end GebLean.Ramified
