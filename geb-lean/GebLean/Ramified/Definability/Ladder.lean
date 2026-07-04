import GebLean.Ramified.Examples

/-!
# The in-system clock ladder at object sorts

The object-sort generalizations of the Leivant III section 2.4 numeric family
over the `1 + X` word algebra `natAlgSig`: numerals, the exponentiation copy,
the in-system `2_m` clock family, the size function, and addition and
multiplication, each at an arbitrary object sort `θ` in place of the base sort
`o`. The committed `o`-sorted constructions of `GebLean/Ramified/Examples.lean`
are the `θ = o` specializations; the constructor operations exist at every
object sort (Leivant III section 2.7: every object sort denotes a copy of the
base carrier), so the same schema identifiers transcribe at every `θ.IsObj`.
Each interpretation lemma reads a denotation on the standard carriers through
`objToNat` (`GebLean/Ramified/Examples.lean`), the numeric reading at an object
sort, and — for the clock family — `GebLean.tower`
(`GebLean/Utilities/Tower.lean`).

## Main definitions

* `numeralTm` — the numerals at an object sort, over the higher-order
  presentation's signature.
* `expFun` — the first-order function sort `θ → θ` at an object sort.
* `succObj`, `compObj` — the successor `sc (x) = c_true x` at `θ` and the
  two-fold application `f (g x)` at `θ`, the atoms the recurrences iterate.
* `expAtIdent` — the exponentiation copy `e^θ : Ω(θ → θ) → (θ → θ)`, the
  `ramExp` construction with `o` replaced by `θ`.
* `applyAtZeroObj` — the wrapper `a ↦ (rec a)(0^θ)`, a `θ→θ`-valued recurrence
  evaluated at the `0` numeral of `θ`.
* `expToObj` — the exponentiation copy of type `Ω(θ → θ) → θ`, the value of
  `e^θ` at the `0` numeral (Leivant III section 2.4(3), "more generally").
* `szRecObj`, `szAtIdent` — the size auxiliary `addsz : Ω(θ → θ) → (θ → θ)` and
  the size function `sz (a) = addsz(a)(α)` at `θ`.
* `clockSort` — the input-sort chain of the in-system `2_m` family.
* `twoPowIdent` — the in-system `2_m` family `clockSort m θ → θ`.
* `addAtIdent`, `mulAtIdent` — addition `θ, Ω θ → θ` and multiplication
  `Ω θ, Ω θ → θ` at `θ`.

## Main statements

* `clockSort_isObj` — each `clockSort m θ` is an object sort.
* `expAtIdent_interp` — the exponentiation copy iterates the successor:
  `objToNat (e^θ (n) (x)) = objToNat x + 2 ^ (count n)`.
* `twoPowIdent_interp` — the clock family aligns with `GebLean.tower`:
  `objToNat (2_m (a)) = tower m (objToNat a)`.
* `szAtIdent_interp` — the size function counts the constructors:
  `objToNat (sz a) = count a + 1`.
* `addAtIdent_interp`, `mulAtIdent_interp` — addition denotes `+` and
  multiplication denotes `*`.

## Implementation notes

Each construction is the committed `o`-sorted item of
`GebLean/Ramified/Examples.lean` with the base sort `o` replaced by an object
sort `θ` and the object-sort hypothesis `hθ` supplied to the constructor
operations. The interpretation lemmas mirror the committed
`freeAlgToNat_*_recurse` structural inductions (via `PolyFix.ind`, decision 8),
replacing `freeAlgToNat` by `objToNat` at `θ`, so the carrier-copy transports of
`RType.interp_isObj` at `θ` enter where the committed proofs had definitional
identities at `o`.

The clock family `twoPowIdent` is an object-language schema identifier — unlike
the carrier-level composite `ramTwoPow`, whose ladder would need a raising
coercion `o → Ω(o → o)` the tier discipline forbids — because the input-sort
chain `clockSort` grows: each exponential step `expToObj (clockSort m θ)` lowers
the tier from `clockSort (m+1) θ` to `clockSort m θ`, so the ladder is assembled
by downward composition (the `ramDeltaIdent` precedent). The induction that the
clock recurrence produces reads `objToNat` through `tower m (2 ^ ·)`, identified
with `tower (m + 1)` by `GebLean.tower_comp`.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`. Addition and multiplication
are section 2.4(2); the exponentiation copy `e` is section 2.4(3) (with its
"more generally" clause at type `Ω(θ → θ) → θ`); the `2_m` clock family is
section 2.4(4); the size function is section 2.4(6). Every object sort denotes a
copy of the base carrier in section 2.7. The object-sort generalization of the
`o`-sorted committed ladder through this development's polynomial-endofunctor
stack (decision 8) is novel packaging.

## Tags

ramified recurrence, object sort, clock, tower, exponentiation, size, addition,
multiplication, elementary complexity
-/

namespace GebLean.Ramified

open CategoryTheory

/-- The numerals at an object sort `s`, over the higher-order presentation's
signature: `0` is the nullary constructor at `s` and `n + 1` the unary
constructor at `s` applied to the numeral `n`. The constructor operations exist
at every object sort (Leivant III section 2.7); a thin generalization of the
base-sort `tmZero`/`tmSucc` (`GebLean/Ramified/Examples.lean`) to an arbitrary
object sort and to the higher-order signature. Novel packaging. -/
def numeralTm {Γ : Ctx RType} (s : RType) (hs : s.IsObj) :
    Nat → Tm (higherOrder natAlgSig).sig Γ s
  | 0 =>
    Tm.op (sig := (higherOrder natAlgSig).sig)
      (Sum.inl (Sum.inl (Sum.inl (⟨s, hs⟩, false)))) finZeroElim
  | n + 1 =>
    Tm.op (sig := (higherOrder natAlgSig).sig)
      (Sum.inl (Sum.inl (Sum.inl (⟨s, hs⟩, true))))
      (Fin.cons (numeralTm s hs n) finZeroElim)

/-- The nullary-constructor term at an object sort `s`, over a definition
signature: the `0` numeral at `s`. The object-sort generalization of the
base-sort `tmZero` (`GebLean/Ramified/Examples.lean`). -/
def tmZeroObj {n : Nat} {h : Fin n → List RType × RType} {Γ : Ctx RType}
    (s : RType) (hs : s.IsObj) : Tm (defnSig natAlgSig n h) Γ s :=
  Tm.op (sig := defnSig natAlgSig n h) (Sum.inl (Sum.inl (Sum.inl (⟨s, hs⟩, false))))
    finZeroElim

/-- The unary-constructor term at an object sort `s`, over a definition
signature: the successor `c_true t` at `s`. The object-sort generalization of
the base-sort `tmSucc` (`GebLean/Ramified/Examples.lean`). -/
def tmSuccObj {n : Nat} {h : Fin n → List RType × RType} {Γ : Ctx RType}
    (s : RType) (hs : s.IsObj) (t : Tm (defnSig natAlgSig n h) Γ s) :
    Tm (defnSig natAlgSig n h) Γ s :=
  Tm.op (sig := defnSig natAlgSig n h) (Sum.inl (Sum.inl (Sum.inl (⟨s, hs⟩, true))))
    (Fin.cons t finZeroElim)

/-- The first-order function sort `θ → θ` at an object sort `θ`: the sort at
which the exponentiation copy `expAtIdent` and the clauses of its second-order
recurrence take their values (Leivant III section 2.4(3)). The object-sort
generalization of the base-sort `ramFun` (`GebLean/Ramified/Examples.lean`). -/
abbrev expFun (θ : RType) : RType := RType.arrow θ θ

/-- The successor `sc (x) = c_true x` at an object sort `θ`, at context `[θ]`
and result `θ`: an explicit definition whose body is the unary constructor at
`θ` applied to the sole variable. The object-sort generalization of the
base-sort `ramSucc` (`GebLean/Ramified/Examples.lean`); the function the
exponentiation base clause iterates. -/
def succObj (θ : RType) (hθ : θ.IsObj) : RIdent natAlgSig [θ] θ :=
  RIdent.defn ⟨0, finZeroElim, tmSuccObj θ hθ (Tm.var 0)⟩ finZeroElim

/-- The two-fold-application identifier `comp (f, g, x) = f (g x)` at an object
sort `θ`, at context `[θ → θ, θ → θ, θ]` and result `θ`: an explicit definition
applying the two function arguments in turn through the application former. The
object-sort generalization of the base-sort `ramComp`
(`GebLean/Ramified/Examples.lean`); the exponentiation and size step clauses use
its combinator form to compose their recursive results. -/
def compObj (θ : RType) : RIdent natAlgSig [expFun θ, expFun θ, θ] θ :=
  RIdent.defn ⟨0, finZeroElim,
    Tm.op (sig := defnSig natAlgSig 0 finZeroElim)
      (Sum.inl (Sum.inl (Sum.inr (θ, θ))))
      (Fin.cons (Tm.var 0)
        (Fin.cons
          (Tm.op (sig := defnSig natAlgSig 0 finZeroElim)
            (Sum.inl (Sum.inl (Sum.inr (θ, θ))))
            (Fin.cons (Tm.var 1) (Fin.cons (Tm.var 2) finZeroElim)))
          finZeroElim))⟩
    finZeroElim

/-- The context and result sort of the identifier the exponentiation base clause
references: the successor `succObj : [θ] → θ`. -/
def expBaseHoleIdxObj (θ : RType) : Fin 1 → List RType × RType :=
  Function.const _ ([θ], θ)

/-- The exponentiation base clause `e_0 = sc` at an object sort `θ`: an explicit
definition at result `θ → θ` whose body is the curried combinator form of the
successor `succObj`. The object-sort generalization of the base-sort
`ramExpBase` (`GebLean/Ramified/Examples.lean`). -/
def expBaseObj (θ : RType) (hθ : θ.IsObj) : RIdent natAlgSig [] (expFun θ) :=
  RIdent.defn ⟨1, expBaseHoleIdxObj θ,
    Tm.op (sig := defnSig natAlgSig 1 (expBaseHoleIdxObj θ))
      (Sum.inr ⟨0, by decide⟩) finZeroElim⟩
    (fun _ => succObj θ hθ)

/-- The context and result sort of the identifier the exponentiation step clause
references: the two-fold application `compObj : [θ → θ, θ → θ, θ] → θ`. -/
def expStepHoleIdxObj (θ : RType) : Fin 1 → List RType × RType :=
  Function.const _ ([expFun θ, expFun θ, θ], θ)

/-- The exponentiation step clause `e_{n+1} = e_n ∘ e_n` at an object sort `θ`:
an explicit definition at context `[θ → θ]` (the recursive result `e_n`) and
result `θ → θ`, composing that recursive-result variable with itself through the
combinator form of `compObj`. The object-sort generalization of the base-sort
`ramExpStep` (`GebLean/Ramified/Examples.lean`). -/
def expStepObj (θ : RType) : RIdent natAlgSig [expFun θ] (expFun θ) :=
  RIdent.defn ⟨1, expStepHoleIdxObj θ,
    Tm.op (sig := defnSig natAlgSig 1 (expStepHoleIdxObj θ))
      (Sum.inl (Sum.inl (Sum.inr (expFun θ, expFun θ))))
      (Fin.cons
        (Tm.op (sig := defnSig natAlgSig 1 (expStepHoleIdxObj θ))
          (Sum.inl (Sum.inl (Sum.inr (expFun θ, RType.arrow (expFun θ) (expFun θ)))))
          (Fin.cons
            (Tm.op (sig := defnSig natAlgSig 1 (expStepHoleIdxObj θ))
              (Sum.inr ⟨0, by decide⟩) finZeroElim)
            (Fin.cons (Tm.var 0) finZeroElim)))
        (Fin.cons (Tm.var 0) finZeroElim))⟩
    (fun _ => compObj θ)

/-- The clauses of the exponentiation recurrence at an object sort `θ`: the base
clause at the nullary constructor, the self-composition step at the unary
constructor. -/
def expStepsObj (θ : RType) (hθ : θ.IsObj) : (i : Bool) →
    RIdent natAlgSig ([] ++ List.replicate (natAlgSig.ar i) (expFun θ)) (expFun θ)
  | false => expBaseObj θ hθ
  | true => expStepObj θ

/-- Leivant III section 2.4(3)'s exponentiation copy at an object sort `θ`,
`e^θ : Ω(θ → θ) → (θ → θ)`, as a ramified monotonic second-order recurrence: the
`ramExp` construction with `o` replaced by `θ`. On a numeral `n` it yields the
`2^n`-fold iterate of the successor, so `e^θ (n) (x)` has count
`count x + 2^n` (`expAtIdent_interp`). -/
def expAtIdent (θ : RType) (hθ : θ.IsObj) :
    RIdent natAlgSig [RType.omega (expFun θ)] (expFun θ) :=
  RIdent.mrec [] (expFun θ) (expStepsObj θ hθ)

/-- The context and result sort of the identifier the size step clause
references beyond `compObj`: the successor `succObj : [θ] → θ`. -/
def szStepHoleIdxObj (θ : RType) : Fin 2 → List RType × RType
  | ⟨0, _⟩ => ([expFun θ, expFun θ, θ], θ)
  | ⟨1, _⟩ => ([θ], θ)

/-- The size step clause `addsz_{n+1} = addsz_n ∘ sc` at an object sort `θ`: an
explicit definition composing the recursive result `addsz_n` with the successor
through the combinator form of `compObj`. The size auxiliary counts one
constructor per step. -/
def szStepObj (θ : RType) (hθ : θ.IsObj) : RIdent natAlgSig [expFun θ] (expFun θ) :=
  RIdent.defn ⟨2, szStepHoleIdxObj θ,
    Tm.op (sig := defnSig natAlgSig 2 (szStepHoleIdxObj θ))
      (Sum.inl (Sum.inl (Sum.inr (expFun θ, expFun θ))))
      (Fin.cons
        (Tm.op (sig := defnSig natAlgSig 2 (szStepHoleIdxObj θ))
          (Sum.inl (Sum.inl (Sum.inr (expFun θ, RType.arrow (expFun θ) (expFun θ)))))
          (Fin.cons
            (Tm.op (sig := defnSig natAlgSig 2 (szStepHoleIdxObj θ))
              (Sum.inr ⟨0, by decide⟩) finZeroElim)
            (Fin.cons (Tm.var 0) finZeroElim)))
        (Fin.cons
          (Tm.op (sig := defnSig natAlgSig 2 (szStepHoleIdxObj θ))
            (Sum.inr ⟨1, by decide⟩) finZeroElim)
          finZeroElim))⟩
    (fun j => match j with
      | ⟨0, _⟩ => compObj θ
      | ⟨1, _⟩ => succObj θ hθ)

/-- The clauses of the size auxiliary recurrence at an object sort `θ`: the
successor at the nullary constructor, the compose-with-successor step at the
unary constructor. -/
def szStepsObj (θ : RType) (hθ : θ.IsObj) : (i : Bool) →
    RIdent natAlgSig ([] ++ List.replicate (natAlgSig.ar i) (expFun θ)) (expFun θ)
  | false => expBaseObj θ hθ
  | true => szStepObj θ hθ

/-- The size auxiliary `addsz : Ω(θ → θ) → (θ → θ)` at an object sort `θ`
(Leivant III section 2.4(6)), a ramified monotonic second-order recurrence:
`addsz (0) = sc` and `addsz (n + 1) = addsz (n) ∘ sc`. On a numeral `n` it is
the `(n + 1)`-fold iterate of the successor, so `addsz (n) (x)` has count
`count x + count n + 1`. -/
def szRecObj (θ : RType) (hθ : θ.IsObj) :
    RIdent natAlgSig [RType.omega (expFun θ)] (expFun θ) :=
  RIdent.mrec [] (expFun θ) (szStepsObj θ hθ)

/-- Application of a `θ→θ` function to the `0` numeral of `θ`, at context
`[θ → θ]` and result `θ`: an explicit definition applying the sole variable to
the `0` numeral through the application former `defnApp`. The value-at-`0` half
of the wrapper `applyAtZeroObj`. -/
def evalAtZeroIdent (θ : RType) (hθ : θ.IsObj) : RIdent natAlgSig [expFun θ] θ :=
  RIdent.defn ⟨0, finZeroElim, defnApp θ θ (Tm.var 0) (tmZeroObj θ hθ)⟩ finZeroElim

/-- The context and result sorts of the two identifiers that the
`applyAtZeroObj` wrapper composes: `rec` and `evalAtZeroIdent`. -/
def applyAtZeroHoleIdxObj (θ : RType) : Fin 2 → List RType × RType
  | ⟨0, _⟩ => ([RType.omega (expFun θ)], expFun θ)
  | ⟨1, _⟩ => ([expFun θ], θ)

/-- The wrapper evaluating a `θ→θ`-valued recurrence at the `0` numeral of `θ`:
`applyAtZeroObj rec (a) = (rec a)(0^θ)`, at context `[Ω(θ → θ)]` and result `θ`.
The composite (through saturated holes) of `rec` at the recurrence argument
followed by `evalAtZeroIdent`, mirroring the two-hole composition of the
committed `ramDeltaIdent`. The shared shape of the exponentiation copy `expToObj`
and the size function `szAtIdent`. -/
def applyAtZeroObj (θ : RType) (hθ : θ.IsObj)
    (rec : RIdent natAlgSig [RType.omega (expFun θ)] (expFun θ)) :
    RIdent natAlgSig [RType.omega (expFun θ)] θ :=
  RIdent.defn ⟨2, applyAtZeroHoleIdxObj θ,
    Tm.op (sig := defnSig natAlgSig 2 (applyAtZeroHoleIdxObj θ))
      (Sum.inl (Sum.inr ⟨1, by decide⟩))
      (Fin.cons
        (Tm.op (sig := defnSig natAlgSig 2 (applyAtZeroHoleIdxObj θ))
          (Sum.inl (Sum.inr ⟨0, by decide⟩))
          (Fin.cons (Tm.var 0) finZeroElim))
        finZeroElim)⟩
    (fun j => match j with
      | ⟨0, _⟩ => rec
      | ⟨1, _⟩ => evalAtZeroIdent θ hθ)

/-- Leivant III section 2.4(3)'s exponentiation copy of type `Ω(θ → θ) → θ` (the
"more generally" clause): the value of `e^θ` at the `0` numeral,
`expToObj (a) = (e^θ a)(0^θ)`. Its count is `2^(count a)` (`expToObj_interp`),
the object-language counterpart of the carrier-level `ramTwoPowStep`. -/
def expToObj (θ : RType) (hθ : θ.IsObj) : RIdent natAlgSig [RType.omega (expFun θ)] θ :=
  applyAtZeroObj θ hθ (expAtIdent θ hθ)

/-- Leivant III section 2.4(6)'s size function at an object sort `θ`,
`sz : Ω(θ → θ) → θ`, `sz (a) = addsz(a)(α)`: the size auxiliary `addsz`
evaluated at the `0` numeral `α = 0^θ`. Over `1 + X` the count is the
constructor count `count a + 1` (`szAtIdent_interp`). The committed base-sort
`ramSize` is the `o`-sorted count-identity specialization. -/
def szAtIdent (θ : RType) (hθ : θ.IsObj) : RIdent natAlgSig [RType.omega (expFun θ)] θ :=
  applyAtZeroObj θ hθ (szRecObj θ hθ)

/-- The input-sort chain of the in-system `2_m` family (Leivant III section
2.4(4)): `clockSort 0 θ = θ` and `clockSort (m + 1) θ = Ω(clockSort m θ →
clockSort m θ)`. Each is an object sort (`clockSort_isObj`). -/
def clockSort : Nat → RType → RType
  | 0, θ => θ
  | m + 1, θ => RType.omega (expFun (clockSort m θ))

/-- Every `clockSort m θ` is an object sort (Leivant III section 2.3): `θ` at
`m = 0`, an `Omega` type otherwise. -/
theorem clockSort_isObj : (m : Nat) → (θ : RType) → θ.IsObj → (clockSort m θ).IsObj
  | 0, _θ, hθ => hθ
  | _m + 1, _θ, _hθ => Or.inr rfl

/-- Leivant III section 2.4(4)'s in-system `2_m` family at an object sort `θ`,
`2_m : clockSort m θ → θ`, by induction on `m`: `2_0` the identity, and
`2_{m+1} = 2_m ∘ (value of e^{clockSort m θ} at the 0 numeral)` — the
exponential step `expToObj (clockSort m θ)` lowering the tier from
`clockSort (m + 1) θ` to `clockSort m θ`, followed by `2_m`. An object-language
schema identifier (unlike the carrier-level `ramTwoPow`), assembled by downward
composition (the `ramDeltaIdent` precedent), because the input-sort chain grows.
Its count aligns with `GebLean.tower` (`twoPowIdent_interp`). -/
def twoPowIdent : (m : Nat) → (θ : RType) → θ.IsObj → RIdent natAlgSig [clockSort m θ] θ
  | 0, _θ, _hθ => RIdent.defn ⟨0, finZeroElim, Tm.var 0⟩ finZeroElim
  | m + 1, θ, hθ =>
    RIdent.defn ⟨2,
      (fun j => match j with
        | ⟨0, _⟩ => ([clockSort m θ], θ)
        | ⟨1, _⟩ => ([clockSort (m + 1) θ], clockSort m θ)),
      Tm.op (sig := defnSig natAlgSig 2 _)
        (Sum.inl (Sum.inr ⟨0, by decide⟩))
        (Fin.cons
          (Tm.op (sig := defnSig natAlgSig 2 _)
            (Sum.inl (Sum.inr ⟨1, by decide⟩))
            (Fin.cons (Tm.var 0) finZeroElim))
          finZeroElim)⟩
      (fun j => match j with
        | ⟨0, _⟩ => twoPowIdent m θ hθ
        | ⟨1, _⟩ => expToObj (clockSort m θ) (clockSort_isObj m θ hθ))

/-- Addition's step at the nullary constructor at an object sort `θ`: return the
parameter. The object-sort generalization of the base-sort `addZeroStep`. -/
def addZeroStepObj (θ : RType) : RIdent natAlgSig [θ] θ :=
  RIdent.defn ⟨0, finZeroElim, Tm.var 0⟩ finZeroElim

/-- Addition's step at the unary constructor at an object sort `θ`: the successor
of the recursive result. The object-sort generalization of the base-sort
`addSuccStep`. -/
def addSuccStepObj (θ : RType) (hθ : θ.IsObj) : RIdent natAlgSig [θ, θ] θ :=
  RIdent.defn ⟨0, finZeroElim, tmSuccObj θ hθ (Tm.var 1)⟩ finZeroElim

/-- Addition's step functions at an object sort `θ`: the parameter at the
nullary constructor, its successor at the unary constructor. -/
def addStepsObj (θ : RType) (hθ : θ.IsObj) : (i : Bool) →
    RIdent natAlgSig ([θ] ++ List.replicate (natAlgSig.ar i) θ) θ
  | false => addZeroStepObj θ
  | true => addSuccStepObj θ hθ

/-- Leivant III section 2.4(2)'s addition `+ : θ, Ω θ → θ` at an object sort
`θ`, a ramified monotonic recurrence on the second argument with the first as
parameter: `a + 0 = a` and `a + (n + 1) = (a + n) + 1`. The object-sort
generalization of the base-sort `ramAdd`. -/
def addAtIdent (θ : RType) (hθ : θ.IsObj) :
    RIdent natAlgSig [θ, RType.omega θ] θ :=
  RIdent.mrec [θ] θ (addStepsObj θ hθ)

/-- The context and result sort of the addition identifier that multiplication's
step invokes at an object sort `θ`. -/
def mulHoleIdxObj (θ : RType) : Fin 1 → List RType × RType :=
  Function.const _ ([θ, RType.omega θ], θ)

/-- Multiplication's step at the nullary constructor at an object sort `θ`:
return `0`. The object-sort generalization of the base-sort `mulZeroStep`. -/
def mulZeroStepObj (θ : RType) (hθ : θ.IsObj) : RIdent natAlgSig [RType.omega θ] θ :=
  RIdent.defn ⟨0, finZeroElim, tmZeroObj θ hθ⟩ finZeroElim

/-- Multiplication's step at the unary constructor at an object sort `θ`: add the
parameter to the recursive result, invoking `addAtIdent` through a hole. The
object-sort generalization of the base-sort `mulSuccStep`. -/
def mulSuccStepObj (θ : RType) (hθ : θ.IsObj) :
    RIdent natAlgSig [RType.omega θ, θ] θ :=
  RIdent.defn ⟨1, mulHoleIdxObj θ,
    Tm.op (sig := defnSig natAlgSig 1 (mulHoleIdxObj θ)) (Sum.inl (Sum.inr ⟨0, by decide⟩))
      (Fin.cons (Tm.var 1) (Fin.cons (Tm.var 0) finZeroElim))⟩
    (fun _ => addAtIdent θ hθ)

/-- Multiplication's step functions at an object sort `θ`: `0` at the nullary
constructor, the parameter added to the recursive result at the unary
constructor. -/
def mulStepsObj (θ : RType) (hθ : θ.IsObj) : (i : Bool) →
    RIdent natAlgSig ([RType.omega θ] ++ List.replicate (natAlgSig.ar i) θ) θ
  | false => mulZeroStepObj θ hθ
  | true => mulSuccStepObj θ hθ

/-- Leivant III section 2.4(2)'s multiplication `x : Ω θ, Ω θ → θ` at an object
sort `θ`, a ramified monotonic recurrence on the second argument with the first
as parameter: `x * 0 = 0` and `x * (n + 1) = x * n + x`, the inner addition
supplied by `addAtIdent`. The object-sort generalization of the base-sort
`ramMul`. -/
def mulAtIdent (θ : RType) (hθ : θ.IsObj) :
    RIdent natAlgSig [RType.omega θ, RType.omega θ] θ :=
  RIdent.mrec [RType.omega θ] θ (mulStepsObj θ hθ)

/-- The nullary constructor at an object sort `θ` reads as `0` under `objToNat`:
the carrier-copy transports of the constructor and the numeric reading compose
to the identity, and the empty node has count `0`. -/
theorem objToNat_cFalse (θ : RType) (hθ : θ.IsObj)
    (g : ∀ i : Fin ((constructorSig natAlgSig RType.IsObj).arity
        ((⟨θ, hθ⟩ : {s : RType // s.IsObj}), false)).length,
      RType.interp (FreeAlg natAlgSig)
        (((constructorSig natAlgSig RType.IsObj).arity (⟨θ, hθ⟩, false)).get i)) :
    objToNat hθ (stdConstructorInterp natAlgSig (⟨θ, hθ⟩, false) g) = 0 := by
  unfold objToNat stdConstructorInterp
  refine (congrArg freeAlgToNat (eq_of_heq ((cast_heq _ _).trans (cast_heq _ _)))).trans ?_
  rfl

/-- The unary constructor at an object sort `θ` reads as the successor under
`objToNat`: the constructor's single child, matched (heterogeneously) with an
explicit `interp θ` value `c`, contributes `objToNat c` and the node adds one. -/
theorem objToNat_cSucc (θ : RType) (hθ : θ.IsObj)
    (g : ∀ i : Fin ((constructorSig natAlgSig RType.IsObj).arity
        ((⟨θ, hθ⟩ : {s : RType // s.IsObj}), true)).length,
      RType.interp (FreeAlg natAlgSig)
        (((constructorSig natAlgSig RType.IsObj).arity (⟨θ, hθ⟩, true)).get i))
    (c : RType.interp (FreeAlg natAlgSig) θ)
    (hc : g ⟨0, Nat.zero_lt_one⟩ ≍ c) :
    objToNat hθ (stdConstructorInterp natAlgSig (⟨θ, hθ⟩, true) g) = objToNat hθ c + 1 := by
  unfold objToNat stdConstructorInterp
  refine (congrArg freeAlgToNat (eq_of_heq ((cast_heq _ _).trans (cast_heq _ _)))).trans ?_
  change freeAlgToNat (FreeAlg.mk true _) = freeAlgToNat (cast _ c) + 1
  refine congrArg (· + 1) (congrArg freeAlgToNat ?_)
  exact eq_of_heq ((cast_heq _ _).trans (hc.trans (cast_heq _ _).symm))

/-- Addition's nullary step returns the parameter (under `objToNat`). -/
theorem objToNat_addZeroStepObj (θ : RType) (hθ : θ.IsObj)
    (env : ∀ i : Fin ([θ] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([θ] : Ctx RType).get i)) :
    objToNat hθ ((addZeroStepObj θ).interp env) = objToNat hθ (env 0) :=
  rfl

/-- Addition's unary step is the successor of the recursive result (under
`objToNat`). -/
theorem objToNat_addSuccStepObj (θ : RType) (hθ : θ.IsObj)
    (env : ∀ i : Fin ([θ, θ] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([θ, θ] : Ctx RType).get i)) :
    objToNat hθ ((addSuccStepObj θ hθ).interp env) = objToNat hθ (env 1) + 1 := by
  have hred : (addSuccStepObj θ hθ).interp env
      = cast (RType.interp_isObj (FreeAlg natAlgSig) hθ).symm
          (FreeAlg.mk (A := natAlgSig) true
            (fun _ => cast (RType.interp_isObj (FreeAlg natAlgSig) hθ) (env 1))) := by
    refine congrArg (cast (RType.interp_isObj (FreeAlg natAlgSig) hθ).symm) ?_
    refine congrArg (FreeAlg.mk (A := natAlgSig) true) (funext fun j => ?_)
    induction j using Fin.cases with
    | zero => exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _).symm)
    | succ j' => exact j'.elim0
  unfold objToNat
  rw [hred]
  refine (congrArg freeAlgToNat (eq_of_heq ((cast_heq _ _).trans (cast_heq _ _)))).trans ?_
  rfl

/-- The numeric reading at object sorts is invariant under a heterogeneous
equality of carrier values: values `x`, `y` at (possibly different) object sorts
that are heterogeneously equal read to the same natural. -/
theorem objToNat_cast_heq {s s' : RType} (hs : s.IsObj) (hs' : s'.IsObj)
    {x : RType.interp (FreeAlg natAlgSig) s} {y : RType.interp (FreeAlg natAlgSig) s'}
    (hxy : x ≍ y) : objToNat hs x = objToNat hs' y := by
  unfold objToNat
  exact congrArg freeAlgToNat
    (eq_of_heq ((cast_heq _ _).trans (hxy.trans (cast_heq _ _).symm)))

/-- Addition's recurrence read numerically: on a parameter environment `pe` and a
recurrence argument `s`, the denotation counts to `objToNat (pe 0)` plus the count
of `s`. The object-sort analogue of the committed `freeAlgToNat_ramAdd_recurse`,
via `PolyFix.ind`; the recurrence-environment reads through `θ = θ` transports,
which vanish by definitional proof irrelevance. -/
theorem addObj_recurse (θ : RType) (hθ : θ.IsObj)
    (pe : ∀ i : Fin ([θ] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([θ] : Ctx RType).get i))
    (s : FreeAlg natAlgSig) :
    objToNat hθ (FreeAlg.recurse (A := natAlgSig) (P := Unit)
        (fun i _ _sub phi =>
          (addStepsObj θ hθ i).interp
            (childEnv [θ] θ (natAlgSig.ar i) pe phi)) () s)
      = objToNat hθ (pe 0) + freeAlgToNat s := by
  refine PolyFix.ind (P := natAlgSig.polyEndo)
    (motive := fun {_} s =>
      objToNat hθ (FreeAlg.recurse (A := natAlgSig) (P := Unit)
          (fun i _ _sub phi =>
            (addStepsObj θ hθ i).interp
              (childEnv [θ] θ (natAlgSig.ar i) pe phi)) () s)
        = objToNat hθ (pe 0) + freeAlgToNat s)
    (fun b children ihc => ?_) s
  cases b with
  | false => exact (Nat.add_zero _).symm
  | true =>
    refine (objToNat_addSuccStepObj θ hθ
      (childEnv [θ] θ 1 pe (fun e => FreeAlg.recurse (A := natAlgSig) (P := Unit)
        (fun i _ _sub phi => (addStepsObj θ hθ i).interp
          (childEnv [θ] θ (natAlgSig.ar i) pe phi)) () (children e)))).trans ?_
    change objToNat hθ (FreeAlg.recurse (A := natAlgSig) (P := Unit)
        (fun i _ _sub phi => (addStepsObj θ hθ i).interp
          (childEnv [θ] θ (natAlgSig.ar i) pe phi)) () (children ⟨0, Nat.zero_lt_one⟩)) + 1
      = objToNat hθ (pe 0) + freeAlgToNat (PolyFix.mk _ true children)
    rw [ihc ⟨0, Nat.zero_lt_one⟩]
    change _ + 1 = objToNat hθ (pe 0)
      + (freeAlgToNat (children ⟨0, Nat.zero_lt_one⟩) + 1)
    omega

/-- Addition denotes `+` on an arbitrary environment at `[θ, Ω θ]`. The
environment reads through `θ = θ` and `Ω θ = Ω θ` transports, which vanish by
definitional proof irrelevance. -/
theorem addAtIdent_interp_env (θ : RType) (hθ : θ.IsObj)
    (ρ : ∀ i : Fin ([θ, RType.omega θ] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([θ, RType.omega θ] : Ctx RType).get i)) :
    objToNat hθ ((addAtIdent θ hθ).interp ρ)
      = objToNat hθ (ρ 0) + freeAlgToNat (ρ 1) :=
  addObj_recurse θ hθ (envHead [θ] (RType.omega θ) ρ) (envLast [θ] (RType.omega θ) ρ)

/-- Multiplication's nullary step returns `0` (under `objToNat`). -/
theorem objToNat_mulZeroStepObj (θ : RType) (hθ : θ.IsObj)
    (env : ∀ i : Fin ([RType.omega θ] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([RType.omega θ] : Ctx RType).get i)) :
    objToNat hθ ((mulZeroStepObj θ hθ).interp env) = 0 := by
  have hred : (mulZeroStepObj θ hθ).interp env
      = cast (RType.interp_isObj (FreeAlg natAlgSig) hθ).symm
          (FreeAlg.mk (A := natAlgSig) false finZeroElim) := by
    refine congrArg (cast (RType.interp_isObj (FreeAlg natAlgSig) hθ).symm) ?_
    exact congrArg (FreeAlg.mk (A := natAlgSig) false) (funext fun j => j.elim0)
  unfold objToNat
  rw [hred]
  refine (congrArg freeAlgToNat (eq_of_heq ((cast_heq _ _).trans (cast_heq _ _)))).trans ?_
  rfl

/-- Multiplication's unary step adds the parameter to the recursive result
(under `objToNat`), invoking `addAtIdent`. -/
theorem objToNat_mulSuccStepObj (θ : RType) (hθ : θ.IsObj)
    (env : ∀ i : Fin ([RType.omega θ, θ] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([RType.omega θ, θ] : Ctx RType).get i)) :
    objToNat hθ ((mulSuccStepObj θ hθ).interp env)
      = objToNat hθ (env 1) + freeAlgToNat (env 0) :=
  addAtIdent_interp_env θ hθ _

/-- Multiplication's recurrence read numerically: on a parameter environment `pe`
and a recurrence argument `s`, the denotation counts to `freeAlgToNat (pe 0)`
times the count of `s`. The object-sort analogue of the committed
`freeAlgToNat_ramMul_recurse`, via `PolyFix.ind`. -/
theorem mulObj_recurse (θ : RType) (hθ : θ.IsObj)
    (pe : ∀ i : Fin ([RType.omega θ] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([RType.omega θ] : Ctx RType).get i))
    (s : FreeAlg natAlgSig) :
    objToNat hθ (FreeAlg.recurse (A := natAlgSig) (P := Unit)
        (fun i _ _sub phi =>
          (mulStepsObj θ hθ i).interp
            (childEnv [RType.omega θ] θ (natAlgSig.ar i) pe phi)) () s)
      = freeAlgToNat (pe 0) * freeAlgToNat s := by
  refine PolyFix.ind (P := natAlgSig.polyEndo)
    (motive := fun {_} s =>
      objToNat hθ (FreeAlg.recurse (A := natAlgSig) (P := Unit)
          (fun i _ _sub phi =>
            (mulStepsObj θ hθ i).interp
              (childEnv [RType.omega θ] θ (natAlgSig.ar i) pe phi)) () s)
        = freeAlgToNat (pe 0) * freeAlgToNat s)
    (fun b children ihc => ?_) s
  cases b with
  | false =>
    refine (objToNat_mulZeroStepObj θ hθ _).trans ?_
    exact (Nat.mul_zero _).symm
  | true =>
    refine (objToNat_mulSuccStepObj θ hθ
      (childEnv [RType.omega θ] θ 1 pe (fun e => FreeAlg.recurse (A := natAlgSig) (P := Unit)
        (fun i _ _sub phi => (mulStepsObj θ hθ i).interp
          (childEnv [RType.omega θ] θ (natAlgSig.ar i) pe phi)) () (children e)))).trans ?_
    change objToNat hθ (FreeAlg.recurse (A := natAlgSig) (P := Unit)
        (fun i _ _sub phi => (mulStepsObj θ hθ i).interp
          (childEnv [RType.omega θ] θ (natAlgSig.ar i) pe phi)) ()
          (children ⟨0, Nat.zero_lt_one⟩)) + freeAlgToNat (pe 0)
      = freeAlgToNat (pe 0) * freeAlgToNat (PolyFix.mk _ true children)
    rw [ihc ⟨0, Nat.zero_lt_one⟩]
    change freeAlgToNat (pe 0) * freeAlgToNat (children ⟨0, Nat.zero_lt_one⟩)
        + freeAlgToNat (pe 0)
      = freeAlgToNat (pe 0) * (freeAlgToNat (children ⟨0, Nat.zero_lt_one⟩) + 1)
    rw [Nat.mul_succ]

/-- Multiplication denotes `*` on an arbitrary environment at `[Ω θ, Ω θ]`. -/
theorem mulAtIdent_interp_env (θ : RType) (hθ : θ.IsObj)
    (ρ : ∀ i : Fin ([RType.omega θ, RType.omega θ] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig)
        (([RType.omega θ, RType.omega θ] : Ctx RType).get i)) :
    objToNat hθ ((mulAtIdent θ hθ).interp ρ)
      = freeAlgToNat (ρ 0) * freeAlgToNat (ρ 1) :=
  mulObj_recurse θ hθ (envHead [RType.omega θ] (RType.omega θ) ρ)
    (envLast [RType.omega θ] (RType.omega θ) ρ)

/-- The successor `sc` at an object sort `θ` is the successor of its argument
(under `objToNat`). -/
theorem objToNat_succObj (θ : RType) (hθ : θ.IsObj)
    (env : ∀ i : Fin ([θ] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([θ] : Ctx RType).get i)) :
    objToNat hθ ((succObj θ hθ).interp env) = objToNat hθ (env 0) + 1 := by
  have hred : (succObj θ hθ).interp env
      = cast (RType.interp_isObj (FreeAlg natAlgSig) hθ).symm
          (FreeAlg.mk (A := natAlgSig) true
            (fun _ => cast (RType.interp_isObj (FreeAlg natAlgSig) hθ) (env 0))) := by
    refine congrArg (cast (RType.interp_isObj (FreeAlg natAlgSig) hθ).symm) ?_
    refine congrArg (FreeAlg.mk (A := natAlgSig) true) (funext fun j => ?_)
    induction j using Fin.cases with
    | zero => exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _).symm)
    | succ j' => exact j'.elim0
  unfold objToNat
  rw [hred]
  refine (congrArg freeAlgToNat (eq_of_heq ((cast_heq _ _).trans (cast_heq _ _)))).trans ?_
  rfl

/-- The exponentiation copy's recurrence read numerically: on the empty parameter
environment, a recurrence argument `s`, and an input `x`, the denotation is the
`2^(count s)`-fold iterate of the successor applied to `x`, so its count is
`objToNat x + 2^(count s)`. The object-sort analogue of the committed
`freeAlgToNat_ramExp_recurse`, via `PolyFix.ind` generalizing over `x`; the
self-composition step reads the recursive result through `θ→θ = θ→θ` transports,
which vanish by definitional proof irrelevance. -/
theorem expObj_recurse (θ : RType) (hθ : θ.IsObj)
    (pe : ∀ i : Fin ([] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([] : Ctx RType).get i))
    (s : FreeAlg natAlgSig) (x : RType.interp (FreeAlg natAlgSig) θ) :
    objToNat hθ ((FreeAlg.recurse (A := natAlgSig) (P := Unit)
        (fun i _ _sub phi => (expStepsObj θ hθ i).interp
          (childEnv [] (expFun θ) (natAlgSig.ar i) pe phi)) () s) x)
      = objToNat hθ x + 2 ^ freeAlgToNat s := by
  revert x
  refine PolyFix.ind (P := natAlgSig.polyEndo)
    (motive := fun {_} s => ∀ x, objToNat hθ ((FreeAlg.recurse (A := natAlgSig) (P := Unit)
        (fun i _ _sub phi => (expStepsObj θ hθ i).interp
          (childEnv [] (expFun θ) (natAlgSig.ar i) pe phi)) () s) x)
      = objToNat hθ x + 2 ^ freeAlgToNat s)
    (fun b children ihc => ?_) s
  cases b with
  | false =>
    intro x
    exact (objToNat_succObj θ hθ (Fin.cons x finZeroElim)).trans rfl
  | true =>
    intro x
    have ih0 := ihc ⟨0, Nat.zero_lt_one⟩
    have key : ((FreeAlg.recurse (A := natAlgSig) (P := Unit)
          (fun i _ _sub phi => (expStepsObj θ hθ i).interp
            (childEnv [] (expFun θ) (natAlgSig.ar i) pe phi)) ()
          (PolyFix.mk _ true children)) x)
        = ((FreeAlg.recurse (A := natAlgSig) (P := Unit)
            (fun i _ _sub phi => (expStepsObj θ hθ i).interp
              (childEnv [] (expFun θ) (natAlgSig.ar i) pe phi)) ()
            (children ⟨0, Nat.zero_lt_one⟩))
            ((FreeAlg.recurse (A := natAlgSig) (P := Unit)
              (fun i _ _sub phi => (expStepsObj θ hθ i).interp
                (childEnv [] (expFun θ) (natAlgSig.ar i) pe phi)) ()
              (children ⟨0, Nat.zero_lt_one⟩)) x)) := rfl
    rw [key, ih0, ih0]
    change objToNat hθ x + 2 ^ freeAlgToNat (children ⟨0, Nat.zero_lt_one⟩)
        + 2 ^ freeAlgToNat (children ⟨0, Nat.zero_lt_one⟩)
      = objToNat hθ x + 2 ^ (freeAlgToNat (children ⟨0, Nat.zero_lt_one⟩) + 1)
    rw [Nat.pow_succ]
    omega

/-- Leivant III section 2.4(3): the exponentiation copy `e^θ` iterates the
successor. On the recurrence argument `ρ 0` (a numeral at `Ω(θ → θ)`) and an
input `x`, the denotation `e^θ (ρ 0) (x)` has count `objToNat x + 2^(count (ρ 0))`.
The form the `2_m` clock family consumes. -/
theorem expAtIdent_interp (θ : RType) (hθ : θ.IsObj)
    (ρ : ∀ i : Fin ([RType.omega (expFun θ)] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig)
        (([RType.omega (expFun θ)] : Ctx RType).get i))
    (x : RType.interp (FreeAlg natAlgSig) θ) :
    objToNat hθ ((expAtIdent θ hθ).interp ρ x)
      = objToNat hθ x + 2 ^ freeAlgToNat (ρ 0) :=
  expObj_recurse θ hθ (envHead [] (RType.omega (expFun θ)) ρ)
    (envLast [] (RType.omega (expFun θ)) ρ) x

/-- The `0` numeral value at an object sort `θ`: the nullary constructor,
transported to the carrier copy. Reads to `0` under `objToNat`. -/
def zeroObjVal (θ : RType) (hθ : θ.IsObj) : RType.interp (FreeAlg natAlgSig) θ :=
  cast (RType.interp_isObj (FreeAlg natAlgSig) hθ).symm
    (FreeAlg.mk (A := natAlgSig) false finZeroElim)

/-- The `0` numeral value reads to `0` under `objToNat`. -/
theorem objToNat_zeroObjVal (θ : RType) (hθ : θ.IsObj) :
    objToNat hθ (zeroObjVal θ hθ) = 0 := by
  unfold objToNat zeroObjVal
  refine (congrArg freeAlgToNat (eq_of_heq ((cast_heq _ _).trans (cast_heq _ _)))).trans ?_
  rfl

/-- Applying a function `f : θ → θ` to the `0` numeral: `evalAtZeroIdent (f)`
denotes `f (0^θ)`. The application former reduces through `defnApp_eval`; the
`0`-numeral term evaluates to `zeroObjVal`. -/
theorem evalAtZeroIdent_interp (θ : RType) (hθ : θ.IsObj)
    (env : ∀ i : Fin ([expFun θ] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([expFun θ] : Ctx RType).get i)) :
    objToNat hθ ((evalAtZeroIdent θ hθ).interp env)
      = objToNat hθ ((env 0) (zeroObjVal θ hθ)) := by
  refine congrArg (objToNat hθ) ?_
  unfold evalAtZeroIdent
  rw [RIdent.interp_defn, defnApp_eval]
  refine congrArg (env 0) ?_
  unfold zeroObjVal
  refine congrArg (cast (RType.interp_isObj (FreeAlg natAlgSig) hθ).symm) ?_
  exact congrArg (FreeAlg.mk (A := natAlgSig) false) (funext fun j => j.elim0)

/-- The wrapper's denotation is the recurrence's value at the recurrence argument,
applied to the `0` numeral of `θ`: `applyAtZeroObj rec (a) = (rec a)(0^θ)`. The
composite fully reduces to `rec`'s value applied to the `0`-numeral term; the
proof matches at that reduced application and rewrites the recurrence-argument
environment (through `θ→θ = θ→θ` transports) and the `0`-numeral to `zeroObjVal`. -/
theorem applyAtZeroObj_interp (θ : RType) (hθ : θ.IsObj)
    (rec : RIdent natAlgSig [RType.omega (expFun θ)] (expFun θ))
    (ρ : ∀ i : Fin ([RType.omega (expFun θ)] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig)
        (([RType.omega (expFun θ)] : Ctx RType).get i)) :
    objToNat hθ ((applyAtZeroObj θ hθ rec).interp ρ)
      = objToNat hθ ((rec.interp ρ) (zeroObjVal θ hθ)) := by
  refine congrArg (objToNat hθ) ?_
  refine congr (congrArg rec.interp (funext fun i => ?_)) ?_
  · induction i using Fin.cases with
    | zero => rfl
    | succ i' => exact i'.elim0
  · unfold zeroObjVal
    refine congrArg (cast (RType.interp_isObj (FreeAlg natAlgSig) hθ).symm) ?_
    exact congrArg (FreeAlg.mk (A := natAlgSig) false) (funext fun j => j.elim0)

/-- Leivant III section 2.4(3) ("more generally"): the exponentiation copy of
type `Ω(θ → θ) → θ` counts to `2^(count a)`. The wrapper feeds `e^θ` the `0`
numeral (count `0`), so `e^θ (a) (0)` has count `0 + 2^(count a)`. -/
theorem expToObj_interp (θ : RType) (hθ : θ.IsObj)
    (ρ : ∀ i : Fin ([RType.omega (expFun θ)] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig)
        (([RType.omega (expFun θ)] : Ctx RType).get i)) :
    objToNat hθ ((expToObj θ hθ).interp ρ) = 2 ^ freeAlgToNat (ρ 0) := by
  rw [expToObj, applyAtZeroObj_interp, expAtIdent_interp, objToNat_zeroObjVal,
    Nat.zero_add]

/-- The size auxiliary's recurrence read numerically: on the empty parameter
environment, a recurrence argument `s`, and an input `x`, `addsz (s) (x)` counts
to `objToNat x + count s + 1` (the `(count s + 1)`-fold iterate of the
successor). By `PolyFix.ind` generalizing over `x`. -/
theorem szObj_recurse (θ : RType) (hθ : θ.IsObj)
    (pe : ∀ i : Fin ([] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([] : Ctx RType).get i))
    (s : FreeAlg natAlgSig) (x : RType.interp (FreeAlg natAlgSig) θ) :
    objToNat hθ ((FreeAlg.recurse (A := natAlgSig) (P := Unit)
        (fun i _ _sub phi => (szStepsObj θ hθ i).interp
          (childEnv [] (expFun θ) (natAlgSig.ar i) pe phi)) () s) x)
      = objToNat hθ x + freeAlgToNat s + 1 := by
  revert x
  refine PolyFix.ind (P := natAlgSig.polyEndo)
    (motive := fun {_} s => ∀ x, objToNat hθ ((FreeAlg.recurse (A := natAlgSig) (P := Unit)
        (fun i _ _sub phi => (szStepsObj θ hθ i).interp
          (childEnv [] (expFun θ) (natAlgSig.ar i) pe phi)) () s) x)
      = objToNat hθ x + freeAlgToNat s + 1)
    (fun b children ihc => ?_) s
  cases b with
  | false =>
    intro x
    exact (objToNat_succObj θ hθ (Fin.cons x finZeroElim)).trans rfl
  | true =>
    intro x
    have ih0 := ihc ⟨0, Nat.zero_lt_one⟩
    have key : ((FreeAlg.recurse (A := natAlgSig) (P := Unit)
          (fun i _ _sub phi => (szStepsObj θ hθ i).interp
            (childEnv [] (expFun θ) (natAlgSig.ar i) pe phi)) ()
          (PolyFix.mk _ true children)) x)
        = ((FreeAlg.recurse (A := natAlgSig) (P := Unit)
            (fun i _ _sub phi => (szStepsObj θ hθ i).interp
              (childEnv [] (expFun θ) (natAlgSig.ar i) pe phi)) ()
            (children ⟨0, Nat.zero_lt_one⟩))
            ((succObj θ hθ).interp (Fin.cons x finZeroElim))) := rfl
    rw [key, ih0, objToNat_succObj θ hθ (Fin.cons x finZeroElim)]
    change objToNat hθ x + 1 + freeAlgToNat (children ⟨0, Nat.zero_lt_one⟩) + 1
      = objToNat hθ x + (freeAlgToNat (children ⟨0, Nat.zero_lt_one⟩) + 1) + 1
    omega

/-- The size auxiliary `addsz` at the recurrence argument `ρ 0` and an input `x`:
`addsz (ρ 0) (x)` counts to `objToNat x + count (ρ 0) + 1`. -/
theorem szRecObj_interp (θ : RType) (hθ : θ.IsObj)
    (ρ : ∀ i : Fin ([RType.omega (expFun θ)] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig)
        (([RType.omega (expFun θ)] : Ctx RType).get i))
    (x : RType.interp (FreeAlg natAlgSig) θ) :
    objToNat hθ ((szRecObj θ hθ).interp ρ x)
      = objToNat hθ x + freeAlgToNat (ρ 0) + 1 :=
  szObj_recurse θ hθ (envHead [] (RType.omega (expFun θ)) ρ)
    (envLast [] (RType.omega (expFun θ)) ρ) x

/-- Leivant III section 2.4(6): the size function at an object sort `θ` counts the
constructors, `objToNat (sz a) = count a + 1`. -/
theorem szAtIdent_interp (θ : RType) (hθ : θ.IsObj)
    (ρ : ∀ i : Fin ([RType.omega (expFun θ)] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig)
        (([RType.omega (expFun θ)] : Ctx RType).get i)) :
    objToNat hθ ((szAtIdent θ hθ).interp ρ) = freeAlgToNat (ρ 0) + 1 := by
  rw [szAtIdent, applyAtZeroObj_interp, szRecObj_interp, objToNat_zeroObjVal,
    Nat.zero_add]

-- Keep the composite's inner step `expToObj (clockSort m θ)` folded in the
-- successor case below, so its occurrence matches `expToObj_interp` instead of
-- unfolding into its large body under `whnf`.
attribute [local irreducible] expToObj

/-- Leivant III section 2.4(4): the in-system `2_m` family aligns with the tower
of twos `GebLean.tower` (`GebLean/Utilities/Tower.lean`): on an input `a` at
`clockSort m θ`, `objToNat (2_m (a)) = tower m (objToNat a)`. Proved by induction
on `m`; each step composes the recursive `2_m` with the exponential lowering step
`expToObj (clockSort m θ)`, and `GebLean.tower_comp` identifies
`tower m (2 ^ ·)` with `tower (m + 1)`. The Phase 5 clock ingredient, the
object-language counterpart of the carrier-level `ramTwoPow_interp`. -/
theorem twoPowIdent_interp :
    (m : Nat) → (θ : RType) → (hθ : θ.IsObj) →
    (ρ : ∀ i : Fin ([clockSort m θ] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([clockSort m θ] : Ctx RType).get i)) →
    objToNat hθ ((twoPowIdent m θ hθ).interp ρ)
      = GebLean.tower m (objToNat (clockSort_isObj m θ hθ) (ρ 0))
  | 0, _θ, _hθ, _ρ => rfl
  | m + 1, θ, hθ, ρ => by
    refine (twoPowIdent_interp m θ hθ _).trans
      ((congrArg (GebLean.tower m)
        (expToObj_interp (clockSort m θ) (clockSort_isObj m θ hθ) _)).trans ?_)
    change GebLean.tower m (2 ^ freeAlgToNat (ρ 0))
      = GebLean.tower (m + 1) (freeAlgToNat (ρ 0))
    rw [← GebLean.tower_comp m 1]
    rfl

end GebLean.Ramified
