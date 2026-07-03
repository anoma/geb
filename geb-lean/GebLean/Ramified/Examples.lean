import GebLean.Ramified.OmegaShift
import GebLean.Utilities.Tower

/-!
# The section 2.4 example ladder

The worked examples of Leivant III section 2.4 over the `1 + X` word algebra
`natAlgSig`: the downward coercions between object sorts, addition,
multiplication, the exponentiation `e` by second-order recurrence, the `2_m`
ladder of towers of twos, and the size function, each a schema identifier of the
higher-order system (or, for the ladder, a carrier-level composite of one) with
an interpretation lemma reading its denotation on the standard carrier as the
intended arithmetic operation. A numeric reading of the standard carrier
`FreeAlg natAlgSig` (`natToFreeAlg`, `freeAlgToNat`, with their round trips)
states those interpretation lemmas as identities of natural numbers.

## Main definitions

* `natToFreeAlg`, `freeAlgToNat` — the numeric reading of the standard carrier
  `FreeAlg natAlgSig`, a copy of the naturals.
* `objToNat` — the numeric reading at an object sort, through the carrier-copy
  equality (needed at the tower sorts `Omega^m o`).
* `ramKappa` — the single `Omega`-lowering coercion `Omega^{m+1} o -> Omega^m o`.
* `ramDeltaIdent` — the tower-sort coercion `Omega^m o -> o`, extensionally the
  identity.
* `ramAdd` — addition `o, Omega o -> o`.
* `ramMul` — multiplication `Omega o, Omega o -> o`.
* `ramComp`, `ramSucc` — the two-fold application `f (g x)` and the successor
  wrapper `succ x`, the identifiers the exponentiation clauses iterate.
* `ramExp` — the exponentiation `e : Omega(o -> o) -> (o -> o)`, a ramified
  monotonic second-order recurrence.
* `ramTwoPow` — the ladder `2_m`, the `m`-fold carrier-level composite of the
  single exponential step of `ramExp`.
* `ramSize` — the size function, extensionally the identity on `o`.

## Main statements

* `freeAlgToNat_natToFreeAlg` — the numeric reading is a left inverse; Phase 3
  supplies the right inverse when it packages the equivalence.
* `ramKappa_interp`, `ramDeltaIdent_interp` — the coercions denote the identity
  on the carrier.
* `ramAdd_interp` — addition denotes `+`.
* `ramMul_interp` — multiplication denotes `*`.
* `ramExp_interp` — exponentiation iterates the successor:
  `e (n) (x)` has count `count x + 2^(count n)`.
* `ramTwoPow_interp` — the ladder `2_m` aligns with `GebLean.tower`:
  `count (2_m (x)) = tower m (count x)`.
* `ramSize_interp` — the size function denotes the identity.

## Implementation notes

Every ladder item is a schema identifier (`RIdent natAlgSig`), interpreted by
`RIdent.interp` on the standard carriers `RType.interp (FreeAlg natAlgSig)`,
which at an object sort is a copy of `FreeAlg natAlgSig` (Leivant III section
2.7). The numeric reading `natToFreeAlg`/`freeAlgToNat` is the pair of
directions of the equivalence `FreeAlg natAlgSig ≃ ℕ`; Phase 3 packages it as
that equivalence, supplying the right-inverse round trip. The interpretation
lemmas are stated on numeric inputs
`natToFreeAlg a` and read out by `freeAlgToNat`, so they read as identities of
naturals.

The two coercions of Leivant III section 2.4(1) are realized here at the
tower sorts `Omega^m o` (the object-sort chains Phase 5 consumes): the single
`Omega`-lowering step `kappa` is the auxiliary coercion `kappaHatIdent`
(`GebLean/Ramified/OmegaShift.lean`) at `Omega^m o`, and the full lowering
`delta : Omega^m o -> o` is `ramDeltaIdent`, the `m`-fold composite of those
steps. Both denote the identity on the carrier (`kappaHatIdent_interp`,
`ramDeltaIdent_interp`).

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`. The coercions `kappa`,
kappa-hat, and `delta`, each defined by ramified recurrence and extensionally
the identity, are section 2.4(1); addition and multiplication are section
2.4(2); the exponentiation `e` by second-order recurrence is section 2.4(3);
the `2_m` ladder is section 2.4(4); the size function is section 2.4(6); every
object sort denotes a copy of the base carrier in section 2.7. The `2_m` ladder
aligns with the tower of twos `GebLean.tower` (`GebLean/Utilities/Tower.lean`).
The realization through this development's polynomial-endofunctor stack
(decision 8) is novel packaging.

## Tags

ramified recurrence, example, coercion, addition, multiplication,
exponentiation, size, elementary complexity, tower
-/

namespace GebLean.Ramified

open CategoryTheory

/-- A natural number as an element of the standard carrier `FreeAlg natAlgSig`:
`0` is the nullary constructor and `n + 1` the unary constructor applied to `n`.
The `ofNat` direction of the equivalence `FreeAlg natAlgSig ≃ ℕ` that Phase 3
packages. -/
def natToFreeAlg : Nat → FreeAlg natAlgSig
  | 0 => FreeAlg.mk false finZeroElim
  | n + 1 => FreeAlg.mk true (fun _ => natToFreeAlg n)

/-- An element of the standard carrier `FreeAlg natAlgSig` as the natural number
counting its unary constructors. The `toNat` direction of the equivalence
`FreeAlg natAlgSig ≃ ℕ` that Phase 3 packages. Realized by the free-algebra
recurrence `FreeAlg.recurse`. -/
def freeAlgToNat (t : FreeAlg natAlgSig) : Nat :=
  FreeAlg.recurse (A := natAlgSig) (P := Unit)
    (fun b _ _sub rec => match b with
      | false => 0
      | true => rec ⟨0, Nat.zero_lt_one⟩ + 1) () t

@[simp] theorem freeAlgToNat_natToFreeAlg (n : Nat) :
    freeAlgToNat (natToFreeAlg n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (· + 1) ih

/-- The numeric reading of an object-sort carrier value, through the carrier-copy
equality of the object sort (Leivant III section 2.7): for `s` an object sort,
`RType.interp (FreeAlg natAlgSig) s` is a copy of `FreeAlg natAlgSig`, and
`objToNat` reads a value there as a natural. Needed at the tower sorts
`Omega^m o`, whose denotation does not reduce to the carrier for a symbolic `m`. -/
def objToNat {s : RType} (hs : s.IsObj)
    (x : RType.interp (FreeAlg natAlgSig) s) : Nat :=
  freeAlgToNat (cast (RType.interp_isObj (FreeAlg natAlgSig) hs) x)

/-- The numeric reading is invariant under a carrier-copy transport between
object sorts. -/
theorem objToNat_cast {s s' : RType} (hs : s.IsObj) (hs' : s'.IsObj)
    (h : RType.interp (FreeAlg natAlgSig) s = RType.interp (FreeAlg natAlgSig) s')
    (x : RType.interp (FreeAlg natAlgSig) s) :
    objToNat hs' (cast h x) = objToNat hs x :=
  congrArg freeAlgToNat
    (eq_of_heq (((cast_heq _ _).trans (cast_heq _ _)).trans (cast_heq _ _).symm))

/-- Leivant III section 2.4(1)'s coercion `kappa`, at the tower sorts: the single
`Omega`-lowering step `Omega^{m+1} o -> Omega^m o`, realized as the auxiliary
coercion `kappaHatIdent` (`GebLean/Ramified/OmegaShift.lean`) at the object sort
`Omega^m o`, whose recurrence reconstructs its argument constructor by
constructor. Extensionally the identity on the carrier (`ramKappa_interp`). The
paper's `kappa` is a downward coercion between object sorts; the tower-sort
chain is the instance Phase 5 consumes. -/
def ramKappa (m : Nat) : RIdent natAlgSig [RType.tower (m + 1)] (RType.tower m) :=
  kappaHatIdent natAlgSig (RType.tower m) (RType.tower_isObj m)

/-- The context and result sort of the two identifiers that the lowering
coercion `delta` at step `m + 1` invokes: the coercion `delta` at `m` and the
single `Omega`-lowering step `kappa` at `m`. -/
def deltaHoleIdx (m : Nat) : Fin 2 → List RType × RType :=
  fun j => match j with
    | ⟨0, _⟩ => ([RType.tower m], RType.o)
    | ⟨1, _⟩ => ([RType.omega (RType.tower m)], RType.tower m)

/-- Leivant III section 2.4(1)'s coercion `delta`, at the tower sorts:
`delta : Omega^m o -> o`, the `m`-fold composite of the single `Omega`-lowering
step `kappa`, lowering all the way to `o`. Realized (decision 8) by recursion on
`m`: the identity at `o`, and at `m + 1` an explicit definition whose body
applies `delta` at `m` to `kappa` at `m` applied to the recurrence argument.
Extensionally the identity on the carrier (`ramDeltaIdent_interp`). The paper's
`delta_theta : theta -> o` is a downward coercion; the tower-sort chain is the
instance Phase 5 consumes. -/
def ramDeltaIdent : (m : Nat) → RIdent natAlgSig [RType.tower m] RType.o
  | 0 => RIdent.defn ⟨0, finZeroElim, Tm.var 0⟩ finZeroElim
  | m + 1 =>
    RIdent.defn ⟨2, deltaHoleIdx m,
      Tm.op (sig := defnSig natAlgSig 2 (deltaHoleIdx m)) (Sum.inl (Sum.inr ⟨0, by decide⟩))
        (Fin.cons
          (Tm.op (sig := defnSig natAlgSig 2 (deltaHoleIdx m))
            (Sum.inl (Sum.inr ⟨1, by decide⟩))
            (Fin.cons (Tm.var 0) finZeroElim))
          finZeroElim)⟩
      (fun j => match j with
        | ⟨0, _⟩ => ramDeltaIdent m
        | ⟨1, _⟩ => kappaHatIdent natAlgSig (RType.tower m) (RType.tower_isObj m))

/-- The single `Omega`-lowering step denotes the identity on the carrier copy,
stated at the omega-form context so that `kappaHatIdent_interp` applies directly.
-/
theorem kappaHatIdent_objToNat (m : Nat)
    (ρ : ∀ i : Fin ([RType.omega (RType.tower m)] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig)
        (([RType.omega (RType.tower m)] : Ctx RType).get i)) :
    objToNat (RType.tower_isObj m)
        ((kappaHatIdent natAlgSig (RType.tower m) (RType.tower_isObj m)).interp ρ)
      = objToNat (RType.tower_isObj (m + 1)) (ρ 0) := by
  rw [kappaHatIdent_interp]
  exact objToNat_cast (RType.tower_isObj (m + 1)) (RType.tower_isObj m) _ (ρ 0)

/-- Leivant III section 2.4(1): the single `Omega`-lowering coercion denotes the
identity on the carrier copy. -/
theorem ramKappa_interp (m : Nat)
    (ρ : ∀ i : Fin ([RType.tower (m + 1)] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([RType.tower (m + 1)] : Ctx RType).get i)) :
    objToNat (RType.tower_isObj m) ((ramKappa m).interp ρ)
      = objToNat (RType.tower_isObj (m + 1)) (ρ 0) :=
  kappaHatIdent_objToNat m ρ

/-- Leivant III section 2.4(1): the lowering coercion `delta : Omega^m o -> o`
denotes the identity on the carrier copy. Proved by induction on `m`; each step
composes the identity denotations of `delta` at `m` and `kappa` at `m`. -/
theorem ramDeltaIdent_interp :
    (m : Nat) → (ρ : ∀ i : Fin ([RType.tower m] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([RType.tower m] : Ctx RType).get i)) →
      freeAlgToNat ((ramDeltaIdent m).interp ρ) = objToNat (RType.tower_isObj m) (ρ 0)
  | 0, _ρ => congrArg freeAlgToNat (eq_of_heq (cast_heq _ _).symm)
  | m + 1, _ρ => (ramDeltaIdent_interp m _).trans (kappaHatIdent_objToNat m _)

/-- The base object sort `o` as an object-sort witness. -/
def oObj : { s : RType // RType.IsObj s } := ⟨RType.o, Or.inl rfl⟩

/-- The nullary-constructor term over a definition signature. -/
def tmZero {n : Nat} {h : Fin n → List RType × RType} {Γ : Ctx RType} :
    Tm (defnSig natAlgSig n h) Γ RType.o :=
  Tm.op (sig := defnSig natAlgSig n h) (Sum.inl (Sum.inl (Sum.inl (oObj, false)))) finZeroElim

/-- The unary-constructor term over a definition signature. -/
def tmSucc {n : Nat} {h : Fin n → List RType × RType} {Γ : Ctx RType}
    (t : Tm (defnSig natAlgSig n h) Γ RType.o) :
    Tm (defnSig natAlgSig n h) Γ RType.o :=
  Tm.op (sig := defnSig natAlgSig n h) (Sum.inl (Sum.inl (Sum.inl (oObj, true))))
    (Fin.cons t finZeroElim)

/-- Addition's step at the nullary constructor: return the parameter. -/
def addZeroStep : RIdent natAlgSig [RType.o] RType.o :=
  RIdent.defn ⟨0, finZeroElim, Tm.var 0⟩ finZeroElim

/-- Addition's step at the unary constructor: the successor of the recursive
result. -/
def addSuccStep : RIdent natAlgSig [RType.o, RType.o] RType.o :=
  RIdent.defn ⟨0, finZeroElim, tmSucc (Tm.var 1)⟩ finZeroElim

/-- Addition's step functions: the parameter at the nullary constructor, its
successor at the unary constructor. -/
def ramAddSteps : (i : Bool) →
    RIdent natAlgSig ([RType.o] ++ List.replicate (natAlgSig.ar i) RType.o) RType.o
  | false => addZeroStep
  | true => addSuccStep

/-- Leivant III section 2.4(2)'s addition `+ : o, Omega o -> o`, as a ramified
monotonic recurrence on the second argument with the first as parameter:
`a + 0 = a` and `a + (n + 1) = (a + n) + 1`. -/
def ramAdd : RIdent natAlgSig [RType.o, RType.omega RType.o] RType.o :=
  RIdent.mrec [RType.o] RType.o ramAddSteps

/-- The environment at addition's context `[o, Omega o]`. -/
def addEnv (a b : FreeAlg natAlgSig) :
    ∀ i : Fin ([RType.o, RType.omega RType.o] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig)
        (([RType.o, RType.omega RType.o] : Ctx RType).get i) :=
  Fin.cons a (Fin.cons b finZeroElim)

/-- Addition's recurrence read numerically: on a parameter environment `pe` and
a recurrence argument `s`, the denotation counts to `pe 0` plus the count of
`s`. Proved by structural induction on `s` via `PolyFix.ind` (decision 8);
`freeAlgToNat` erases the carrier-copy transports of the step interpretations. -/
theorem freeAlgToNat_ramAdd_recurse
    (pe : ∀ i : Fin ([RType.o] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([RType.o] : Ctx RType).get i))
    (s : FreeAlg natAlgSig) :
    freeAlgToNat (FreeAlg.recurse (A := natAlgSig) (P := Unit)
        (fun i _ _sub phi =>
          (ramAddSteps i).interp
            (childEnv [RType.o] RType.o (natAlgSig.ar i) pe phi)) () s)
      = freeAlgToNat (pe 0) + freeAlgToNat s := by
  refine PolyFix.ind (P := natAlgSig.polyEndo)
    (motive := fun {_} s =>
      freeAlgToNat (FreeAlg.recurse (A := natAlgSig) (P := Unit)
          (fun i _ _sub phi =>
            (ramAddSteps i).interp
              (childEnv [RType.o] RType.o (natAlgSig.ar i) pe phi)) () s)
        = freeAlgToNat (pe 0) + freeAlgToNat s)
    (fun b children ihc => ?_) s
  cases b with
  | false => exact (Nat.add_zero _).symm
  | true =>
    have h := ihc ⟨0, by decide⟩
    change freeAlgToNat (FreeAlg.recurse (A := natAlgSig) (P := Unit)
        (fun i _ _sub phi =>
          (ramAddSteps i).interp
            (childEnv [RType.o] RType.o (natAlgSig.ar i) pe phi)) ()
        (children ⟨0, by decide⟩)) + 1
      = freeAlgToNat (pe 0)
        + (freeAlgToNat (children ⟨0, by decide⟩) + 1)
    rw [h]; omega

/-- Addition denotes `+` on an arbitrary environment: `freeAlgToNat` of the
denotation is the sum of the counts of the two context entries. -/
theorem ramAdd_interp_env
    (ρ : ∀ i : Fin ([RType.o, RType.omega RType.o] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig)
        (([RType.o, RType.omega RType.o] : Ctx RType).get i)) :
    freeAlgToNat (ramAdd.interp ρ) = freeAlgToNat (ρ 0) + freeAlgToNat (ρ 1) :=
  freeAlgToNat_ramAdd_recurse
    (envHead [RType.o] (RType.omega RType.o) ρ)
    (envLast [RType.o] (RType.omega RType.o) ρ)

/-- Addition denotes `+` on carrier elements: `freeAlgToNat` of the denotation
is the sum of the counts. -/
theorem ramAdd_interp_carrier (a b : FreeAlg natAlgSig) :
    freeAlgToNat (ramAdd.interp (addEnv a b))
      = freeAlgToNat a + freeAlgToNat b :=
  ramAdd_interp_env (addEnv a b)

/-- Leivant III section 2.4(2): addition denotes `+`. On numeric inputs the
denotation of `ramAdd` reads out as the sum. -/
theorem ramAdd_interp (a b : Nat) :
    freeAlgToNat (ramAdd.interp (addEnv (natToFreeAlg a) (natToFreeAlg b)))
      = a + b := by
  rw [ramAdd_interp_carrier, freeAlgToNat_natToFreeAlg, freeAlgToNat_natToFreeAlg]

/-- The context and result sort of the addition identifier that
multiplication's step invokes. -/
def mulHoleIdx : Fin 1 → List RType × RType :=
  Function.const _ ([RType.o, RType.omega RType.o], RType.o)

/-- Multiplication's step at the nullary constructor: return `0`. -/
def mulZeroStep : RIdent natAlgSig [RType.omega RType.o] RType.o :=
  RIdent.defn ⟨0, finZeroElim, tmZero⟩ finZeroElim

/-- Multiplication's step at the unary constructor: add the parameter to the
recursive result, invoking `ramAdd` through a hole. -/
def mulSuccStep : RIdent natAlgSig [RType.omega RType.o, RType.o] RType.o :=
  RIdent.defn ⟨1, mulHoleIdx,
    Tm.op (sig := defnSig natAlgSig 1 mulHoleIdx) (Sum.inl (Sum.inr ⟨0, by decide⟩))
      (Fin.cons (Tm.var 1) (Fin.cons (Tm.var 0) finZeroElim))⟩
    (fun _ => ramAdd)

/-- Multiplication's step functions: `0` at the nullary constructor, the
parameter added to the recursive result at the unary constructor. -/
def mulSteps : (i : Bool) →
    RIdent natAlgSig
      ([RType.omega RType.o] ++ List.replicate (natAlgSig.ar i) RType.o) RType.o
  | false => mulZeroStep
  | true => mulSuccStep

/-- Leivant III section 2.4(2)'s multiplication `x : Omega o, Omega o -> o`, as a
ramified monotonic recurrence on the second argument with the first as
parameter: `x * 0 = 0` and `x * (n + 1) = x * n + x`, the inner addition
supplied by `ramAdd`. -/
def ramMul : RIdent natAlgSig [RType.omega RType.o, RType.omega RType.o] RType.o :=
  RIdent.mrec [RType.omega RType.o] RType.o mulSteps

/-- The environment at multiplication's context `[Omega o, Omega o]`. -/
def mulEnv (x y : FreeAlg natAlgSig) :
    ∀ i : Fin ([RType.omega RType.o, RType.omega RType.o] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig)
        (([RType.omega RType.o, RType.omega RType.o] : Ctx RType).get i) :=
  Fin.cons x (Fin.cons y finZeroElim)

/-- Multiplication's recurrence step on the carrier, parameterized by the
parameter environment. The `Unit` accumulator and the subterms are required by
the `FreeAlg.recurse` step signature but unused in the monotonic step. -/
@[nolint unusedArguments]
def mulStep
    (pe : ∀ i : Fin ([RType.omega RType.o] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([RType.omega RType.o] : Ctx RType).get i)) :
    (i : Bool) → Unit → (Fin (natAlgSig.ar i) → FreeAlg natAlgSig) →
      (Fin (natAlgSig.ar i) → RType.interp (FreeAlg natAlgSig) RType.o) →
      RType.interp (FreeAlg natAlgSig) RType.o :=
  fun i _ _sub phi =>
    (mulSteps i).interp (childEnv [RType.omega RType.o] RType.o (natAlgSig.ar i) pe phi)

/-- Multiplication's recurrence read numerically: on a parameter environment
`pe` and a recurrence argument `s`, the denotation counts to `pe 0` times the
count of `s`. Proved by structural induction on `s` via `PolyFix.ind`; the
unary step invokes `ramAdd_interp_env` on the hole's environment. -/
theorem freeAlgToNat_ramMul_recurse
    (pe : ∀ i : Fin ([RType.omega RType.o] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([RType.omega RType.o] : Ctx RType).get i))
    (s : FreeAlg natAlgSig) :
    freeAlgToNat (FreeAlg.recurse (A := natAlgSig) (P := Unit) (mulStep pe) () s)
      = freeAlgToNat (pe 0) * freeAlgToNat s := by
  refine PolyFix.ind (P := natAlgSig.polyEndo)
    (motive := fun {_} s =>
      freeAlgToNat (FreeAlg.recurse (A := natAlgSig) (P := Unit) (mulStep pe) () s)
        = freeAlgToNat (pe 0) * freeAlgToNat s)
    (fun b children ihc => ?_) s
  cases b with
  | false => exact (Nat.mul_zero _).symm
  | true =>
    have h := ihc ⟨0, by decide⟩
    have hstep : freeAlgToNat (FreeAlg.recurse (A := natAlgSig) (P := Unit)
        (mulStep pe) () (PolyFix.mk PUnit.unit true children))
        = freeAlgToNat (FreeAlg.recurse (A := natAlgSig) (P := Unit)
            (mulStep pe) () (children ⟨0, by decide⟩)) + freeAlgToNat (pe 0) :=
      ramAdd_interp_env _
    have hm : freeAlgToNat (PolyFix.mk PUnit.unit true children)
        = freeAlgToNat (children ⟨0, by decide⟩) + 1 := rfl
    rw [hstep, h, hm, Nat.mul_succ]

/-- Multiplication denotes `*` on an arbitrary environment. -/
theorem ramMul_interp_env
    (ρ : ∀ i : Fin ([RType.omega RType.o, RType.omega RType.o] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig)
        (([RType.omega RType.o, RType.omega RType.o] : Ctx RType).get i)) :
    freeAlgToNat (ramMul.interp ρ) = freeAlgToNat (ρ 0) * freeAlgToNat (ρ 1) :=
  freeAlgToNat_ramMul_recurse
    (envHead [RType.omega RType.o] (RType.omega RType.o) ρ)
    (envLast [RType.omega RType.o] (RType.omega RType.o) ρ)

/-- Multiplication denotes `*` on carrier elements. -/
theorem ramMul_interp_carrier (x y : FreeAlg natAlgSig) :
    freeAlgToNat (ramMul.interp (mulEnv x y))
      = freeAlgToNat x * freeAlgToNat y :=
  ramMul_interp_env (mulEnv x y)

/-- Leivant III section 2.4(2): multiplication denotes `*`. On numeric inputs the
denotation of `ramMul` reads out as the product. -/
theorem ramMul_interp (x y : Nat) :
    freeAlgToNat (ramMul.interp (mulEnv (natToFreeAlg x) (natToFreeAlg y)))
      = x * y := by
  rw [ramMul_interp_carrier, freeAlgToNat_natToFreeAlg, freeAlgToNat_natToFreeAlg]

/-- The size clause at the nullary constructor: return `0`. -/
def sizeZeroClause : RIdent natAlgSig [] RType.o :=
  RIdent.defn ⟨0, finZeroElim, tmZero⟩ finZeroElim

/-- The size clause at the unary constructor: the successor of the subterm. Over
`1 + X` this reconstructs the recurrence argument, so the size function is the
identity. -/
def sizeSuccClause : RIdent natAlgSig [RType.o] RType.o :=
  RIdent.defn ⟨0, finZeroElim, tmSucc (Tm.var 0)⟩ finZeroElim

/-- The size clauses: `0` at the nullary constructor, the successor of the
subterm at the unary constructor. -/
def sizeClauses : (i : Bool) →
    RIdent natAlgSig ([] ++ List.replicate (natAlgSig.ar i) RType.o) RType.o
  | false => sizeZeroClause
  | true => sizeSuccClause

/-- Leivant III section 2.4(6)'s size function `sz`, as a flat recurrence on `o`.
Over the `1 + X` word algebra the clauses reconstruct the recurrence argument,
so `ramSize` is extensionally the identity on `o`. -/
def ramSize : RIdent natAlgSig [RType.o] RType.o :=
  RIdent.frec [] RType.o sizeClauses

/-- The environment at the size function's context `[o]`. -/
def sizeEnv (t : FreeAlg natAlgSig) :
    ∀ i : Fin ([RType.o] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([RType.o] : Ctx RType).get i) :=
  Fin.cons t finZeroElim

/-- The size function's flat recurrence read numerically: it preserves the
count. Proved by cases on the top constructor via `PolyFix.ind`; the clauses
rebuild the node, so no recursive call is consulted. -/
theorem freeAlgToNat_ramSize_recurse
    (pe : ∀ i : Fin ([] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([] : Ctx RType).get i))
    (s : FreeAlg natAlgSig) :
    freeAlgToNat (FreeAlg.recurse (A := natAlgSig) (P := Unit)
        (fun i _ sub _phi =>
          (sizeClauses i).interp
            (childEnv [] RType.o (natAlgSig.ar i) pe (fun j => sub j))) () s)
      = freeAlgToNat s := by
  refine PolyFix.ind (P := natAlgSig.polyEndo)
    (motive := fun {_} s =>
      freeAlgToNat (FreeAlg.recurse (A := natAlgSig) (P := Unit)
          (fun i _ sub _phi =>
            (sizeClauses i).interp
              (childEnv [] RType.o (natAlgSig.ar i) pe (fun j => sub j))) () s)
        = freeAlgToNat s)
    (fun b _children _ihc => ?_) s
  cases b <;> rfl

/-- Leivant III section 2.4(6): the size function denotes the identity on `o`
over the `1 + X` word algebra. `freeAlgToNat` of the denotation is the count of
the recurrence argument. -/
theorem ramSize_interp (t : FreeAlg natAlgSig) :
    freeAlgToNat (ramSize.interp (sizeEnv t)) = freeAlgToNat t :=
  freeAlgToNat_ramSize_recurse (envHead [] RType.o (sizeEnv t))
    (envLast [] RType.o (sizeEnv t))

/-- The first-order function sort `o → o`, at which the exponentiation
identifier `ramExp` and the clauses of its second-order recurrence take their
values (Leivant III section 2.4(3)). -/
abbrev ramFun : RType := RType.arrow RType.o RType.o

/-- The two-fold-application identifier `comp (f, g, x) = f (g x)`, at context
`[o → o, o → o, o]` and result `o`: an explicit definition whose body applies
the two function arguments in turn through the application former. It references
no previously defined identifier. The exponentiation step clause uses its
combinator form to compose the recursive result with itself (Leivant III section
2.4(3), the second-order recurrence for `e`). Novel packaging. -/
def ramComp : RIdent natAlgSig [ramFun, ramFun, RType.o] RType.o :=
  RIdent.defn ⟨0, finZeroElim,
    Tm.op (sig := defnSig natAlgSig 0 finZeroElim)
      (Sum.inl (Sum.inl (Sum.inr (RType.o, RType.o))))
      (Fin.cons (Tm.var 0)
        (Fin.cons
          (Tm.op (sig := defnSig natAlgSig 0 finZeroElim)
            (Sum.inl (Sum.inl (Sum.inr (RType.o, RType.o))))
            (Fin.cons (Tm.var 1) (Fin.cons (Tm.var 2) finZeroElim)))
          finZeroElim))⟩
    finZeroElim

/-- The successor-wrapper identifier `sc (x) = succ x`, at context `[o]` and
result `o`. The exponentiation base clause uses its combinator form as the
function iterated by the second-order recurrence (Leivant III section 2.4(3)).
Novel packaging. -/
def ramSucc : RIdent natAlgSig [RType.o] RType.o :=
  RIdent.defn ⟨0, finZeroElim, tmSucc (Tm.var 0)⟩ finZeroElim

/-- The context and result sort of the identifier the exponentiation base clause
references: the successor wrapper `ramSucc : [o] → o`. -/
def ramExpBaseHoleIdx : Fin 1 → List RType × RType :=
  Function.const _ ([RType.o], RType.o)

/-- The exponentiation base clause `e_0 = sc`: an explicit definition at result
`o → o` whose body is the curried combinator form of the successor wrapper
`ramSucc`, a value at the curried sort `o → o`. The base of the second-order
recurrence defining `e` (Leivant III section 2.4(3)). Novel packaging. -/
def ramExpBase : RIdent natAlgSig [] ramFun :=
  RIdent.defn ⟨1, ramExpBaseHoleIdx,
    Tm.op (sig := defnSig natAlgSig 1 ramExpBaseHoleIdx)
      (Sum.inr ⟨0, by decide⟩) finZeroElim⟩
    (fun _ => ramSucc)

/-- The context and result sort of the identifier the exponentiation step clause
references: the two-fold application `ramComp : [o → o, o → o, o] → o`. -/
def ramExpStepHoleIdx : Fin 1 → List RType × RType :=
  Function.const _ ([ramFun, ramFun, RType.o], RType.o)

/-- The exponentiation step clause `e_{n+1} = e_n ∘ e_n`: an explicit definition
at context `[o → o]` (the recursive result `e_n`) and result `o → o`, whose body
composes that recursive-result variable with itself by applying the combinator
form of `ramComp` to it twice through the application former. The step of the
second-order recurrence defining `e` (Leivant III section 2.4(3)). Novel
packaging. -/
def ramExpStep : RIdent natAlgSig [ramFun] ramFun :=
  RIdent.defn ⟨1, ramExpStepHoleIdx,
    Tm.op (sig := defnSig natAlgSig 1 ramExpStepHoleIdx)
      (Sum.inl (Sum.inl (Sum.inr (ramFun, ramFun))))
      (Fin.cons
        (Tm.op (sig := defnSig natAlgSig 1 ramExpStepHoleIdx)
          (Sum.inl (Sum.inl (Sum.inr (ramFun, RType.arrow ramFun ramFun))))
          (Fin.cons
            (Tm.op (sig := defnSig natAlgSig 1 ramExpStepHoleIdx)
              (Sum.inr ⟨0, by decide⟩) finZeroElim)
            (Fin.cons (Tm.var 0) finZeroElim)))
        (Fin.cons (Tm.var 0) finZeroElim))⟩
    (fun _ => ramComp)

/-- The clauses of the exponentiation recurrence: the base clause at the nullary
constructor, the self-composition step at the unary constructor. -/
def ramExpSteps : (i : Bool) →
    RIdent natAlgSig ([] ++ List.replicate (natAlgSig.ar i) ramFun) ramFun
  | false => ramExpBase
  | true => ramExpStep

/-- Leivant III section 2.4(3)'s exponentiation `e : Ω(o → o) → (o → o)`, as a
ramified monotonic second-order recurrence on the `Ω(o → o)` argument whose
recursive results carry the function sort `o → o`: `e (0) = sc` and
`e (n + 1) = e (n) ∘ e (n)`. On a numeral `n` the recurrence yields the
`2^n`-fold iterate of the successor, so `e (n) (x) = x + 2^n`
(`ramExp_interp`). -/
def ramExp : RIdent natAlgSig [RType.omega ramFun] ramFun :=
  RIdent.mrec [] ramFun ramExpSteps

/-- Exponentiation's recurrence read numerically: on an empty parameter
environment `pe`, a recurrence argument `s`, and an input `x`, the denotation is
the `2^(count s)`-fold iterate of the successor applied to `x`, so its count is
`count x + 2^(count s)`. Proved by structural induction on `s` via `PolyFix.ind`
(decision 8), generalizing over `x`; the unary step reads the recursive result
as `e_n` and, through `ramComp`, evaluates to `e_n ∘ e_n`. -/
theorem freeAlgToNat_ramExp_recurse
    (pe : ∀ i : Fin ([] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([] : Ctx RType).get i))
    (s x : FreeAlg natAlgSig) :
    freeAlgToNat
        ((FreeAlg.recurse (A := natAlgSig) (P := Unit)
          (fun i _ _sub phi => (ramExpSteps i).interp
            (childEnv [] ramFun (natAlgSig.ar i) pe phi)) () s) x)
      = freeAlgToNat x + 2 ^ freeAlgToNat s := by
  revert x
  refine PolyFix.ind (P := natAlgSig.polyEndo)
    (motive := fun {_} s => ∀ x, freeAlgToNat
        ((FreeAlg.recurse (A := natAlgSig) (P := Unit)
          (fun i _ _sub phi => (ramExpSteps i).interp
            (childEnv [] ramFun (natAlgSig.ar i) pe phi)) () s) x)
      = freeAlgToNat x + 2 ^ freeAlgToNat s)
    (fun b children ihc => ?_) s
  cases b with
  | false => intro x; rfl
  | true =>
    intro x
    have ih0 := ihc ⟨0, by decide⟩
    have key : (FreeAlg.recurse (A := natAlgSig) (P := Unit)
          (fun i _ _sub phi => (ramExpSteps i).interp
            (childEnv [] ramFun (natAlgSig.ar i) pe phi)) ()
          (PolyFix.mk PUnit.unit true children)) x
        = (FreeAlg.recurse (A := natAlgSig) (P := Unit)
            (fun i _ _sub phi => (ramExpSteps i).interp
              (childEnv [] ramFun (natAlgSig.ar i) pe phi)) ()
            (children ⟨0, by decide⟩))
            ((FreeAlg.recurse (A := natAlgSig) (P := Unit)
              (fun i _ _sub phi => (ramExpSteps i).interp
                (childEnv [] ramFun (natAlgSig.ar i) pe phi)) ()
              (children ⟨0, by decide⟩)) x) := rfl
    have hm : freeAlgToNat (PolyFix.mk PUnit.unit true children)
        = freeAlgToNat (children ⟨0, by decide⟩) + 1 := rfl
    rw [key, ih0, ih0, hm, Nat.pow_succ]
    omega

/-- Leivant III section 2.4(3): the exponentiation `e` iterates the successor.
On the recurrence argument `ρ 0` (a numeral at `Ω(o → o)`) and an input `x`, the
denotation `e (ρ 0) (x)` has count `count x + 2^(count (ρ 0))`; equivalently it
is the `2^(count (ρ 0))`-fold iterate of the successor applied to `x`. This is
the form the `2_m` ladder consumes. -/
theorem ramExp_interp
    (ρ : ∀ i : Fin ([RType.omega ramFun] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([RType.omega ramFun] : Ctx RType).get i))
    (x : FreeAlg natAlgSig) :
    freeAlgToNat ((ramExp.interp ρ) x)
      = freeAlgToNat x + 2 ^ freeAlgToNat (ρ 0) :=
  freeAlgToNat_ramExp_recurse (envHead [] (RType.omega ramFun) ρ)
    (envLast [] (RType.omega ramFun) ρ) x

/-- The single exponential step of the `2_m` ladder: `2^x`, obtained from the
second-order recurrence `ramExp` by driving it with the argument `x` at
`Ω(o → o)` and evaluating the resulting function at `0`, so
`ramTwoPowStep (x) = e (x) (0)`. Its count is `2^(count x)`
(`freeAlgToNat_ramTwoPowStep`). Novel packaging: the semantic composite of the
higher-type recurrence that the `2_m` ladder iterates. -/
def ramTwoPowStep (x : FreeAlg natAlgSig) : FreeAlg natAlgSig :=
  (ramExp.interp (Fin.cons x finZeroElim)) (natToFreeAlg 0)

/-- The single exponential step denotes `2^·`: `count (ramTwoPowStep x)` is
`2^(count x)`. A specialization of `ramExp_interp` at input `0`. -/
theorem freeAlgToNat_ramTwoPowStep (x : FreeAlg natAlgSig) :
    freeAlgToNat (ramTwoPowStep x) = 2 ^ freeAlgToNat x := by
  unfold ramTwoPowStep
  rw [ramExp_interp, freeAlgToNat_natToFreeAlg, Nat.zero_add]
  exact congrArg (2 ^ ·) (congrArg freeAlgToNat (Fin.cons_zero _ _))

/-- Leivant III section 2.4(4)'s ladder `2_m`, realized by induction on `m` as
the `m`-fold composite of the single exponential step `ramTwoPowStep`:
`2_0 (x) = x` and `2_{m+1} (x) = 2^(2_m (x))`. The tier discipline forbids a
raising coercion `o → Ω(o → o)` (no identity-realizing coercion into a strictly
higher tier exists; see `GebLean.Ramified.kappaHatIdent`), so the iterate is
assembled at the carrier level by composing the second-order recurrence `ramExp`
`m` times, rather than as a single object-language morphism. Its count aligns
with `GebLean.tower` (`ramTwoPow_interp`). Novel packaging. -/
def ramTwoPow : Nat → FreeAlg natAlgSig → FreeAlg natAlgSig
  | 0, x => x
  | m + 1, x => ramTwoPowStep (ramTwoPow m x)

/-- Leivant III section 2.4(4): the ladder `2_m` denotes the tower of twos
`GebLean.tower` (`GebLean/Utilities/Tower.lean`), which satisfies
`tower 0 y = y` and `tower (m+1) y = 2^(tower m y)`. On a carrier element `x`,
`count (2_m (x)) = tower m (count x)`. The left side counts the ladder's output;
the right side is the height-`m` tower of twos applied to the input's count.
This is the Phase 5 ingredient. Proved by induction on `m`, each step invoking
`freeAlgToNat_ramTwoPowStep`. -/
theorem ramTwoPow_interp (m : Nat) (x : FreeAlg natAlgSig) :
    freeAlgToNat (ramTwoPow m x) = GebLean.tower m (freeAlgToNat x) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change freeAlgToNat (ramTwoPowStep (ramTwoPow m x))
      = GebLean.tower (m + 1) (freeAlgToNat x)
    rw [freeAlgToNat_ramTwoPowStep, ih, GebLean.tower_succ]

end GebLean.Ramified
