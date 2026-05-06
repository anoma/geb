import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

/-!
# Lawvere theory of the K^sim hierarchy: term language

This module defines `KMor1 : ℕ → Type`, the type family of
K^sim single-output morphisms representing functions
`ℕ^n → ℕ`, and `KMorN : ℕ → ℕ → Type`, the multi-output
wrapper representing functions `ℕ^n → ℕ^m` as families of
`m` single-output morphisms.  Basic operations on `KMorN`
(`id`, `terminal`, `fst`, `snd`, `pair`, `comp`) parallel the
corresponding `ERMorN` definitions.  The structural level of a
`KMor1` term is given by `KMor1.level`; `simrec` and `raise`
each increment the level by one, while `comp` takes the maximum
level of its subterms.  `KMorN.levelN` is the corresponding
maximum level over a multi-output family.  See
`docs/lawvere-k-sim-hierarchy.md` for the canonical
mathematical reference and design principles P1 – P10.
-/

namespace GebLean

/-- The K^sim term language at arity `n`: K^sim
single-output morphisms representing functions `ℕ^n → ℕ`.

Generators per `docs/lawvere-k-sim-hierarchy.md`:
`zero`, `succ`, `proj`, `comp`, `simrec`, `raise`.  Per P8,
`simrec` carries an output index plus base and step
families written as `KMorN`-shaped values; the families
are unfolded inline as `Fin (k+1) → KMor1 _` because
`KMorN` itself is defined later as an abbreviation. -/
inductive KMor1 : ℕ → Type where
  /-- Constant `0` at any arity. -/
  | zero {n : ℕ} : KMor1 n
  /-- Successor function (arity `1`). -/
  | succ : KMor1 1
  /-- The `i`-th projection out of `n` arguments. -/
  | proj {n : ℕ} (i : Fin n) : KMor1 n
  /-- Composition: apply a `b`-ary morphism to the
  results of `b` `a`-ary morphisms. -/
  | comp {a b : ℕ} (f : KMor1 b)
      (gs : Fin b → KMor1 a) : KMor1 a
  /-- Simultaneous primitive recursion at output index
  `i`, with system size `k+1`, base-case family `h`,
  and step-function family `g`.  Produces a morphism
  of arity `a+1` (one slot for the recursion variable
  followed by `a` slots for the parameter list). -/
  | simrec {a k : ℕ}
      (i : Fin (k+1))
      (h : Fin (k+1) → KMor1 a)
      (g : Fin (k+1) → KMor1 (a + 1 + (k + 1))) :
      KMor1 (a + 1)
  /-- Level-bumping marker (no operational effect on
  `interp`; lifts a term's structural level by one). -/
  | raise {n : ℕ} (f : KMor1 n) : KMor1 n

instance (n : ℕ) : Inhabited (KMor1 n) := ⟨KMor1.zero⟩

/-- Multi-output K^sim Lawvere-theory wrapper:
`KMorN n m` represents a morphism `ℕ^n → ℕ^m` as a
family of `m` single-output morphisms.  Parallels
`ERMorN`'s definition. -/
abbrev KMorN (n m : ℕ) : Type := Fin m → KMor1 n

/-- Identity morphism on `n` arguments: the family of
`n` projections. -/
def KMorN.id (n : ℕ) : KMorN n n :=
  fun i => KMor1.proj i

/-- Terminal morphism `ℕ^n → ℕ^0`: the empty family. -/
def KMorN.terminal (n : ℕ) : KMorN n 0 :=
  Fin.elim0

/-- First projection `ℕ^(n+m) → ℕ^n`. -/
def KMorN.fst {n m : ℕ} : KMorN (n + m) n :=
  fun i => KMor1.proj (Fin.castAdd m i)

/-- Second projection `ℕ^(n+m) → ℕ^m`. -/
def KMorN.snd {n m : ℕ} : KMorN (n + m) m :=
  fun i => KMor1.proj (Fin.natAdd n i)

/-- Pairing of two morphisms with shared domain: given
`f : KMorN k n` and `g : KMorN k m`, produce
`⟨f, g⟩ : KMorN k (n + m)`. -/
def KMorN.pair {k n m : ℕ}
    (f : KMorN k n) (g : KMorN k m) : KMorN k (n + m) :=
  fun i =>
    if h : i.val < n then
      f ⟨i.val, h⟩
    else
      g ⟨i.val - n, by omega⟩

/-- Composition of multi-output morphisms: `f ∘ g`
where `g : KMorN n m` and `f : KMorN m k`. -/
def KMorN.comp {n m k : ℕ}
    (f : KMorN m k) (g : KMorN n m) : KMorN n k :=
  fun i => KMor1.comp (f i) g

/-- Structural level of a `KMor1` term per design
principle P2: `simrec` and `raise` each add one to
the maximum-children level; `comp` takes the maximum
without adding. -/
def KMor1.level : {n : ℕ} → KMor1 n → ℕ
  | _, .zero        => 0
  | _, .succ        => 0
  | _, .proj _      => 0
  | _, .comp f gs   =>
      max (KMor1.level f)
        (Finset.univ.sup (fun i => (gs i).level))
  | _, .simrec _ h g =>
      max (Finset.univ.sup (fun i => (h i).level))
          (Finset.univ.sup (fun i => (g i).level)) + 1
  | _, .raise f      => f.level + 1

/-- Level of a multi-output `KMorN` family: the
maximum level over the family. -/
def KMorN.levelN {n m : ℕ} (f : KMorN n m) : ℕ :=
  Finset.univ.sup (fun i => (f i).level)

/-- Single-output (non-simultaneous) primitive recursion at arity
`a + 1`.  The base `h : KMor1 a` returns the value at recursion
variable `0`; the step `g : KMor1 (a + 2)` receives the recursion
variable, the parameters, and the previous value, in this slot order:

* slot `0`        : recursion variable `x`
* slots `1, …, a` : parameters `y_1, …, y_a`
* slot `a + 1`    : previous value `f(x, y⃗)`

It returns the value at `x + 1`.  Definitional reduction to
`KMor1.simrec` with `k = 0`, `i = 0`.

Tourlakis Notes 10.2.7 (definition of K^sim, with simultaneous
recursion as the primitive); the non-simultaneous case is the
`k = 0` specialization. -/
def KMor1.rec1 {a : ℕ} (h : KMor1 a) (g : KMor1 (a + 2)) :
    KMor1 (a + 1) :=
  KMor1.simrec (a := a) (k := 0) (i := ⟨0, by decide⟩)
    (fun _ => h) (fun _ => g)

example : (KMor1.rec1
    (h := (KMor1.zero : KMor1 0))
    (g := (KMor1.zero : KMor1 2))).level = 1 := by decide

/-- Precompose a `KMor1 m` term with a context-projection map
`σ : Fin m → Fin n`. Given `f : KMor1 m`, produces a `KMor1 n`
that interprets at context `ctx : Fin n → ℕ` as
`f.interp (fun i => ctx (σ i))`.

Built from `comp` and `proj` only; no new constructors. The level
is unchanged from `f.level`: `comp` takes `max` over children's
levels and the inner `proj`s are level 0. -/
def KMor1.permArgs {n m : ℕ} (σ : Fin m → Fin n) (f : KMor1 m) :
    KMor1 n :=
  KMor1.comp f (fun i => KMor1.proj (σ i))

/-- Argument-swap for 2-argument K^sim morphisms:
`(KMor1.swap f).interp ctx = f.interp ![ctx 1, ctx 0]`.
Specialization of `permArgs` to the swap permutation on `Fin 2`. -/
def KMor1.swap (f : KMor1 2) : KMor1 2 :=
  KMor1.permArgs
    (fun i => match i with
      | ⟨0, _⟩ => ⟨1, by decide⟩
      | ⟨1, _⟩ => ⟨0, by decide⟩) f

theorem KMor1.level_le_succ {n : ℕ} (f : KMor1 n)
    {d : ℕ} (h : f.level ≤ d) : f.level ≤ d + 1 :=
  Nat.le_succ_of_le h

theorem KMorN.levelN_le_succ {n m : ℕ}
    (f : KMorN n m) {d : ℕ} (h : f.levelN ≤ d) :
    f.levelN ≤ d + 1 :=
  Nat.le_succ_of_le h

end GebLean
