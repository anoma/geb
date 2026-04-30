import Mathlib.Data.Fin.Basic

/-!
# Lawvere theory of the K^sim hierarchy: term language

This module defines `KMor1 : ℕ → Type`, the type family of
K^sim single-output morphisms representing functions
`ℕ^n → ℕ`, and `KMorN : ℕ → ℕ → Type`, the multi-output
wrapper representing functions `ℕ^n → ℕ^m` as families of
`m` single-output morphisms.  Basic operations on `KMorN`
(`id`, `terminal`, `fst`, `snd`, `pair`, `comp`) parallel the
corresponding `ERMorN` definitions.  See
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

end GebLean
