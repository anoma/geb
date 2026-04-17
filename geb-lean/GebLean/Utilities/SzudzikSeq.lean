import Mathlib.Data.Nat.Pairing
import GebLean.LawvereBT
import GebLean.LawvereBTPrimrec

/-!
# Szudzik Sequence Encoding and Tree-Fold Simulation

Generic Lean-native arithmetic building blocks for the
`LawvereTreeERCat ≅ LawvereERCat` isomorphism:

* `Nat.seqPack` / `Nat.seqAt` — encode a list of naturals as
  one natural via iterated right-associated Szudzik pairing.
* `Nat.treeFoldOnCode` — simulate `BT.fold` via
  course-of-values recursion on a Gödel-encoded tree.
* `Nat.tupleRecN` — finite-arity mutumorphism via iterated
  pair.

All functions are elementary recursive (E₃).  Reduction rules
are proved with `@[simp]` and are suitable for use in
downstream `TreeERMor1`-level agreement theorems.
-/

namespace Nat

/-- Encode a list of naturals as a single natural via
iterated right-associated Szudzik pairing.  Empty list is 0;
`x :: xs` packs as `pair x (seqPack xs) + 1`. -/
def seqPack : List ℕ → ℕ
  | []      => 0
  | x :: xs => pair x (seqPack xs) + 1

@[simp] theorem seqPack_nil : seqPack [] = 0 := rfl

@[simp] theorem seqPack_cons (x : ℕ) (xs : List ℕ) :
    seqPack (x :: xs) = pair x (seqPack xs) + 1 := rfl

/-- Extract the `i`-th element from a packed sequence.
Returns 0 if out of range.  On in-range indices, satisfies
`seqAt (seqPack xs) i = xs.get ⟨i, h⟩`. -/
def seqAt : ℕ → ℕ → ℕ
  | 0,     _     => 0
  | n + 1, 0     => (unpair n).1
  | n + 1, i + 1 => seqAt (unpair n).2 i

@[simp] theorem seqAt_zero_head (n : ℕ) :
    seqAt (n + 1) 0 = (unpair n).1 := rfl

@[simp] theorem seqAt_succ_tail (n i : ℕ) :
    seqAt (n + 1) (i + 1) = seqAt (unpair n).2 i := rfl

@[simp] theorem seqAt_zero_of_zero (i : ℕ) :
    seqAt 0 i = 0 := by
  cases i <;> rfl

theorem seqAt_seqPack :
    ∀ (xs : List ℕ) (i : ℕ) (h : i < xs.length),
      seqAt (seqPack xs) i = xs.get ⟨i, h⟩
  | [],        i,     h => absurd h (by simp)
  | x :: xs,   0,     _ => by
      simp [seqPack, unpair_pair]
  | x :: xs,   i + 1, h => by
      simp [seqPack, unpair_pair]
      exact seqAt_seqPack xs i (by
        simp [List.length_cons] at h; omega)

/-- Simulate `BT.fold` via course-of-values recursion on a
Gödel code.  The encoding `code(leaf) = 0`,
`code(branch l r) = 1 + pair(code l)(code r)` matches
`encodeBT` from `LawvereBTPrimrec.lean`. -/
def treeFoldOnCode {α : Type*}
    (h₀ : α) (h₁ : α → α → α) : ℕ → α
  | 0     => h₀
  | n + 1 =>
      h₁ (treeFoldOnCode h₀ h₁ (unpair n).1)
         (treeFoldOnCode h₀ h₁ (unpair n).2)
  termination_by n => n
  decreasing_by
    · exact Nat.lt_succ_of_le (unpair_left_le n)
    · exact Nat.lt_succ_of_le (unpair_right_le n)

@[simp] theorem treeFoldOnCode_zero {α : Type*}
    (h₀ : α) (h₁ : α → α → α) :
    treeFoldOnCode h₀ h₁ 0 = h₀ := by
  simp [treeFoldOnCode]

@[simp] theorem treeFoldOnCode_succ {α : Type*}
    (h₀ : α) (h₁ : α → α → α) (n : ℕ) :
    treeFoldOnCode h₀ h₁ (n + 1) =
      h₁ (treeFoldOnCode h₀ h₁ (unpair n).1)
         (treeFoldOnCode h₀ h₁ (unpair n).2) := by
  simp [treeFoldOnCode]

/-- Multi-slot course-of-values recursion on a Gödel
code.  With `m` slots, given `m` initial values (for
`n = 0`) and an `m`-ary step combining the `m` slot
values from each unpair component, compute all slots'
values at Gödel code `n`.  Generalizes
`treeFoldOnCode` from single slot to mutual `m`-slot.
At `n = encodeBT t` agrees with the `m`-slot `BT.fold`
over `t`. -/
def mutuTreeFoldOnCode {α : Type*} {m : ℕ}
    (base : Fin m → α)
    (step : (Fin m → α) → (Fin m → α) → Fin m → α) :
    ℕ → Fin m → α
  | 0     => base
  | n + 1 => step
      (mutuTreeFoldOnCode base step (unpair n).1)
      (mutuTreeFoldOnCode base step (unpair n).2)
  termination_by n => n
  decreasing_by
    · exact Nat.lt_succ_of_le (unpair_left_le n)
    · exact Nat.lt_succ_of_le (unpair_right_le n)

@[simp] theorem mutuTreeFoldOnCode_zero {α : Type*}
    {m : ℕ} (base : Fin m → α)
    (step : (Fin m → α) → (Fin m → α) → Fin m → α) :
    mutuTreeFoldOnCode base step 0 = base := by
  simp [mutuTreeFoldOnCode]

@[simp] theorem mutuTreeFoldOnCode_succ {α : Type*}
    {m : ℕ} (base : Fin m → α)
    (step : (Fin m → α) → (Fin m → α) → Fin m → α)
    (n : ℕ) :
    mutuTreeFoldOnCode base step (n + 1) =
      step
        (mutuTreeFoldOnCode base step (unpair n).1)
        (mutuTreeFoldOnCode base step (unpair n).2) := by
  simp [mutuTreeFoldOnCode]

/-- Finite-arity mutumorphism: `k` mutually recursive
functions folded simultaneously over a natural-number bound.

Each step takes the current index and the full tuple of `k`
accumulated values from all slots and produces the fresh
tuple for the next iteration.

This is the ℕ-level mutumorphism primitive; tree-ER's native
multi-slot fold (`BTMor1.fold`'s `m` parameter) is the
structural analog, but on ℕ we need this simulation via
tupling. -/
def tupleRecN {k : ℕ}
    (init : Fin k → ℕ)
    (step : ℕ → (Fin k → ℕ) → (Fin k → ℕ))
    (n : ℕ) : Fin k → ℕ :=
  Nat.rec init (fun m acc => step m acc) n

@[simp] theorem tupleRecN_zero {k : ℕ}
    (init : Fin k → ℕ)
    (step : ℕ → (Fin k → ℕ) → (Fin k → ℕ)) :
    tupleRecN init step 0 = init := rfl

@[simp] theorem tupleRecN_succ {k : ℕ}
    (init : Fin k → ℕ)
    (step : ℕ → (Fin k → ℕ) → (Fin k → ℕ))
    (n : ℕ) :
    tupleRecN init step (n + 1) =
      step n (tupleRecN init step n) := rfl

end Nat

namespace GebLean

/-- Correctness of `Nat.treeFoldOnCode` against `BT.fold`:
running the course-of-values recursion on the Gödel code of
a tree agrees with the structural fold of that tree. -/
theorem treeFoldOnCode_encodeBT {α : Type}
    (t : BT.{0}) (h₀ : α) (h₁ : α → α → α) :
    Nat.treeFoldOnCode h₀ h₁ (encodeBT t) =
      BT.fold h₀ h₁ t := by
  refine BT.ind (motive := fun t =>
    Nat.treeFoldOnCode h₀ h₁ (encodeBT t) =
      BT.fold h₀ h₁ t) ?_ ?_ t
  · simp only [encodeBT, BT.fold_leaf,
      Nat.treeFoldOnCode_zero]
  · intro l r hl hr
    simp only [encodeBT, BT.fold_node]
    rw [show BT.fold 0
      (fun el er => Nat.pair el er + 1) =
      encodeBT from rfl]
    rw [Nat.treeFoldOnCode_succ, Nat.unpair_pair, hl, hr]

/-- Correctness of `Nat.mutuTreeFoldOnCode` against the
`m`-slot `BT.fold`: running the multi-slot
course-of-values recursion on the Gödel code of a tree
agrees with the structural multi-slot fold. -/
theorem mutuTreeFoldOnCode_encodeBT {α : Type} {m : ℕ}
    (t : BT.{0}) (base : Fin m → α)
    (step : (Fin m → α) → (Fin m → α) → Fin m → α) :
    Nat.mutuTreeFoldOnCode base step (encodeBT t) =
      BT.fold (α := Fin m → α) base step t := by
  refine BT.ind (motive := fun t =>
    Nat.mutuTreeFoldOnCode base step (encodeBT t) =
      BT.fold (α := Fin m → α) base step t) ?_ ?_ t
  · simp only [encodeBT, BT.fold_leaf,
      Nat.mutuTreeFoldOnCode_zero]
  · intro l r hl hr
    simp only [encodeBT, BT.fold_node]
    rw [show BT.fold 0
      (fun el er => Nat.pair el er + 1) =
      encodeBT from rfl]
    rw [Nat.mutuTreeFoldOnCode_succ, Nat.unpair_pair,
        hl, hr]

end GebLean
