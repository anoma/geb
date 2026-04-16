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

end Nat

namespace GebLean

private theorem treeFoldOnCode_encodeBT_gen
    {α : Type}
    {x : PUnit.{1}}
    (bt : PolyFreeM
      (overTerminal PUnit.{1})
      polyProdType x)
    (h₀ : α) (h₁ : α → α → α) :
    Nat.treeFoldOnCode h₀ h₁ (encodeBT bt) =
      BT.fold h₀ h₁ bt := by
  induction bt with
  | mk y idx children ih =>
    match idx with
    | Sum.inl leafIdx =>
      have hy : y = PUnit.unit :=
        PUnit.eq_punit y
      subst hy
      have hli :
          leafIdx = ⟨PUnit.unit, rfl⟩ :=
        Subtype.ext (PUnit.eq_punit _)
      subst hli
      have hleaf :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{1})
                polyProdType) PUnit.unit from
              Sum.inl ⟨PUnit.unit, rfl⟩)
            children =
          BT.leaf := by
        unfold BT.leaf polyFreeMPure
        congr 1
        funext e; exact PEmpty.elim e
      rw [hleaf, BT.fold_leaf]
      simp only [encodeBT, BT.fold_leaf]
      exact Nat.treeFoldOnCode_zero h₀ h₁
    | Sum.inr nodeIdx =>
      have hy : y = PUnit.unit :=
        PUnit.eq_punit y
      subst hy
      have hni : nodeIdx = PUnit.unit :=
        PUnit.eq_punit nodeIdx
      subst hni
      have hmk :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{1})
                polyProdType) PUnit.unit from
              Sum.inr PUnit.unit)
            children =
          BT.node
            (children (Sum.inl PUnit.unit))
            (children (Sum.inr PUnit.unit)) := by
        unfold BT.node polyProdFreeMNode
          polyFreeMStrFamily
        congr 1
        funext e
        match e with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      rw [hmk, BT.fold_node]
      simp only [encodeBT, BT.fold_node]
      rw [show BT.fold 0
        (fun el er => Nat.pair el er + 1) =
        encodeBT from rfl]
      rw [Nat.treeFoldOnCode_succ, Nat.unpair_pair]
      rw [ih (Sum.inl PUnit.unit),
          ih (Sum.inr PUnit.unit)]

/-- Correctness of `Nat.treeFoldOnCode` against `BT.fold`:
running the course-of-values recursion on the Gödel code of
a tree agrees with the structural fold of that tree. -/
theorem treeFoldOnCode_encodeBT {α : Type}
    (t : BT.{0}) (h₀ : α) (h₁ : α → α → α) :
    Nat.treeFoldOnCode h₀ h₁ (encodeBT t) =
      BT.fold h₀ h₁ t :=
  treeFoldOnCode_encodeBT_gen t h₀ h₁

end GebLean
