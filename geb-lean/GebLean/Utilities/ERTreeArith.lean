import GebLean.Utilities.ERArith
import GebLean.Utilities.SzudzikSeq
import GebLean.LawvereNatBT

/-!
# ER-Derived BTL Operations

`ERMor1`-level versions of `BTL.encode` (leaf and node cases)
and `BTL.fold`-on-Gödel-code.  The encode primitives are direct
closed-form arithmetic; the fold-on-code combinator builds on
`ERMor1.boundedRec` plus a Gödel β-encoded fold table.

Used by Stage β Task 14's back-translation.
-/

namespace GebLean

/-- The constant `2` as an `n`-ary ER term: applies `succ`
twice to `zeroN n`. -/
def ERMor1.twoN (n : ℕ) : ERMor1 n :=
  ERMor1.comp ERMor1.succ
    (fun (_ : Fin 1) => ERMor1.oneN n)

/-- Interpretation of `twoN`: always returns `2`. -/
@[simp] theorem ERMor1.interp_twoN
    {n : ℕ} (ctx : Fin n → ℕ) :
    (ERMor1.twoN n).interp ctx = 2 :=
  rfl

/-- ER-derived `BTL.encode` of a leaf: `btlEncodeLeaf ![lbl]`
returns `2 * lbl`, matching `BTL.encode (BTL.leaf lbl)`. -/
def ERMor1.btlEncodeLeaf : ERMor1 1 :=
  ERMor1.comp ERMor1.mulN
    (fun i => match i with
      | ⟨0, _⟩ => ERMor1.twoN 1
      | ⟨1, _⟩ => ERMor1.proj 0)

/-- Interpretation of `btlEncodeLeaf`: matches
`BTL.encode (BTL.leaf lbl)`. -/
@[simp] theorem ERMor1.interp_btlEncodeLeaf (lbl : ℕ) :
    ERMor1.btlEncodeLeaf.interp ![lbl] =
      BTL.encode (BTL.leaf lbl) := by
  unfold ERMor1.btlEncodeLeaf
  simp only [ERMor1.interp_comp, ERMor1.interp_mulN,
    ERMor1.interp_twoN, ERMor1.interp_proj,
    BTL.encode, Matrix.cons_val_zero]

/-- ER-derived `BTL.encode` for a node, with pre-encoded child
codes.  `btlEncodeNode ![l, r]` returns
`2 * Nat.pair l r + 1`, matching
`BTL.encode (BTL.node t_l t_r)` when `l = BTL.encode t_l` and
`r = BTL.encode t_r`. -/
def ERMor1.btlEncodeNode : ERMor1 2 :=
  ERMor1.comp ERMor1.succ
    (fun (_ : Fin 1) =>
      ERMor1.comp ERMor1.mulN
        (fun i => match i with
          | ⟨0, _⟩ => ERMor1.twoN 2
          | ⟨1, _⟩ =>
              ERMor1.comp ERMor1.natPair
                (fun j => match j with
                  | ⟨0, _⟩ => ERMor1.proj 0
                  | ⟨1, _⟩ => ERMor1.proj 1)))

/-- Interpretation of `btlEncodeNode`: given pre-encoded child
codes, produces the parent node's code. -/
@[simp] theorem ERMor1.interp_btlEncodeNode (l r : ℕ) :
    ERMor1.btlEncodeNode.interp ![l, r] =
      2 * Nat.pair l r + 1 := by
  have hpair : ERMor1.natPair.interp ![l, r] =
      Nat.pair l r := ERMor1.interp_natPair l r
  unfold ERMor1.btlEncodeNode
  simp only [ERMor1.interp_comp, ERMor1.interp_succ,
    ERMor1.interp_mulN, ERMor1.interp_twoN]
  change 2 * ERMor1.natPair.interp ![l, r] + 1 =
      2 * Nat.pair l r + 1
  rw [hpair]

end GebLean
