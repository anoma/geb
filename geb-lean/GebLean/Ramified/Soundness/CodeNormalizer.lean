import GebLean.Ramified.Soundness.CodeTm

/-!
# Ramified recurrence: code-level substitution

The code-level image of single-variable substitution on the terms of the
simply-typed calculus `1λ(natAlgSig)` (Leivant III section 4.2), opening the
realization layer of the deterministic normalizer. `subCode j e` is the numeric
shadow of `Binding.instantiate₁`: it rewrites the Gödel code `codeTm d` of a
body into the code of the reduct `codeTm (instantiate₁ e d)`, working purely on
the `Nat.pair` numerals with `codeTm e` supplied as the substituend code.

`shiftCode j` is the code-level image of the append-at-end weakening
`ren Thinning.weakAppend`: because `codeTm` records de Bruijn *levels* (the
variable index `x.1.val`, which is the position of the variable's binder counted
from the outermost context entry), a variable's code depends on the ambient
context length. Weakening the target context by one entry at the end therefore
increments the level of every variable whose binder lies at or beyond the
insertion point; `shiftCode j` performs exactly that increment on the code,
bumping every variable leaf of level at least `j` by one and leaving the
operation structure otherwise intact.

`subCode j e` dispatches on the code shape. A variable leaf `Nat.pair 0 i`
rewrites by the three-way comparison of its level `i` against the substituted
level `j`: below `j` it is unchanged, at `j` it becomes the substituend code
`e`, and above `j` it drops by one (the substituted variable's level is
vacated). An operation node `Nat.pair 1 (Nat.pair op pack)` recurses into its
child codes, keeping the substituted level `j` fixed throughout (the append-at-
end convention leaves the target level of the substituted variable unchanged
under every binder). The substituend code, by contrast, is weakened by
`shiftCode j` whenever the recursion crosses an abstraction node, mirroring the
term-level weakening that `Binding.instantiate₁` applies to `e` under a binder.

## Main definitions

* `OneLambda.shiftCode` — the code-level append-at-end weakening: increment every
  variable leaf of level at least `j` by one.
* `OneLambda.subCode` — the code-level single-variable substitution: rewrite a
  body code against a substituted level `j` and a substituend code `e`.

## Main statements

* `OneLambda.shiftCode_var`, `OneLambda.shiftCode_app`, `OneLambda.shiftCode_lam`,
  `OneLambda.shiftCode_const` — the node equations of `shiftCode`.
* `OneLambda.subCode_var`, `OneLambda.subCode_app`, `OneLambda.subCode_lam`,
  `OneLambda.subCode_const` — the node equations of `subCode`.

## Implementation notes

`shiftCode` and `subCode` are strong recursions on the code value, terminating by
the same pairing bounds that guard `ordCode` and `decodeWord`
(`GebLean/Ramified/Soundness/CodeTm.lean`): each child code sits strictly below
its node code through `Nat.unpair_left_le`/`Nat.unpair_right_le` and the strict
step `OneLambda.self_lt_pair_one` past the kind bit `1`. Both dispatch on the
operation kind bit `(Nat.unpair op).1` to recover the node's arity — `0` for the
binary application, `1` for the unary abstraction, and every other value for the
nullary constants — so the child codes are unpacked at fixed depths rather than
by walking the `List.foldr Nat.pair 0` terminator (which is indistinguishable
from a level-`0` variable code, since `Nat.pair 0 0 = 0`).

The substituend weakening under a binder reflects that `codeTm` is *not* stable
under `ren Thinning.weakAppend`: a substituend's own bound variables have levels
at or above the target context length, so a weakening that lengthens the target
context raises them. The single-step image of that weakening is `shiftCode j`
(the fusion `codeTm (ren Thinning.weakAppend t) = shiftCode Δ.length (codeTm t)`
identifies the two); `subCode` therefore applies `shiftCode j` to `e` at each
abstraction node it descends through.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher
type recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`, section 4.2 (p. 223): the
operations and terms of the simply-typed calculus `1λ(A)`, and its
single-variable substitution. The code-level substitution `subCode` and the
code-level weakening `shiftCode` are a novel realization; the substitution
convention transcribes the append-at-end de Bruijn presentation of
`GebLean/Binding/Substitution.lean`.

## Tags

ramified recurrence, Gödel numbering, de Bruijn level, substitution, weakening,
well-founded recursion, term code
-/

namespace GebLean.Ramified

open GebLean.Binding

namespace OneLambda

/-- The code-level append-at-end weakening: increment every variable leaf of
level at least `j` by one, leaving the operation structure intact. The numeric
image of `ren Thinning.weakAppend` under `codeTm`, by strong recursion on the
code value: a variable node `Nat.pair 0 i` bumps its level when `j ≤ i`; an
operation node recurses into its child codes at the fixed depths given by the
operation kind bit `(Nat.unpair op).1` (`0` binary, `1` unary, else nullary),
keeping `j` unchanged since levels are counted from the outermost entry. Novel
realization. -/
def shiftCode (j : ℕ) (c : ℕ) : ℕ :=
  match h : (Nat.unpair c).1, (Nat.unpair (Nat.unpair (Nat.unpair c).2).1).1 with
  | 0, _ =>
      if (Nat.unpair c).2 < j then Nat.pair 0 (Nat.unpair c).2
      else Nat.pair 0 ((Nat.unpair c).2 + 1)
  | 1, 0 =>
      Nat.pair 1 (Nat.pair (Nat.unpair (Nat.unpair c).2).1
        (Nat.pair (shiftCode j (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).1)
          (Nat.pair (shiftCode j (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).2).1)
            0)))
  | 1, 1 =>
      Nat.pair 1 (Nat.pair (Nat.unpair (Nat.unpair c).2).1
        (Nat.pair (shiftCode j (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).1) 0))
  | _, _ => c
  termination_by c
  decreasing_by
    all_goals
      have key : (Nat.unpair c).2 < c := by
        conv_rhs => rw [← Nat.pair_unpair c, h]
        exact self_lt_pair_one _
      first
      | exact Nat.lt_of_le_of_lt
          (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)) key
      | exact Nat.lt_of_le_of_lt
          (le_trans (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _))
            (Nat.unpair_right_le _)) key

/-- The node equation of `shiftCode` at a variable leaf `Nat.pair 0 i`: the level
`i` is bumped when it lies at or beyond the insertion level `j`. -/
theorem shiftCode_var (j i : ℕ) :
    shiftCode j (Nat.pair 0 i) =
      if i < j then Nat.pair 0 i else Nat.pair 0 (i + 1) := by
  rw [shiftCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `shiftCode` at an application node (op kind bit `0`): the
weakening recurses into the two child codes at the fixed level `j`. -/
theorem shiftCode_app (j op c0 c1 : ℕ) (hop : (Nat.unpair op).1 = 0) :
    shiftCode j (Nat.pair 1 (Nat.pair op (Nat.pair c0 (Nat.pair c1 0))))
      = Nat.pair 1 (Nat.pair op
          (Nat.pair (shiftCode j c0) (Nat.pair (shiftCode j c1) 0))) := by
  rw [shiftCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `shiftCode` at an abstraction node (op kind bit `1`): the
weakening recurses into the sole body child code at the fixed level `j`. -/
theorem shiftCode_lam (j op c0 : ℕ) (hop : (Nat.unpair op).1 = 1) :
    shiftCode j (Nat.pair 1 (Nat.pair op (Nat.pair c0 0)))
      = Nat.pair 1 (Nat.pair op (Nat.pair (shiftCode j c0) 0)) := by
  rw [shiftCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `shiftCode` at a nullary constant node (op kind bit at
least `2`): the code is unchanged. -/
theorem shiftCode_const (j op pack : ℕ) (hop : 2 ≤ (Nat.unpair op).1) :
    shiftCode j (Nat.pair 1 (Nat.pair op pack)) = Nat.pair 1 (Nat.pair op pack) := by
  rw [shiftCode]; split <;> simp_all [Nat.unpair_pair]

/-- The code-level single-variable substitution: rewrite a body code against a
substituted level `j` and a substituend code `e`, the numeric image of
`Binding.instantiate₁` under `codeTm`. By strong recursion on the code value: a
variable leaf `Nat.pair 0 i` rewrites by the three-way comparison of its level
`i` with `j` (below `j` unchanged, at `j` the substituend `e`, above `j` dropped
by one); an operation node recurses into its child codes at the fixed depths
given by the operation kind bit `(Nat.unpair op).1`, keeping `j` fixed. The
substituend `e` is weakened by `shiftCode j` at each abstraction node the
recursion descends through, mirroring the term-level weakening of `e` under a
binder. Novel realization. -/
def subCode (j e : ℕ) (c : ℕ) : ℕ :=
  match h : (Nat.unpair c).1, (Nat.unpair (Nat.unpair (Nat.unpair c).2).1).1 with
  | 0, _ =>
      if (Nat.unpair c).2 < j then Nat.pair 0 (Nat.unpair c).2
      else if (Nat.unpair c).2 = j then e
      else Nat.pair 0 ((Nat.unpair c).2 - 1)
  | 1, 0 =>
      Nat.pair 1 (Nat.pair (Nat.unpair (Nat.unpair c).2).1
        (Nat.pair (subCode j e (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).1)
          (Nat.pair (subCode j e
            (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).2).1) 0)))
  | 1, 1 =>
      Nat.pair 1 (Nat.pair (Nat.unpair (Nat.unpair c).2).1
        (Nat.pair (subCode j (shiftCode j e) (Nat.unpair (Nat.unpair (Nat.unpair c).2).2).1)
          0))
  | _, _ => c
  termination_by c
  decreasing_by
    all_goals
      have key : (Nat.unpair c).2 < c := by
        conv_rhs => rw [← Nat.pair_unpair c, h]
        exact self_lt_pair_one _
      first
      | exact Nat.lt_of_le_of_lt
          (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)) key
      | exact Nat.lt_of_le_of_lt
          (le_trans (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _))
            (Nat.unpair_right_le _)) key

/-- The node equation of `subCode` at a variable leaf `Nat.pair 0 i`: the
three-way comparison of the level `i` with the substituted level `j`. -/
theorem subCode_var (j e i : ℕ) :
    subCode j e (Nat.pair 0 i) =
      if i < j then Nat.pair 0 i else if i = j then e else Nat.pair 0 (i - 1) := by
  rw [subCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `subCode` at an application node (op kind bit `0`): the
substitution recurses into the two child codes with the substituend `e` and level
`j` unchanged. -/
theorem subCode_app (j e op c0 c1 : ℕ) (hop : (Nat.unpair op).1 = 0) :
    subCode j e (Nat.pair 1 (Nat.pair op (Nat.pair c0 (Nat.pair c1 0))))
      = Nat.pair 1 (Nat.pair op
          (Nat.pair (subCode j e c0) (Nat.pair (subCode j e c1) 0))) := by
  rw [subCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `subCode` at an abstraction node (op kind bit `1`): the
substitution recurses into the sole body child with the substituend weakened by
`shiftCode j` and the level `j` unchanged. -/
theorem subCode_lam (j e op c0 : ℕ) (hop : (Nat.unpair op).1 = 1) :
    subCode j e (Nat.pair 1 (Nat.pair op (Nat.pair c0 0)))
      = Nat.pair 1 (Nat.pair op (Nat.pair (subCode j (shiftCode j e) c0) 0)) := by
  rw [subCode]; split <;> simp_all [Nat.unpair_pair]

/-- The node equation of `subCode` at a nullary constant node (op kind bit at
least `2`): the code is unchanged. -/
theorem subCode_const (j e op pack : ℕ) (hop : 2 ≤ (Nat.unpair op).1) :
    subCode j e (Nat.pair 1 (Nat.pair op pack)) = Nat.pair 1 (Nat.pair op pack) := by
  rw [subCode]; split <;> simp_all [Nat.unpair_pair]

end OneLambda

end GebLean.Ramified
