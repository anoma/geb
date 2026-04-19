import Mathlib.Data.Fin.Basic
import GebLean.Utilities

/-!
# `LawvereNatRamified`: Tier-Disciplined Ramified Recurrence on ℕ

A Nat-sort Lawvere theory whose morphisms are elementary
recursive functions presented via tier-disciplined ramified
recurrence (Leivant 1999).  Each morphism carries a `Tier`
index (`NonRec` or `MayRec`) constraining where recursion
can occur.

Constructors include the seven Wikipedia-literal ER generators
recast in tier-tagged form (`zero`, `succ`, `proj`, `sub`,
`comp`, plus `add` and `mul` as Leivant-standard non-recursive
primitives) together with the recursive destructor
`foldMutNat` and one-level case match `natMatch`.

The categorical equivalence with `LawvereERCat` is established
in `LawvereERNatRamifiedEquiv.lean`.  The two-stage chain
`LawvereERCat ≃ LawvereNatRamified ≃ LawvereNatBTRamified`
is documented in
`docs/superpowers/specs/2026-04-18-lawvere-natramified-two-stage-design.md`.
-/

namespace GebLean

/-- Tier index for tier-disciplined ramified recurrence.
`nonRec` marks a non-recursive primitive; `mayRec` allows the
unfolding step.  Recursive constructors require their step
argument to be `nonRec`, ensuring `step`'s `towerHeight` is a
fixed structural quantity. -/
inductive Tier : Type
  | nonRec : Tier
  | mayRec : Tier
  deriving DecidableEq, Repr, Inhabited

/-- Tier propagation: composition of two morphisms takes the
maximum tier.  `nonRec` is the bottom; `mayRec` is the top. -/
def Tier.max : Tier → Tier → Tier
  | .nonRec, .nonRec => .nonRec
  | _, _ => .mayRec

@[simp] theorem Tier.max_nonRec_nonRec :
    Tier.max .nonRec .nonRec = .nonRec := rfl

@[simp] theorem Tier.max_nonRec_mayRec :
    Tier.max .nonRec .mayRec = .mayRec := rfl

@[simp] theorem Tier.max_mayRec_nonRec :
    Tier.max .mayRec .nonRec = .mayRec := rfl

@[simp] theorem Tier.max_mayRec_mayRec :
    Tier.max .mayRec .mayRec = .mayRec := rfl

/-- Tier-disciplined ramified term over ℕ.  Indexed by domain
arity `n` and tier `t`.  Constructors:

* `zero`/`succ`/`proj`/`sub`: Wikipedia-literal ER primitives
  at tier `nonRec`.
* `add`/`mul`: Leivant-standard non-recursive primitives at
  tier `nonRec`.  Definable via `bsum`/`bprod` in
  `LawvereERCat`, but exposed here as primitives so that
  ramified `foldMutNat` step terms can use them without
  triggering `mayRec`.
* `comp`: composition; tier propagates as `Tier.max`.
* `natMatch`: one-level pattern match on a `nonRec` argument's
  zero/succ shape.  The `succCase` has arity `n + 1`, binding the
  predecessor in slot `0`.  Tier propagates as the max of the
  two branches.  Note: `natMatch` is at tier `nonRec` when both
  branches are `nonRec`, distinguishing it from `foldMutNat`,
  which always produces tier `mayRec`.
* `foldMutNat`: unbounded primitive recursion on ℕ.  The
  `step` argument is constrained to tier `nonRec`; the result
  is tier `mayRec`. -/
inductive NatRamifiedMor1 : ℕ → Tier → Type
  | zero {n : ℕ} : NatRamifiedMor1 n .nonRec
  | succ {n : ℕ} : NatRamifiedMor1 (n + 1) .nonRec
  | proj {n : ℕ} (i : Fin n) : NatRamifiedMor1 n .nonRec
  | sub {n : ℕ} : NatRamifiedMor1 (n + 2) .nonRec
  | add {n : ℕ} : NatRamifiedMor1 (n + 2) .nonRec
  | mul {n : ℕ} : NatRamifiedMor1 (n + 2) .nonRec
  | comp {a b : ℕ} {t1 t2 : Tier}
      (f : NatRamifiedMor1 b t1)
      (g : Fin b → NatRamifiedMor1 a t2) :
      NatRamifiedMor1 a (Tier.max t1 t2)
  | natMatch {n : ℕ} {t1 t2 : Tier}
      (zeroCase : NatRamifiedMor1 n t1)
      (succCase : NatRamifiedMor1 (n + 1) t2)
      (k : NatRamifiedMor1 (n + 1) .nonRec) :
      NatRamifiedMor1 (n + 1) (Tier.max t1 t2)
  | foldMutNat {n : ℕ} {tb : Tier}
      (base : NatRamifiedMor1 n tb)
      (step : NatRamifiedMor1 (n + 2) .nonRec)
      (k : NatRamifiedMor1 n .nonRec) :
      NatRamifiedMor1 n .mayRec

end GebLean
