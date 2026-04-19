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

/-- Standard interpretation: maps a domain context `Fin n → ℕ`
to a ℕ value.  `foldMutNat` uses unbounded `Nat.rec`; total. -/
def NatRamifiedMor1.interp :
    {n : ℕ} → {t : Tier} → NatRamifiedMor1 n t →
    (Fin n → ℕ) → ℕ
  | _, _, NatRamifiedMor1.zero, _ => 0
  | _, _, NatRamifiedMor1.succ, ctx => Nat.succ (ctx 0)
  | _, _, NatRamifiedMor1.proj i, ctx => ctx i
  | _, _, NatRamifiedMor1.sub, ctx => Nat.sub (ctx 0) (ctx 1)
  | _, _, NatRamifiedMor1.add, ctx => ctx 0 + ctx 1
  | _, _, NatRamifiedMor1.mul, ctx => ctx 0 * ctx 1
  | _, _, NatRamifiedMor1.comp f g, ctx =>
      NatRamifiedMor1.interp f
        (fun i => NatRamifiedMor1.interp (g i) ctx)
  | _, _, NatRamifiedMor1.natMatch zeroCase succCase k, ctx =>
      match NatRamifiedMor1.interp k ctx with
      | 0 => NatRamifiedMor1.interp zeroCase (Fin.tail ctx)
      | m + 1 =>
          NatRamifiedMor1.interp succCase
            (Fin.cons m (Fin.tail ctx))
  | _, _, NatRamifiedMor1.foldMutNat base step k, ctx =>
      Nat.rec (motive := fun _ => ℕ)
        (NatRamifiedMor1.interp base ctx)
        (fun j prev =>
          NatRamifiedMor1.interp step
            (Fin.cons j (Fin.cons prev ctx)))
        (NatRamifiedMor1.interp k ctx)

@[simp] theorem NatRamifiedMor1.interp_zero {n : ℕ}
    (ctx : Fin n → ℕ) :
    (NatRamifiedMor1.zero : NatRamifiedMor1 n .nonRec).interp ctx
      = 0 := rfl

@[simp] theorem NatRamifiedMor1.interp_succ {n : ℕ}
    (ctx : Fin (n + 1) → ℕ) :
    (NatRamifiedMor1.succ :
        NatRamifiedMor1 (n + 1) .nonRec).interp ctx
      = Nat.succ (ctx 0) := rfl

@[simp] theorem NatRamifiedMor1.interp_proj {n : ℕ}
    (i : Fin n) (ctx : Fin n → ℕ) :
    (NatRamifiedMor1.proj i).interp ctx = ctx i := rfl

@[simp] theorem NatRamifiedMor1.interp_sub {n : ℕ}
    (ctx : Fin (n + 2) → ℕ) :
    (NatRamifiedMor1.sub :
        NatRamifiedMor1 (n + 2) .nonRec).interp ctx
      = Nat.sub (ctx 0) (ctx 1) := rfl

@[simp] theorem NatRamifiedMor1.interp_add {n : ℕ}
    (ctx : Fin (n + 2) → ℕ) :
    (NatRamifiedMor1.add :
        NatRamifiedMor1 (n + 2) .nonRec).interp ctx
      = ctx 0 + ctx 1 := rfl

@[simp] theorem NatRamifiedMor1.interp_mul {n : ℕ}
    (ctx : Fin (n + 2) → ℕ) :
    (NatRamifiedMor1.mul :
        NatRamifiedMor1 (n + 2) .nonRec).interp ctx
      = ctx 0 * ctx 1 := rfl

@[simp] theorem NatRamifiedMor1.interp_comp {a b : ℕ}
    {t1 t2 : Tier}
    (f : NatRamifiedMor1 b t1)
    (g : Fin b → NatRamifiedMor1 a t2)
    (ctx : Fin a → ℕ) :
    (NatRamifiedMor1.comp f g).interp ctx
      = f.interp (fun i => (g i).interp ctx) := rfl

@[simp] theorem NatRamifiedMor1.interp_natMatch {n : ℕ}
    {t1 t2 : Tier}
    (zeroCase : NatRamifiedMor1 n t1)
    (succCase : NatRamifiedMor1 (n + 1) t2)
    (k : NatRamifiedMor1 (n + 1) .nonRec)
    (ctx : Fin (n + 1) → ℕ) :
    (NatRamifiedMor1.natMatch zeroCase succCase k).interp ctx
      = match k.interp ctx with
        | 0 => zeroCase.interp (Fin.tail ctx)
        | m + 1 =>
            succCase.interp (Fin.cons m (Fin.tail ctx)) := rfl

@[simp] theorem NatRamifiedMor1.interp_foldMutNat {n : ℕ}
    {tb : Tier}
    (base : NatRamifiedMor1 n tb)
    (step : NatRamifiedMor1 (n + 2) .nonRec)
    (k : NatRamifiedMor1 n .nonRec)
    (ctx : Fin n → ℕ) :
    (NatRamifiedMor1.foldMutNat base step k).interp ctx
      = Nat.rec (motive := fun _ => ℕ)
          (base.interp ctx)
          (fun j prev =>
            step.interp (Fin.cons j (Fin.cons prev ctx)))
          (k.interp ctx) := rfl

end GebLean
