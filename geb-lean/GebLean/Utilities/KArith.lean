import GebLean.LawvereKSim
import GebLean.LawvereKSimInterp

/-!
# K^sim-Derived Arithmetic

`KMor1`-level versions of basic arithmetic functions: `pred`,
`isZero`, `add`, `double`, `cond`, `notEq1`, `mult`, `monus`,
`pow2`, `mod`, `div`, `divNat`.  Each function carries an
`@[simp]`-marked correctness theorem linking its interpretation to
its `Nat` counterpart, plus a `level ≤ N` placement proof.

Every function is a closed-form `KMor1` term built from the
generators `zero`, `succ`, `proj`, `comp`, `simrec` (and the
non-simultaneous wrapper `rec1`); the `KMor1` inductive is not
extended.

Levels follow Tourlakis's classification (Notes Prop 10.2.12;
PR §0.1.0.17); `mod`, `div`, `divNat` are placed using
constructions in this module.

Sibling of `Utilities/ERArith.lean`; spec at
`docs/superpowers/specs/2026-05-05-karith-design.md`.
-/

namespace GebLean

/-- The constant `1` morphism at arity 0.

PR §0.1.0.17 implicit (constants and `succ` generate K^sim_0). -/
def KMor1.one : KMor1 0 :=
  KMor1.comp KMor1.succ (fun _ : Fin 1 => KMor1.zero)

/-- Interpretation of `one`: always returns `1`. -/
@[simp] theorem KMor1.interp_one (ctx : Fin 0 → ℕ) :
    KMor1.one.interp ctx = 1 := rfl

example : KMor1.one.level = 0 := by decide

end GebLean
