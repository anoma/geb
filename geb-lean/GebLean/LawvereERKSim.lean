import GebLean.LawvereER
import GebLean.Utilities.ZeroTestURM

/-!
# erToK: ER → K^sim_2 via zero-test URM simulation

The compiler half of the erToK construction: emit a
`URMProgram` from an `ERMor1 a` term such that running the
URM long enough produces `e.interp v` in the output
register.

## References

- Tourlakis 2018 §0.1.0.37 (pp. 15–16): URM semantics.
- Tourlakis 2018 p. 19: worked URM examples (M template
  for `λx.x`, N template for `λx.x+1`, R^XY_Z template
  for `λxy.xy`).
- Tourlakis 2018 p. 20: Loop-to-URM translation template
  with per-Loop scratch register B.
- Tourlakis 2018 p. 21: bounded-recursion URM template.
- Tourlakis 2018 §0.1.0.42 (p. 18): `f ∈ E^n` is
  URM-computable within time bound in `E^n`.
- Spec §5 (ER → URM compiler):
  `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`.

## Tags

URM, compiler, ER, Tourlakis, simulation
-/

namespace GebLean

namespace LawvereERKSim

end LawvereERKSim

end GebLean
