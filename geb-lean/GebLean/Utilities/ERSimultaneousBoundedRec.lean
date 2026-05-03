import GebLean.Utilities.SimRec
import GebLean.Utilities.ERTupling
import GebLean.Utilities.ERPackedBound

/-!
# ER-side multi-output bounded simultaneous recursion

Realizes Tourlakis 2018 §0.1.0.34 (closure of E^2 under
simultaneous bounded recursion via the pairing-based
pack-and-unpack proof technique; §0.1.0.35 is the
higher-level corollary for `n ≥ 2`).  Master design §3.2.

Packs the `(k + 1)`-component state into a single
natural via `Nat.tuplePack` (step 1), applies single-
output `ERMor1.boundedRec` with packed-state bound
`ERMor1.tuplePackedBound k componentBound` (this step's
ERPackedBound module), and unpacks component-wise via
`Nat.tupleAt` (step 1).  Bottom-up named composite per
CLAUDE.md "bottom-up named-composite discipline".

Outer `simRecVec` step input convention (matching master
design §3.2's prose `g_j(n, x⃗, F_0..F_k)`): slot 0 is the
iteration counter, slots 1..a are the parameter context,
slots a+1..a+k+1 are the previous-iteration component
values.  Inner `boundedRec` step input convention
(matching `Utilities/ERArith.lean:2200`): slot 0 is the
counter, slot 1 is the packed previous state, slots
2..a+1 are the parameters.

See
`docs/superpowers/specs/2026-05-03-step-2-er-simultaneous-bounded-rec-design.md`
and master design §3.2 in
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`.
-/

namespace GebLean
namespace ERMor1

/-- Initial packed state for `simultaneousBoundedRec`:
applies the `(k + 1)` bases and packs the resulting
vector via `Nat.tuplePack`.  Master design §3.2 step 3. -/
def packedBase (k a : ℕ)
    (h : Fin (k + 1) → ERMor1 a) : ERMor1 a :=
  ERMor1.comp (ERMor1.tuplePack k) h

/-- Slot-routing for `packedStep`'s input context: takes
a `Fin (a + 1 + (k + 1))` index and returns the
`ERMor1 (a + 2)` selecting the appropriate slot.

Outer `(a + 1 + (k + 1))`-context (matching master design
§3.2 `g_j(n, x⃗, F_0..F_k)`):

- Slot 0 = counter.
- Slots 1..a = parameters.
- Slots a+1..a+k+1 = previous-iteration components.

Inner `(a + 2)`-context (matching `ERMor1.boundedRec`'s
step input convention, `Utilities/ERArith.lean:2200`):

- Slot 0 = counter.
- Slot 1 = packed previous state.
- Slots 2..a+1 = parameters.

Routing:

- Outer slot 0 → inner slot 0 (`proj 0`).
- Outer slots 1..a (parameter indices 0..a-1) → inner
  slots 2..a+1 (`proj (v + 1)` for outer index `v + 1`
  with `v < a`).
- Outer slots a+1..a+k+1 (prev indices 0..k) → tupleAt
  extraction from inner slot 1 (the packed previous
  state).  Master design §3.2. -/
def packedStepCtx (k a : ℕ) :
    Fin (a + 1 + (k + 1)) → ERMor1 (a + 2)
  | ⟨0, _⟩ => ERMor1.proj 0
  | ⟨v + 1, h_v⟩ =>
      if h_param : v < a then
        ERMor1.proj ⟨v + 2, by omega⟩
      else
        ERMor1.comp
          (ERMor1.tupleAt k ⟨v - a, by omega⟩)
          ![ERMor1.proj 1]

/-- Packed step function: takes the packed previous
state and produces the packed next state.  Each
component step `g j` is evaluated on the unpacked
context (counter + parameters + previous-component
vector), results are repacked via `Nat.tuplePack`.
Master design §3.2 step 1. -/
def packedStep (k a : ℕ)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1))) :
    ERMor1 (a + 2) :=
  ERMor1.comp (ERMor1.tuplePack k)
    (fun j : Fin (k + 1) =>
      ERMor1.comp (g j) (ERMor1.packedStepCtx k a))

/-- Multi-output bounded simultaneous recursion in ER.
Realizes Tourlakis 2018 §0.1.0.34 (the proof technique:
closure of E^2 under simultaneous bounded recursion via
pairing-based pack-and-unpack; §0.1.0.35 is the
higher-level corollary for `n ≥ 2`).  Master design §3.2.

The implementation packs the `(k + 1)`-component state
into a single natural via `Nat.tuplePack`, applies
single-output `ERMor1.boundedRec` with a packed-state
bound derived via `ERMor1.tuplePackedBound`, then
unpacks the result component-wise via `Nat.tupleAt`.
Bottom-up named composite per CLAUDE.md "bottom-up
named-composite discipline". -/
def simultaneousBoundedRec (k a : ℕ)
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)))
    (componentBound : ERMor1 (a + 1)) :
    ERMorN (a + 1) (k + 1) :=
  let packedRec : ERMor1 (a + 1) :=
    ERMor1.boundedRec
      (ERMor1.packedBase k a h)
      (ERMor1.packedStep k a g)
      (ERMor1.tuplePackedBound k componentBound)
  fun i : Fin (k + 1) =>
    ERMor1.comp (ERMor1.tupleAt k i) ![packedRec]

end ERMor1
end GebLean
