import GebLean.Ramified.Soundness.Normalization

/-!
# Tests for the Lemma 12 normalization bound

Tests for the type-order measure `RType.ord` (task 6.3.3).
-/

namespace GebLean.Ramified

/-- The order of the twice-nested arrow `(o → o) → o` is `2` (Leivant III
section 2.2, p. 213): the outer `arrow` takes the maximum of `1 + ord (o → o)`
and `ord o`, and `ord (o → o) = max (1 + ord o) (ord o) = 1`. -/
example : (RType.arrow (RType.arrow RType.o RType.o) RType.o).ord = 2 := by simp

end GebLean.Ramified
