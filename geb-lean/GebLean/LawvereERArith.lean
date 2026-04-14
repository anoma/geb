import GebLean.LawvereER

/-!
# Arithmetic on Elementary Recursive Terms

Derived arithmetic operations beyond the generators:
exponentiation via bounded product.
-/

namespace GebLean

/-- Product of a constant function: multiplying `y` over
`bound` iterations equals `y ^ bound`. -/
theorem natBProd_const (bound y : ℕ) :
    natBProd bound (fun _ => y) = y ^ bound := by
  induction bound with
  | zero => rfl
  | succ b ih =>
    change natBProd b (fun _ => y) * y = y ^ (b + 1)
    rw [ih, Nat.pow_succ]

end GebLean
