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

/-- Exponentiation as an elementary recursive term:
`expER` interprets at context `[n, y]` as `y ^ n`,
built via bounded product of the projection onto `y`. -/
def ERMor1.expER : ERMor1 2 :=
  ERMor1.bprod (ERMor1.proj 1)

/-- Interpretation of `expER`: `expER.interp [n, y] = y ^ n`. -/
@[simp] theorem ERMor1.interp_expER (ctx : Fin 2 → ℕ) :
    ERMor1.expER.interp ctx = (ctx 1) ^ (ctx 0) := by
  change natBProd (ctx 0)
    (fun i => (ERMor1.proj (k := 2) 1).interp
      (Fin.cons i (Fin.tail ctx))) = (ctx 1) ^ (ctx 0)
  have hpt : (fun i : ℕ =>
      (ERMor1.proj (k := 2) 1).interp
        (Fin.cons i (Fin.tail ctx))) =
      (fun _ => ctx 1) := by
    funext i
    rw [ERMor1.interp_proj]
    change Fin.cons i (Fin.tail ctx) (Fin.succ 0) = ctx 1
    rw [Fin.cons_succ]
    rfl
  rw [hpt, natBProd_const]

end GebLean
