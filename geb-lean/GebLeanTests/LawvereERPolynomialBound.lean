import GebLean.LawvereERPolynomialBound

/-!
# Tests for LawvereERPolynomialBound

Tests for `PolyBound` constructor builders and the
`to_iter_step_form` adapter.
-/

open GebLean

example : ERMor1.PolyBound.ofZero.degree = 0 := rfl
example : ERMor1.PolyBound.ofZero.coefficient = 0 := rfl
example : ERMor1.PolyBound.ofZero.constant = 0 := rfl

example : ERMor1.PolyBound.ofSucc.degree = 1 := rfl
example : ERMor1.PolyBound.ofSucc.coefficient = 1 := rfl
example : ERMor1.PolyBound.ofSucc.constant = 1 := rfl

example : (ERMor1.PolyBound.ofProj (k := 1) 0).degree = 1 := rfl
example : (ERMor1.PolyBound.ofProj (k := 1) 0).coefficient = 1 := rfl
example : (ERMor1.PolyBound.ofProj (k := 1) 0).constant = 0 := rfl

example : ERMor1.PolyBound.ofSub.degree = 1 := rfl
example : ERMor1.PolyBound.ofSub.coefficient = 1 := rfl
example : ERMor1.PolyBound.ofSub.constant = 0 := rfl

example : (0 : ℕ) ≤
    ERMor1.PolyBound.ofZero.coefficient *
      ((Finset.univ : Finset (Fin 0)).sup Fin.elim0 + 1) ^
        ERMor1.PolyBound.ofZero.degree
    + ERMor1.PolyBound.ofZero.constant :=
  ERMor1.PolyBound.ofZero.bounds Fin.elim0

private def succProj0 : ERMor1 1 :=
  ERMor1.comp ERMor1.succ
    (fun (_ : Fin 1) => ERMor1.proj (k := 1) 0)

private def pb_succProj0 : ERMor1.PolyBound succProj0 :=
  ERMor1.PolyBound.ofComp ERMor1.PolyBound.ofSucc
    (fun _ => ERMor1.PolyBound.ofProj 0)

example (ctx : Fin 1 → ℕ) :
    succProj0.interp ctx ≤
      pb_succProj0.coefficient *
        ((Finset.univ : Finset (Fin 1)).sup ctx + 1) ^
          pb_succProj0.degree
      + pb_succProj0.constant :=
  pb_succProj0.bounds ctx

private def stepBody : ERMor1 (1 + 2) :=
  ERMor1.comp ERMor1.succ
    (fun (_ : Fin 1) => ERMor1.proj (k := 3) 0)

private def pb_stepBody : ERMor1.PolyBound stepBody :=
  ERMor1.PolyBound.ofComp ERMor1.PolyBound.ofSucc
    (fun _ => ERMor1.PolyBound.ofProj 0)

example (params : Fin 1 → ℕ) (v x : ℕ) :
    stepBody.interp (Fin.cons x (Fin.cons v params)) ≤
      (max v (max x ((Finset.univ : Finset (Fin 1)).sup params))
        + 2) ^
        (pb_stepBody.degree + pb_stepBody.coefficient +
          pb_stepBody.constant + 2) :=
  ERMor1.PolyBound.to_iter_step_form stepBody pb_stepBody params v x

private def pb_bsum_succ : ERMor1.PolyBound (ERMor1.bsum ERMor1.succ) :=
  ERMor1.PolyBound.ofBsum ERMor1.PolyBound.ofSucc

example (ctx : Fin 1 → ℕ) :
    (ERMor1.bsum ERMor1.succ).interp ctx ≤
      pb_bsum_succ.coefficient *
        ((Finset.univ : Finset (Fin 1)).sup ctx + 1) ^
          pb_bsum_succ.degree
      + pb_bsum_succ.constant :=
  pb_bsum_succ.bounds ctx
