import GebLean.LawvereKSim

/-!
# Interpretation of K^sim morphisms into ℕ

This module defines `KMor1.interp` and `KMorN.interp`,
mapping each K^sim morphism to its corresponding
ℕ-valued function.  Per design principle P10
(`docs/lawvere-k-sim-hierarchy.md`), every named composite
elsewhere in the development is paired with an interp lemma.
-/

namespace GebLean

/-- Standard interpretation of a `KMor1` term as a
function `(Fin n → ℕ) → ℕ`.  Each constructor is
interpreted pointwise; `simrec` runs the simultaneous
recursion straightforwardly via `Nat.rec` on the
recursion variable, building the (k+1)-vector of
intermediate values and selecting the requested
output. -/
def KMor1.interp : {n : ℕ} → KMor1 n →
    (Fin n → ℕ) → ℕ
  | _, .zero,   _   => 0
  | _, .succ,   ctx => (ctx 0).succ
  | _, .proj i, ctx => ctx i
  | _, .comp f gs, ctx =>
      f.interp (fun i => (gs i).interp ctx)
  | _, .simrec (a := a) (k := k) i h g, ctx =>
      let recVar : ℕ := ctx 0
      let params : Fin a → ℕ :=
        fun j => ctx (Fin.succ j)
      let stepVec : ℕ → (Fin (k + 1) → ℕ) :=
        Nat.rec
          (fun j => (h j).interp params)
          (fun m prev =>
            fun j =>
              let stepCtx :
                  Fin (a + 1 + (k + 1)) → ℕ :=
                fun idx =>
                  if h₁ : idx.val < a + 1 then
                    if h₂ : idx.val = 0 then
                      m
                    else
                      params ⟨idx.val - 1, by omega⟩
                  else
                    prev ⟨idx.val - (a + 1), by omega⟩
              (g j).interp stepCtx)
      stepVec recVar i
  | _, .raise f, ctx => f.interp ctx

/-- `KMorN.interp`: interpret a multi-output K^sim
morphism as a function `(Fin n → ℕ) → (Fin m → ℕ)`.
Each output component is interpreted independently
via `KMor1.interp`. -/
def KMorN.interp {n m : ℕ} (f : KMorN n m)
    (ctx : Fin n → ℕ) : Fin m → ℕ :=
  fun i => (f i).interp ctx

/-- Interpretation of `zero`. -/
@[simp] theorem KMor1.interp_zero {n : ℕ}
    (ctx : Fin n → ℕ) :
    (KMor1.zero (n := n)).interp ctx = 0 :=
  rfl

/-- Interpretation of `succ`. -/
@[simp] theorem KMor1.interp_succ
    (ctx : Fin 1 → ℕ) :
    KMor1.succ.interp ctx = (ctx 0).succ :=
  rfl

/-- Interpretation of `proj`. -/
@[simp] theorem KMor1.interp_proj {n : ℕ}
    (i : Fin n) (ctx : Fin n → ℕ) :
    (KMor1.proj i).interp ctx = ctx i :=
  rfl

/-- Interpretation of `raise` is identity on the
underlying interp; `raise` is a level marker only. -/
@[simp] theorem KMor1.interp_raise {n : ℕ}
    (f : KMor1 n) (ctx : Fin n → ℕ) :
    (KMor1.raise f).interp ctx = f.interp ctx :=
  rfl

end GebLean
