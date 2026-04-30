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
recursion via `Nat.rec` on the recursion variable,
building the (k+1)-vector of intermediate values and
selecting the requested output. -/
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

/-- The (k+1)-component vector of intermediate values
produced by `simrec` when applied to `n` recursive
steps.  The base case (n = 0) applies each `h j` to
`params`; the step case builds a context from the
step index, original parameters, and the previous
vector, then applies each `g j`. -/
def KMor1.simrecVec {a k : ℕ}
    (h : Fin (k + 1) → KMor1 a)
    (g : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (params : Fin a → ℕ) : ℕ → (Fin (k + 1) → ℕ)
  | 0 => fun j => (h j).interp params
  | n + 1 =>
    let prev := KMor1.simrecVec h g params n
    fun j =>
      let stepCtx : Fin (a + 1 + (k + 1)) → ℕ :=
        fun idx =>
          if h₁ : idx.val < a + 1 then
            if h₂ : idx.val = 0 then
              n
            else
              params ⟨idx.val - 1, by omega⟩
          else
            prev ⟨idx.val - (a + 1), by omega⟩
      (g j).interp stepCtx

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

/-- Interpretation of composition: apply `f`'s
interpretation to the family of `gs`'s interpretations
at the given context. -/
@[simp] theorem KMor1.interp_comp
    {a b : ℕ} (f : KMor1 b) (gs : Fin b → KMor1 a)
    (ctx : Fin a → ℕ) :
    (KMor1.comp f gs).interp ctx
      = f.interp (fun i => (gs i).interp ctx) :=
  rfl

/-- The `simrec` case of `interp` agrees with
`simrecVec KMor1.interp`. -/
private theorem KMor1.interp_simrec_eq_simrecVec
    {a k : ℕ}
    (h : Fin (k + 1) → KMor1 a)
    (g : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (params : Fin a → ℕ) (n : ℕ) :
    (fun j =>
      let stepVec : ℕ → Fin (k + 1) → ℕ :=
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
      stepVec n j)
    = KMor1.simrecVec h g params n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [KMor1.simrecVec]
    funext j
    congr 1
    funext idx
    by_cases h₁ : idx.val < a + 1
    · simp only [h₁, dite_true]
    · simp only [h₁, dite_false]
      exact congr_fun ih ⟨idx.val - (a + 1), by omega⟩

/-- Interpretation of `simrec` expressed via
`simrecVec`: applies the recursion vector at the step
count given by the first context entry, with
parameters drawn from the remaining entries. -/
@[simp] theorem KMor1.interp_simrec
    {a k : ℕ}
    (i : Fin (k + 1))
    (h : Fin (k + 1) → KMor1 a)
    (g : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (ctx : Fin (a + 1) → ℕ) :
    (KMor1.simrec i h g).interp ctx
      = KMor1.simrecVec h g
          (fun j => ctx (Fin.succ j))
          (ctx 0) i := by
  simp only [KMor1.interp]
  exact congr_fun
    (KMor1.interp_simrec_eq_simrecVec h g
      (fun j => ctx (Fin.succ j)) (ctx 0)) i

/-- Base case of `simrecVec`: at step zero, each
output is the base morphism `h j` applied to
`params`. -/
@[simp] theorem KMor1.simrecVec_zero
    {a k : ℕ}
    (h : Fin (k + 1) → KMor1 a)
    (g : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (params : Fin a → ℕ) (j : Fin (k + 1)) :
    KMor1.simrecVec h g params 0 j
      = (h j).interp params :=
  rfl

/-- Step case of `simrecVec`: at step `n + 1`, each
output is the step morphism `g j` applied to a
context assembled from `n`, `params`, and the
previous vector. -/
@[simp] theorem KMor1.simrecVec_succ
    {a k : ℕ}
    (h : Fin (k + 1) → KMor1 a)
    (g : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (params : Fin a → ℕ) (n : ℕ) (j : Fin (k + 1)) :
    KMor1.simrecVec h g params (n + 1) j
      = (g j).interp
          (fun idx =>
            if h₁ : idx.val < a + 1 then
              if h₂ : idx.val = 0 then
                n
              else
                params ⟨idx.val - 1, by omega⟩
            else
              KMor1.simrecVec h g params n
                ⟨idx.val - (a + 1), by omega⟩) :=
  rfl

end GebLean
