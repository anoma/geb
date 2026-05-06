import GebLean.LawvereKSim
import GebLean.Utilities.SimRec

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

/-- Step-case interp for `simrecVec` in the `Fin.append (Fin.cons …)`
form. Equivalent to `simrecVec_succ` (which produces a dite-form
context) but expressed via the standard `Fin.append` of
`Fin.cons (recvar, params)` and the `simrecVec`-at-`n` family.
This is the form used by `KMor1.interp_rec1_succ` and any other
caller that wants to treat the step context positionally. -/
@[simp] theorem KMor1.simrecVec_succ_append {a k : ℕ}
    (h : Fin (k + 1) → KMor1 a)
    (g : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (params : Fin a → ℕ) (n : ℕ) (j : Fin (k + 1)) :
    KMor1.simrecVec h g params (n + 1) j
      = (g j).interp (Fin.append (Fin.cons n params)
                                  (KMor1.simrecVec h g params n)) := by
  simp only [KMor1.simrecVec_succ]
  congr 1
  funext idx
  rcases idx with ⟨v, h_v⟩
  by_cases h₁ : v < a + 1
  · have h_cast : (⟨v, h_v⟩ : Fin (a + 1 + (k + 1)))
        = Fin.castAdd (k + 1) (⟨v, h₁⟩ : Fin (a + 1)) := by
      apply Fin.ext; rfl
    rw [show Fin.append (Fin.cons n params)
            (KMor1.simrecVec h g params n) ⟨v, h_v⟩
            = Fin.append (Fin.cons n params)
                (KMor1.simrecVec h g params n)
                (Fin.castAdd (k + 1) (⟨v, h₁⟩ : Fin (a + 1)))
        from congrArg _ h_cast,
        Fin.append_left]
    simp only [h₁, dite_true]
    by_cases h₂ : v = 0
    · simp only [h₂, dite_true]; rfl
    · simp only [h₂, dite_false]
      have h_succ : (⟨v, h₁⟩ : Fin (a + 1))
          = Fin.succ (⟨v - 1, by omega⟩ : Fin a) := by
        apply Fin.ext; change v = (v - 1) + 1; omega
      rw [h_succ, Fin.cons_succ]
  · have h_cast : (⟨v, h_v⟩ : Fin (a + 1 + (k + 1)))
        = Fin.natAdd (a + 1)
            (⟨v - (a + 1), by omega⟩ : Fin (k + 1)) := by
      apply Fin.ext
      change v = (a + 1) + (v - (a + 1))
      omega
    rw [show Fin.append (Fin.cons n params)
            (KMor1.simrecVec h g params n) ⟨v, h_v⟩
            = Fin.append (Fin.cons n params)
                (KMor1.simrecVec h g params n)
                (Fin.natAdd (a + 1)
                  (⟨v - (a + 1), by omega⟩ : Fin (k + 1)))
        from congrArg _ h_cast,
        Fin.append_right]
    simp only [h₁, dite_false]

/-- Base-case interp for `rec1`: at recursion variable `0`,
`rec1 h g` returns `h.interp params`. -/
@[simp] theorem KMor1.interp_rec1_zero {a : ℕ}
    (h : KMor1 a) (g : KMor1 (a + 2))
    (params : Fin a → ℕ) :
    (KMor1.rec1 h g).interp (Fin.cons 0 params)
      = h.interp params := by
  unfold KMor1.rec1
  rw [KMor1.interp_simrec]
  rfl

/-- Step-case interp for `rec1`: at recursion variable `n + 1`,
`rec1 h g` returns `g.interp` applied to the context
`(n, params, prev)` where `prev = (rec1 h g).interp (Fin.cons n
params)`. -/
@[simp] theorem KMor1.interp_rec1_succ {a : ℕ}
    (h : KMor1 a) (g : KMor1 (a + 2))
    (n : ℕ) (params : Fin a → ℕ) :
    (KMor1.rec1 h g).interp (Fin.cons (n + 1) params)
      = g.interp (Fin.append (m := a + 1) (n := 1)
          ((Fin.cons n params : Fin (a + 1) → ℕ))
          (fun _ : Fin 1 =>
            (KMor1.rec1 h g).interp (Fin.cons n params))) := by
  set prev := (KMor1.rec1 h g).interp (Fin.cons n params) with hprev
  unfold KMor1.rec1
  rw [KMor1.interp_simrec]
  have h_ctx0 :
      (Fin.cons (n + 1) params : Fin (a + 1) → ℕ) 0 = n + 1 := by
    simp [Fin.cons_zero]
  have h_params :
      (fun j => (Fin.cons (n + 1) params : Fin (a + 1) → ℕ)
          (Fin.succ j)) = params := by
    funext j; simp [Fin.cons_succ]
  rw [h_ctx0, h_params]
  simp only [KMor1.simrecVec_succ]
  congr 1
  funext idx
  rcases idx with ⟨v, h_v⟩
  by_cases h₁ : v < a + 1
  · have h_cast : (⟨v, h_v⟩ : Fin (a + 1 + 1))
        = Fin.castAdd 1 (⟨v, h₁⟩ : Fin (a + 1)) := by
      apply Fin.ext; rfl
    rw [show Fin.append (Fin.cons n params)
            (fun _ : Fin 1 => prev) ⟨v, h_v⟩
            = Fin.append (Fin.cons n params)
                (fun _ : Fin 1 => prev)
                (Fin.castAdd 1 (⟨v, h₁⟩ : Fin (a + 1)))
          from congrArg _ h_cast,
        Fin.append_left]
    simp only [h₁, dite_true]
    by_cases h₂ : v = 0
    · simp only [h₂, dite_true]; rfl
    · simp only [h₂, dite_false]
      have h_succ : (⟨v, h₁⟩ : Fin (a + 1))
          = Fin.succ (⟨v - 1, by omega⟩ : Fin a) := by
        apply Fin.ext; change v = (v - 1) + 1; omega
      rw [h_succ, Fin.cons_succ]
  · have h_cast : (⟨v, h_v⟩ : Fin (a + 1 + 1))
        = Fin.natAdd (a + 1) ⟨v - (a + 1), by omega⟩ := by
      apply Fin.ext
      change v = (a + 1) + (v - (a + 1))
      omega
    rw [show Fin.append (Fin.cons n params)
            (fun _ : Fin 1 => prev) ⟨v, h_v⟩
            = Fin.append (Fin.cons n params)
                (fun _ : Fin 1 => prev)
                (Fin.natAdd (a + 1) ⟨v - (a + 1), by omega⟩)
          from congrArg _ h_cast,
        Fin.append_right]
    simp only [h₁, dite_false]
    have h_idx : (⟨v - (a + 1), by omega⟩ : Fin 1)
        = ⟨0, by decide⟩ := by
      apply Fin.ext; omega
    rw [h_idx]
    rw [hprev]
    unfold KMor1.rec1
    rw [KMor1.interp_simrec]
    have h_ctx0' :
        (Fin.cons n params : Fin (a + 1) → ℕ) 0 = n := by
      simp [Fin.cons_zero]
    have h_params' :
        (fun j => (Fin.cons n params : Fin (a + 1) → ℕ)
            (Fin.succ j)) = params := by
      funext j; simp [Fin.cons_succ]
    rw [h_ctx0', h_params']

/-- Interpretation of `KMorN.id`: applying the identity
morphism to a context returns the context itself. -/
@[simp] theorem KMorN.interp_id (n : ℕ)
    (ctx : Fin n → ℕ) :
    (KMorN.id n).interp ctx = ctx := by
  funext i
  simp [KMorN.id, KMorN.interp]

/-- Interpretation of `KMorN.terminal`: the empty
morphism produces the empty function. -/
@[simp] theorem KMorN.interp_terminal (n : ℕ)
    (ctx : Fin n → ℕ) :
    (KMorN.terminal n).interp ctx = Fin.elim0 := by
  funext i
  exact i.elim0

/-- Interpretation of `KMorN.fst`: each output is
the corresponding element from the first `n`
components of the context. -/
@[simp] theorem KMorN.interp_fst {n m : ℕ}
    (ctx : Fin (n + m) → ℕ) :
    (KMorN.fst (n := n) (m := m)).interp ctx
      = fun i => ctx (Fin.castAdd m i) := by
  funext i
  simp [KMorN.fst, KMorN.interp]

/-- Interpretation of `KMorN.snd`: each output is
the corresponding element from the last `m`
components of the context. -/
@[simp] theorem KMorN.interp_snd {n m : ℕ}
    (ctx : Fin (n + m) → ℕ) :
    (KMorN.snd (n := n) (m := m)).interp ctx
      = fun i => ctx (Fin.natAdd n i) := by
  funext i
  simp [KMorN.snd, KMorN.interp]

/-- Interpretation of `KMorN.comp`: composing `f`
after `g` first applies `g`'s interpretation to
the context, then applies `f`'s interpretation. -/
@[simp] theorem KMorN.interp_comp
    {n m k : ℕ}
    (f : KMorN m k) (g : KMorN n m)
    (ctx : Fin n → ℕ) :
    (KMorN.comp f g).interp ctx
      = (f.interp (g.interp ctx)) :=
  rfl

/-- Interpretation of `KMorN.pair`: concatenates
the results of interpreting `f` and `g`. -/
@[simp] theorem KMorN.interp_pair
    {k n m : ℕ}
    (f : KMorN k n) (g : KMorN k m)
    (ctx : Fin k → ℕ) :
    (KMorN.pair f g).interp ctx
      = fun i =>
          if h : i.val < n then
            f.interp ctx ⟨i.val, h⟩
          else
            g.interp ctx
              ⟨i.val - n, by omega⟩ := by
  funext i
  simp [KMorN.pair, KMorN.interp]
  split_ifs <;> rfl

/-- Bridge between K^sim's `simrecVec` interpreter (which
recurses with `KMor1.interp` calls inline) and `Nat.simRecVec`
(the value-side simultaneous recursion consumed by
`ERMor1.simultaneousBoundedRec_interp_correct`).  Master
design §3.5; supports the simrec branch of step 5's
`kToER_simrec_dominates` / `kToER_interp_simrec`. -/
theorem KMor1.simrecVec_eq_Nat_simRecVec {a k : ℕ}
    (h : Fin (k + 1) → KMor1 a)
    (g : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (params : Fin a → ℕ) :
    ∀ (n : ℕ) (j : Fin (k + 1)),
      KMor1.simrecVec h g params n j
        = Nat.simRecVec k a (fun j' => (h j').interp)
            (fun j' => (g j').interp) n params j := by
  intro n
  induction n with
  | zero => intro j; rfl
  | succ n ih =>
      intro j
      simp only [KMor1.simrecVec, Nat.simRecVec_succ]
      congr 1
      funext idx
      rcases idx with ⟨v, h_v⟩
      by_cases h₁ : v < a + 1
      · have h_cast :
            (⟨v, h_v⟩ : Fin (a + 1 + (k + 1)))
              = Fin.castAdd (k + 1)
                  (⟨v, h₁⟩ : Fin (a + 1)) := by
          apply Fin.ext; rfl
        rw [show Fin.append (Fin.cons n params)
              (Nat.simRecVec k a (fun j' => (h j').interp)
                (fun j' => (g j').interp) n params)
              ⟨v, h_v⟩
              = Fin.append (Fin.cons n params)
                  (Nat.simRecVec k a
                    (fun j' => (h j').interp)
                    (fun j' => (g j').interp) n params)
                  (Fin.castAdd (k + 1)
                    (⟨v, h₁⟩ : Fin (a + 1))) from
            congrArg _ h_cast,
          Fin.append_left]
        simp only [h₁, dite_true]
        by_cases h₂ : v = 0
        · simp only [h₂, dite_true]
          rfl
        · simp only [h₂, dite_false]
          have h_succ :
              (⟨v, h₁⟩ : Fin (a + 1))
                = Fin.succ
                    (⟨v - 1, by omega⟩ : Fin a) := by
            apply Fin.ext
            change v = (v - 1) + 1
            omega
          rw [h_succ, Fin.cons_succ]
      · have h_cast :
            (⟨v, h_v⟩ : Fin (a + 1 + (k + 1)))
              = Fin.natAdd (a + 1)
                  ⟨v - (a + 1), by omega⟩ := by
          apply Fin.ext
          change v = (a + 1) + (v - (a + 1))
          omega
        rw [show Fin.append (Fin.cons n params)
              (Nat.simRecVec k a (fun j' => (h j').interp)
                (fun j' => (g j').interp) n params)
              ⟨v, h_v⟩
              = Fin.append (Fin.cons n params)
                  (Nat.simRecVec k a
                    (fun j' => (h j').interp)
                    (fun j' => (g j').interp) n params)
                  (Fin.natAdd (a + 1)
                    ⟨v - (a + 1), by omega⟩) from
            congrArg _ h_cast,
          Fin.append_right]
        simp only [h₁, dite_false]
        exact ih ⟨v - (a + 1), by omega⟩

end GebLean
