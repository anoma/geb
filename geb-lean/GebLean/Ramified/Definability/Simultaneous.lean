import GebLean.Ramified.Examples

/-!
# Case analysis, the destructor, and the selector

The definability building blocks of Leivant III's Lemma 2 (simultaneous
recurrence, section 2.6) over the `1 + X` word algebra `natAlgSig`: the case
function `case^τ`, the destructor `dstr`, and the selector `choose`, each a
schema identifier of the higher-order system (`GebLean/Ramified/HigherOrder.lean`)
with an interpretation lemma reading its denotation on the standard carriers.
The case function and the destructor are flat recurrences (`RIdent.frec`); the
selector is a family, indexed by its entry count, built by recursion on that
count from `case` and `dstr` compositions per the proof of Lemma 2. The selector
is total: a selector value at or beyond the entry count falls through to the last
entry (`chooseIdent_interp_ge`).

## Main definitions

* `ramCase` — the case function `case^τ : o, τ, τ → τ`: the flat recurrence whose
  clause at constructor `c_i` returns the `i`-th parameter.
* `ramDstr` — the destructor `dstr : o → o`: the predecessor, a flat recurrence
  reading the subterm.
* `chooseIdent` — the selector `choose : o, τ^(m+1) → τ` over `m + 1` entries,
  built by recursion on `m` from `ramCase` and `ramDstr`.

## Main statements

* `ramCase_interp` — the case function selects the parameter indexed by the
  argument's top constructor.
* `ramDstr_interp` — the destructor is the predecessor on counts.
* `chooseIdent_interp` — on a selector numeral `j ≤ m` the selector denotes the
  entry `y_j`.
* `chooseIdent_interp_ge` — on a selector numeral `j ≥ m` the selector denotes
  the last entry `y_m` (the fall-through).

## Implementation notes

Every identifier is a schema identifier (`RIdent natAlgSig`), interpreted by
`RIdent.interp` on the standard carriers `RType.interp (FreeAlg natAlgSig)`,
which at an object sort is a copy of `FreeAlg natAlgSig` (Leivant III section
2.7). The selector's recursion on the entry count `m` is a plain structural
definition over `Nat`, following the committed precedent `ramDeltaIdent`
(`GebLean/Ramified/Examples.lean`); no Lean-native recursive type is introduced.
The selector step `chooseIdent (m + 1)` is an explicit definition
(`RIdent.defn`) whose holes reference `ramCase τ`, `ramDstr`, and
`chooseIdent m τ`, realizing `choose(z, y₀ … y_{m+1}) = case^τ(y₀,
chooseIdent m (dstr z) (y₁ …), z)`.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`. The case and destructor
functions are section 2.5; the selector is the proof of Lemma 2, section 2.6
(p. 218). The fall-through of the selector on out-of-range values is novel
packaging (the total indexing at `m + 1` and the routing of every out-of-range
selector to the last entry), consumed by the machine simulation's implicit-halt
arm.

## Tags

ramified recurrence, case, destructor, predecessor, selector, definability,
simultaneous recurrence
-/

namespace GebLean.Ramified

open CategoryTheory

/-- The clauses of the case function's flat recurrence: at each constructor
label `i` an explicit definition returning the `i`-th parameter variable
(`false` returns parameter `0`, `true` returns parameter `1`), ignoring the
subterm of the recurrence argument. -/
def ramCaseClauses (τ : RType) : (i : Bool) →
    RIdent natAlgSig ([τ, τ] ++ List.replicate (natAlgSig.ar i) RType.o) τ
  | false =>
    (RIdent.defn ⟨0, finZeroElim, Tm.var 0⟩ finZeroElim :
      RIdent natAlgSig [τ, τ] τ)
  | true =>
    (RIdent.defn ⟨0, finZeroElim, Tm.var 1⟩ finZeroElim :
      RIdent natAlgSig [τ, τ, RType.o] τ)

/-- Leivant III section 2.5's case function `case^τ : o, τ, τ → τ` over the
`1 + X` word algebra, as the flat recurrence (`RIdent.frec`) with parameters
`[τ, τ]` — one entry per constructor of `natAlgSig`, in the order `false`,
`true` — and recurrence argument at `o`: the clause at constructor `c_i` returns
the `i`-th parameter, `case^τ(y₀, y₁, 0) = y₀` and
`case^τ(y₀, y₁, succ a) = y₁`. The result sort `τ` is arbitrary
(`RIdent.frec` permits it), so the section 2.5 / eq. (2) explicit-definition lift
of a case function to an arbitrary result sort is subsumed and not needed as a
separate construction. -/
def ramCase (τ : RType) : RIdent natAlgSig ([τ, τ] ++ [RType.o]) τ :=
  RIdent.frec [τ, τ] τ (ramCaseClauses τ)

/-- The clauses of the destructor's flat recurrence: the `false` clause returns
`0` (`tmZero`); the `true` clause returns the sole subterm variable of the
recurrence argument. -/
def ramDstrClauses : (i : Bool) →
    RIdent natAlgSig ([] ++ List.replicate (natAlgSig.ar i) RType.o) RType.o
  | false =>
    (RIdent.defn ⟨0, finZeroElim, tmZero⟩ finZeroElim :
      RIdent natAlgSig [] RType.o)
  | true =>
    (RIdent.defn ⟨0, finZeroElim, Tm.var 0⟩ finZeroElim :
      RIdent natAlgSig [RType.o] RType.o)

/-- Leivant III sections 2.5 and 4.1's destructor `dstr : o → o` over the
`1 + X` word algebra, the predecessor, as the flat recurrence (`RIdent.frec`)
with no parameters and recurrence argument at `o`: `dstr(0) = 0` (the clause for
the nullary constructor, the paper's `j > r_i` clause returning the argument's
absent subterm as `0`) and `dstr(succ a) = a` (the clause for the unary
constructor, reading the subterm). -/
def ramDstr : RIdent natAlgSig [RType.o] RType.o :=
  RIdent.frec [] RType.o ramDstrClauses

/-- The environment at the case function's context `[τ, τ, o]`: the two
parameters `y₀`, `y₁` and the recurrence argument `z`. -/
def caseEnv (τ : RType) (y0 y1 : RType.interp (FreeAlg natAlgSig) τ)
    (z : FreeAlg natAlgSig) :
    ∀ i : Fin ([τ, τ] ++ [RType.o] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([τ, τ] ++ [RType.o] : Ctx RType).get i) :=
  Fin.cons y0 (Fin.cons y1 (Fin.cons z finZeroElim))

/-- The environment at the destructor's context `[o]`: the sole recurrence
argument `z`. -/
def dstrEnv (z : FreeAlg natAlgSig) :
    ∀ i : Fin ([RType.o] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([RType.o] : Ctx RType).get i) :=
  Fin.cons z finZeroElim

/-- Leivant III section 2.5: the case function selects the parameter indexed by
the recurrence argument's top constructor — `y₀` at the nullary constructor,
`y₁` at the unary constructor. -/
theorem ramCase_interp (τ : RType) (y0 y1 : RType.interp (FreeAlg natAlgSig) τ)
    (b : Bool) (subs : Fin (natAlgSig.ar b) → FreeAlg natAlgSig) :
    (ramCase τ).interp (caseEnv τ y0 y1 (FreeAlg.mk b subs)) = cond b y1 y0 := by
  cases b <;> rfl

/-- Leivant III sections 2.5, 4.1: the destructor returns `0` at the nullary
constructor. -/
theorem ramDstr_interp_zero (subs : Fin (natAlgSig.ar false) → FreeAlg natAlgSig) :
    ramDstr.interp (dstrEnv (FreeAlg.mk false subs)) = natToFreeAlg 0 :=
  congrArg (FreeAlg.mk (A := natAlgSig) false) (funext (fun i : Fin 0 => i.elim0))

/-- Leivant III sections 2.5, 4.1: the destructor returns the sole subterm at the
unary constructor (the predecessor). -/
theorem ramDstr_interp_succ (subs : Fin (natAlgSig.ar true) → FreeAlg natAlgSig) :
    ramDstr.interp (dstrEnv (FreeAlg.mk true subs)) = subs ⟨0, by decide⟩ := rfl

/-- Leivant III sections 2.5, 4.1: the destructor denotes the predecessor on
counts, `freeAlgToNat (dstr z) = freeAlgToNat z - 1`, uniformly over both
constructors. -/
theorem ramDstr_interp (z : FreeAlg natAlgSig) :
    freeAlgToNat (ramDstr.interp (dstrEnv z)) = freeAlgToNat z - 1 := by
  cases z with
  | mk _ b subs =>
    cases b with
    | false =>
      change freeAlgToNat (ramDstr.interp (dstrEnv (FreeAlg.mk false subs))) = _
      rw [ramDstr_interp_zero]; rfl
    | true =>
      change freeAlgToNat (ramDstr.interp (dstrEnv (FreeAlg.mk true subs))) = _
      rw [ramDstr_interp_succ]; rfl

/-- Every non-head position of the selector's context `o :: τ^n` carries the
entry sort `τ`. -/
theorem chooseCtx_get_pos (τ : RType) (n : Nat)
    (k : Fin (RType.o :: List.replicate n τ : Ctx RType).length) (hk : 0 < k.val) :
    (RType.o :: List.replicate n τ : Ctx RType).get k = τ := by
  obtain ⟨kv, hkv⟩ := k
  cases kv with
  | zero => exact absurd hk (by simp)
  | succ k' => simp [List.get_eq_getElem, List.getElem_replicate]

/-- The context and result sort of the three identifiers the selector step
invokes: the case function `ramCase τ`, the destructor `ramDstr`, and the
selector `chooseIdent m τ` at one fewer entry. -/
def chooseHoleIdx (m : Nat) (τ : RType) : Fin 3 → List RType × RType
  | ⟨0, _⟩ => ([τ, τ, RType.o], τ)
  | ⟨1, _⟩ => ([RType.o], RType.o)
  | ⟨2, _⟩ => (RType.o :: List.replicate (m + 1) τ, τ)

/-- Evaluation of a reindexed variable reads the environment at the variable's
position, heterogeneously (the reindexing transport erased). A helper for the
interpretation lemmas at symbolic context positions, where the reindexing
equality is not definitional. -/
theorem Tm.eval_reind_var_heq {S : Type} {sig : SortedSig S} {Γ : Ctx S}
    (M : SortedModel sig) (ρ : M.Env Γ) {i : Fin Γ.length} {b : S}
    (h : Γ.get i = b) :
    (Tm.reind h (Tm.var (sig := sig) i)).eval M ρ ≍ ρ i := by
  subst h; rfl

/-- Position `0` is in range for the selector step's context. -/
theorem chooseStep_lt0 (m : Nat) (τ : RType) :
    0 < (RType.o :: List.replicate (m + 1 + 1) τ : Ctx RType).length := by
  simp only [List.length_cons, List.length_replicate]; omega

/-- Position `1` is in range for the selector step's context. -/
theorem chooseStep_lt1 (m : Nat) (τ : RType) :
    1 < (RType.o :: List.replicate (m + 1 + 1) τ : Ctx RType).length := by
  simp only [List.length_cons, List.length_replicate]; omega

/-- The tail-entry position `k + 2` is in range for the selector step's
context. -/
theorem chooseStep_ltTail (m : Nat) (τ : RType) {k : Nat} (hk : k < m + 1) :
    k + 2 < (RType.o :: List.replicate (m + 1 + 1) τ : Ctx RType).length := by
  simp only [List.length_cons, List.length_replicate]; omega

/-- The defining term of the selector step `chooseIdent (m + 1)`: the case
function applied to the head entry `y₀ = var 1`, the recursive selector call, and
the selector variable `z = var 0`. The recursive call is the `chooseIdent m`
hole applied to the destructor of `z` and the tail entries `y₁ … y_{m+1}`
(variables `2 … m + 2`). The three holes reference `ramCase τ`, `ramDstr`, and
`chooseIdent m τ`. -/
def chooseStepBody (m : Nat) (τ : RType) :
    Tm (defnSig natAlgSig 3 (chooseHoleIdx m τ))
      (RType.o :: List.replicate (m + 1 + 1) τ) τ :=
  Tm.op (sig := defnSig natAlgSig 3 (chooseHoleIdx m τ))
    (Sum.inl (Sum.inr (0 : Fin 3)))
    (Fin.cons
      (Tm.reind (chooseCtx_get_pos τ (m + 1 + 1) ⟨1, chooseStep_lt1 m τ⟩ Nat.one_pos)
        (Tm.var ⟨1, chooseStep_lt1 m τ⟩))
      (Fin.cons
        (Tm.op (sig := defnSig natAlgSig 3 (chooseHoleIdx m τ))
          (Sum.inl (Sum.inr (2 : Fin 3)))
          (Fin.cons
            (Tm.op (sig := defnSig natAlgSig 3 (chooseHoleIdx m τ))
              (Sum.inl (Sum.inr (1 : Fin 3)))
              (Fin.cons (Tm.var ⟨0, chooseStep_lt0 m τ⟩) finZeroElim))
            (fun j =>
              Tm.reind
                (by
                  simp only [defnSig, SortedSig.sum, holeSig, Sum.elim_inl, Sum.elim_inr,
                    chooseHoleIdx, List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ,
                    List.getElem_replicate])
                (Tm.var ⟨j.val + 2, chooseStep_ltTail m τ (by simpa using j.isLt)⟩))))
        (Fin.cons (Tm.var ⟨0, chooseStep_lt0 m τ⟩) finZeroElim)))

/-- The identifiers filling the selector step's three holes: the case function,
the destructor, and the selector `rec` at one fewer entry. -/
def chooseChildren (m : Nat) (τ : RType)
    (rec : RIdent natAlgSig (RType.o :: List.replicate (m + 1) τ) τ) : (j : Fin 3) →
    RIdent natAlgSig (chooseHoleIdx m τ j).1 (chooseHoleIdx m τ j).2
  | ⟨0, _⟩ => ramCase τ
  | ⟨1, _⟩ => ramDstr
  | ⟨2, _⟩ => rec

/-- Leivant III's selector `choose : o, τ^(m+1) → τ` over `m + 1` entries (the
proof of Lemma 2, section 2.6, p. 218): on an environment
`(z, y₀, …, y_m)` it returns the entry `y_z` indexed by the selector numeral
`z`, and falls through to the last entry `y_m` for every selector value at or
beyond `m` (`chooseIdent_interp`, `chooseIdent_interp_ge`). Built by recursion
on the entry count `m`: the base returns its sole entry, and the step is the
explicit definition `choose(z, y₀ … y_{m+1}) = case^τ(y₀,
chooseIdent m (dstr z) (y₁ …), z)` (`chooseStepBody`), whose holes reference
`ramCase τ`, `ramDstr`, and `chooseIdent m τ` (`chooseChildren`). The total
indexing at `m + 1` and the fall-through routing are novel packaging, consumed
by the machine simulation's implicit-halt arm. -/
def chooseIdent : (m : Nat) → (τ : RType) →
    RIdent natAlgSig (RType.o :: List.replicate (m + 1) τ) τ
  | 0, τ =>
    (RIdent.defn ⟨0, finZeroElim, Tm.var 1⟩ finZeroElim :
      RIdent natAlgSig [RType.o, τ] τ)
  | m + 1, τ =>
    RIdent.defn ⟨3, chooseHoleIdx m τ, chooseStepBody m τ⟩
      (chooseChildren m τ (chooseIdent m τ))

/-- The model interpreting the selector step's defining term: `defnModel` with
each hole read by the denotation of the identifier filling it. -/
def chooseStepModel (m : Nat) (τ : RType) :
    SortedModel (defnSig natAlgSig 3 (chooseHoleIdx m τ)) :=
  defnModel natAlgSig 3 (chooseHoleIdx m τ)
    (fun j => (chooseChildren m τ (chooseIdent m τ) j).interp)

/-- The environment at the selector's context `o :: τ^(m+1)`, assembled from a
selector value `z` and an entry vector `y₀ … y_m`. -/
def chooseEnv (m : Nat) (τ : RType) (z : FreeAlg natAlgSig)
    (y : Fin (m + 1) → RType.interp (FreeAlg natAlgSig) τ) :
    ∀ i : Fin (RType.o :: List.replicate (m + 1) τ : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig)
        ((RType.o :: List.replicate (m + 1) τ : Ctx RType).get i) :=
  Fin.cons z
    (fun k => cast (by
        simp only [List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ,
          List.getElem_replicate])
      (y ⟨k.val, by simpa using k.isLt⟩))

/-- The selector step unfolds to the case function applied to the head entry, the
recursive selector call on the destructed selector and the tail entries, and the
selector value. -/
theorem chooseIdent_succ_reduce (m : Nat) (τ : RType) (z : FreeAlg natAlgSig)
    (y : Fin (m + 2) → RType.interp (FreeAlg natAlgSig) τ) :
    (chooseIdent (m + 1) τ).interp (chooseEnv (m + 1) τ z y)
      = (ramCase τ).interp (caseEnv τ (y 0)
          ((chooseIdent m τ).interp (chooseEnv m τ (ramDstr.interp (dstrEnv z))
            (fun k => y k.succ)))
          z) := by
  refine congrArg (ramCase τ).interp (funext (fun e => ?_))
  induction e using Fin.cases with
  | zero => rfl
  | succ e' =>
    induction e' using Fin.cases with
    | zero =>
      refine congrArg (chooseIdent m τ).interp (funext (fun i => ?_))
      induction i using Fin.cases with
      | zero => rfl
      | succ k =>
        have hk : k.val < m + 1 := by simpa using k.isLt
        have h1 : chooseEnv (m + 1) τ z y ⟨k.val + 2, chooseStep_ltTail m τ hk⟩
            ≍ y ⟨k.val + 1, by omega⟩ := cast_heq _ _
        have h2 : chooseEnv m τ (ramDstr.interp (dstrEnv z)) (fun k' => y k'.succ) k.succ
            ≍ y ⟨k.val + 1, by omega⟩ := cast_heq _ _
        refine eq_of_heq ((HEq.trans ?_ h1).trans h2.symm)
        exact Tm.eval_reind_var_heq (chooseStepModel m τ) (chooseEnv (m + 1) τ z y)
          (i := ⟨k.val + 2, chooseStep_ltTail m τ hk⟩)
          (b := (RType.o :: List.replicate (m + 1) τ : Ctx RType).get k.succ)
          ((chooseCtx_get_pos τ (m + 1 + 1) ⟨k.val + 2, chooseStep_ltTail m τ hk⟩
              (Nat.succ_pos _)).trans
            (chooseCtx_get_pos τ (m + 1) k.succ (Nat.succ_pos _)).symm)
    | succ e'' =>
      induction e'' using Fin.cases with
      | zero => rfl
      | succ e''' => exact e'''.elim0

/-- Leivant III's selector picks the entry indexed by the selector numeral: on
`chooseEnv m τ z y` with `z` the numeral `j ≤ m`, the selector denotes `y j`
(the proof of Lemma 2, section 2.6). -/
theorem chooseIdent_interp : (m : Nat) → (τ : RType) → (z : FreeAlg natAlgSig) →
    (y : Fin (m + 1) → RType.interp (FreeAlg natAlgSig) τ) → (j : Fin (m + 1)) →
    z = natToFreeAlg j.val →
    (chooseIdent m τ).interp (chooseEnv m τ z y) = y j
  | 0, τ, z, y, j, _hz => by
    obtain rfl : j = 0 := Fin.fin_one_eq_zero j
    rfl
  | m + 1, τ, z, y, j, hz => by
    subst hz
    induction j using Fin.cases with
    | zero =>
      simp only [Fin.val_zero]
      exact (chooseIdent_succ_reduce m τ _ y).trans
        (ramCase_interp τ (y 0) _ false finZeroElim)
    | succ j' =>
      exact (chooseIdent_succ_reduce m τ _ y).trans
        ((ramCase_interp τ (y 0) _ true _).trans
          (chooseIdent_interp m τ _ (fun k => y k.succ) j' rfl))

/-- Leivant III's selector falls through to the last entry on out-of-range
values: on `chooseEnv m τ z y` with `z` the numeral `j ≥ m`, the selector
denotes `y m` (the last entry). Novel packaging (the fall-through routing),
consumed by the machine simulation's implicit-halt arm. -/
theorem chooseIdent_interp_ge : (m : Nat) → (τ : RType) → (z : FreeAlg natAlgSig) →
    (y : Fin (m + 1) → RType.interp (FreeAlg natAlgSig) τ) → (j : Nat) →
    m ≤ j → z = natToFreeAlg j →
    (chooseIdent m τ).interp (chooseEnv m τ z y) = y (Fin.last m)
  | 0, _τ, _z, _y, _j, _hj, _hz => rfl
  | m + 1, τ, z, y, j, hj, hz => by
    subst hz
    cases j with
    | zero => exact absurd hj (by omega)
    | succ j' =>
      exact (chooseIdent_succ_reduce m τ _ y).trans
        ((ramCase_interp τ (y 0) _ true _).trans
          (chooseIdent_interp_ge m τ _ (fun k => y k.succ) j' (by omega) rfl))

end GebLean.Ramified
