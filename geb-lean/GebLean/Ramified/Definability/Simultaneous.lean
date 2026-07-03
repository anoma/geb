import GebLean.Ramified.Examples

/-!
# Simultaneous recurrence: case, destructor, selector, and the family

Leivant III's Lemma 2 (simultaneous recurrence, section 2.6) over the `1 + X`
word algebra `natAlgSig`: the definability building blocks — the case function
`case^τ`, the destructor `dstr`, and the selector `choose` — and the
simultaneous family itself, realized as a single function-valued ramified
monotonic recurrence with per-component projections. Each construction is a
schema identifier of the higher-order system
(`GebLean/Ramified/HigherOrder.lean`) with an interpretation lemma reading its
denotation on the standard carriers. The case function and the destructor are
flat recurrences (`RIdent.frec`); the selector is a family, indexed by its
entry count, built by recursion on that count from `case` and `dstr`
compositions per the proof of Lemma 2. The selector is total: a selector value
at or beyond the entry count falls through to the last entry
(`chooseIdent_interp_ge`).

## Main definitions

* `ramCase` — the case function `case^τ : o, τ, τ → τ`: the flat recurrence whose
  clause at constructor `c_i` returns the `i`-th parameter.
* `ramDstr` — the destructor `dstr : o → o`: the predecessor, a flat recurrence
  reading the subterm.
* `chooseIdent` — the selector `choose : o, τ^(m+1) → τ` over `m + 1` entries,
  built by recursion on `m` from `ramCase` and `ramDstr`.
* `SimulSteps` — clause data for an `m`-fold simultaneous recurrence: one step
  identifier per component and constructor, reading the recursive results at
  the function sort `o → τ`.
* `simulIdent` — the single function-valued recurrence realizing the family
  (eq. (7)): recursive results at `o → τ`, count argument at `Ω (o → τ)`.
* `simulProj` — the `j`-th component `f_j = f-hat (b_j)`: `simulIdent` applied
  to the selector numeral `j`.
* `simulSol` — the carrier-level componentwise reference solution, mirroring
  `KMor1.simrecVec` over the ramified sorts.

## Main statements

* `ramCase_interp` — the case function selects the parameter indexed by the
  argument's top constructor.
* `ramDstr_interp` — the destructor is the predecessor on counts.
* `chooseIdent_interp` — on a selector numeral `j ≤ m` the selector denotes the
  entry `y_j`.
* `chooseIdent_interp_ge` — on a selector numeral `j ≥ m` the selector denotes
  the last entry `y_m` (the fall-through).
* `simulProj_interp` — the projected components satisfy the simultaneous
  defining equations: `simulProj j` at count numeral `n` denotes
  `simulSol … n j`.

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

The simultaneous family is realized function-valued (a presentation adaptation
recorded at `simulIdent`): each `mrec` step is an explicit definition whose
body applies the curried combinator form of an auxiliary identifier
(`simulAux`, the selector applied to the per-component steps) to the step
context's variables — the `ramExpStep` curried-hole idiom
(`GebLean/Ramified/Examples.lean`) at a symbolic context, via
`appChainVarsTm`. The environment extension `snocEnv` is defined by recursion
on the context so its cons step is definitional, and the currying coherence
`cast_curryInterp_snoc` connects the curried hole's denotation to the
auxiliary's saturated one.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`. The case and destructor
functions are section 2.5; the selector is the proof of Lemma 2, section 2.6
(p. 218); the simultaneous-recurrence schema and its reduction to plain
recurrence are section 2.6, eqs. (6)-(7), p. 217-218 incl. footnote 6. The
fall-through of the selector on out-of-range values is novel packaging (the
total indexing at `m + 1` and the routing of every out-of-range selector to
the last entry), consumed by the machine simulation's implicit-halt arm. The
function-valued realization of the family, its count sort `Ω (o → τ)`, and the
dropped subterm arguments of eq. (6) are a recorded presentation adaptation;
see `simulIdent`.

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

/-- The environment over `Γ ++ [σ]` extending an environment over `Γ` by one
value at the end. Defined by recursion on `Γ` (through `Fin.cons`) so that the
cons step is definitional, avoiding position-arithmetic transports. Novel
packaging. -/
def snocEnv {C : RType → Type} : (Γ : List RType) → (σ : RType) →
    (∀ v : Fin Γ.length, C (Γ.get v)) → C σ →
    ∀ k : Fin (Γ ++ [σ]).length, C ((Γ ++ [σ]).get k)
  | [], _σ, _ρ, x => Fin.cons x finZeroElim
  | _γ :: Γ', σ, ρ, x => Fin.cons (ρ 0) (snocEnv Γ' σ (fun v => ρ v.succ) x)

/-- The extended environment reads the appended value at every position at or
beyond `Γ.length`, heterogeneously (the append transport erased). -/
theorem snocEnv_heq_right {C : RType → Type} : (Γ : List RType) → (σ : RType) →
    (ρ : ∀ v : Fin Γ.length, C (Γ.get v)) → (x : C σ) →
    (k : Fin (Γ ++ [σ]).length) → Γ.length ≤ k.val →
    snocEnv Γ σ ρ x k ≍ x
  | [], _σ, _ρ, _x, k, _hk => by
    induction k using Fin.cases with
    | zero => exact HEq.rfl
    | succ k' => exact k'.elim0
  | _γ :: Γ', σ, ρ, x, k, hk => by
    induction k using Fin.cases with
    | zero => exact absurd hk (by simp)
    | succ k' =>
      refine (heq_of_eq (Fin.cons_succ _ _ k')).trans ?_
      exact snocEnv_heq_right Γ' σ (fun v => ρ v.succ) x k' (by simpa using hk)

/-- The extended environment reads the source environment at every position
below `Γ.length`, heterogeneously (the append transport erased). -/
theorem snocEnv_heq_left {C : RType → Type} : (Γ : List RType) → (σ : RType) →
    (ρ : ∀ v : Fin Γ.length, C (Γ.get v)) → (x : C σ) → (i : Fin Γ.length) →
    (k : Fin (Γ ++ [σ]).length) → k.val = i.val →
    snocEnv Γ σ ρ x k ≍ ρ i
  | [], _σ, _ρ, _x, i, _k, _hk => i.elim0
  | _γ :: Γ', σ, ρ, x, i, k, hk => by
    induction k using Fin.cases with
    | zero =>
      obtain ⟨iv, hiv⟩ := i
      obtain rfl : iv = 0 := by simpa using hk.symm
      exact HEq.rfl
    | succ k' =>
      obtain ⟨iv, hiv⟩ := i
      cases iv with
      | zero => exact absurd hk (by simp)
      | succ iv' =>
        refine (heq_of_eq (Fin.cons_succ _ _ k')).trans ?_
        exact snocEnv_heq_left Γ' σ (fun v => ρ v.succ) x
          ⟨iv', by have h := hiv; simp only [List.length_cons] at h; omega⟩ k'
          (by simpa using hk)

/-- Reading the recurrence parameters off an extended environment recovers the
source environment. -/
theorem envHead_snocEnv {C : RType → Type} (Γ : List RType) (σ : RType)
    (ρ : ∀ v : Fin Γ.length, C (Γ.get v)) (x : C σ) :
    envHead Γ σ (snocEnv Γ σ ρ x) = ρ := by
  funext i
  exact eq_of_heq ((cast_heq _ _).trans
    (snocEnv_heq_left Γ σ ρ x i (finAppL Γ [σ] i) rfl))

/-- Reading the recurrence argument off an extended environment recovers the
appended value. -/
theorem envLast_snocEnv {C : RType → Type} (Γ : List RType) (σ : RType)
    (ρ : ∀ v : Fin Γ.length, C (Γ.get v)) (x : C σ) :
    envLast Γ σ (snocEnv Γ σ ρ x) = x :=
  eq_of_heq ((cast_heq _ _).trans
    (snocEnv_heq_right Γ σ ρ x (finAppR Γ [σ] ⟨0, Nat.one_pos⟩) (Nat.le_add_right _ _)))

/-- The curried sort of an appended context iterates the currying: the right
fold of `RType.arrow` splits along the append (`List.foldr_append`). -/
theorem RType.curried_append (Γ Δ : List RType) (τ : RType) :
    RType.curried (Γ ++ Δ) τ = RType.curried Γ (RType.curried Δ τ) :=
  List.foldr_append

/-- Application commutes with a codomain-only transport of a function at an
arrow sort: casting along `RType.arrow γ X = RType.arrow γ Y` and applying
equals applying and casting along `X = Y`. -/
theorem interp_arrow_cast_apply {C : Type} {γ X Y : RType} (e : X = Y)
    (f : RType.interp C (RType.arrow γ X)) (a : RType.interp C γ) :
    cast (congrArg (RType.interp C) (congrArg (RType.arrow γ) e)) f a
      = cast (congrArg (RType.interp C) e) (f a) := by
  subst e; rfl

/-- Clause data for an `m`-fold ramified simultaneous (monotonic) recurrence at
result sort `τ` with parameters `params` (Leivant III section 2.6, eq. (6),
monotonic reading): for each component `j` and constructor `i`, a step
identifier seeing the parameters and the `m` recursive results of all
components at each subterm, presented at the function sort `o → τ`
(selector-indexed). The trailing `o` is the selector position of the
function-valued carrier; the step reads recursive results as `o → τ` values
and extracts components by applying them to selector numerals. Eq. (6)'s
subterm arguments are dropped (`RIdent.mrec`'s monotonic reading), part of the
recorded presentation adaptation; see `simulIdent`. -/
def SimulSteps (m : Nat) (params : List RType) (τ : RType) : Type :=
  (j : Fin m) → (i : Bool) →
    RIdent natAlgSig
      (params ++ List.replicate (natAlgSig.ar i) (RType.arrow RType.o τ) ++ [RType.o]) τ

/-- The environment at a simultaneous step's context
`params ++ (o → τ)^(ar i) ++ [o]`: the parameters, the function-valued
recursive results, and the selector value at the end. -/
def simulStepEnv (params : List RType) (τ : RType) (i : Bool)
    (pe : ∀ v : Fin params.length, RType.interp (FreeAlg natAlgSig) (params.get v))
    (phi : Fin (natAlgSig.ar i) →
      RType.interp (FreeAlg natAlgSig) (RType.arrow RType.o τ))
    (u : FreeAlg natAlgSig) :
    ∀ k : Fin (params ++ List.replicate (natAlgSig.ar i) (RType.arrow RType.o τ)
        ++ [RType.o] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig)
        ((params ++ List.replicate (natAlgSig.ar i) (RType.arrow RType.o τ)
          ++ [RType.o] : Ctx RType).get k) :=
  snocEnv (params ++ List.replicate (natAlgSig.ar i) (RType.arrow RType.o τ)) RType.o
    (childEnv params (RType.arrow RType.o τ) (natAlgSig.ar i) pe phi) u

/-- The context and result sort of the identifiers the simultaneous auxiliary
invokes: hole `0` is the selector `chooseIdent (m - 1) τ` over the family's `m`
entries, and hole `k + 1` is the `k`-th component's step identifier at the
auxiliary's own context. -/
def simulHoleIdx (m : Nat) (params : List RType) (τ : RType) (i : Bool) :
    Fin (m + 1) → List RType × RType
  | ⟨0, _⟩ => (RType.o :: List.replicate (m - 1 + 1) τ, τ)
  | ⟨_ + 1, _⟩ =>
    (params ++ List.replicate (natAlgSig.ar i) (RType.arrow RType.o τ) ++ [RType.o], τ)

/-- A selector entry position, shifted past the selector hole, is in range for
the simultaneous auxiliary's hole indexing. -/
theorem simulAux_entry_lt {m : Nat} (hm : 0 < m) {τ : RType}
    (k : Fin (List.replicate (m - 1 + 1) τ).length) : k.val + 1 < m + 1 := by
  have hkv := k.isLt
  simp only [List.length_replicate] at hkv
  omega

/-- The defining term of the simultaneous auxiliary at constructor `i`: the
selector `chooseIdent (m - 1) τ` (hole `0`) applied to the selector variable
(the last context position) and, at entry `k`, the `k`-th component's step
identifier (hole `k + 1`) applied to the whole context — the parameters, the
function-valued recursive results, and the selector. Realizes the entry list
`g-hat_1 … g-hat_m` of Leivant III eq. (7); see `simulIdent` for the recorded
adaptation. -/
def simulAuxBody {m : Nat} (hm : 0 < m) (params : List RType) (τ : RType) (i : Bool) :
    Tm (defnSig natAlgSig (m + 1) (simulHoleIdx m params τ i))
      (params ++ List.replicate (natAlgSig.ar i) (RType.arrow RType.o τ) ++ [RType.o])
      τ :=
  Tm.op (sig := defnSig natAlgSig (m + 1) (simulHoleIdx m params τ i))
    (Sum.inl (Sum.inr (⟨0, Nat.succ_pos m⟩ : Fin (m + 1))))
    (Fin.cons
      (Tm.reind
        (get_finAppR (params ++ List.replicate (natAlgSig.ar i)
          (RType.arrow RType.o τ)) [RType.o] ⟨0, Nat.one_pos⟩)
        (Tm.var (finAppR (params ++ List.replicate (natAlgSig.ar i)
          (RType.arrow RType.o τ)) [RType.o] ⟨0, Nat.one_pos⟩)))
      (fun k =>
        Tm.reind
          (by simp only [defnSig, SortedSig.sum, holeSig, Sum.elim_inl, Sum.elim_inr,
            simulHoleIdx, List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ,
            List.getElem_replicate])
          (Tm.op (sig := defnSig natAlgSig (m + 1) (simulHoleIdx m params τ i))
            (Sum.inl (Sum.inr (⟨k.val + 1, simulAux_entry_lt hm k⟩ : Fin (m + 1))))
            (fun v => Tm.var v))))

/-- The identifiers filling the simultaneous auxiliary's holes: the selector
`chooseIdent (m - 1) τ` at hole `0`, and the `k`-th component's step identifier
at hole `k + 1`. -/
def simulAuxChildren {m : Nat} (params : List RType) (τ : RType)
    (steps : SimulSteps m params τ) (i : Bool) : (h : Fin (m + 1)) →
    RIdent natAlgSig (simulHoleIdx m params τ i h).1 (simulHoleIdx m params τ i h).2
  | ⟨0, _⟩ => chooseIdent (m - 1) τ
  | ⟨k + 1, hk⟩ => steps ⟨k, by omega⟩ i

/-- The simultaneous auxiliary at constructor `i`: the explicit definition at
the step context extended by the selector, whose body is `simulAuxBody` — the
value, at selector `u`, of `choose(u, step₁ᵢ …, step_mᵢ)`. Its currying is the
`mrec` step of `simulIdent`; the projections apply the recurrence to selector
numerals `j < m`, so the selector's fall-through entry is unreachable from
`simulProj`. -/
def simulAux {m : Nat} (hm : 0 < m) (params : List RType) (τ : RType)
    (steps : SimulSteps m params τ) (i : Bool) :
    RIdent natAlgSig
      (params ++ List.replicate (natAlgSig.ar i) (RType.arrow RType.o τ) ++ [RType.o])
      τ :=
  RIdent.defn ⟨m + 1, simulHoleIdx m params τ i, simulAuxBody hm params τ i⟩
    (simulAuxChildren params τ steps i)

/-- The model interpreting the simultaneous auxiliary's defining term:
`defnModel` with each hole read by the denotation of the identifier filling
it. -/
def simulAuxModel {m : Nat} (params : List RType) (τ : RType)
    (steps : SimulSteps m params τ) (i : Bool) :
    SortedModel (defnSig natAlgSig (m + 1) (simulHoleIdx m params τ i)) :=
  defnModel natAlgSig (m + 1) (simulHoleIdx m params τ i)
    (fun h => (simulAuxChildren params τ steps i h).interp)

/-- The simultaneous auxiliary denotes the selector applied to the selector
value and the per-component step denotations at the auxiliary's own
environment: the semantic reading of `simulAuxBody`. -/
theorem simulAux_interp {m : Nat} (hm : 0 < m) (params : List RType) (τ : RType)
    (steps : SimulSteps m params τ) (i : Bool)
    (pe : ∀ v : Fin params.length, RType.interp (FreeAlg natAlgSig) (params.get v))
    (phi : Fin (natAlgSig.ar i) →
      RType.interp (FreeAlg natAlgSig) (RType.arrow RType.o τ))
    (u : FreeAlg natAlgSig) :
    (simulAux hm params τ steps i).interp (simulStepEnv params τ i pe phi u)
      = (chooseIdent (m - 1) τ).interp (chooseEnv (m - 1) τ u
          (fun k => (steps (Fin.cast (Nat.succ_pred_eq_of_pos hm) k) i).interp
            (simulStepEnv params τ i pe phi u))) := by
  refine congrArg (chooseIdent (m - 1) τ).interp (funext (fun e => ?_))
  induction e using Fin.cases with
  | zero =>
    exact eq_of_heq ((Tm.eval_reind_var_heq (simulAuxModel params τ steps i)
      (simulStepEnv params τ i pe phi u) _).trans
      (snocEnv_heq_right _ _ _ _ _ (Nat.le_add_right _ _)))
  | succ k =>
    exact eq_of_heq (((heq_of_eq (Tm.eval_transport (simulAuxModel params τ steps i)
      (simulStepEnv params τ i pe phi u) _ _)).trans
      (cast_heq _ _)).trans (HEq.symm (cast_heq _ _)))

/-- The term applying a curried value to a selection of the ambient context's
variables, one application-former step per peeled sort: from a term at
`RType.curried Γ κ` in context `Γfull`, with each position of `Γ` read at a
sort-matching position of `Γfull`, to a term at `κ`. The `ramExpStep` idiom
(`GebLean/Ramified/Examples.lean`) at a symbolic context. Novel packaging. -/
def appChainVarsTm {n : Nat} {hI : Fin n → List RType × RType} {Γfull : Ctx RType} :
    (Γ : List RType) → (κ : RType) →
    (pos : Fin Γ.length → Fin Γfull.length) →
    (hpos : ∀ v, Γfull.get (pos v) = Γ.get v) →
    Tm (defnSig natAlgSig n hI) Γfull (RType.curried Γ κ) →
    Tm (defnSig natAlgSig n hI) Γfull κ
  | [], _κ, _pos, _hpos, t => t
  | γ :: Γ', κ, pos, hpos, t =>
    appChainVarsTm Γ' κ (fun v => pos v.succ) (fun v => hpos v.succ)
      (Tm.op (sig := defnSig natAlgSig n hI)
        (Sum.inl (Sum.inl (Sum.inr (γ, RType.curried Γ' κ))))
        (Fin.cons t (Fin.cons (Tm.reind (hpos 0) (Tm.var (pos 0))) finZeroElim)))

/-- The variable application chain evaluates to the semantic application chain
`appChain` of the head term's value at the environment read off the selected
positions. -/
theorem appChainVarsTm_eval {n : Nat} {hI : Fin n → List RType × RType}
    (ih : ∀ j : Fin n,
      (∀ v : Fin (hI j).1.length, RType.interp (FreeAlg natAlgSig) ((hI j).1.get v)) →
        RType.interp (FreeAlg natAlgSig) (hI j).2)
    {Γfull : Ctx RType} (ρ : (defnModel natAlgSig n hI ih).Env Γfull) :
    (Γ : List RType) → (κ : RType) →
    (pos : Fin Γ.length → Fin Γfull.length) →
    (hpos : ∀ v, Γfull.get (pos v) = Γ.get v) →
    (t : Tm (defnSig natAlgSig n hI) Γfull (RType.curried Γ κ)) →
    (appChainVarsTm Γ κ pos hpos t).eval (defnModel natAlgSig n hI ih) ρ
      = appChain natAlgSig Γ κ (t.eval (defnModel natAlgSig n hI ih) ρ)
          (fun v => cast (congrArg (RType.interp (FreeAlg natAlgSig)) (hpos v))
            (ρ (pos v)))
  | [], _κ, _pos, _hpos, _t => rfl
  | γ :: Γ', κ, pos, hpos, t => by
    refine (appChainVarsTm_eval ih ρ Γ' κ (fun v => pos v.succ)
      (fun v => hpos v.succ) _).trans ?_
    refine congrArg (fun z => appChain natAlgSig Γ' κ z
      (fun v => cast (congrArg (RType.interp (FreeAlg natAlgSig)) (hpos v.succ))
        (ρ (pos v.succ)))) ?_
    exact congrArg (t.eval (defnModel natAlgSig n hI ih) ρ)
      (Tm.eval_transport (defnModel natAlgSig n hI ih) ρ (hpos 0) (Tm.var (pos 0)))

/-- Currying at an append transports to the currying of the extended
environment: the transport of `curryInterp` along `RType.curried_append`
curries the source context and consumes the appended sort as the final
argument, read through `snocEnv`. -/
theorem cast_curryInterp_snoc (A : AlgSig) : (Γ : List RType) → (σ τ : RType) →
    (g : (∀ k : Fin (Γ ++ [σ]).length,
        RType.interp (FreeAlg A) ((Γ ++ [σ]).get k)) → RType.interp (FreeAlg A) τ) →
    cast (congrArg (RType.interp (FreeAlg A)) (RType.curried_append Γ [σ] τ))
        (curryInterp A (Γ ++ [σ]) τ g)
      = curryInterp A Γ (RType.arrow σ τ) (fun ρ x => g (snocEnv Γ σ ρ x))
  | [], σ, τ, g =>
    eq_of_heq ((cast_heq _ _).trans (heq_of_eq (funext (fun _x => rfl))))
  | γ :: Γ', σ, τ, g => by
    funext a
    refine (interp_arrow_cast_apply (C := FreeAlg A)
      (RType.curried_append Γ' [σ] τ)
      (curryInterp A ((γ :: Γ') ++ [σ]) τ g) a).trans ?_
    exact cast_curryInterp_snoc A Γ' σ τ (fun ρ' => g (Fin.cons a ρ'))

/-- The context and result sort of the identifier a simultaneous `mrec` step
references: the simultaneous auxiliary at the step context extended by the
selector. -/
def simulStepHoleIdx (params : List RType) (τ : RType) (i : Bool) :
    Fin 1 → List RType × RType :=
  Function.const _
    (params ++ List.replicate (natAlgSig.ar i) (RType.arrow RType.o τ) ++ [RType.o], τ)

/-- The defining term of a simultaneous `mrec` step at constructor `i`: the
curried combinator form of the simultaneous auxiliary (a value at the curried
sort of the selector-extended context), applied through the application former
to every variable of the step context, leaving the selector abstracted — a
value at `o → τ`. The `ramExpStep` curried-hole idiom at a symbolic context. -/
def simulStepBody (params : List RType) (τ : RType) (i : Bool) :
    Tm (defnSig natAlgSig 1 (simulStepHoleIdx params τ i))
      (params ++ List.replicate (natAlgSig.ar i) (RType.arrow RType.o τ))
      (RType.arrow RType.o τ) :=
  appChainVarsTm (params ++ List.replicate (natAlgSig.ar i) (RType.arrow RType.o τ))
    (RType.arrow RType.o τ) (fun v => v) (fun _v => rfl)
    (Tm.reind
      (RType.curried_append
        (params ++ List.replicate (natAlgSig.ar i) (RType.arrow RType.o τ))
        [RType.o] τ)
      (Tm.op (sig := defnSig natAlgSig 1 (simulStepHoleIdx params τ i))
        (Sum.inr (0 : Fin 1)) finZeroElim))

/-- The `mrec` step of the simultaneous recurrence at constructor `i`: the
explicit definition whose body is `simulStepBody`, referencing the simultaneous
auxiliary through its curried hole. -/
def simulStep {m : Nat} (hm : 0 < m) (params : List RType) (τ : RType)
    (steps : SimulSteps m params τ) (i : Bool) :
    RIdent natAlgSig
      (params ++ List.replicate (natAlgSig.ar i) (RType.arrow RType.o τ))
      (RType.arrow RType.o τ) :=
  RIdent.defn ⟨1, simulStepHoleIdx params τ i, simulStepBody params τ i⟩
    (fun _h => simulAux hm params τ steps i)

/-- The `mrec` step denotes, at selector `u`, the simultaneous auxiliary at the
step environment extended by `u`: the coherence of the curried-hole body with
the auxiliary's saturated denotation, by `appChainVarsTm_eval`,
`cast_curryInterp_snoc`, and `appChain_curryInterp`. -/
theorem simulStep_interp {m : Nat} (hm : 0 < m) (params : List RType) (τ : RType)
    (steps : SimulSteps m params τ) (i : Bool)
    (ρ : ∀ v : Fin (params ++ List.replicate (natAlgSig.ar i)
        (RType.arrow RType.o τ) : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig)
        ((params ++ List.replicate (natAlgSig.ar i) (RType.arrow RType.o τ)
          : Ctx RType).get v))
    (u : FreeAlg natAlgSig) :
    (simulStep hm params τ steps i).interp ρ u
      = (simulAux hm params τ steps i).interp
          (snocEnv (params ++ List.replicate (natAlgSig.ar i) (RType.arrow RType.o τ))
            RType.o ρ u) := by
  have h1 := @appChainVarsTm_eval 1 (simulStepHoleIdx params τ i)
    (fun _h => (simulAux hm params τ steps i).interp)
    (params ++ List.replicate (natAlgSig.ar i) (RType.arrow RType.o τ)) ρ
    (params ++ List.replicate (natAlgSig.ar i) (RType.arrow RType.o τ))
    (RType.arrow RType.o τ) (fun v => v) (fun _v => rfl)
    (Tm.reind
      (RType.curried_append
        (params ++ List.replicate (natAlgSig.ar i) (RType.arrow RType.o τ))
        [RType.o] τ)
      (Tm.op (sig := defnSig natAlgSig 1 (simulStepHoleIdx params τ i))
        (Sum.inr (0 : Fin 1)) finZeroElim))
  have h2 : (Tm.reind
        (RType.curried_append
          (params ++ List.replicate (natAlgSig.ar i) (RType.arrow RType.o τ))
          [RType.o] τ)
        (Tm.op (sig := defnSig natAlgSig 1 (simulStepHoleIdx params τ i))
          (Sum.inr (0 : Fin 1)) finZeroElim)).eval
        (defnModel natAlgSig 1 (simulStepHoleIdx params τ i)
          (fun _h => (simulAux hm params τ steps i).interp)) ρ
      = curryInterp natAlgSig
          (params ++ List.replicate (natAlgSig.ar i) (RType.arrow RType.o τ))
          (RType.arrow RType.o τ)
          (fun ρ' x => (simulAux hm params τ steps i).interp
            (snocEnv (params ++ List.replicate (natAlgSig.ar i)
              (RType.arrow RType.o τ)) RType.o ρ' x)) :=
    (Tm.eval_transport (defnModel natAlgSig 1 (simulStepHoleIdx params τ i)
        (fun _h => (simulAux hm params τ steps i).interp)) ρ _ _).trans
      (cast_curryInterp_snoc natAlgSig
        (params ++ List.replicate (natAlgSig.ar i) (RType.arrow RType.o τ))
        RType.o τ (simulAux hm params τ steps i).interp)
  refine (congrFun h1 u).trans ?_
  refine (congrFun (congrArg (fun z => appChain natAlgSig
      (params ++ List.replicate (natAlgSig.ar i) (RType.arrow RType.o τ))
      (RType.arrow RType.o τ) z ρ) h2) u).trans ?_
  refine (congrFun (appChain_curryInterp natAlgSig
    (params ++ List.replicate (natAlgSig.ar i) (RType.arrow RType.o τ))
    (RType.arrow RType.o τ) _ _) u).trans ?_
  rfl

/-- Leivant III Lemma 2's single function-valued recurrence realizing the
simultaneous family (section 2.6, eqs. (6)-(7), p. 217-218 incl. footnote 6,
DOI `10.1016/S0168-0072(98)00040-2`): the ramified monotonic recurrence in type
`o → τ` — recursive results carry `o → τ`, count argument at `Ω (o → τ)` —
whose step at constructor `i` builds, as the value at selector `u`,
`choose(u, step₁ᵢ …, step_mᵢ)`. In the glossary vocabulary, eq. (7) reduces
the simultaneous family (eq. (6)) to the plain recurrence

`f-hat (parameters, cᵢ (subterms), u) = choose (u, g-hat₁ᵢ, …, g-hat_mᵢ)`,

where `g-hat_jᵢ` is the `j`-th component's step function applied to the
parameters and the recursive calls of `f-hat` at instantiated selector values
`b₁ … b_m`, and each component is recovered as `f_j = f-hat (b_j)` (footnote 6,
p. 218, accompanies the display; its exact wording was not verifiable at
execution time and the citation is by locator). Presentation adaptation (spec
s1.2 kind), recorded per the sub-plan's standing decision 5: a step of
`RIdent.mrec` sees only its own identifier's recursive results at its own
parameters, so eq. (7)'s selector-instantiated recursive calls `f-hat (…, b_j)`
are inexpressible directly; the recurrence is instead realized function-valued
— the recursive results carry the whole selector-to-value function at
`o → τ`, the count argument sits at `Ω (o → τ)` rather than the paper's
`Ω τ`, and the step functions extract components by applying the
function-valued recursive results to selector numerals. The same monotonic
reading drops eq. (6)'s subterm arguments from the clause data
(`SimulSteps`). -/
def simulIdent {m : Nat} (hm : 0 < m) (params : List RType) (τ : RType)
    (steps : SimulSteps m params τ) :
    RIdent natAlgSig (params ++ [RType.omega (RType.arrow RType.o τ)])
      (RType.arrow RType.o τ) :=
  RIdent.mrec params (RType.arrow RType.o τ) (fun i => simulStep hm params τ steps i)

/-- The carrier-level reference value of the function-valued recurrence after
`n` steps: the selector applied to the input and the per-component step
denotations, the recursive results after `n` steps supplied to the count-`n + 1`
steps as this function itself. The function-valued counterpart of `simulSol`,
needed because a step identifier reads its recursive results as whole `o → τ`
values. Novel packaging. -/
def simulSolFun {m : Nat} (hm : 0 < m) (params : List RType) (τ : RType)
    (steps : SimulSteps m params τ)
    (pe : ∀ v : Fin params.length, RType.interp (FreeAlg natAlgSig) (params.get v)) :
    Nat → FreeAlg natAlgSig → RType.interp (FreeAlg natAlgSig) τ
  | 0, u => (chooseIdent (m - 1) τ).interp (chooseEnv (m - 1) τ u
      (fun k => (steps (Fin.cast (Nat.succ_pred_eq_of_pos hm) k) false).interp
        (simulStepEnv params τ false pe finZeroElim u)))
  | n + 1, u => (chooseIdent (m - 1) τ).interp (chooseEnv (m - 1) τ u
      (fun k => (steps (Fin.cast (Nat.succ_pred_eq_of_pos hm) k) true).interp
        (simulStepEnv params τ true pe
          (fun _v => simulSolFun hm params τ steps pe n) u)))

/-- The carrier-level reference solution of the simultaneous family, mirroring
`KMor1.simrecVec` (`GebLean/LawvereKSimInterp.lean`) over the ramified sorts:
the componentwise value after `n` steps, by recursion on `n` — component `j` at
count `0` is the base step at selector numeral `j`, and at count `n + 1` the
step at constructor `true` reading the function-valued solution after `n` steps
(`simulSolFun`) as its recursive result. Novel packaging. -/
def simulSol {m : Nat} (params : List RType) (τ : RType)
    (steps : SimulSteps m params τ)
    (pe : ∀ v : Fin params.length, RType.interp (FreeAlg natAlgSig) (params.get v)) :
    Nat → Fin m → RType.interp (FreeAlg natAlgSig) τ
  | 0, j => (steps j false).interp
      (simulStepEnv params τ false pe finZeroElim (natToFreeAlg j.val))
  | n + 1, j => (steps j true).interp
      (simulStepEnv params τ true pe
        (fun _v => simulSolFun j.pos params τ steps pe n) (natToFreeAlg j.val))

/-- The function-valued reference solution at a selector numeral `j < m` is the
`j`-th componentwise value: `chooseIdent_interp` picks entry `j`. -/
theorem simulSolFun_numeral {m : Nat} (hm : 0 < m) (params : List RType) (τ : RType)
    (steps : SimulSteps m params τ)
    (pe : ∀ v : Fin params.length, RType.interp (FreeAlg natAlgSig) (params.get v))
    (n : Nat) (j : Fin m) :
    simulSolFun hm params τ steps pe n (natToFreeAlg j.val)
      = simulSol params τ steps pe n j := by
  have hj : j.val < m - 1 + 1 := by have := j.isLt; omega
  cases n with
  | zero => exact chooseIdent_interp (m - 1) τ _ _ ⟨j.val, hj⟩ rfl
  | succ n' => exact chooseIdent_interp (m - 1) τ _ _ ⟨j.val, hj⟩ rfl

/-- The recurrence underlying `simulIdent`, read at the reference solution: on
a parameter environment `pe` and a recurrence argument `s`, the recursion
denotes the function-valued reference solution after `count s` steps. Proved by
structural induction on `s` via `PolyFix.ind` (decision 8); each constructor
case reduces the step through `simulStep_interp` and `simulAux_interp`. -/
theorem simulRecurse_eq {m : Nat} (hm : 0 < m) (params : List RType) (τ : RType)
    (steps : SimulSteps m params τ)
    (pe : ∀ v : Fin params.length, RType.interp (FreeAlg natAlgSig) (params.get v))
    (s : FreeAlg natAlgSig) :
    FreeAlg.recurse (A := natAlgSig) (P := Unit)
        (fun i _ _sub phi => (simulStep hm params τ steps i).interp
          (childEnv params (RType.arrow RType.o τ) (natAlgSig.ar i) pe phi)) () s
      = simulSolFun hm params τ steps pe (freeAlgToNat s) := by
  refine PolyFix.ind (P := natAlgSig.polyEndo)
    (motive := fun {_} s =>
      FreeAlg.recurse (A := natAlgSig) (P := Unit)
          (fun i _ _sub phi => (simulStep hm params τ steps i).interp
            (childEnv params (RType.arrow RType.o τ) (natAlgSig.ar i) pe phi)) () s
        = simulSolFun hm params τ steps pe (freeAlgToNat s))
    (fun b children ihc => ?_) s
  cases b with
  | false =>
    funext u
    refine (simulStep_interp hm params τ steps false _ u).trans ?_
    refine (simulAux_interp hm params τ steps false pe _ u).trans ?_
    exact congrArg
      (fun p => (chooseIdent (m - 1) τ).interp (chooseEnv (m - 1) τ u
        (fun k => (steps (Fin.cast (Nat.succ_pred_eq_of_pos hm) k) false).interp
          (simulStepEnv params τ false pe p u))))
      (funext (fun v => v.elim0))
  | true =>
    funext u
    have hcount : freeAlgToNat (PolyFix.mk PUnit.unit true children)
        = freeAlgToNat (children ⟨0, by decide⟩) + 1 := rfl
    rw [hcount]
    refine (simulStep_interp hm params τ steps true _ u).trans ?_
    refine (simulAux_interp hm params τ steps true pe _ u).trans ?_
    refine congrArg
      (fun p => (chooseIdent (m - 1) τ).interp (chooseEnv (m - 1) τ u
        (fun k => (steps (Fin.cast (Nat.succ_pred_eq_of_pos hm) k) true).interp
          (simulStepEnv params τ true pe p u))))
      (funext (fun v => ?_))
    induction v using Fin.cases with
    | zero => exact ihc ⟨0, by decide⟩
    | succ v' => exact v'.elim0

/-- The environment at the simultaneous recurrence's context
`params ++ [Ω (o → τ)]`: the parameters extended by the count value. -/
def simulEnv (params : List RType) (τ : RType)
    (pe : ∀ v : Fin params.length, RType.interp (FreeAlg natAlgSig) (params.get v))
    (c : FreeAlg natAlgSig) :
    ∀ k : Fin (params ++ [RType.omega (RType.arrow RType.o τ)] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig)
        ((params ++ [RType.omega (RType.arrow RType.o τ)] : Ctx RType).get k) :=
  snocEnv params (RType.omega (RType.arrow RType.o τ)) pe c

/-- The function-valued recurrence denotes the function-valued reference
solution after `count c` steps. -/
theorem simulIdent_interp {m : Nat} (hm : 0 < m) (params : List RType) (τ : RType)
    (steps : SimulSteps m params τ)
    (pe : ∀ v : Fin params.length, RType.interp (FreeAlg natAlgSig) (params.get v))
    (c : FreeAlg natAlgSig) :
    (simulIdent hm params τ steps).interp (simulEnv params τ pe c)
      = simulSolFun hm params τ steps pe (freeAlgToNat c) := by
  refine Eq.trans (b := simulSolFun hm params τ steps
    (envHead params (RType.omega (RType.arrow RType.o τ)) (simulEnv params τ pe c))
    (freeAlgToNat (envLast params (RType.omega (RType.arrow RType.o τ))
      (simulEnv params τ pe c))))
    (simulRecurse_eq hm params τ steps
      (envHead params (RType.omega (RType.arrow RType.o τ)) (simulEnv params τ pe c))
      (envLast params (RType.omega (RType.arrow RType.o τ)) (simulEnv params τ pe c)))
    ?_
  rw [show envHead params (RType.omega (RType.arrow RType.o τ))
        (simulEnv params τ pe c) = pe from envHead_snocEnv _ _ _ _,
      show envLast params (RType.omega (RType.arrow RType.o τ))
        (simulEnv params τ pe c) = c from envLast_snocEnv _ _ _ _]

/-- The numeral `k` as a term over a definition signature: the `k`-fold
`tmSucc` of `tmZero`. -/
def tmNat {n : Nat} {h : Fin n → List RType × RType} {Γ : Ctx RType} :
    Nat → Tm (defnSig natAlgSig n h) Γ RType.o
  | 0 => tmZero
  | k + 1 => tmSucc (tmNat k)

/-- A numeral term evaluates to the numeral carrier value in any hole model. -/
theorem tmNat_eval {n : Nat} {hI : Fin n → List RType × RType}
    (ih : ∀ j : Fin n,
      (∀ v : Fin (hI j).1.length, RType.interp (FreeAlg natAlgSig) ((hI j).1.get v)) →
        RType.interp (FreeAlg natAlgSig) (hI j).2)
    {Γ : Ctx RType} (ρ : (defnModel natAlgSig n hI ih).Env Γ) : (k : Nat) →
    (tmNat k).eval (defnModel natAlgSig n hI ih) ρ = natToFreeAlg k
  | 0 => congrArg (FreeAlg.mk (A := natAlgSig) false) (funext (fun v => v.elim0))
  | k + 1 => by
    refine congrArg (FreeAlg.mk (A := natAlgSig) true) (funext (fun v => ?_))
    induction v using Fin.cases with
    | zero => exact tmNat_eval ih ρ k
    | succ v' => exact v'.elim0

/-- The context and result sort of the identifier a component projection
references: the simultaneous recurrence itself, a value at `o → τ` on the
projection's own context. -/
def simulProjHoleIdx (params : List RType) (τ : RType) : Fin 1 → List RType × RType :=
  Function.const _
    (params ++ [RType.omega (RType.arrow RType.o τ)], RType.arrow RType.o τ)

/-- The `j`-th component of the simultaneous family (Leivant III Lemma 2,
section 2.6): the explicit definition applying the function-valued recurrence
`simulIdent` — referenced through a saturated hole at the projection's own
context — to the selector numeral `j`; the paper's `f_j = f-hat (b_j)` with
`b_j` the selector numeral of component `j`. The projections use selector
numerals `j < m`, so the selector's out-of-range fall-through is unreachable
from `simulProj`. See `simulIdent` for the recorded presentation adaptation. -/
def simulProj {m : Nat} (hm : 0 < m) (params : List RType) (τ : RType)
    (steps : SimulSteps m params τ) (j : Fin m) :
    RIdent natAlgSig (params ++ [RType.omega (RType.arrow RType.o τ)]) τ :=
  RIdent.defn ⟨1, simulProjHoleIdx params τ,
    Tm.op (sig := defnSig natAlgSig 1 (simulProjHoleIdx params τ))
      (Sum.inl (Sum.inl (Sum.inr (RType.o, τ))))
      (Fin.cons
        (Tm.op (sig := defnSig natAlgSig 1 (simulProjHoleIdx params τ))
          (Sum.inl (Sum.inr (0 : Fin 1))) (fun v => Tm.var v))
        (Fin.cons (tmNat j.val) finZeroElim))⟩
    (fun _h => simulIdent hm params τ steps)

/-- Leivant III Lemma 2's interpretation lemma: the projected components
satisfy the simultaneous defining equations — `simulProj j` at count numeral
`n` denotes the componentwise reference solution `simulSol … n j` (the shape of
`KMor1.simrecVec`, restated over the ramified sorts). -/
theorem simulProj_interp {m : Nat} (hm : 0 < m) (params : List RType) (τ : RType)
    (steps : SimulSteps m params τ)
    (pe : ∀ v : Fin params.length, RType.interp (FreeAlg natAlgSig) (params.get v))
    (n : Nat) (j : Fin m) :
    (simulProj hm params τ steps j).interp (simulEnv params τ pe (natToFreeAlg n))
      = simulSol params τ steps pe n j := by
  have h1 : (simulProj hm params τ steps j).interp (simulEnv params τ pe (natToFreeAlg n))
      = (simulIdent hm params τ steps).interp (simulEnv params τ pe (natToFreeAlg n))
          (natToFreeAlg j.val) :=
    congrArg
      ((simulIdent hm params τ steps).interp (simulEnv params τ pe (natToFreeAlg n)))
      (@tmNat_eval 1 (simulProjHoleIdx params τ)
        (fun _h => (simulIdent hm params τ steps).interp)
        (params ++ [RType.omega (RType.arrow RType.o τ)])
        (simulEnv params τ pe (natToFreeAlg n)) j.val)
  rw [h1, simulIdent_interp hm params τ steps pe (natToFreeAlg n),
    freeAlgToNat_natToFreeAlg]
  exact simulSolFun_numeral hm params τ steps pe n j

end GebLean.Ramified
