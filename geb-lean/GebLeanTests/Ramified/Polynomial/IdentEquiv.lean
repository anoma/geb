import GebLean
import GebLean.Ramified.Polynomial.IdentEquiv

/-!
# Tests for the identifier bridge equivalence

Executable checks over the `1 + X` word algebra `natAlgSig` that the bridge
equivalence `identSliceEquiv` carries the Task C.10 sample identifiers
(`idZero'`, `idVar'`, `pred'`) and the monotonic recurrence `mrecSample'` to
the legacy schema formers of the translated data, through the
former-naturality lemmas `identSliceEquiv_defn`, `identSliceEquiv_mrec`, and
`identSliceEquiv_frec`, and that it round-trips with its inverse.
-/

namespace GebLeanTests.Ramified.Polynomial.IdentEquivTest

open GebLean.Ramified GebLean.Ramified.Polynomial GebLean.PolyBridge

/-- The `1 + X` word algebra. -/
abbrev A : AlgSig := natAlgSig

/-- The base object sort `o` as an object-sort witness on the slice `W`-type. -/
def oObj' : { s : RType' // RType'.IsObj s } :=
  ⟨RType'.o, Or.inl (RType'.shape_mk RTypeShape.o Fin.elim0)⟩

/-- The zero term over a definition signature with no holes. -/
def tmZero' {n : Nat} {h : Fin n → List RType' × RType'} {Γ' : Ctx RType'} :
    Tm' (defnSig' A n h) Γ' RType'.o :=
  Tm'.op (sig := defnSig' A n h) (Sum.inl (Sum.inl (Sum.inl (oObj', false)))) finZeroElim

/-- The explicit definition returning `0`. -/
def idZero' : RIdent' A [] RType'.o :=
  RIdent'.defn ⟨0, finZeroElim, tmZero'⟩ finZeroElim

/-- The explicit definition returning its sole argument. -/
def idVar' : RIdent' A [RType'.o] RType'.o :=
  RIdent'.defn ⟨0, finZeroElim, Tm'.var 0⟩ finZeroElim

/-- The predecessor recurrence clauses. -/
def predClauses : (i : A.B) → RIdent' A ([] ++ List.replicate (A.ar i) RType'.o) RType'.o :=
  fun i => match i with | false => idZero' | true => idVar'

/-- The predecessor as a flat recurrence. -/
def pred' : RIdent' A [RType'.o] RType'.o :=
  RIdent'.frec [] RType'.o predClauses

/-- A monotonic recurrence sample: the flat-recurrence clauses reused as
steps at `τ' = o`. -/
def mrecSample' : RIdent' A [RType'.omega RType'.o] RType'.o :=
  RIdent'.mrec [] RType'.o predClauses

-- The image of `idZero'` is the legacy explicit definition of the translated
-- data, with the (empty) children carried through the equivalence.
example :
    identSliceEquiv idZero' =
      RIdent.defn (defnShapeEquiv A [] RType'.o ⟨0, finZeroElim, tmZero'⟩) finZeroElim := by
  unfold idZero'
  rw [identSliceEquiv_defn]
  congr 1
  funext j
  exact j.elim0

-- Round trips through the inverse.
example : identSliceEquiv.symm (identSliceEquiv idZero') = idZero' :=
  Equiv.symm_apply_apply _ _

example : identSliceEquiv.symm (identSliceEquiv pred') = pred' :=
  Equiv.symm_apply_apply _ _

example : identSliceEquiv.symm (identSliceEquiv mrecSample') = mrecSample' :=
  Equiv.symm_apply_apply _ _

-- The image of the monotonic-recurrence sample is the context-transported
-- legacy monotonic recurrence of the translated data.
example :
    identSliceEquiv mrecSample'
      = RIdent.reindCtx
          (by simp)
          (RIdent.mrec (List.map rTypeSliceEquiv []) (rTypeSliceEquiv RType'.o)
            (fun i => RIdent.reindCtx (by simp)
              (identSliceEquiv (predClauses i)))) :=
  identSliceEquiv_mrec [] RType'.o predClauses _ _

-- The image of `pred'` is the context-transported legacy flat recurrence of
-- the translated data.
example :
    identSliceEquiv pred'
      = RIdent.reindCtx
          (by simp)
          (RIdent.frec (List.map rTypeSliceEquiv []) (rTypeSliceEquiv RType'.o)
            (fun i => RIdent.reindCtx (by simp)
              (identSliceEquiv (predClauses i)))) :=
  identSliceEquiv_frec [] RType'.o predClauses _ _

-- The denotation of the projection identifier agrees across the bridge: the
-- legacy denotation of the translated identifier, at the pushed-forward
-- environment, is the carrier-bridge image of the primed denotation, which
-- reads the environment at position `0`.
example (ρ' : ∀ i : Fin [RType'.o].length, RType'.interp (FreeAlg' A) ([RType'.o].get i)) :
    (identSliceEquiv idVar').interp (envSlice A [RType'.o] ρ')
      = carrierSliceEquiv A RType'.o (ρ' 0) := by
  rw [identSliceEquiv_interp]
  refine congrArg (carrierSliceEquiv A RType'.o) ?_
  unfold idVar'
  rw [RIdent'.interp_defn]
  exact Tm'.eval_var _ _ _

/-- A one-element environment at the predecessor recurrence-argument sort `o`,
mirroring the legacy `envPred` (`GebLeanTests/Ramified/HigherOrder.lean`). -/
def envPred' (n : Nat) :
    ∀ i : Fin ([] ++ [RType'.o]).length,
      RType'.interp (FreeAlg' A) (([] ++ [RType'.o]).get i) :=
  Fin.cons (natToFreeAlg' n) finZeroElim

-- The denotation of the flat-recurrence sample agrees across the bridge,
-- evaluated through the computation rules of both sides at a concrete input:
-- `pred' 1 = 0`.
example :
    (identSliceEquiv pred').interp (envSlice A ([] ++ [RType'.o]) (envPred' 1))
      = carrierSliceEquiv A RType'.o (natToFreeAlg' 0) := by
  have hp : pred'.interp (envPred' 1) = natToFreeAlg' 0 := by
    change (RIdent'.frec [] RType'.o predClauses).interp (envPred' 1) = natToFreeAlg' 0
    rw [RIdent'.interp_frec]
    change FreeAlg'.recurse
        (fun i _ sub _phi => (predClauses i).interp
          (childEnv' [] RType'.o (A.ar i) (envHead' [] RType'.o (envPred' 1)) fun j => sub j))
        () (FreeAlg'.mk true (fun _ => natToFreeAlg' 0)) = natToFreeAlg' 0
    rw [FreeAlg'.recurse_mk]
    change idVar'.interp
        (childEnv' [] RType'.o (A.ar true) (envHead' [] RType'.o (envPred' 1))
          fun _ => natToFreeAlg' 0) = natToFreeAlg' 0
    unfold idVar'
    rw [RIdent'.interp_defn]
    exact Tm'.eval_var _ _ _
  exact (identSliceEquiv_interp pred' (envPred' 1)).trans
    (congrArg (carrierSliceEquiv A RType'.o) hp)

-- The same fact, computed independently through the legacy computation rules
-- (`identSliceEquiv_frec`, `RIdent.interp_frec`, `FreeAlg.recurse_mk`) down to
-- the `idVar'` recursive step, rather than through the primed side: a second,
-- disjoint route to the same concrete value.
example :
    (identSliceEquiv pred').interp (envSlice A ([] ++ [RType'.o]) (envPred' 1))
      = carrierSliceEquiv A RType'.o (natToFreeAlg' 0) := by
  have hctx : List.map rTypeSliceEquiv ([] : List RType') ++ [RType.o]
      = List.map rTypeSliceEquiv (([] : List RType') ++ [RType'.o]) := by simp
  have hstep : ∀ i : A.B,
      List.map rTypeSliceEquiv (([] : List RType') ++ List.replicate (A.ar i) RType'.o)
        = List.map rTypeSliceEquiv ([] : List RType') ++ List.replicate (A.ar i) RType.o := by
    intro i; simp
  refine Eq.trans (congrArg (fun z => z.interp (envSlice A ([] ++ [RType'.o]) (envPred' 1)))
    (identSliceEquiv_frec [] RType'.o predClauses hctx hstep)) ?_
  refine Eq.trans (RIdent.interp_reindCtx hctx _ _) ?_
  refine Eq.trans (congrFun (RIdent.interp_frec (List.map rTypeSliceEquiv ([] : List RType'))
    (rTypeSliceEquiv RType'.o)
    (fun i => RIdent.reindCtx (hstep i) (identSliceEquiv (predClauses i)))) _) ?_
  have hla := envLast_agree ([] : List RType') RType'.o RType.o isObj_o' (Or.inl rfl)
    rTypeSliceEquiv_o.symm (envPred' 1)
    (envCtxCast hctx.symm (envSlice A ([] ++ [RType'.o]) (envPred' 1)))
    (envAgree_envCtxCast hctx.symm (envAgree_envSlice _ (envPred' 1)))
  have hll : envLast (List.map rTypeSliceEquiv ([] : List RType')) RType.o
      (envCtxCast hctx.symm (envSlice A ([] ++ [RType'.o]) (envPred' 1))) = natToFreeAlg 1 :=
    hla.trans (congrArg (freeAlgSliceEquiv A)
      (rfl : cast (RType'.interp_isObj (FreeAlg' A) isObj_o') (envLast' [] RType'.o (envPred' 1))
        = natToFreeAlg' 1)) |>.trans (freeAlgSliceEquiv_natToFreeAlg' 1)
  simp only [hll]
  change FreeAlg.recurse
      (fun i _ sub _phi => (RIdent.reindCtx (hstep i) (identSliceEquiv (predClauses i))).interp
        (childEnv (List.map rTypeSliceEquiv ([] : List RType')) RType.o (A.ar i)
          (envHead (List.map rTypeSliceEquiv ([] : List RType')) RType.o
            (envCtxCast hctx.symm (envSlice A ([] ++ [RType'.o]) (envPred' 1))))
          fun j => sub j))
      () (FreeAlg.mk true (fun _ => natToFreeAlg 0))
      = carrierSliceEquiv A RType'.o (natToFreeAlg' 0)
  rw [FreeAlg.recurse_mk]
  refine Eq.trans (RIdent.interp_reindCtx (hstep true) _ _) ?_
  have hρ₁ : EnvAgree (envPred' 1)
      (envCtxCast hctx.symm (envSlice A ([] ++ [RType'.o]) (envPred' 1))) :=
    envAgree_envCtxCast hctx.symm (envAgree_envSlice _ (envPred' 1))
  have hhead := envAgree_envHead ([] : List RType') RType'.o RType.o (envPred' 1)
    (envCtxCast hctx.symm (envSlice A ([] ++ [RType'.o]) (envPred' 1))) hρ₁
  have hchild := envAgree_childEnv ([] : List RType') RType'.o RType.o (A.ar true)
    (envHead' [] RType'.o (envPred' 1))
    (envHead (List.map rTypeSliceEquiv ([] : List RType')) RType.o
      (envCtxCast hctx.symm (envSlice A ([] ++ [RType'.o]) (envPred' 1))))
    hhead (fun _ => natToFreeAlg' 0) (fun _ => natToFreeAlg 0)
    (fun _ => (heq_of_eq (freeAlgSliceEquiv_natToFreeAlg' 0).symm).trans
      ((heq_of_eq (carrierSliceEquiv_o (natToFreeAlg' 0)).symm).trans (cast_heq _ _)))
  have henv := envAgree_eq (envAgree_envCtxCast (hstep true).symm hchild)
  rw [henv]
  refine Eq.trans ?_ (identSliceEquiv_interp idVar' (Fin.cons (natToFreeAlg' 0) finZeroElim))
  refine congrArg (fun ρ => (identSliceEquiv idVar').interp (envSlice A [RType'.o] ρ)) ?_
  funext j
  fin_cases j
  rfl

/-- A one-element environment at the monotonic-recurrence argument sort `Ω o`,
mirroring `envPred'`. -/
def envMrec' (n : Nat) :
    ∀ i : Fin ([] ++ [RType'.omega RType'.o]).length,
      RType'.interp (FreeAlg' A) (([] ++ [RType'.omega RType'.o]).get i) :=
  Fin.cons (natToFreeAlg' n) finZeroElim

-- The denotation of the monotonic-recurrence sample agrees across the bridge,
-- evaluated through the computation rules of both sides at a concrete input:
-- `mrecSample' 1 = 0`. Genuinely exercises the recursive-results path: `phi 0`
-- at the `true` step is a nested `FreeAlg'.recurse` call, not the raw subterm.
set_option maxHeartbeats 1000000 in
-- two nested `change`-driven `FreeAlg'.recurse` unfoldings exceed the default
-- elaborator budget.
example :
    (identSliceEquiv mrecSample').interp (envSlice A ([] ++ [RType'.omega RType'.o]) (envMrec' 1))
      = carrierSliceEquiv A RType'.o (natToFreeAlg' 0) := by
  have hp : mrecSample'.interp (envMrec' 1) = natToFreeAlg' 0 := by
    change (RIdent'.mrec [] RType'.o predClauses).interp (envMrec' 1) = natToFreeAlg' 0
    rw [RIdent'.interp_mrec]
    change FreeAlg'.recurse
        (fun i _ _sub phi => (predClauses i).interp
          (childEnv' [] RType'.o (A.ar i) (envHead' [] (RType'.omega RType'.o) (envMrec' 1)) phi))
        () (FreeAlg'.mk true (fun _ => natToFreeAlg' 0)) = natToFreeAlg' 0
    rw [FreeAlg'.recurse_mk]
    change idVar'.interp
        (childEnv' [] RType'.o (A.ar true) (envHead' [] (RType'.omega RType'.o) (envMrec' 1))
          (fun _ => FreeAlg'.recurse
            (fun i _ _sub phi => (predClauses i).interp
              (childEnv' [] RType'.o (A.ar i) (envHead' [] (RType'.omega RType'.o) (envMrec' 1))
                phi))
            () (natToFreeAlg' 0))) = natToFreeAlg' 0
    unfold idVar'
    rw [RIdent'.interp_defn]
    refine Eq.trans (Tm'.eval_var _ _ _) ?_
    change FreeAlg'.recurse
        (fun i _ _sub phi => (predClauses i).interp
          (childEnv' [] RType'.o (A.ar i) (envHead' [] (RType'.omega RType'.o) (envMrec' 1)) phi))
        () (FreeAlg'.mk false finZeroElim) = natToFreeAlg' 0
    rw [FreeAlg'.recurse_mk]
    have step : idZero'.interp finZeroElim = natToFreeAlg' 0 := by
      unfold idZero'
      rw [RIdent'.interp_defn]
      dsimp only
      unfold tmZero'
      refine Eq.trans (Tm'.eval_op _ _ _ _) ?_
      refine congrArg (@FreeAlg'.mk A false) ?_
      funext i
      exact i.elim0
    refine Eq.trans ?_ step
    congr 1
    funext j
    exact j.elim0
  exact (identSliceEquiv_interp mrecSample' (envMrec' 1)).trans
    (congrArg (carrierSliceEquiv A RType'.o) hp)

/-- Bridge agreement of a concrete constant denotation, at the empty context:
`g'` / `g` are concrete (not hypothesized) functions and `hg` is proved (not
assumed) through `carrierSliceEquiv_o` and `freeAlgSliceEquiv_natToFreeAlg'`. -/
def natConstAgree : ∀ ρ' : ∀ i : Fin ([] : List RType').length,
      RType'.interp (FreeAlg' A) (([] : List RType').get i),
    (fun _ : ∀ i : Fin (List.map rTypeSliceEquiv ([] : List RType')).length,
        RType.interp (FreeAlg A) ((List.map rTypeSliceEquiv ([] : List RType')).get i) =>
      natToFreeAlg 1) (envSlice A [] ρ')
      = carrierSliceEquiv A RType'.o ((fun _ => natToFreeAlg' 1) ρ') :=
  fun _ => ((carrierSliceEquiv_o (natToFreeAlg' 1)).trans (freeAlgSliceEquiv_natToFreeAlg' 1)).symm

-- The currying of that constant denotation agrees across the bridge: the
-- concrete instance of `curryInterp'_agree` at `g'` / `g` / `natConstAgree`.
example :
    curryInterp A (List.map rTypeSliceEquiv ([] : List RType')) (rTypeSliceEquiv RType'.o)
        (fun _ => natToFreeAlg 1)
      = cast (congrArg (RType.interp (FreeAlg A)) (rTypeSliceEquiv_curried [] RType'.o))
          (carrierSliceEquiv A (RType'.curried [] RType'.o)
            (curryInterp' A [] RType'.o (fun _ => natToFreeAlg' 1))) :=
  curryInterp'_agree A [] RType'.o (fun _ => natToFreeAlg' 1) (fun _ => natToFreeAlg 1)
    natConstAgree

-- The two curried denotations above reduce, through `curryInterp` /
-- `curryInterp'`'s own `[]`-case computation rule (direct match unfolding),
-- to the concrete numeral both sides agree on.
example :
    curryInterp A (List.map rTypeSliceEquiv ([] : List RType')) (rTypeSliceEquiv RType'.o)
        (fun _ => natToFreeAlg 1) = natToFreeAlg 1 := rfl

example : curryInterp' A ([] : List RType') RType'.o (fun _ => natToFreeAlg' 1) = natToFreeAlg' 1 :=
  rfl

end GebLeanTests.Ramified.Polynomial.IdentEquivTest
