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

-- The denotation of the flat-recurrence sample agrees across the bridge.
example (ρ' : ∀ i : Fin ([] ++ [RType'.o]).length,
      RType'.interp (FreeAlg' A) (([] ++ [RType'.o]).get i)) :
    (identSliceEquiv pred').interp (envSlice A ([] ++ [RType'.o]) ρ')
      = carrierSliceEquiv A RType'.o (pred'.interp ρ') :=
  identSliceEquiv_interp pred' ρ'

-- The currying of a denotation agrees across the bridge at the empty context.
example (g' : (∀ i : Fin ([] : List RType').length,
      RType'.interp (FreeAlg' A) (([] : List RType').get i)) → RType'.interp (FreeAlg' A) RType'.o)
    (g : (∀ i : Fin (List.map rTypeSliceEquiv ([] : List RType')).length,
        RType.interp (FreeAlg A) ((List.map rTypeSliceEquiv ([] : List RType')).get i)) →
      RType.interp (FreeAlg A) (rTypeSliceEquiv RType'.o))
    (hg : ∀ ρ', g (envSlice A [] ρ') = carrierSliceEquiv A RType'.o (g' ρ')) :
    curryInterp A (List.map rTypeSliceEquiv []) (rTypeSliceEquiv RType'.o) g
      = cast (congrArg (RType.interp (FreeAlg A)) (rTypeSliceEquiv_curried [] RType'.o))
          (carrierSliceEquiv A (RType'.curried [] RType'.o) (curryInterp' A [] RType'.o g')) :=
  curryInterp'_agree A [] RType'.o g' g hg

end GebLeanTests.Ramified.Polynomial.IdentEquivTest
