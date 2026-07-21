import GebLean
import GebLean.Ramified.Polynomial.Ident

/-!
# Tests for the primed schema-identifier data on the slice `W`-type

Executable checks over the `1 + X` word algebra `natAlgSig` (a nullary
`zero` and a unary `succ`). A flat recurrence (`RIdent'.frec`) is built with
`RIdent'.defn`-formed clauses (each with no holes): the zero clause returns
the base object `o`, and the successor clause returns the subterm variable.
The checks exercise the `val_defn` / `val_frec` characterization lemmas —
recovering each former's shape component through `SlicePFunctor.W.dest` —
and the index fiber property recorded in each identifier's `.2` witness.
-/

namespace GebLeanTests.Ramified.Polynomial.IdentTest

open GebLean.Ramified GebLean.Ramified.Polynomial GebLean.PolyBridge

/-- The `1 + X` word algebra: `false` is the nullary constructor, `true` the
unary one. -/
abbrev A : AlgSig := natAlgSig

/-- The base object sort `o` as an object-sort witness on the slice
`W`-type. -/
def oObj' : { s : RType' // RType'.IsObj s } :=
  ⟨RType'.o, Or.inl (RType'.shape_mk RTypeShape.o Fin.elim0)⟩

/-- The zero term over a definition signature with no holes. -/
def tmZero' {n : Nat} {h : Fin n → List RType' × RType'} {Γ' : Ctx RType'} :
    Tm' (defnSig' A n h) Γ' RType'.o :=
  Tm'.op (sig := defnSig' A n h) (Sum.inl (Sum.inl (Sum.inl (oObj', false)))) finZeroElim

/-- The explicit definition returning `0` (context `[]`, no holes). -/
def idZero' : RIdent' A [] RType'.o :=
  RIdent'.defn ⟨0, finZeroElim, tmZero'⟩ finZeroElim

/-- The explicit definition returning its sole argument (context `[o]`, no
holes): the successor clause of the predecessor recurrence. -/
def idVar' : RIdent' A [RType'.o] RType'.o :=
  RIdent'.defn ⟨0, finZeroElim, Tm'.var 0⟩ finZeroElim

/-- The predecessor recurrence clauses: `idZero'` at `zero`, `idVar'` at
`succ`. -/
def predClauses : (i : A.B) → RIdent' A ([] ++ List.replicate (A.ar i) RType'.o) RType'.o :=
  fun i => match i with | false => idZero' | true => idVar'

/-- The predecessor as a flat recurrence: `idZero'` at `zero`, `idVar'` at
`succ`. -/
def pred' : RIdent' A [RType'.o] RType'.o :=
  RIdent'.frec [] RType'.o predClauses

-- The index fiber: `idZero'` sits over `([], o)`.
example : (toSlice (identEndo' A)).wIndex idZero'.1 = ([], RType'.o) :=
  idZero'.2

-- The index fiber: `idVar'` sits over `([o], o)`.
example : (toSlice (identEndo' A)).wIndex idVar'.1 = ([RType'.o], RType'.o) :=
  idVar'.2

-- The index fiber: `pred'` sits over `([o], o)`.
example : (toSlice (identEndo' A)).wIndex pred'.1 = ([RType'.o], RType'.o) :=
  pred'.2

-- The `val_defn` characterization lemma recovers `idZero'`'s shape (a
-- `defn'` node) through `SlicePFunctor.W.dest`.
example :
    (SlicePFunctor.W.dest idZero'.1).1.1 = ⟨([], RType'.o), Sum.inl ⟨0, finZeroElim, tmZero'⟩⟩ := by
  unfold idZero'
  rw [RIdent'.val_defn, SlicePFunctor.W.dest_mk]

-- The `val_frec` characterization lemma recovers `pred'`'s shape (a `frec'`
-- node) through `SlicePFunctor.W.dest`.
example :
    (SlicePFunctor.W.dest pred'.1).1.1 =
      ⟨([RType'.o], RType'.o),
        Sum.inr (Sum.inr (⟨([] : List RType'), rfl⟩ : FrecShape' A _ _))⟩ := by
  unfold pred'
  rw [RIdent'.val_frec, SlicePFunctor.W.dest_mk]
  rfl

-- The variable-projection definition denotes its argument (through
-- `RIdent'.interp_defn` and `Tm'.eval_var`, folding the body against
-- `defnModel'`): the value of `idVar'` on an environment `ρ` is `ρ 0`, the sole
-- argument. This is the successor clause of the predecessor recurrence.
example (ρ : ∀ i : Fin [RType'.o].length, RType'.interp (FreeAlg' A) ([RType'.o].get i)) :
    idVar'.interp ρ = ρ 0 := by
  unfold idVar'
  rw [RIdent'.interp_defn]
  exact Tm'.eval_var _ _ _

-- The flat recurrence selects its successor clause (through
-- `RIdent'.interp_frec` and `FreeAlg'.recurse_mk`): on an environment whose
-- recurrence argument is a successor `succ sub`, `pred'` reduces to the
-- `true`-clause identifier `idVar'` on the child environment carrying the
-- subterm.
example
    (ρ : ∀ i : Fin ([] ++ [RType'.o]).length,
      RType'.interp (FreeAlg' A) (([] ++ [RType'.o]).get i))
    (sub : Fin (A.ar true) → FreeAlg' A)
    (hρ : envLast' [] RType'.o ρ = FreeAlg'.mk true sub) :
    (RIdent'.frec [] RType'.o predClauses).interp ρ =
      idVar'.interp (childEnv' [] RType'.o (A.ar true) (envHead' [] RType'.o ρ) sub) := by
  rw [RIdent'.interp_frec [] RType'.o predClauses]
  beta_reduce
  rw [hρ, FreeAlg'.recurse_mk]
  rfl

end GebLeanTests.Ramified.Polynomial.IdentTest
