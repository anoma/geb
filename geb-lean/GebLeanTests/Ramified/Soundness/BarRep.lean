import GebLean.Ramified.Soundness.BarRep

/-!
# Tests for the Berarducci-Böhm representation

The bare names `Tm`, `Tm.op`, and `Tm.var` are qualified to `GebLean.Binding`
throughout, since `GebLean.Ramified` carries its own `Tm` (the sorted-signature
term type of `GebLean/Ramified/Term.lean`) that would otherwise shadow the
binder-kit `Tm` used here.
-/

namespace GebLean.Ramified

/-- The concrete `o`-term of the zero value elaborates: `conc (natToFreeAlg 0)`
is the nullary constructor spine, a closed `oneLambdaSig` term of sort `o`. -/
example : Binding.Tm (oneLambdaSig natAlgSig) [] RType.o :=
  conc (natToFreeAlg 0)

/-- The concrete `o`-term of the value `2` elaborates as a closed term of sort
`o`: the successor constructor applied twice to the zero constructor. -/
example : Binding.Tm (oneLambdaSig natAlgSig) [] RType.o :=
  conc (natToFreeAlg 2)

/-- The type `Ā[o]` of the Berarducci-Böhm representation over `natAlgSig` is the
Church type `N̄` (Leivant III section 4.2, p. 223), in the `ctorList natAlgSig`
enumeration order (zero-first): `o → (o→o) → o`, the constructor reordering of
Leivant's presented `(o→o)→o→o`. -/
example : bbType natAlgSig RType.o =
    RType.arrow RType.o (RType.arrow (RType.arrow RType.o RType.o) RType.o) := by
  simp only [bbType, stepTypes, ctorList_natAlgSig]
  rfl

/-- The Berarducci-Böhm representation `2̄^o` elaborates at the type `bbType
natAlgSig o = N̄` (the `N̄` example of task 6.2.0): the abstract representation of
the value `2` binds the two constructors and reruns the concrete fold. -/
example : Binding.Tm (oneLambdaSig natAlgSig) [] (bbType natAlgSig RType.o) :=
  bbRep (natToFreeAlg 2) RType.o

/-- The Berarducci-Böhm representation is uniform in the sort `σ`: `2̄^{o→o}`
elaborates at `bbType natAlgSig (o→o)`, exercising `bbRep` at a non-base sort. -/
example :
    Binding.Tm (oneLambdaSig natAlgSig) [] (bbType natAlgSig (RType.arrow RType.o RType.o)) :=
  bbRep (natToFreeAlg 2) (RType.arrow RType.o RType.o)

/-- The type bar-map sends `Ω o` to the Berarducci-Böhm type at the bar of its
argument (Leivant III section 4.2): `overline(Ω o) = Ω̄ ō = bbType natAlgSig ō`. -/
example : barTy (RType.omega RType.o) = bbType natAlgSig RType.o := by
  simp only [barTy_omega, barTy_o]

/-- The bar-map's image is omega-free (simple), the faithfulness invariant of
the bar-translation (Leivant III section 4.2): `overline(Ω o)` is simple. -/
example : (barTy (RType.omega RType.o)).IsSimple := barTy_isSimple _

/-- The constructor bar-map of the successor constructor `true` at `τ = o`
elaborates as a closed `1λ(A)` term of sort `(Ω̄o)^1 → Ω̄o` (Leivant III section
4.2): the bar image of `c_true^{Ωo}` binds its single Berarducci-Böhm argument
and the two constructor variables before rebuilding the node. -/
example : Binding.Tm (oneLambdaSig natAlgSig) []
    (RType.curried (List.replicate (natAlgSig.ar true) (bbType natAlgSig (barTy RType.o)))
      (bbType natAlgSig (barTy RType.o))) :=
  barConOmega true RType.o

/-- The constructor bar-map of the zero constructor `false` at `τ = o` elaborates
as a closed `1λ(A)` term of sort `(Ω̄o)^0 → Ω̄o = Ω̄o` (Leivant III section 4.2):
the nullary constructor case, binding only the two constructor variables. -/
example : Binding.Tm (oneLambdaSig natAlgSig) []
    (RType.curried (List.replicate (natAlgSig.ar false) (bbType natAlgSig (barTy RType.o)))
      (bbType natAlgSig (barTy RType.o))) :=
  barConOmega false RType.o

/-- The recurrence bar-map at `τ = o` elaborates as a closed `1λ(A)` term of
sort `ξ̄_1, ξ̄_2, Ω̄o → ō` (Leivant III section 4.2): the bar image of `R^o` binds
the two step functions and the Berarducci-Böhm argument, then iterates the
argument on the steps. -/
example : Binding.Tm (oneLambdaSig natAlgSig) []
    (RType.curried (stepTypes natAlgSig (barTy RType.o) (barTy RType.o))
      (RType.arrow (bbType natAlgSig (barTy RType.o)) (barTy RType.o))) :=
  barRecur RType.o

/-- The case bar-map at the base object sort `o` elaborates as a closed `1λ(A)`
term of sort `o → (ō)^k → ō` (Leivant III section 4.2): the `casē^o` clause is
the base case combinator, so no descent under branch abstractions occurs. -/
example : Binding.Tm (oneLambdaSig natAlgSig) []
    (RType.arrow RType.o
      (RType.curried (List.replicate natAlgSig.numCtors (barTy RType.o)) (barTy RType.o))) :=
  barCase RType.o (Or.inl rfl)

/-- The case bar-map at the higher object sort `Ω o` elaborates as a closed
`1λ(A)` term (Leivant III section 4.2): the `casē^{Ωo}` clause pushes the case
under the abstractions of its branch functions, since the branches now have the
Berarducci-Böhm type `Ω̄o = σ⃗ → o` rather than the base sort. -/
example : Binding.Tm (oneLambdaSig natAlgSig) []
    (RType.arrow RType.o
      (RType.curried (List.replicate natAlgSig.numCtors (barTy (RType.omega RType.o)))
        (barTy (RType.omega RType.o)))) :=
  barCase (RType.omega RType.o) (Or.inr rfl)

/-- The term bar-map of the identity `λx:o. x` applied to the zero constructor
elaborates at the barred sort `ō = o` (Leivant III section 4.2): a closed
`o`-variant term exercising the `app`, `lam`, variable, and `con^o` clauses of
`barTm`. -/
example : Binding.Tm (oneLambdaSig natAlgSig) ([].map barTy) (barTy RType.o) :=
  barTm (app' (lam' (Binding.Tm.var boundVar))
    (Binding.Tm.op (S := rlmrOSig natAlgSig)
      (RlmrOOp.con RType.o (Or.inl rfl) false) (fun k => k.elim0)))

/-- The term bar-map of the shifted successor constructor `c_true^{Ωo}`
elaborates at the barred sort (Leivant III section 4.2): the `con^{Ωτ}` clause of
`barTm` dispatches to `barConOmega`. -/
example : Binding.Tm (oneLambdaSig natAlgSig) ([].map barTy)
    (barTy (RType.arrow (RType.omega RType.o) (RType.omega RType.o))) :=
  barTm (Binding.Tm.op (S := rlmrOSig natAlgSig)
    (RlmrOOp.con (RType.omega RType.o) (Or.inr rfl) true) (fun k => k.elim0))

/-- The term bar-map of the recurrence combinator `R^o` elaborates at the barred
sort (Leivant III section 4.2): the `recur` clause of `barTm` dispatches to
`barRecur`. -/
example : Binding.Tm (oneLambdaSig natAlgSig) ([].map barTy)
    (barTy ((rlmrOSig natAlgSig).result (RlmrOOp.recur RType.o))) :=
  barTm (Binding.Tm.op (S := rlmrOSig natAlgSig) (RlmrOOp.recur RType.o) (fun k => k.elim0))

/-- The term bar-map of the case combinator `case^o` elaborates at the barred
sort (Leivant III section 4.2): the `case` clause of `barTm` dispatches to
`barCase`. -/
example : Binding.Tm (oneLambdaSig natAlgSig) ([].map barTy)
    (barTy ((rlmrOSig natAlgSig).result (RlmrOOp.case RType.o (Or.inl rfl)))) :=
  barTm (Binding.Tm.op (S := rlmrOSig natAlgSig)
    (RlmrOOp.case RType.o (Or.inl rfl)) (fun k => k.elim0))

/-- The term bar-map of the destructor `dstr_0 : o → o` elaborates at the
barred sort (Leivant III section 4.2): the `dstr` clause of `barTm` dispatches
to the base destructor `dstr j` of `1λ(A)`. -/
example : Binding.Tm (oneLambdaSig natAlgSig) ([].map barTy)
    (barTy ((rlmrOSig natAlgSig).result
      (RlmrOOp.dstr (⟨0, by decide⟩ : Fin natAlgSig.maxArity)))) :=
  barTm (Binding.Tm.op (S := rlmrOSig natAlgSig)
    (RlmrOOp.dstr (⟨0, by decide⟩ : Fin natAlgSig.maxArity)) (fun k => k.elim0))

/-- The term bar-map of the case combinator `case^{Ωo}` at the higher object
sort elaborates at the barred sort (Leivant III section 4.2): the `case`
clause of `barTm` dispatches to `barCase`, which here descends into its
`omega` shape-split — the branch not exercised by the `case^o` example above,
reached through the fold rather than by calling `barCase` directly. -/
example : Binding.Tm (oneLambdaSig natAlgSig) ([].map barTy)
    (barTy ((rlmrOSig natAlgSig).result
      (RlmrOOp.case (RType.omega RType.o) (Or.inr rfl)))) :=
  barTm (Binding.Tm.op (S := rlmrOSig natAlgSig)
    (RlmrOOp.case (RType.omega RType.o) (Or.inr rfl)) (fun k => k.elim0))

end GebLean.Ramified
