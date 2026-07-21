import GebLean
import GebLean.Ramified.Polynomial.Collapse

/-!
# Tests for the primed collapse packaging and the denotation agreement

Executable checks over the `1 + X` word algebra `natAlgSig`. The numeric
transports `objToNat'` / `objFromNat'` are pinned at the base object sort `o`:
each is checked against the carrier numeral `natToFreeAlg'` and the two round
trips are exercised. The collapse denotation is computed on a variable tuple —
the second projection `[o, o] ⟶ [o]` — through `collapseDenotation'_apply`, its
composition law is checked against an explicit composite, and the agreement
`collapseDenotation_sliceEquiv` transports the computation to the legacy
first-order syntactic category.
-/

namespace GebLeanTests.Ramified.Polynomial.CollapseTest

open GebLean.Ramified GebLean.Ramified.Polynomial CategoryTheory

/-- The object-sort witness of the base sort `o`. -/
theorem oIsObj : RType'.IsObj RType'.o := oObj'.2

-- `objToNat'` reads the carrier numeral `4`, transported into the base sort's
-- carrier copy, back as `4`.
example :
    objToNat' oIsObj
        (cast (RType'.interp_isObj (FreeAlg' natAlgSig) oIsObj).symm (natToFreeAlg' 4))
      = 4 := by
  unfold objToNat'
  rw [cast_cast, cast_eq]
  exact natFreeAlgEquiv'_natToFreeAlg' 4

-- `objFromNat'` transports the carrier numeral `4` into the base sort's carrier
-- copy.
example :
    objFromNat' oIsObj 4
      = cast (RType'.interp_isObj (FreeAlg' natAlgSig) oIsObj).symm (natToFreeAlg' 4) := by
  unfold objFromNat'
  exact congrArg _ ((Equiv.symm_apply_eq natFreeAlgEquiv').mpr
    (natFreeAlgEquiv'_natToFreeAlg' 4).symm)

-- The numeric reading inverts the carrier-copy transport.
example (k : ℕ) : objToNat' oIsObj (objFromNat' oIsObj k) = k :=
  objToNat'_objFromNat' oIsObj k

-- The carrier-copy transport inverts the numeric reading.
example (x : RType'.interp (FreeAlg' natAlgSig) RType'.o) :
    objFromNat' oIsObj (objToNat' oIsObj x) = x :=
  objFromNat'_objToNat' oIsObj x

/-- The two-entry object-sort context `[o, o]` as a first-order object. -/
def ctx2 : SynCatFO' where
  obj := [RType'.o, RType'.o]
  property := by
    intro i
    refine Fin.cases oIsObj (fun k => ?_) i
    exact Fin.cases oIsObj (fun k' => k'.elim0) k

/-- The one-entry object-sort context `[o]` as a first-order object. -/
def ctx1 : SynCatFO' where
  obj := [RType'.o]
  property := by
    intro i
    exact Fin.cases oIsObj (fun k => k.elim0) i

/-- The second projection `[o, o] ⟶ [o]`: the variable tuple reading the
second context entry. -/
def proj2 : ctx2 ⟶ ctx1 :=
  ObjectProperty.homMk
    (Quotient.mk _ (Fin.cons (Tm'.var (Γ := ctx2.obj) ⟨1, by decide⟩) finZeroElim))

/-- The diagonal `[o] ⟶ [o, o]`: the variable tuple reading the sole context
entry at both output positions. -/
def diag1 : ctx1 ⟶ ctx2 :=
  ObjectProperty.homMk
    (Quotient.mk _ (Fin.cons (Tm'.var (Γ := ctx1.obj) ⟨0, by decide⟩)
      (Fin.cons (Tm'.var (Γ := ctx1.obj) ⟨0, by decide⟩) finZeroElim)))

/-- The collapse denotation of the second projection reads the second input. -/
theorem collapseDenotation'_proj2 (v : Fin (objLen' ctx2) → ℕ) (j : Fin (objLen' ctx1)) :
    collapseDenotation' proj2 v j = v ⟨1, by decide⟩ := by
  rw [collapseDenotation'_apply]
  refine Fin.cases ?_ (fun k => k.elim0) j
  exact objToNat'_objFromNat' _ _

/-- The collapse denotation of the diagonal repeats its sole input. -/
theorem collapseDenotation'_diag1 (v : Fin (objLen' ctx1) → ℕ) (j : Fin (objLen' ctx2)) :
    collapseDenotation' diag1 v j = v ⟨0, by decide⟩ := by
  rw [collapseDenotation'_apply]
  refine Fin.cases ?_ (fun k => ?_) j
  · exact objToNat'_objFromNat' _ _
  · refine Fin.cases ?_ (fun k' => k'.elim0) k
    exact objToNat'_objFromNat' _ _

-- The composition law at `proj2 ≫ diag1`: both outputs read the second input.
example (v : Fin (objLen' ctx2) → ℕ) (j : Fin (objLen' ctx2)) :
    collapseDenotation' (proj2 ≫ diag1) v j = v ⟨1, by decide⟩ := by
  rw [collapseDenotation'_comp, Function.comp_apply, collapseDenotation'_diag1,
    collapseDenotation'_proj2]

-- The agreement instance: the legacy collapse denotation of the image of the
-- second projection reads the second input.
example (v : Fin (objLen (synCatFOSliceEquiv.functor.obj ctx2)) → ℕ)
    (j : Fin (objLen (synCatFOSliceEquiv.functor.obj ctx1))) :
    collapseDenotation (synCatFOSliceEquiv.functor.map proj2) v j
      = v ⟨1, objLen_functor_obj ctx2 ▸ (by decide : 1 < objLen' ctx2)⟩ := by
  rw [collapseDenotation_sliceEquiv, arityCongr_apply, collapseDenotation'_proj2]
  rfl

end GebLeanTests.Ramified.Polynomial.CollapseTest
