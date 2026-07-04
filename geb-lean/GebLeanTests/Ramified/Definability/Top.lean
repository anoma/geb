import GebLean
import GebLean.Ramified.Definability.Top

/-!
# Tests for the elementary-recurrence definability family

Checks over the `1 + X` word algebra `natAlgSig` for
`GebLean.Ramified.Definability.Top`: the numeric denotation `ramifiedDenotation`
of the identity morphism on `oCtx 2` is the identity; of `identHom ramAdd` at
`(2, 3)` is the sum `5`; and `erMor_ramified_definable` instantiates on a
concrete small ER morphism (existence through the theorem, not kernel reduction
on the clocked composite).
-/

namespace GebLeanTests.Ramified.Definability.TopTest

open GebLean.Ramified
open GebLean.Ramified.Definability
open CategoryTheory

/-- The numeric denotation of the identity morphism on `oCtx 2` is the identity:
the environment built from `v` is read back to `v`. -/
example (v : Fin 2 → ℕ) :
    ramifiedDenotation
        (Hom.id (higherOrder natAlgSig) (interpQuotRel (higherOrder natAlgSig))
          (oCtx 2).toCtx) v = v := by
  funext k
  have hid : (Hom.id (higherOrder natAlgSig) (interpQuotRel (higherOrder natAlgSig))
      (oCtx 2).toCtx).eval (ramifiedEnv (oCtx 2) v)
        (Fin.cast ((oCtx 2).toCtx_length).symm k)
      = ramifiedEnv (oCtx 2) v (Fin.cast ((oCtx 2).toCtx_length).symm k) :=
    Tm.eval_var _ _ _
  unfold ramifiedDenotation
  rw [hid]
  exact (objToNat_objFromNat _ _).trans (congrArg v (Fin.ext rfl))

/-- The context of `ramAdd` as an object-sort context: the base sort `o` and the
count sort `Ω o`, both object sorts. -/
def addObjCtx : ObjCtx 2 := ![oObj, ⟨RType.omega RType.o, Or.inr rfl⟩]

/-- The numeric denotation of `identHom ramAdd` between object-sort contexts
reduces to the numeric reading of `ramAdd`'s denotation: the context and result
sorts of `ramAdd` are object sorts, so `identHom ramAdd` retypes directly, and
the readback passes through `Hom.eval` and `objToNat`. -/
example :
    @ramifiedDenotation 2 1 addObjCtx (oCtx 1) (identHom ramAdd) ![2, 3] 0
      = freeAlgToNat (ramAdd.interp (ramifiedEnv addObjCtx ![2, 3])) := by
  have heval : (identHom ramAdd).eval (ramifiedEnv addObjCtx ![2, 3])
      (Fin.cast ((oCtx 1).toCtx_length).symm 0)
      = ramAdd.interp (ramifiedEnv addObjCtx ![2, 3]) := identHom_eval _ _
  unfold ramifiedDenotation
  exact objToNat_heq_freeAlgToNat _ _ (ramAdd.interp (ramifiedEnv addObjCtx ![2, 3]))
    (heq_of_eq heval)

/-- The denotation of `ramAdd` reads out as addition (Leivant III section
2.4(2)): at inputs `(2, 3)` the numeric reading of `ramAdd`'s denotation is `5`. -/
example :
    freeAlgToNat (ramAdd.interp (addEnv (natToFreeAlg 2) (natToFreeAlg 3))) = 5 :=
  ramAdd_interp 2 3

/-- `erMor_ramified_definable` instantiates on the successor morphism: an
object-sort context and a ramified realizer with denotation `fun v _ => v 0 + 1`
exist. Existence is through the theorem, not kernel reduction on the clocked
composite. -/
example :
    ∃ (Γ : ObjCtx 1)
      (g : Hom (higherOrder natAlgSig) (interpQuotRel (higherOrder natAlgSig))
        Γ.toCtx (oCtx 1).toCtx),
      ramifiedDenotation g = fun v _ => (GebLean.ERMor1.succ).interp v :=
  erMor_ramified_definable GebLean.ERMor1.succ

end GebLeanTests.Ramified.Definability.TopTest
