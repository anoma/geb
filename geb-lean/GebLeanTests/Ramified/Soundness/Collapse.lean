import GebLean.Ramified.Soundness.Collapse
import GebLeanTests.Ramified.HigherOrder

/-!
# Tests for the collapse packaging

Acceptance examples for the collapse packaging: the collapse denotation of an
identity morphism of `SynCatFO` is the identity function, through
`collapseDenotation_id`; the soundness functor `collapseFunctor` lands the
Phase 2 doubling morphism on an `ERMorN` whose interpretation doubles its
input, through the interpretation lemmas (`collapseTupleER_interp`); and the
functor's morphism map is injective, through `collapseFunctor.Faithful`.
-/

namespace GebLeanTests.Ramified.CollapseTest

open CategoryTheory
open GebLean GebLean.Ramified GebLean.Ramified.Definability
open GebLeanTests.Ramified.HigherOrderTest

/-- The collapse denotation of the identity morphism is the identity function. -/
example (Γ : SynCatFO) : collapseDenotation (𝟙 Γ) = id :=
  collapseDenotation_id Γ

/-- The doubling recurrence-argument context `[Ω o]` as a `SynCatFO` object. -/
def ctxDoubleFO : SynCatFO :=
  ⟨[RType.omega RType.o], fun i => Fin.cases (Or.inr rfl) (fun j => j.elim0) i⟩

/-- The doubling result context `[o]` as a `SynCatFO` object. -/
def ctxOFO : SynCatFO :=
  ⟨[RType.o], fun i => Fin.cases (Or.inl rfl) (fun j => j.elim0) i⟩

/-- The Phase 2 doubling morphism as a `SynCatFO` morphism: the identifier
`doubling` applied to the context's sole variable. -/
def doublingMorFO : ctxDoubleFO ⟶ ctxOFO :=
  ⟨identHom doubling⟩

/-- The doubling tuple at the bridged contexts of the `SynCatFO` objects: the
representative of `doublingMorFO`'s underlying hom, read at the
`SynCatFO.toObjCtx` contexts. -/
def doublingTupleFO :
    HomTuple (higherOrder A) (ctxDoubleFO.toObjCtx.2).toCtx
      (ctxOFO.toObjCtx.2).toCtx :=
  Fin.cons
    (Tm.op (sig := (higherOrder A).sig)
      (Sum.inl (Sum.inr ⟨[RType.omega RType.o], RType.o, doubling⟩))
      (fun k => Tm.var k))
    finZeroElim

/-- The numeric denotation of the doubling tuple is the numeric reading of the
doubling identifier's denotation. -/
theorem doublingTupleFO_denotation (v : Fin 1 → ℕ) :
    ramifiedDenotation (Quotient.mk
        (homSetoid (higherOrder A) (interpQuotRel (higherOrder A))
          (ctxDoubleFO.toObjCtx.2).toCtx (ctxOFO.toObjCtx.2).toCtx)
        doublingTupleFO) v (0 : Fin 1)
      = freeAlgToNat (doubling.interp (envDouble (v 0))) := rfl

/-- The soundness functor lands the doubling morphism on an `ERMorN` whose
interpretation is the doubling identifier's denotation at every input — the
acceptance example of task 6.5b, read off the interpretation lemmas rather
than kernel reduction of the landed morphism — and in particular doubles the
inputs `0`, `1`, and `3`. -/
example : ∃ e : ERMorN 1 1,
    collapseFunctor.map doublingMorFO = Quotient.mk (erMorNSetoid 1 1) e ∧
      (∀ v : Fin 1 → ℕ,
        e.interp v 0 = freeAlgToNat (doubling.interp (envDouble (v 0)))) ∧
      e.interp ![0] 0 = 0 ∧ e.interp ![1] 0 = 2 ∧ e.interp ![3] 0 = 6 := by
  have hhom : collapseHom doublingMorFO
      = Quotient.mk (homSetoid (higherOrder A) (interpQuotRel (higherOrder A))
          (ctxDoubleFO.toObjCtx.2).toCtx (ctxOFO.toObjCtx.2).toCtx)
        doublingTupleFO := rfl
  have hinterp : ∀ v : Fin 1 → ℕ,
      (collapseTupleER ctxDoubleFO.toObjCtx.2 ctxOFO.toObjCtx.2 doublingTupleFO :
        ERMorN 1 1).interp v 0
        = freeAlgToNat (doubling.interp (envDouble (v 0))) := fun v =>
    (congrFun (collapseTupleER_interp _ _ doublingTupleFO v) (0 : Fin 1)).trans
      (doublingTupleFO_denotation v)
  refine ⟨collapseTupleER ctxDoubleFO.toObjCtx.2 ctxOFO.toObjCtx.2 doublingTupleFO,
    congrArg (collapseHomER ctxDoubleFO.toObjCtx.2 ctxOFO.toObjCtx.2) hhom,
    hinterp, ?_, ?_, ?_⟩
  · rw [hinterp ![0]]; decide
  · rw [hinterp ![1]]; decide
  · rw [hinterp ![3]]; decide


/-- The soundness functor is faithful on the doubling hom-set. -/
example :
    Function.Injective (fun g : ctxDoubleFO ⟶ ctxOFO => collapseFunctor.map g) :=
  fun _ _ h => collapseFunctor.map_injective h

end GebLeanTests.Ramified.CollapseTest
