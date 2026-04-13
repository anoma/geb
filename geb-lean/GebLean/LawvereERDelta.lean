import GebLean.LawvereERLex
import GebLean.LawvereERQuot
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Embedding `Δ : LawvereERCat ⥤ LawvereERLexCat`

Defines the canonical embedding of `LawvereERCat`
(the Lawvere theory of elementary recursive
functions) into `LawvereERLexCat` (its finite-limit
completion via decidable subobjects), sending arity
`n` to the object `(n, ⊤)` cut out by the always-true
predicate.
-/

namespace GebLean

open CategoryTheory

/-- Object map of the embedding: arity `n` is sent
to `(n, ⊤)`, the object whose predicate is the
constantly-true predicate at arity `n`. -/
def erDelta.obj (n : LawvereERCat) : LawvereERLexCat :=
  { arity := n, pred := ERBoolPredE.alwaysTrue n }

/-- Raw morphism lift: an `ERMorN n m` becomes an
`ERLexMorN` from `(n, ⊤)` to `(m, ⊤)`.  The respect
proof is trivial because the target predicate `⊤`
always evaluates to `1`. -/
def erDeltaRaw {n m : ℕ} (f : ERMorN n m) :
    ERLexMorN (erDelta.obj n) (erDelta.obj m) :=
  ⟨f, fun _ _ => rfl⟩

/-- Morphism map of the embedding: lift through the
quotient.  Well-defined because full extensional
equality of `ERMorN` tuples implies their lifted
forms agree on `⊤`-satisfying contexts. -/
def erDelta.map {n m : ℕ} (f : ERMorNQuo n m) :
    ERLexMorNQuo (erDelta.obj n) (erDelta.obj m) :=
  Quotient.lift
    (s := erMorNSetoid n m)
    (fun f' =>
      Quotient.mk
        (erLexMorNSetoid (erDelta.obj n)
          (erDelta.obj m))
        (erDeltaRaw f'))
    (fun _ _ h =>
      Quotient.sound
        (s := erLexMorNSetoid (erDelta.obj n)
          (erDelta.obj m))
        (fun ctx _ => h ctx))
    f

/-- Δ preserves identity morphisms. -/
theorem erDelta.map_id (n : LawvereERCat) :
    erDelta.map (ERMorNQuo.id n) =
      ERLexMorNQuo.id (erDelta.obj n) := by
  rfl

/-- Δ preserves composition of morphisms. -/
theorem erDelta.map_comp {n m k : ℕ}
    (f : ERMorNQuo n m) (g : ERMorNQuo m k) :
    erDelta.map (ERMorNQuo.comp f g) =
      ERLexMorNQuo.comp (erDelta.map f)
        (erDelta.map g) := by
  refine Quotient.ind₂ ?_ f g
  intro f_raw g_raw
  rfl

/-- The full and faithful embedding
`LawvereERCat ⥤ LawvereERLexCat`. -/
def erDeltaFunctor :
    LawvereERCat ⥤ LawvereERLexCat where
  obj := erDelta.obj
  map := erDelta.map
  map_id := erDelta.map_id
  map_comp := erDelta.map_comp

end GebLean
