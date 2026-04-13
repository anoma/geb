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

/-- Δ is faithful: distinct ER morphism classes give
distinct `LawvereERLexCat` morphism classes.
Immediate because the source-restricted setoid on
the always-true predicate `⊤` reduces to full
extensional equality. -/
instance : erDeltaFunctor.Faithful where
  map_injective {n m} {f g} h := by
    induction f using Quotient.ind with
    | _ f_raw =>
      induction g using Quotient.ind with
      | _ g_raw =>
        apply Quotient.sound
          (s := erMorNSetoid n m)
        intro ctx
        have hrel := Quotient.exact
          (s := erLexMorNSetoid (erDelta.obj n)
            (erDelta.obj m)) h
        exact hrel ctx rfl

/-- Preimage of a `LawvereERLexCat` morphism between
trivially-cut-out objects.  Lifts through the
quotient by extracting the underlying `ERMorN` tuple;
well-defined because source-restricted equivalence
under `⊤` reduces to full extensional equality. -/
def erDelta.preimage {n m : ℕ}
    (h : ERLexMorNQuo (erDelta.obj n)
      (erDelta.obj m)) :
    ERMorNQuo n m :=
  Quotient.lift
    (s := erLexMorNSetoid (erDelta.obj n)
      (erDelta.obj m))
    (fun h_raw =>
      Quotient.mk (erMorNSetoid n m) h_raw.val)
    (fun _ _ hrel =>
      Quotient.sound
        (s := erMorNSetoid n m)
        (fun ctx => hrel ctx rfl))
    h

/-- The preimage is a section of `Δ.map`: applying
Δ to the preimage of `h` recovers `h`. -/
theorem erDelta.map_preimage {n m : ℕ}
    (h : ERLexMorNQuo (erDelta.obj n)
      (erDelta.obj m)) :
    erDelta.map (erDelta.preimage h) = h := by
  induction h using Quotient.ind with
  | _ h_raw =>
    apply Quotient.sound
      (s := erLexMorNSetoid (erDelta.obj n)
        (erDelta.obj m))
    intro ctx _
    rfl

/-- Δ is full: every `LawvereERLexCat` morphism
between trivially-cut-out objects comes from a
unique `LawvereERCat` morphism (uniqueness via
faithfulness; existence via `erDelta.preimage`). -/
instance : erDeltaFunctor.Full where
  map_surjective h :=
    ⟨erDelta.preimage h, erDelta.map_preimage h⟩

end GebLean
