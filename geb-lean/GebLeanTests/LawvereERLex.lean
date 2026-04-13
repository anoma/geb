import GebLean.LawvereERLex

/-!
# Tests for LawvereERLex

Sanity tests for the decidable ER-subobject category.
-/

open GebLean
open CategoryTheory

-- The always-one predicate at arity 0: the constant
-- successor applied to zero at the empty context.
private def oneZero : ERMor1 0 :=
  ERMor1.comp ERMor1.succ
    (fun (_ : Fin 1) =>
      ERMor1.comp ERMor1.zero Fin.elim0)

-- oneZero evaluates to 1 at the empty context.
example : oneZero.interp Fin.elim0 = 1 := rfl

-- As a Boolean predicate at arity 0.
private def truePred0 : ERBoolPred 0 :=
  { pred := oneZero
    bool := fun _ => by
      show oneZero.interp _ ≤ 1
      rfl }

-- Construct an object.
private def trueObj0 : LexObj :=
  { arity := 0, pred := truePred0 }

-- Category instance is inferred.
example : Category LawvereERLexCat := inferInstance

-- Identity composed with itself yields identity.
example :
    (𝟙 trueObj0 : trueObj0 ⟶ trueObj0) ≫
    (𝟙 trueObj0) = 𝟙 trueObj0 := by
  rw [Category.id_comp]

-- Terminal uniqueness: any morphism to terminal
-- equals the terminal morphism.
example (obj : LexObj)
    (f : obj ⟶ (LexObj.terminal :
        LawvereERLexCat)) :
    f = ERLexMorNQuo.toTerminal obj :=
  ERLexMorNQuo.toTerminal_uniq f

-- HasChosenFiniteProducts is available for
-- LawvereERLexCat.
example : HasChosenFiniteProducts LawvereERLexCat :=
  inferInstance

-- Product of the terminal with itself has arity 0.
example : (LexObj.prod LexObj.terminal
    LexObj.terminal).arity = 0 := rfl

-- Equalizer of a morphism with itself is a
-- well-typed object.
example (a b : LawvereERLexCat)
    (f : ERLexMorN a b) : LawvereERLexCat :=
  LexObj.equalizer f f

-- Equalizer morphism types correctly.
example (a b : LawvereERLexCat)
    (f g : ERLexMorN a b) :
    ERLexMorNQuo (LexObj.equalizer f g) a :=
  ERLexMorNQuo.equalizerMap f g

-- Equalizer arity matches the source arity.
example (a b : LawvereERLexCat)
    (f g : ERLexMorN a b) :
    (LexObj.equalizer f g).arity = a.arity :=
  rfl
