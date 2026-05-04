import GebLean.LawvereBTEqCompletion

/-!
# Equalizer Completion Tests

Tests for the equalizer completion of the Lawvere
BT theory, verifying field accessors on concrete
examples and the interpretation functor's behavior
on trivially-embedded objects.
-/

open GebLean CategoryTheory

-- Trivially-embedded object: src and tgt agree.
#guard (cpEmbed
  (1 : LawvereBTQuotCat)).src = 1

#guard (cpEmbed
  (1 : LawvereBTQuotCat)).tgt = 1

-- Trivially-embedded zero.
#guard (cpEmbed
  (0 : LawvereBTQuotCat)).src = 0

-- Terminal object has src = 0.
#guard (cpTerminal
  (C := LawvereBTQuotCat)).src = 0

-- Product of trivially-embedded objects:
-- product in LawvereBTQuotCat is addition.
#guard (cpProd
  (cpEmbed (2 : LawvereBTQuotCat))
  (cpEmbed (3 : LawvereBTQuotCat))).src = 5

-- Product with terminal (zero) is the identity.
#guard (cpProd
  (cpEmbed (4 : LawvereBTQuotCat))
  (cpTerminal
    (C := LawvereBTQuotCat))).src = 4

-- The embedding preserves the underlying object.
#guard (cpEmbedding.obj
  (3 : LawvereBTQuotCat)).src = 3

-- lexInterpEmbedEquiv round-trip on the zero
-- object: the equivalence is well-typed.
example : Equiv
    (lexInterpObj (cpEmbed
      (0 : LawvereBTQuotCat)))
    (interpFunctor.{0}.obj
      (0 : LawvereBTQuotCat)) :=
  lexInterpEmbedEquiv.{0} 0
