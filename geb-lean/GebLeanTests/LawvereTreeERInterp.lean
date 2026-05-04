import GebLean.LawvereTreeERInterp

/-!
# Tests for LawvereTreeERInterp

Faithful interpretation functor and faithful
inclusion sanity tests.
-/

open GebLean CategoryTheory

attribute [local instance 2000]
  instCategoryStructLawvereTreeERCat
attribute [local instance 2000]
  instCategoryLawvereTreeERCat

-- Interpretation functor type-checks.
example : LawvereTreeERCat ⥤ Type :=
  treeErInterpFunctor

-- Faithful instance is available.
example : treeErInterpFunctor.Faithful :=
  inferInstance

-- Inclusion functor type-checks.
example : LawvereTreeERCat ⥤ LawvereBTQuotObj :=
  treeErInclusion

-- Inclusion is faithful.
example : treeErInclusion.Faithful :=
  inferInstance
