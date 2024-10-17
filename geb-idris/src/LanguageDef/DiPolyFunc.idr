module LanguageDef.DiPolyFunc

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.InternalProfunctor
import public LanguageDef.SlicePolyCat
import public LanguageDef.PolyDifunc

%default total

-- In favor of the (identical) one from `SliceFuncCat`.
%hide Library.IdrisCategories.BaseChangeF

------------------------------------------------------
------------------------------------------------------
---- Dipolynomial functors: objects and morphisms ----
------------------------------------------------------
------------------------------------------------------

-- A dipolynomial functor is a coproduct of direpresentables -- that is,
-- diYoneda-embedded objects of `opProd(c)` for some category `c`.  It
-- is determined by the same data as a polynomial endo-profunctor, but
-- interpreted differently -- in other words, the category of dipolynomial
-- functors has the same objects as the category of polynomial endo-profunctors,
-- but has different morphisms.  (This resembles the way in which polynomial
-- and Dirichlet functors are determined by the same arenas but have different
-- morphisms and interpretations as functors.)
