module LanguageDef.MLQuivPoly

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.Quiver
import public LanguageDef.MLQuivCat
import public LanguageDef.MLQuivUniv
import public LanguageDef.PolyCat

---------------------------------------------------------
---------------------------------------------------------
---- Quivers internal to polynomial-functor category ----
---------------------------------------------------------
---------------------------------------------------------

public export
record PolyQuiv where
  constructor PQuiv
  pqPos : PolyFunc
  pqDir : PFAlg pqPos PolyFunc

----------------------------------------
----------------------------------------
---- Polynomial functors on quivers ----
----------------------------------------
----------------------------------------
