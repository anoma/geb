module LanguageDef.Figures

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.Atom
import public LanguageDef.RefinedADT

%default total

------------------------------------------------------------
------------------------------------------------------------
---- Presheaf/figure-style diagram/category definitions ----
------------------------------------------------------------
------------------------------------------------------------

-- A representation of a directed graph (such as underlies a category)
-- as a covariant presheaf.
public export
record CovPSDiag where
  constructor CovDiag
  cdNode : Type
  cdEdge : Type
  cdSrc : cdEdge -> cdNode
  cdTgt : cdEdge -> cdNode
