module LanguageDef.MLTwistPair

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import LanguageDef.QType
import public LanguageDef.InternalCat
import public LanguageDef.SliceFuncCat
import public LanguageDef.MLDirichCat
import public LanguageDef.PolyCat
import public LanguageDef.MLBundleCat
import public LanguageDef.IntArena

%default total

-- In favor of the (identical) one from `SliceFuncCat`.
%hide Library.IdrisCategories.BaseChangeF

-------------------------------
-------------------------------
---- Objects and morphisms ----
-------------------------------
-------------------------------

-----------------
---- Objects ----
-----------------

public export
record MLTwPobj where
  constructor TwPo
  mltwPred : Type
  mltwStruct : SliceObj mltwPred

public export
record MLTwPmorTot where
  constructor TwPmT
  mltwCodPred :
    Type
  mltwCodStruct :
    SliceObj mltwCodPred
  mltwDomPred :
    SliceObj mltwCodPred
  mltwDomStruct :
    SliceObj (Sigma {a=mltwCodPred} mltwDomPred)
  mltwStructMap :
    SliceMorphism {a=mltwCodPred}
      mltwCodStruct
      (SlSliceToSlice {c=mltwCodPred} {a=mltwDomPred} mltwDomStruct)
