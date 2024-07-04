module LanguageDef.MLTwistPair

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import LanguageDef.QType
import public LanguageDef.InternalCat
import public LanguageDef.SliceFuncCat
import public LanguageDef.MLDirichCat
import public LanguageDef.PolyCat
import public LanguageDef.IntArena

%default total

-- In favor of the (identical) one from `SliceFuncCat`.
%hide Library.IdrisCategories.BaseChangeF

---------------------------------------------------------
---------------------------------------------------------
---- Objects and morphisms of `MLTwistPair` category ----
---------------------------------------------------------
---------------------------------------------------------

-----------------
---- Objects ----
-----------------

public export
record MLTwPobj where
  constructor TwPo
  mltwPred : Type
  mltwStruct : SliceObj mltwPred

-------------------
---- Morphisms ----
-------------------

public export
record MLTwPmorTot where
  constructor TwPmT
  mltwCodPred :
    Type
  mltwDomPred :
    SliceObj mltwCodPred
  mltwDomStruct :
    SliceOfSlice {a=mltwCodPred} mltwDomPred
  mltwCodStruct :
    SliceOfSlice {a=(Sigma {a=mltwCodPred} mltwDomPred)} mltwDomStruct

public export
MLTwPmorDomPred : MLTwPmorTot -> Type
MLTwPmorDomPred mor = Sigma {a=(mltwCodPred mor)} (mltwDomPred mor)

public export
MLTwPmorDomStruct : MLTwPmorTot -> Type
MLTwPmorDomStruct mor = Sigma {a=(MLTwPmorDomPred mor)} (mltwDomStruct mor)

public export
MLTwPmorCodStruct : MLTwPmorTot -> Type
MLTwPmorCodStruct mor = Sigma {a=(MLTwPmorDomStruct mor)} (mltwCodStruct mor)
