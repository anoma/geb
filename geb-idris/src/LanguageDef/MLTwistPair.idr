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

public export
MLTwPobjPair : Type
MLTwPobjPair = ProductMonad MLTwPobj

public export
MLTwPstruct : MLTwPobj -> Type
MLTwPstruct twp = Sigma {a=(mltwPred twp)} (mltwStruct twp)

public export
mltwpMor : (twp : MLTwPobj) -> MLTwPstruct twp -> mltwPred twp
mltwpMor twp = DPair.fst

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
MLTwPmorDomStructCodPredSl : (mor : MLTwPmorTot) -> SliceObj (mltwCodPred mor)
MLTwPmorDomStructCodPredSl mor =
  SlSliceToSlice {c=(mltwCodPred mor)} {a=(mltwDomPred mor)} (mltwDomStruct mor)

public export
MLTwPmorCodStruct : MLTwPmorTot -> Type
MLTwPmorCodStruct mor = Sigma {a=(MLTwPmorDomStruct mor)} (mltwCodStruct mor)

public export
MLTwPmorCodStructDomPredSl : (mor : MLTwPmorTot) ->
  SliceOfSlice {a=(mltwCodPred mor)} (mltwDomPred mor)
MLTwPmorCodStructDomPredSl mor =
  SlSliceToSlice {c=(MLTwPmorDomPred mor)} {a=(mltwDomStruct mor)}
    (mltwCodStruct mor)

public export
MLTwPmorCodStructCodPredSl : (mor : MLTwPmorTot) -> SliceObj (mltwCodPred mor)
MLTwPmorCodStructCodPredSl mor =
  SlSliceToSlice {c=(mltwCodPred mor)} {a=(MLTwPmorDomStructCodPredSl mor)}
    (mltwCodStruct mor . dpAssocLeft)

public export
MLTwPmorDom : MLTwPmorTot -> MLTwPobj
MLTwPmorDom mor = TwPo (MLTwPmorDomPred mor) (mltwDomStruct mor)

public export
MLTwPmorCod : MLTwPmorTot -> MLTwPobj
MLTwPmorCod mor = TwPo (mltwCodPred mor) (MLTwPmorCodStructCodPredSl mor)

public export
MLTwPmorSig : MLTwPmorTot -> MLTwPobjPair
MLTwPmorSig mor = (MLTwPmorDom mor, MLTwPmorCod mor)

public export
MLTwPpredMor : (mor : MLTwPmorTot) ->
  MLTwPmorDomPred mor -> mltwCodPred mor
MLTwPpredMor mor = DPair.fst

public export
MLTwPdomMor : (mor : MLTwPmorTot) ->
  MLTwPmorDomStruct mor -> MLTwPmorDomPred mor
MLTwPdomMor mor = mltwpMor (MLTwPmorDom mor)

public export
MLTwPstructMor : (mor : MLTwPmorTot) ->
  MLTwPmorCodStruct mor -> MLTwPmorDomStruct mor
MLTwPstructMor mor = DPair.fst

public export
MLTwPcodMor : (mor : MLTwPmorTot) ->
  MLTwPmorCodStruct mor -> mltwCodPred mor
MLTwPcodMor mor = MLTwPpredMor mor . MLTwPdomMor mor . MLTwPstructMor mor

public export
MLTwPmor : IntMorSig MLTwPobj
MLTwPmor x y = WPreImage {a=MLTwPmorTot} {b=MLTwPobjPair} MLTwPmorSig (x, y)
