module LanguageDef.MLDiPolyFunc

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.InternalProfunctor
import public LanguageDef.SlicePolyCat
import public LanguageDef.DiPolyFunc

%default total

-- In favor of the (identical) one from `SliceFuncCat`.
%hide Library.IdrisCategories.BaseChangeF
