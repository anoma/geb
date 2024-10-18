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

-- Dipolynomial functors in Idris's metalanguage(s).

-------------------------------
-------------------------------
---- Objects and morphisms ----
-------------------------------
-------------------------------

public export
MLPolyDiSig : Type
MLPolyDiSig = PolyDiSig Type

public export
mlpdPos : MLPolyDiSig -> Type
mlpdPos = pdPos {c=Type}

public export
mlpdDirL : (pd : MLPolyDiSig) -> mlpdPos pd -> Type
mlpdDirL = pdDirL {c=Type}

public export
mlpdDirR : (pd : MLPolyDiSig) -> mlpdPos pd -> Type
mlpdDirR = pdDirR {c=Type}

public export
InterpMLPolyDi : MLPolyDiSig -> IntDifunctorSig Type
InterpMLPolyDi = InterpPolyDi {c=Type} TypeMor

public export
mlipdPos : {p : MLPolyDiSig} ->
  {x, y : Type} -> InterpMLPolyDi p x y -> mlpdPos p
mlipdPos = ipdPos {c=Type} {mor=TypeMor}

public export
mlipdDirL : {p : MLPolyDiSig} ->
  {x, y : Type} -> (ipd : InterpMLPolyDi p x y) ->
  x -> mlpdDirL p (mlipdPos {p} {x} {y} ipd)
mlipdDirL = ipdDirL {c=Type} {mor=TypeMor}

public export
mlipdDirR : {p : MLPolyDiSig} ->
  {x, y : Type} -> (ipd : InterpMLPolyDi p x y) ->
  mlpdDirR p (mlipdPos {p} {x} {y} ipd) -> y
mlipdDirR = ipdDirR {c=Type} {mor=TypeMor}
