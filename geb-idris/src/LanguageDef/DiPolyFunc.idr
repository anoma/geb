module LanguageDef.DiPolyFunc

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.DisliceCat

--------------------------------------------------------
--------------------------------------------------------
---- Dipolynomial functors and difunctors on `Type` ----
--------------------------------------------------------
--------------------------------------------------------

--------------------------
---- Categorial-style ----
--------------------------

---------------------
---- Arena-style ----
---------------------

public export
record ADiArena where
  constructor DiAr
  daPos : Type
  daCat : daPos -> ADisliceCat

public export
DAobj : (da : ADiArena) -> SliceObj (daPos da)
DAobj da = ADisliceObj . daCat da

public export
DAbase : (da : ADiArena) -> SliceObj (daPos da)
DAbase da = adscBase . daCat da

public export
DAtot : {da : ADiArena} -> {i : daPos da} -> SliceObj (DAobj da i)
DAtot {da} {i} = Sigma {a=(DAbase da i)} . adsoTot {cat=(daCat da i)}

public export
data InterpDAf : ADiArena -> Type -> Type where
  DAf : {0 da : ADiArena} ->
    (i : daPos da) -> (obj : DAobj da i) -> InterpDAf da (DAtot {da} {i} obj)

public export
idaPos : {0 da : ADiArena} -> {0 x : Type} -> InterpDAf da x -> daPos da
idaPos (DAf i _) = i

public export
idaObj : {0 da : ADiArena} -> {0 x : Type} ->
  (e : InterpDAf da x) -> DAobj da (idaPos {da} {x} e)
idaObj (DAf _ obj) = obj
