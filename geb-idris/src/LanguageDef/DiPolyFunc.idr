module LanguageDef.DiPolyFunc

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.DisliceCat

--------------------------------------------------------
--------------------------------------------------------
---- Dipolynomial functors and difunctors on `Type` ----
--------------------------------------------------------
--------------------------------------------------------

public export
record DiArena where
  constructor DiAr
  daPos : Type
  daCat : daPos -> ADisliceCat

public export
DAobj : (da : DiArena) -> SliceObj (daPos da)
DAobj da = ADisliceObj . daCat da

public export
DAbase : (da : DiArena) -> SliceObj (daPos da)
DAbase da = adscBase . daCat da

public export
data InterpDAf : DiArena -> Type -> Type where
  DAf : {0 da : DiArena} -> (i : daPos da) -> (obj : DAobj da i) ->
    InterpDAf da (Sigma {a=(DAbase da i)} $ adsoTot {cat=(daCat da i)} obj)

public export
idaPos : {0 da : DiArena} -> {0 x : Type} -> InterpDAf da x -> daPos da
idaPos (DAf i _) = i

public export
idaObj : {0 da : DiArena} -> {0 x : Type} ->
  (e : InterpDAf da x) -> DAobj da (idaPos {da} {x} e)
idaObj (DAf _ obj) = obj
