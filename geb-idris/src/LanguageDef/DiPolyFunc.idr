module LanguageDef.DiPolyFunc

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.DisliceCat

------------------------------------------------------------------
------------------------------------------------------------------
---- Dependent (dislice) dipolynomial functors and difunctors ----
------------------------------------------------------------------
------------------------------------------------------------------

--------------------------
---- Categorial-style ----
--------------------------

---------------------
---- Inductively ----
---------------------

export
ADSLbc : {b, b' : Type} -> {cb : SliceObj b} ->
  (m : b' -> b) -> ADSLomap (ADSC b cb) (ADSC b' (cb . m))
ADSLbc {b} {b'} {cb} m (ADSO tot inj) = ADSO (tot . m) (\eb' => inj $ m eb')

export
ADSLcbc : {b : Type} -> {cb, cb' : SliceObj b} ->
  SliceMorphism {a=b} cb' cb -> ADSLomap (ADSC b cb) (ADSC b cb')
ADSLcbc {b} {cb} {cb'} m (ADSO tot inj) =
  ADSO tot (\eb, ecb' => inj eb $ m eb ecb')

-- Dichange: simultaneous base and cobase change.
export
ADSLdc : {b, b' : Type} -> {cb : SliceObj b} -> {cb' : SliceObj b'} ->
  (mb : b' -> b) -> SliceMorphism {a=b'} cb' (cb . mb) ->
  ADSLomap (ADSC b cb) (ADSC b' cb')
ADSLdc {b} {b'} {cb} {cb'} mb mc =
  ADSLcbc {b=b'} {cb=(cb . mb)} {cb'} mc . ADSLbc {b} {b'} {cb} mb

export
ADSLsigma : {b : Type} -> (p : SliceObj b) -> {cb : SliceObj (Sigma {a=b} p)} ->
  ADSLomap
    (ADSC (Sigma {a=b} p) cb)
    (ADSC b $ \eb => Sigma {a=(p eb)} $ DPair.curry cb eb)
ADSLsigma {b} p {cb} (ADSO tot inj) =
  ADSO
    (\eb => Sigma {a=(p eb)} $ DPair.curry tot eb)
    (\eb, (ep ** ecb) => (ep ** inj (eb ** ep) ecb))

export
ADSLpi : {b : Type} -> (p : SliceObj b) -> {cb : SliceObj (Sigma {a=b} p)} ->
  ADSLomap
    (ADSC (Sigma {a=b} p) cb)
    (ADSC b $ \eb => Pi {a=(p eb)} $ DPair.curry cb eb)
ADSLpi {b} p {cb} (ADSO tot inj) =
  ADSO
    (\eb => Pi {a=(p eb)} $ DPair.curry tot eb)
    (\eb, pi, ep => inj (eb ** ep) $ pi ep)

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
