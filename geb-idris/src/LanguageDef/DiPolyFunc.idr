module LanguageDef.DiPolyFunc

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.DisliceCat
import LanguageDef.PolyCat
import LanguageDef.Geb

---------------------------------------------------
---------------------------------------------------
---- Dipolynomial functors from dislice arenas ----
---------------------------------------------------
---------------------------------------------------

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
DAcobase : (da : ADiArena) -> (i : daPos da) -> SliceObj (DAbase da i)
DAcobase da i = adscCobase (daCat da i)

public export
DAtot : {da : ADiArena} -> {i : daPos da} -> SliceObj (DAobj da i)
DAtot {da} {i} = Sigma {a=(DAbase da i)} . adsoTot {cat=(daCat da i)}

public export
record InterpDAf (da : ADiArena) (x : Type) where
  constructor IDAf
  idafPos : daPos da
  idafProj : x -> DAbase da idafPos
  idafDir :
    SliceMorphism {a=(DAbase da idafPos)}
      (DAcobase da idafPos)
      (SliceFromCSlice (x ** idafProj))

-- An object of the category of elements of `InterpDAF da` is
-- a dislice object.
export
IDAfobj : {da : ADiArena} -> {x : Type} ->
  (e : InterpDAf da x) -> DAobj da (idafPos e)
IDAfobj {da} {x} (IDAf pos proj dir) = ADSO (SliceFromCSlice (x ** proj)) dir

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

--------------------------------------------------
--------------------------------------------------
---- Polynomial profunctors as curried arenas ----
--------------------------------------------------
--------------------------------------------------

record PolyProAr where
  constructor PPA
  ppPos : Type -> Type
  ppContramap : (0 x, y : Type) -> (y -> x) -> ppPos x -> ppPos y
  ppDir : NaturalTransformation ppPos (const Type)
  ppNaturality :
    (0 x, y : Type) -> (0 m : y -> x) ->
    ExtEq {a=(ppPos x)} {b=Type} (ppDir x) (ppDir y . ppContramap x y m)

InterpPPA : PolyProAr -> ProfunctorSig
InterpPPA (PPA pos cmap dir nat) x y = (i : pos x ** dir x i -> y)

InterpPPAdimap : (ppa : PolyProAr) -> TypeDimapSig (InterpPPA ppa)
InterpPPAdimap (PPA pos cmap dir nat) s t a b mas mtb (i ** d) =
  (cmap s a mas i ** replace {p=(ContravarHomFunc b)} (nat s a mas i) $ mtb . d)
