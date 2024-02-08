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

-- If we consider `ADiArena`s where `pos : Type` is `Type` itself,
-- then, given that `ADiArena` actually has effectively the same
-- signature as `PolyFunc`, then we are considering arenas of type
-- `Type -> PolyFunc`.  If we absorb the type parameter into the
-- structure, we obtain a position functor and a natural transformation
-- from that functor to the constant functor which returns `Type`
-- itself.
--
-- In order to obtain a profunctor, it turns out that we must make
-- the position functor contravariant, i.e. into a functor not
-- `Type -> Type`, but `op(Type) -> Type`.
--
-- However, that definition by itself requires multiple pieces of
-- other attendant definitions and proof content:  the position
-- functor requires a `contramap`, which must be proven to obey the
-- functor laws, and the natural transformation requires a proof of
-- the naturality condition.
--
-- Furthermore, it is unclear in that definition whether we should
-- consider the resulting profunctor "polynomial", in particular because
-- there is no constraint on the contravariant position functor.
--
-- Thus, we can take a further step and require that the position functor
-- be _Dirichlet_ -- a "contravariant polynomial functor".  This provides
-- an implicit `contramap` which is guaranteed to obey the functor laws,
-- and furthermore provides a notion of Dirichlet natural transformation
-- which is guaranteed to obey the naturality condition.
--
-- It also allows a reduction of some components of the structure,
-- for example to eliminate functions to `Unit`, which are redundant
-- as they can only be the unique morphism to the terminal object.
--
-- Once such reductions are performed, it results in the `PolyProAr`
-- structure below.  This structure specializes to polynomial functors
-- when all the `ppContra`s are `Unit`, and to Dirichlet functors when
-- all the `ppCovar`s are `Void`.  It also corresponds to the notion
-- of a slice polynomial functor where the domain is `Fin(2)` and the
-- codomain is `Fin(1)`, which is isomorphic to just `Type` -- in
-- effect, an uncurried form of the signature of an endoprofunctor on
-- `Type`, i.e. `(Type, Type) -> Type` -- but interpreted so that the
-- first parameter is contravariant.
public export
record PolyProAr where
  constructor PPA
  ppPos : Type
  ppContra : SliceObj ppPos
  ppCovar : SliceObj ppPos

export
InterpPPA : PolyProAr -> ProfunctorSig
InterpPPA (PPA pos contra covar) x y =
  (i : pos ** (x -> contra i, covar i -> y))

export
InterpPPAdimap : (ppa : PolyProAr) -> TypeDimapSig (InterpPPA ppa)
InterpPPAdimap (PPA pos contra covar) s t a b mas mtb (i ** (dx, dy)) =
  (i ** (dx . mas, mtb . dy))
