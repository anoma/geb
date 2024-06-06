module LanguageDef.SlicePolyUMorph

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.InternalCat
import public LanguageDef.SlicePolyCat

------------------------------------------------
------------------------------------------------
---- Universal slice polynomial 2-morphisms ----
------------------------------------------------
------------------------------------------------

-- Here we define universal objects in the category of all slice
-- polynomial functors, where the universal morphisms are
-- 2-morphisms, also known as cells.
--
-- Note that a universal object in the category of slice polynomial
-- functors between some fixed domain and codomain slice categories
-- is a special case of a universal object in the category of all
-- slice polynomial functors, where the vertical sides of the cell
-- are both identities.

------------------------------------------------
------------------------------------------------
---- Limits/colimits of polynomial functors ----
------------------------------------------------
------------------------------------------------

-- Limits and colimits are right and left adjoints respectively to
-- diagonal functors, forming an adjoint triple.
--
-- The following are not limits and colimits within categories of
-- polynomial functors.  Rather, they are limits and colimits within
-- slice categories, but specifically of slice-polynomial _diagrams_
-- (recall that diagrams are simply functors).

public export
SPFDdiagF : (a, b : Type) -> SliceObj b -> SPFData a b
SPFDdiagF a b sb = SPFD sb (\_, _, _ => Void)

public export
InterpSPFDdiagF : (a, b : Type) -> SliceObj b -> SliceFunctor a b
InterpSPFDdiagF a b sb = InterpSPFData $ SPFDdiagF a b sb

public export
InterpSPFDdiagFmap : {a, b : Type} ->
  (sb : SliceObj b) -> SliceFMap (InterpSPFDdiagF a b sb)
InterpSPFDdiagFmap {a} {b} sb = InterpSPFDataMap $ SPFDdiagF a b sb

public export
SPFDdiagToSDF : {a, b : Type} -> (sb : SliceObj b) -> (sa : SliceObj a) ->
  SliceMorphism {a=b} (InterpSPFDdiagF a b sb sa) (SliceDiagF {a} {b} sb sa)
SPFDdiagToSDF {a} {b} sb sa eb = DPair.fst

public export
SPFDdiagFromSDF : {a, b : Type} -> (sb : SliceObj b) -> (sa : SliceObj a) ->
  SliceMorphism {a=b} (SliceDiagF {a} {b} sb sa) (InterpSPFDdiagF a b sb sa)
SPFDdiagFromSDF {a} {b} sb sa eb esb = (esb ** \_, v => void v)

public export
spfdDiagFmap : {a, b : Type} ->
  IntFMapSig (SliceMor b) (SPFnt {dom=a} {cod=b}) (SPFDdiagF a b)
spfdDiagFmap {a} {b} sb sb' m = SPFDm m (\_, _, _, v => void v)

public export
SPFDdiagFSig : (a, b : Type) -> IntFunctorSig (SliceCat b) (SPFDcat a b)
SPFDdiagFSig a b = IFunctor (SPFDdiagF a b) (spfdDiagFmap {a} {b})

public export
SPFDColimit : {a, b : Type} -> SPFData a b -> SliceObj b
SPFDColimit {a} {b} = SliceFColimit {a} {b} . InterpSPFData {dom=a} {cod=b}

public export
spfdColimitMap : {a, b : Type} -> (f, g : SPFData a b) ->
  SPFnt {dom=a} {cod=b} f g ->
  SliceMorphism {a=b} (SPFDColimit f) (SPFDColimit g)
spfdColimitMap {a} {b} f g alpha =
  sliceFColimitMap {a} {b}
    (InterpSPFData f)
    (InterpSPFData g)
    (InterpSPFnt f g alpha)

public export
SPFDColimitFSig : (a, b : Type) -> IntFunctorSig (SPFDcat a b) (SliceCat b)
SPFDColimitFSig a b = IFunctor (SPFDColimit {a} {b}) (spfdColimitMap {a} {b})

public export
SPFDLimit : {a, b : Type} -> SPFData a b -> SliceObj b
SPFDLimit {a} {b} = SliceFLimit {a} {b} . InterpSPFData {dom=a} {cod=b}

public export
spfdLimitMap : {a, b : Type} -> (f, g : SPFData a b) ->
  SPFnt {dom=a} {cod=b} f g ->
  SliceMorphism {a=b} (SPFDLimit f) (SPFDLimit g)
spfdLimitMap {a} {b} f g alpha =
  sliceFLimitMap {a} {b}
    (InterpSPFData f)
    (InterpSPFData g)
    (InterpSPFnt f g alpha)

public export
SPFDLimitFSig : (a, b : Type) -> IntFunctorSig (SPFDcat a b) (SliceCat b)
SPFDLimitFSig a b = IFunctor (SPFDLimit {a} {b}) (spfdLimitMap {a} {b})

public export
SPFDColimitMonad : (a, b : Type) -> SPFData a b -> SPFData a b
SPFDColimitMonad a b = IntAdjMonad {c=(SPFData a b)} {d=(SliceObj b)}
  (SPFDColimit {a} {b}) (SPFDdiagF a b)

public export
SPFDColimitComonad : (a, b : Type) -> SliceEndofunctor b
SPFDColimitComonad a b = IntAdjComonad {c=(SPFData a b)} {d=(SliceObj b)}
  (SPFDColimit {a} {b}) (SPFDdiagF a b)

public export
SPFDLimitMonad : (a, b : Type) -> SliceEndofunctor b
SPFDLimitMonad a b = IntAdjMonad {c=(SliceObj b)} {d=(SPFData a b)}
  (SPFDdiagF a b) (SPFDLimit {a} {b})

public export
SPFDLimitComonad : (a, b : Type) -> SPFData a b -> SPFData a b
SPFDLimitComonad a b = IntAdjComonad {c=(SliceObj b)} {d=(SPFData a b)}
  (SPFDdiagF a b) (SPFDLimit {a} {b})

public export
SPFDColimitUnit : (a, b : Type) ->
  IntAdjUnitSig {c=(SPFData a b)} {d=(SliceObj b)}
    (SPFnt {dom=a} {cod=b}) (SPFDColimit {a} {b}) (SPFDdiagF a b)
SPFDColimitUnit a b f =
  SPFDm
    (\eb, ep => (spfdDir f eb ep ** ep ** \ea, efd => efd))
    (\_, _, _, v => void v)

public export
SPFDColimitCounit : (a, b : Type) ->
  IntAdjCounitSig {c=(SPFData a b)} {d=(SliceObj b)}
    (SliceMor b) (SPFDColimit {a} {b}) (SPFDdiagF a b)
SPFDColimitCounit a b x eb ex = DPair.fst $ DPair.snd ex

public export
SPFDLimitUnit : (a, b : Type) ->
  IntAdjUnitSig {c=(SliceObj b)} {d=(SPFData a b)}
    (SliceMor b) (SPFDdiagF a b) (SPFDLimit {a} {b})
SPFDLimitUnit a b sb eb esb sa = (esb ** \_, v => void v)

public export
SPFDLimitCounit : (a, b : Type) ->
  IntAdjCounitSig {c=(SliceObj b)} {d=(SPFData a b)}
    (SPFnt {dom=a} {cod=b}) (SPFDdiagF a b) (SPFDLimit {a} {b})
SPFDLimitCounit a b (SPFD pos dir) =
  SPFDm
    (\eb, sa => fst $ sa $ \ea => Void)
    (\eb, ep => snd $ ep $ \ea => Void)

public export
SPFDColimitAdjoints : (a, b : Type) ->
  IntAdjointsSig (SliceCat b) (SPFDcat a b)
SPFDColimitAdjoints a b =
  IAdjoints (SPFDColimitFSig a b) (SPFDdiagFSig a b)

public export
SPFDLimitAdjoints : (a, b : Type) ->
  IntAdjointsSig (SPFDcat a b) (SliceCat b)
SPFDLimitAdjoints a b =
  IAdjoints (SPFDdiagFSig a b) (SPFDLimitFSig a b)

public export
SPFDColimitUnits : (a, b : Type) ->
  IntUnitsSig (SPFDColimitAdjoints a b)
SPFDColimitUnits a b = IUnits (SPFDColimitUnit a b) (SPFDColimitCounit a b)

public export
SPFDLimitUnits : (a, b : Type) ->
  IntUnitsSig (SPFDLimitAdjoints a b)
SPFDLimitUnits a b = IUnits (SPFDLimitUnit a b) (SPFDLimitCounit a b)

public export
SPFDColimitAdj : (a, b : Type) ->
  IntAdjunctionSig (SliceCat b) (SPFDcat a b)
SPFDColimitAdj a b =
  IntAdjunctionFromUnits (SPFDColimitAdjoints a b) (SPFDColimitUnits a b)

public export
SPFDLimitAdj : (a, b : Type) ->
  IntAdjunctionSig (SPFDcat a b) (SliceCat b)
SPFDLimitAdj a b =
  IntAdjunctionFromUnits (SPFDLimitAdjoints a b) (SPFDLimitUnits a b)

public export
SPFDLimitColimitTripleAdjoints : (a, b : Type) ->
  IntTripleAdjointsSig (SPFDcat a b) (SliceCat b)
SPFDLimitColimitTripleAdjoints a b =
  ITripleAdjoints
    (SPFDColimitFSig a b)
    (SPFDdiagFSig a b)
    (SPFDLimitFSig a b)

public export
SPFDLimitTripleUnitsSig : (a, b : Type) ->
  ITAUnitsSig (SPFDLimitColimitTripleAdjoints a b)
SPFDLimitTripleUnitsSig a b =
  ITUnits
    (SPFDColimitUnits a b)
    (SPFDLimitUnits a b)

public export
SPFDLimitTripleAdjunctionSig : (a, b : Type) ->
  ITASig (SPFDcat a b) (SliceCat b)
SPFDLimitTripleAdjunctionSig a b =
  ITAFromUnits
    (SPFDLimitColimitTripleAdjoints a b)
    (SPFDLimitTripleUnitsSig a b)
