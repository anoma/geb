module Library.IdrisAlgebra

import Library.IdrisUtils
import Library.IdrisCategories

%default total

----------------------------------------
----------------------------------------
---- F-algebra universal properties ----
----------------------------------------
----------------------------------------

------------------------------
---- Initiality in `Type` ----
------------------------------

public export
FAlgEq : {f : Type -> Type} -> {a : Type} -> Algebra f a -> Algebra f a -> Type
FAlgEq {f} a b = ExtEq a b

public export
FAlgIso :
  {f : Type -> Type} -> {fm : {0 a, b : Type} -> (a -> b) -> f a -> f b} ->
  FAlgObj f -> FAlgObj f -> Type
FAlgIso {f} {fm} a b =
  Subset0 (FAlgMorph {fm} a b, FAlgMorph {fm} b a) $
    \(m, m') => ExtInverse (fst0 m) (fst0 m')

public export
IsCandidateInitialFAlg :
  {f : Type -> Type} -> {fm : {0 a, b : Type} -> (a -> b) -> f a -> f b} ->
  FAlgObj f -> Type
IsCandidateInitialFAlg {f} {fm} a = (b : FAlgObj f) -> FAlgMorph {fm} a b

public export
IsUniqueInitialFAlg :
  {f : Type -> Type} -> {fm : {0 a, b : Type} -> (a -> b) -> f a -> f b} ->
  FAlgObj f -> Type
IsUniqueInitialFAlg {f} {fm} a =
  (b : FAlgObj f) -> IsCandidateInitialFAlg {f} {fm} b -> FAlgIso {fm} a b

public export
IsInitialFAlg :
  {f : Type -> Type} -> {fm : {0 a, b : Type} -> (a -> b) -> f a -> f b} ->
  FAlgObj f -> Type
IsInitialFAlg {f} {fm} a =
  (IsCandidateInitialFAlg {f} {fm} a, IsUniqueInitialFAlg {f} {fm} a)

public export
InitialFAlg :
  (f : Type -> Type) -> {fm : {0 a, b : Type} -> (a -> b) -> f a -> f b} ->
  Type
InitialFAlg f {fm} = Subset0 (FAlgObj f) (IsInitialFAlg {f} {fm})

-------------------------------
-------------------------------
---- `Fin` with equalizers ----
-------------------------------
-------------------------------

-- The effect of an equalizer on morphisms between objects of `FinSet`
-- may be viewed as erasing some terms from the domain, so we can represent
-- objects of `FinSet` as lists of booleans, where the length is the
-- cardinality of the underlying set without any equalizers, and the booleans
-- indicate which terms have been erased.

-- Rather than the concrete type `List Bool`, we use algebras of `BinNatF`,
-- thereby requiring only that the type implement the interface of `List Bool`,
-- not that it be `List Bool` precisely.
public export
FSEqObj : Type
FSEqObj = FAlgObj FreeBinNat

public export
freeBinNatMap : {a, b : Type} -> (a -> b) -> FreeBinNat a -> FreeBinNat b
freeBinNatMap = freeMap cataBinNatF

public export
bnAlgFromFreeObj : (alg : FAlgObj FreeBinNat) -> Algebra BinNatF (fst alg)
bnAlgFromFreeObj = FAlgFromFreeObj {f=BinNatF} {fm=map}

public export
bnAlgObjFromFree : FAlgObj FreeBinNat -> FAlgObj BinNatF
bnAlgObjFromFree = FAlgObjFromFree {f=BinNatF} {fm=map}

public export
bnAlgObjToFree : (alg : FAlgObj BinNatF) -> FreeMAlgSig BinNatF (fst alg)
bnAlgObjToFree = FAlgObjToFree {f=BinNatF} cataBinNatF

public export
bnAlgObjToFreeObj : FAlgObj BinNatF -> FAlgObj FreeBinNat
bnAlgObjToFreeObj = FAlgObjToFreeObj {f=BinNatF} cataBinNatF

public export
bnAlgObjToFreeIso : (a : FAlgObj BinNatF) ->
  FAlgIso {f=BinNatF} {fm=Prelude.map}
    (bnAlgObjFromFree (bnAlgObjToFreeObj a)) a
bnAlgObjToFreeIso (a ** m) =
  Element0
    (Element0 id $ \el => case el of NilF => Refl ; ConsF b x => Refl,
     Element0 id $ \el => case el of NilF => Refl ; ConsF b x => Refl)
    (\el => Refl, \el => Refl)
