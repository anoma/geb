module LanguageDef.RQFin

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.QType
import public LanguageDef.InternalCat

%hide Library.IdrisCategories.BaseChangeF

-- Finite sets with explicit refinements (equalizers) and
-- quotients (coequalizers).

------------------------------------
------------------------------------
---- Lawvere theory of booleans ----
------------------------------------
------------------------------------

public export
RQF_LBobj : Type
RQF_LBobj = Nat

--------------------------------------
--------------------------------------
---- Category-generating functors ----
--------------------------------------
--------------------------------------

public export
CSliceObjFMap : (a, b : Type) -> (a -> b) -> CSliceObj a -> CSliceObj b
CSliceObjFMap a b = CSSigma {c=a} {d=b}

-- Given a type of objects, the type on which morphisms depend.
public export
MorBaseType : Type -> Type
MorBaseType = ProductMonad

public export
MorBaseTypeMap : (a, b : Type) -> (a -> b) -> MorBaseType a -> MorBaseType b
MorBaseTypeMap a b = map {f=ProductMonad} {a} {b}

-- Given a type of objects, the type of morphisms.
public export
MorType : Type -> Type
MorType = CSliceObj . MorBaseType

public export
mtMor : {obj : Type} -> (mty : MorType obj) -> Type
mtMor {obj} = CSliceObjDomain {c=(ProductMonad obj)}

public export
mtSig : {obj : Type} -> (mty : MorType obj) -> mtMor mty -> ProductMonad obj
mtSig {obj} = CSliceObjMap {c=(ProductMonad obj)}

public export
mtDom : {obj : Type} -> (mty : MorType obj) -> mtMor mty -> obj
mtDom {obj} mty = Builtin.fst . mtSig {obj} mty

public export
mtCod : {obj : Type} -> (mty : MorType obj) -> mtMor mty -> obj
mtCod {obj} mty = Builtin.snd . mtSig {obj} mty

public export
MorTypeMap : (a, b : Type) -> (a -> b) -> MorType a -> MorType b
MorTypeMap a b =
  CSliceObjFMap (ProductMonad a) (ProductMonad b)
  . MorBaseTypeMap a b

-- The type of object/morphism pairs.
public export
ObjMorType : Type
ObjMorType = Sigma {a=Type} MorType

public export
omtObjType : ObjMorType -> Type
omtObjType = DPair.fst

public export
omtMorType : (omt : ObjMorType) -> MorType (omtObjType omt)
omtMorType = DPair.snd

public export
omtMor : (omt : ObjMorType) -> Type
omtMor omt =
  CSliceObjDomain {c=(ProductMonad (omtObjType omt))} (omtMorType omt)

public export
omtSig : (omt : ObjMorType) -> omtMor omt -> ProductMonad (omtObjType omt)
omtSig omt = CSliceObjMap {c=(ProductMonad (omtObjType omt))} (omtMorType omt)

public export
omtDom : (omt : ObjMorType) -> omtMor omt -> omtObjType omt
omtDom omt = Builtin.fst . omtSig omt

public export
omtCod : (omt : ObjMorType) -> omtMor omt -> omtObjType omt
omtCod omt = Builtin.snd . omtSig omt

-------------------------
-------------------------
---- Terminal object ----
-------------------------
-------------------------

-- There is one (free) terminal object.
public export
RQTermObj : Type
RQTermObj = Unit
