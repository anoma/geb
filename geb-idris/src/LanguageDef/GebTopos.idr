module LanguageDef.GebTopos

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.Atom
import public LanguageDef.ProgFinSet
import public LanguageDef.PolyCat
import public LanguageDef.Syntax

%default total

public export
FinV : {0 len : Nat} -> SliceObj (Vect len Nat)
FinV [] = ()
FinV [n] = BoundedNat n
FinV (n :: ns@(_ :: _)) = (BoundedNat n, FinV ns)

public export
finVToNatL : {0 len : Nat} -> {v : Vect len Nat} -> FinV v -> List Nat
finVToNatL {len=0} {v=[]} () = []
finVToNatL {len=1} {v=([n])} (Element0 m sat) = [m]
finVToNatL {len=(S (S len))} {v=(n :: ns@(_ :: _))} (Element0 m sat, ms) =
  m :: finVToNatL {len=(S len)} {v=ns} ms

public export
showFinV : {0 len : Nat} -> {v : Vect len Nat} -> FinV v -> String
showFinV = show . finVToNatL

public export
(v : Vect len Nat) => Show (FinV v) where
  show = showFinV

public export
finVEq : {0 len : Nat} -> {v : Vect len Nat} -> (l, l' : FinV v) -> Dec (l = l')
finVEq {len=0} {v=[]} () () = Yes Refl
finVEq {len=1} {v=([n])} (Element0 m sat) (Element0 m' sat') =
  case decEq m m' of
    Yes Refl => rewrite uip {eq=sat} {eq'=sat'} in Yes Refl
    No neq => No $ \eq => case eq of Refl => neq Refl
finVEq {len=(S (S len))} {v=(n :: n' :: ns')}
  (Element0 m sat, ms) (Element0 m' sat', ms') =
    case decEq m m' of
      Yes Refl => case finVEq {len=(S len)} {v=(n' :: ns')} ms ms' of
        Yes Refl => rewrite uip {eq=sat} {eq'=sat'} in Yes Refl
        No neq => No $ \eq => case eq of Refl => neq Refl
      No neq => No $ \eq => case eq of Refl => neq Refl

public export
(v : Vect len Nat) => DecEq (FinV v) where
  decEq = finVEq

public export
record Constructor (0 nty : Nat) where
  constructor Ctor
  numConst : Nat
  cconst : Vect numConst Nat
  numDir : Nat
  cdir : Vect numDir (Fin nty)

public export
showConstr : {0 nty : Nat} -> Constructor nty -> String
showConstr {nty} (Ctor nc cc nd cd) =
  "(" ++ show (map finToNat cd) ++ "," ++ show cc ++ ")"

public export
Show (Constructor nty) where
  show = showConstr

public export
constrEq : {0 nty : Nat} -> (c, c' : Constructor nty) -> Dec (c = c')
constrEq {nty} (Ctor nc cc nd cd) (Ctor nc' cc' nd' cd') =
  case decEq nc nc' of
    Yes Refl => case decEq cc cc' of
      Yes Refl => case decEq nd nd' of
        Yes Refl => case decEq cd cd' of
          Yes Refl => Yes Refl
          No neq => No $ \eq => case eq of Refl => neq Refl
        No neq => No $ \eq => case eq of Refl => neq Refl
      No neq => No $ \eq => case eq of Refl => neq Refl
    No neq => No $ \eq => case eq of Refl => neq Refl

public export
DecEq (Constructor nty) where
  decEq = constrEq

public export
record RecType (0 nty : Nat) where
  constructor RType
  numCtor : Nat
  ctor : Vect numCtor (Constructor nty)

public export
showRecType : {0 nty : Nat} -> RecType nty -> String
showRecType {nty} (RType nc cs) = show cs

public export
Show (RecType nty) where
  show = showRecType

public export
recTypeEq : {0 nty : Nat} -> (ty, ty' : RecType nty) -> Dec (ty = ty')
recTypeEq {nty} (RType nc cs) (RType nc' cs') =
  case decEq nc nc' of
    Yes Refl => case decEq cs cs' of
      Yes Refl => Yes Refl
      No neq => No $ \eq => case eq of Refl => neq Refl
    No neq => No $ \eq => case eq of Refl => neq Refl

public export
DecEq (RecType nty) where
  decEq = recTypeEq

public export
record TypeFamily (0 nty : Nat) where
  constructor TFamily
  rtype : Vect nty (RecType nty)

public export
showTypeFam : {0 nty : Nat} -> TypeFamily nty -> String
showTypeFam {nty} (TFamily rtype) = show rtype

public export
Show (TypeFamily nty) where
  show = showTypeFam

public export
typeFamEq : {0 nty : Nat} -> (tf, tf' : TypeFamily nty) -> Dec (tf = tf')
typeFamEq {nty} (TFamily rt) (TFamily rt') =
  case decEq rt rt' of
    Yes Refl => Yes Refl
    No neq => No $ \eq => case eq of Refl => neq Refl

public export
DecEq (TypeFamily nty) where
  decEq = typeFamEq

public export
tfRtype : {0 nty : Nat} -> TypeFamily nty -> Fin nty -> RecType nty
tfRtype tf i = index i tf.rtype

public export
tfnumCtor : {0 nty : Nat} -> TypeFamily nty -> Fin nty -> Nat
tfnumCtor tf i = (tfRtype tf i).numCtor

public export
tfCtorV : {0 nty : Nat} -> (tf : TypeFamily nty) -> (i : Fin nty) ->
  Vect (tfnumCtor tf i) (Constructor nty)
tfCtorV tf i = (tfRtype tf i).ctor

public export
tfCtor : {0 nty : Nat} -> (tf : TypeFamily nty) -> (i : Fin nty) ->
  Fin (tfnumCtor tf i) -> Constructor nty
tfCtor tf i j = index j (tfCtorV tf i)

public export
tfnumDir : {0 nty : Nat} -> (tf : TypeFamily nty) -> (i : Fin nty) ->
  Fin (tfnumCtor tf i) -> Nat
tfnumDir tf i j = (tfCtor tf i j).numDir

public export
tfDirV : {0 nty : Nat} -> (tf : TypeFamily nty) -> (i : Fin nty) ->
  (j : Fin (tfnumCtor tf i)) -> Vect (tfnumDir tf i j) (Fin nty)
tfDirV tf i j = (tfCtor tf i j).cdir

public export
tfnumConst : {0 nty : Nat} -> (tf : TypeFamily nty) -> (i : Fin nty) ->
  Fin (tfnumCtor tf i) -> Nat
tfnumConst tf i j = (tfCtor tf i j).numConst

public export
tfConstV : {0 nty : Nat} -> (tf : TypeFamily nty) -> (i : Fin nty) ->
  (j : Fin (tfnumCtor tf i)) -> Vect (tfnumConst tf i j) Nat
tfConstV tf i j = (tfCtor tf i j).cconst

public export
InterpTF : {0 nty : Nat} -> TypeFamily nty -> FinSliceEndofunctor nty
InterpTF {nty} tf sl ity =
  (i : Fin (tfnumCtor tf ity) **
   let ct = tfCtor tf ity i in
   (FinV {len=ct.numConst} ct.cconst,
    HVect {k=ct.numDir} $ map sl ct.cdir))

public export
showITF : {0 nty : Nat} ->
  (tf : TypeFamily nty) -> (sl : FinSliceObj nty) ->
  (sh : (i' : Fin nty) -> sl i' -> String) ->
  (i : Fin nty) ->
  InterpTF {nty} tf sl i -> String
showITF {nty} tf sl sh i (j ** (fv, hv)) =
  "(" ++ show j ++ " ** " ++ "(" ++ showFinV fv ++ "," ++
    showHV sl sh (index j (index i tf.rtype).ctor).cdir hv ++ "))"

public export
itfEq : {0 nty : Nat} ->
  (tf : TypeFamily nty) -> (sl : FinSliceObj nty) ->
  (deq : (i' : Fin nty) -> DecEqPred (sl i')) ->
  (i : Fin nty) ->
  (x, x' : InterpTF {nty} tf sl i) -> Dec (x = x')
itfEq {nty} tf sl deq i (j ** (fv, hv)) (j' ** (fv', hv')) =
  case decEq j j' of
    Yes Refl => case finVEq fv fv' of
      Yes eq =>
        case hvDecEq sl deq (tfDirV tf i j') hv hv' of
          Yes Refl => Yes $
            replace
              {p=(\fv'' =>
                (MkDPair j' (fv, hv')) =
                (MkDPair j'
                  {p=(\j'' =>
                    (FinV (tfConstV tf i j''),
                     HVect
                      (map sl ((tfDirV tf i j'')))))}
                      (fv'', hv')))}
              eq Refl
          No neq => No $ \eq => case eq of Refl => neq Refl
      No neq => No $ \eq => case eq of Refl => neq Refl
    No neq => No $ \eq => case eq of Refl => neq Refl

public export
data MuTF : {0 nty : Nat} -> TypeFamily nty -> FinSliceObj nty where
  InTF : {0 nty : Nat} -> {tf : TypeFamily nty} ->
    (i : Fin nty) -> InterpTF {nty} tf (MuTF tf) i -> MuTF tf i

public export
TFAlg : {nty : Nat} -> TypeFamily nty -> FinSliceObj nty -> Type
TFAlg {nty} tf sl = SliceMorphism (InterpTF {nty} tf sl) sl

mutual
  public export
  tfCata : {0 nty : Nat} -> {tf : TypeFamily nty} -> {sl : FinSliceObj nty} ->
    TFAlg tf sl -> SliceMorphism {a=(Fin nty)} (MuTF tf) sl
  tfCata {nty} {tf} {sl} alg i (InTF i (j ** (fv, hv))) =
    alg i
      (j **
       (fv, tfCataV {nty} {tf} {sl} alg (tfnumDir tf i j) (tfDirV tf i j) hv))

  public export
  tfCataV : {0 nty : Nat} -> {tf : TypeFamily nty} -> {sl : FinSliceObj nty} ->
    TFAlg tf sl -> (n : Nat) -> (v : Vect n (Fin nty)) ->
    HVect (map (MuTF tf) v) -> HVect (map sl v)
  tfCataV {nty} {tf} {sl} alg Z [] [] = []
  tfCataV {nty} {tf} {sl} alg (S n) (i :: v) (x :: hv) =
    tfCata {nty} {tf} {sl} alg i x :: tfCataV {nty} {tf} {sl} alg n v hv

public export
ShowMuTFAlg : {nty : Nat} -> (tf : TypeFamily nty) -> TFAlg tf (const String)
ShowMuTFAlg {nty} tf = showITF {nty} tf (const String) (const id)

public export
showMuTF : {nty : Nat} ->
  (tf : TypeFamily nty) -> (i : Fin nty) -> MuTF {nty} tf i -> String
showMuTF {nty} tf = tfCata {nty} {tf} (ShowMuTFAlg {nty} tf)

public export
record Position where
  constructor Pos
  pDirTy : Type
  pDir : List pDirTy

public export
record Arena where
  constructor Ar
  aTy : Type
  aPosIdx : Type
  aPos : aPosIdx -> Position
  aPosTyMap : (i : aPosIdx) -> (aPos i).pDirTy -> aTy
  aAssign : aPosIdx -> aTy

public export
APDirType : (ar : Arena) -> ar.aPosIdx -> Type
APDirType ar i = (ar.aPos i).pDirTy

public export
record SliceArena (domSlice, codSlice : Type) where
  constructor ProdAr
  saTy : codSlice -> Arena
  saAssign : (i : codSlice) -> (saTy i).aTy -> domSlice

public export
SliceEndoArena : Type -> Type
SliceEndoArena base = SliceArena base base

public export
saAr : SliceArena domSlice codSlice -> codSlice -> Arena
saAr sa ci = sa.saTy ci

public export
saPosIdx : SliceArena domSlice codSlice -> codSlice -> Type
saPosIdx sa ci = (saAr sa ci).aPosIdx

public export
saPos : (sa : SliceArena domSlice codSlice) ->
  (ci : codSlice) -> saPosIdx sa ci -> Position
saPos sa ci pi = (saAr sa ci).aPos pi

public export
saDirTy : (sa : SliceArena domSlice codSlice) ->
  (ci : codSlice) -> saPosIdx sa ci -> Type
saDirTy sa ci pi = (saPos sa ci pi).pDirTy

public export
saDir :
  (sa : SliceArena domSlice codSlice) -> (ci : codSlice) ->
  (pi : saPosIdx sa ci) -> List (saDirTy sa ci pi)
saDir sa ci pi = (saPos sa ci pi).pDir

public export
saDirIdx :
  (sa : SliceArena domSlice codSlice) -> (ci : codSlice) ->
  (pi : saPosIdx sa ci) -> Type
saDirIdx sa ci pi = (i : Nat ** InBounds i (saDir sa ci pi))

public export
sapAssign : (sa : SliceArena domSlice codSlice) -> (ci : codSlice) ->
  (pi : saPosIdx sa ci) -> saDirTy sa ci pi -> domSlice
sapAssign sa ci pi = sa.saAssign ci . (saTy sa ci).aPosTyMap pi

public export
SAInterpPoly : {domSlice : Type} -> {0 codSlice : Type} ->
  SliceArena domSlice codSlice -> SliceFunctor domSlice codSlice
SAInterpPoly sa ds ci =
  (pi : saPosIdx sa ci ** piDir : List (Sigma {a=domSlice} ds) **
   map fst piDir = map (sapAssign sa ci pi) (saDir sa ci pi))

public export
saInterpPolyMap : {domSlice : Type} -> {0 codSlice : Type} ->
  (sa : SliceArena domSlice codSlice) ->
  {ds, ds' : SliceObj domSlice} ->
  SliceMorphism ds ds' ->
  SliceMorphism (SAInterpPoly sa ds) (SAInterpPoly sa ds')
saInterpPolyMap {domSlice} {codSlice} sa {ds} {ds'} m ci (pi ** piDir ** eq) =
  (pi ** smMap m piDir ** trans (smMapFstEq m piDir) eq)

public export
SAInterpDirich : {domSlice : Type} -> {codSlice : Type} ->
  SliceArena domSlice codSlice -> SliceFunctor domSlice codSlice
SAInterpDirich {domSlice} {codSlice} sa ds ci =
  (pi : saPosIdx sa ci **
   piDir : Sigma {a=domSlice} ds -> saDirIdx sa ci pi **
   (di : domSlice) -> (dd : ds di) ->
    sapAssign
      sa ci pi (index (fst (piDir (di ** dd))) {ok=(snd (piDir (di ** dd)))}
      (saDir sa ci pi)) =
    di)

public export
saInterpDirichMap : {domSlice : Type} -> {0 codSlice : Type} ->
  (sa : SliceArena domSlice codSlice) ->
  {ds, ds' : SliceObj domSlice} ->
  SliceMorphism ds ds' ->
  SliceMorphism (SAInterpDirich sa ds') (SAInterpDirich sa ds)
saInterpDirichMap {domSlice} {codSlice} sa {ds} {ds'} m ci (pi ** piDir ** eq) =
  (pi ** piDir . smApp m ** \di, dd => eq di (m di dd))

public export
SAAlg : {base : Type} -> SliceEndoArena base -> SliceObj base -> Type
SAAlg {base} sa s = SliceMorphism {a=base} (SAInterpPoly sa s) s

public export
data SAInterpMu : {0 base : Type} -> SliceEndoArena base -> SliceObj base where
  InSAM :
    {0 base : Type} -> {0 sa : SliceEndoArena base} ->
    SAAlg {base} sa (SAInterpMu sa)

------------------------------------------------------------------
------------------------------------------------------------------
---- Experiments with subobject classifiers and power objects ----
------------------------------------------------------------------
------------------------------------------------------------------

-- A type together with a term of that type.
public export
SubCFromType : Type
SubCFromType = Exists0 Type (\ty => ty)

public export
PowerObjFromType : Type -> Type
PowerObjFromType a = Exists0 (SliceObj a) (\sl => (x : a) -> sl x)

public export
CharToPowerFromType : {0 a : Type} -> (a -> SubCFromType) -> PowerObjFromType a
CharToPowerFromType chi = Evidence0 (fst0 . chi) (\x => snd0 (chi x))

public export
PowerToCharFromType : {0 a : Type} -> PowerObjFromType a -> (a -> SubCFromType)
PowerToCharFromType po e = Evidence0 (fst0 po e) (snd0 po e)

public export
TrueFromType : () -> SubCFromType
TrueFromType () = Evidence0 (Unit, Unit) ((), ())

-- Produce the characteristic function of `Equalizer f g`.
public export
ChiForType : {0 a, b : Type} -> (f, g : a -> b) -> (a -> SubCFromType)
ChiForType {a} {b} f g ea = Evidence0 (b, b) (f ea, g ea)

public export
ChiForTypeToPb :
  (subCmereProp : {p, p' : SubCFromType} -> p = p') ->
  {0 a, b : Type} -> (f, g : a -> b) ->
  Equalizer f g ->
  Pullback {a} {b=Unit} {c=SubCFromType} (ChiForType f g) TrueFromType
ChiForTypeToPb subCmereProp {a} {b} f g (Element0 eeq eq) =
  Element0 (eeq, ()) subCmereProp

public export
ChiForTypeFromPb : {0 a, b : Type} -> (f, g : a -> b) ->
  Pullback {a} {b=Unit} {c=SubCFromType} (ChiForType f g) TrueFromType ->
  Equalizer f g
ChiForTypeFromPb {a} {b} f g (Element0 (ea, ()) eq) =
  Element0 ea $ case exists0inj1 eq of
    Refl =>
      let eq2 = exists0inj2 eq in
      rewrite fstEq eq2 in
      rewrite sndEq eq2 in
      Refl

public export
SubCFromBoolPred : Type
SubCFromBoolPred = Exists0 Type (\ty => ty -> Bool)

public export
PowerObjFromBoolPred : Type -> Type
PowerObjFromBoolPred a = Exists0 (SliceObj a) (\ty => Sigma {a} ty -> Bool)

public export
CharToPowerFromBoolPred : {0 a : Type} ->
  (a -> SubCFromBoolPred) -> PowerObjFromBoolPred a
CharToPowerFromBoolPred chi =
  Evidence0 (fst0 . chi) (\x => snd0 (chi (fst x)) (snd x))

public export
PowerToCharFromBoolPred : {0 a : Type} -> PowerObjFromBoolPred a ->
  (a -> SubCFromBoolPred)
PowerToCharFromBoolPred po e =
  Evidence0 (fst0 po e) (\edp => snd0 po (e ** edp))

public export
TrueFromBoolPred : () -> SubCFromBoolPred
TrueFromBoolPred () =
  Evidence0 ((Bool, Bool) -> Bool) (\decrel => decrel (True, True))

-- Produce the characteristic function of `Equalizer f g`.
public export
ChiForBoolPred : {0 a, b : Type} -> (f, g : a -> b) -> (a -> SubCFromBoolPred)
ChiForBoolPred {a} {b} f g ea =
  Evidence0 ((b, b) -> Bool) (\decrel => decrel (f ea, g ea))

public export
ChiForBoolPredToPb :
  (subCmereProp : (ty, ty' : Type) -> (x : ty) -> (x' : ty') ->
    Evidence0 {type=Type} {this=(\ty'' => ty'' -> Bool)}
      ((ty, ty) -> Bool)
      (\decrel : ((ty, ty) -> Bool) => decrel (x, x))
    ~=~
    Evidence0 {type=Type} {this=(\ty'' => ty'' -> Bool)}
      ((ty', ty') -> Bool)
      (\decrel : ((ty', ty') -> Bool) => decrel (x', x'))) ->
  {0 a, b : Type} -> (f, g : a -> b) ->
  Equalizer f g ->
  Pullback
    {a} {b=Unit} {c=SubCFromBoolPred} (ChiForBoolPred f g) TrueFromBoolPred
ChiForBoolPredToPb subCmereProp {a} {b} f g (Element0 ea eq) =
  Element0 (ea, ()) $ rewrite eq in subCmereProp b Bool _ True

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
---- Subobject classifiers for monics only (and those from equalizers only) ----
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

public export
0 SubCFromEq : Type
SubCFromEq = Exists0 Type (\ty => (ty, ty))

public export
0 PowerObjFromEq : Type -> Type
PowerObjFromEq a = Exists0 (SliceObj a) (\sl => (Pi sl, Pi sl))

public export
CharToPowerFromEq : {0 a : Type} -> (a -> SubCFromEq) -> PowerObjFromEq a
CharToPowerFromEq chi =
  Evidence0 (fst0 . chi) (\x => fst (snd0 (chi x)), \x => snd (snd0 (chi x)))

public export
PowerToCharFromEq : {0 a : Type} -> PowerObjFromEq a -> (a -> SubCFromEq)
PowerToCharFromEq {a} po ea =
  Evidence0 (fst0 po ea) (fst (snd0 po) ea, snd (snd0 po) ea)

public export
TrueFromEq : () -> SubCFromEq
TrueFromEq () = Evidence0 Unit ((), ())

-- Produce the characteristic function of `Equalizer f g`.
public export
ChiForEq : {0 a, b : Type} -> (f, g : a -> b) -> (a -> SubCFromEq)
ChiForEq {a} {b} f g ea = Evidence0 b (f ea, g ea)

public export
ChiForEqToPb :
  (subCmereProp :
    {p, p' : SubCFromEq} ->
    fst (snd0 p) = snd (snd0 p) ->
    fst (snd0 p') = snd (snd0 p') ->
    p = p') ->
  {0 a, b : Type} -> (f, g : a -> b) ->
  Equalizer f g ->
  Pullback {a} {b=Unit} {c=SubCFromEq} (ChiForEq f g) TrueFromEq
ChiForEqToPb subCmereProp {a} {b} f g (Element0 eeq eq) =
  Element0 (eeq, ()) (subCmereProp eq Refl)

public export
ChiForEqFromPb : {0 a, b : Type} -> (f, g : a -> b) ->
  Pullback {a} {b=Unit} {c=SubCFromEq} (ChiForEq f g) TrueFromEq ->
  Equalizer f g
ChiForEqFromPb {a} {b} f g (Element0 (ea, ()) eq) =
  Element0 ea $ case exists0inj1 eq of
    Refl =>
      let eq2 = exists0inj2 eq in
      rewrite fstEq eq2 in
      rewrite sndEq eq2 in
      Refl

public export
ChiForEqTrueCorrect :
  (subCmereProp :
    {p, p' : SubCFromEq} ->
    fst (snd0 p) = snd (snd0 p) ->
    fst (snd0 p') = snd (snd0 p') ->
    p = p') ->
  {0 a, b : Type} -> (f, g : a -> b) ->
  (x : a) -> (eq : f x = g x) ->
  ChiForEq f g x = TrueFromEq ()
ChiForEqTrueCorrect subCmereProp f g x eq = subCmereProp eq Refl

public export
ChiForEqFalseCorrect :
  {a, b : Type} -> (f, g : a -> b) ->
  (x : a) -> Not (f x = g x) ->
  Not (ChiForEq f g x = TrueFromEq ())
ChiForEqFalseCorrect f g x neq eq with (exists0inj1 eq)
  ChiForEqFalseCorrect f g x neq eq | Refl =
      neq $
        let eq2 = exists0inj2 eq in
        rewrite fstEq eq2 in
        rewrite sndEq eq2 in
        Refl

---------------------------------------------------------------
---------------------------------------------------------------
---- Categories internal to 'Type' as a well-pointed topos ----
---------------------------------------------------------------
---------------------------------------------------------------

public export
record TCatSig where
  constructor TCat
  tcObj : Type
  0 tcObjEq : tcObj -> tcObj -> Type
  0 tcObjEqRefl : (0 a : tcObj) -> tcObjEq a a
  0 tcObjEqSym : {0 a, b : tcObj} ->
    (0 _ : tcObjEq a b) -> tcObjEq b a
  0 tcObjEqTrans : {0 a, b, c : tcObj} ->
    (0 _ : tcObjEq b c) -> (0 _ : tcObjEq a b) -> tcObjEq a c
  tcMorph : tcObj -> tcObj -> Type
  0 tcMorphEq : {0 dom, cod, dom', cod' : tcObj} ->
    (0 _ : tcObjEq dom dom') -> (0 _ : tcObjEq cod cod') ->
    (0 _ : tcMorph dom cod) -> (0 _ : tcMorph dom' cod') -> Type
  0 tcMorphEqRefl : {0 dom, cod : tcObj} ->
    (0 domeq : tcObjEq dom dom) -> (0 codeq : tcObjEq cod cod) ->
    (0 m : tcMorph dom cod) -> tcMorphEq domeq codeq m m
  0 tcMorphEqSym : {0 dom, cod, dom', cod' : tcObj} ->
    {0 domeq : tcObjEq dom dom'} -> {0 codeq : tcObjEq cod cod'} ->
    {0 domeqsym : tcObjEq dom' dom} -> {0 codeqsym : tcObjEq cod' cod} ->
    (0 m : tcMorph dom cod) -> (0 m' : tcMorph dom' cod') ->
    (0 _ : tcMorphEq domeq codeq m m') -> tcMorphEq domeqsym codeqsym m' m
  0 tcMorphEqTrans : {0 dom, cod, dom', cod', dom'', cod'' : tcObj} ->
    {0 domeq : tcObjEq dom dom'} -> {0 codeq : tcObjEq cod cod'} ->
    {0 domeq' : tcObjEq dom' dom''} -> {0 codeq' : tcObjEq cod' cod''} ->
    {0 domeq'' : tcObjEq dom dom''} -> {0 codeq'' : tcObjEq cod cod''} ->
    (0 m : tcMorph dom cod) -> (0 m' : tcMorph dom' cod') ->
    (0 m'' : tcMorph dom'' cod'') ->
    (0 m''' : tcMorph dom'' cod'') ->
    (0 _ : tcMorphEq domeq' codeq' m' m'') ->
    (0 _ : tcMorphEq domeq codeq m m') ->
    tcMorphEq domeq'' codeq'' m m''
  tcId : (obj : tcObj) -> tcMorph obj obj
  tcCompose : {0 a, b, b', c : tcObj} ->
    (0 _ : tcObjEq b b') ->
    tcMorph b' c -> tcMorph a b -> tcMorph a c
  0 tcIdLeft : {0 a, b, b' : tcObj} ->
    {0 domeq : tcObjEq a a} -> {0 codeq, codeq' : tcObjEq b b'} ->
    (0 m : tcMorph a b) ->
    tcMorphEq {dom=a} {cod=b} {dom'=a} {cod'=b'}
      domeq codeq m (tcCompose {a} {b} {b'} {c=b'} codeq' (tcId b') m)
  0 tcIdRight : {0 a, a', b : tcObj} ->
    {0 domeq, domeq' : tcObjEq a a'} -> {0 codeq : tcObjEq b b} ->
    (0 m : tcMorph a' b) ->
    tcMorphEq {dom=a} {cod=b} {dom'=a'} {cod'=b}
      domeq codeq (tcCompose {a} {b=a} {b'=a'} {c=b} domeq' m (tcId a)) m
  0 tcComposeAssoc : {0 a, b, b', c, c', d : tcObj} ->
    {0 domeq : tcObjEq a a} -> {0 codeq : tcObjEq d d} ->
    {0 beq, beq' : tcObjEq b b'} -> {0 ceq, ceq' : tcObjEq c c'} ->
    (0 h : tcMorph c' d) -> (0 g : tcMorph b' c) -> (0 f : tcMorph a b) ->
    tcMorphEq {dom=a} {cod=d}
      domeq codeq
      (tcCompose ceq h (tcCompose beq' g f))
      (tcCompose beq (tcCompose ceq' h g) f)

public export
record TFunctorSig (c, d : TCatSig) where
  constructor TFunctor
  tfObjMap : c.tcObj -> d.tcObj
  0 tfObjMapCorrect : {0 a, b : c.tcObj} ->
    (0 _ : c.tcObjEq a b) -> d.tcObjEq (tfObjMap a) (tfObjMap b)
  tfMorphMap : {0 a, b : c.tcObj} ->
    c.tcMorph a b -> d.tcMorph (tfObjMap a) (tfObjMap b)
  0 tfMorphMapCorrect : {0 a, b, a', b' : c.tcObj} ->
    {0 m : c.tcMorph a b} -> {0 m' : c.tcMorph a' b'} ->
    (0 domeq : c.tcObjEq a a') -> (0 codeq : c.tcObjEq b b') ->
    (0 domMapEq : d.tcObjEq (tfObjMap a) (tfObjMap a')) ->
    (0 codMapEq : d.tcObjEq (tfObjMap b) (tfObjMap b')) ->
    (0 _ : c.tcMorphEq {dom=a} {dom'=a'} {cod=b} {cod'=b'} domeq codeq m m') ->
    d.tcMorphEq
      {dom=(tfObjMap a)} {cod=(tfObjMap b)}
      {dom'=(tfObjMap a')} {cod'=(tfObjMap b')}
      domMapEq codMapEq
      (tfMorphMap {a} {b} m) (tfMorphMap {a=a'} {b=b'} m')

-------------------------
-------------------------
---- Terminal object ----
-------------------------
-------------------------

-------------------------
-------------------------
---- Finite products ----
-------------------------
-------------------------

--------------------------------
--------------------------------
---- Natural-numbers object ----
--------------------------------
--------------------------------

-------------------------------------------------
-------------------------------------------------
---- Geb s-expressions as polynomial functor ----
-------------------------------------------------
-------------------------------------------------

public export
data GWExpSlice : Type where
  GSATOM : GWExpSlice
  GSNAT : GWExpSlice
  GSNATL : GWExpSlice
  GSEXP : GWExpSlice
  GSEXPL : GWExpSlice

public export
gSliceAtom : GWExpSlice -> GebAtom
gSliceAtom GSATOM = SL_ATOM
gSliceAtom GSNAT = SL_NAT
gSliceAtom GSNATL = SL_NATL
gSliceAtom GSEXP = SL_EXP
gSliceAtom GSEXPL = SL_EXPL

public export
Show GWExpSlice where
  show = show . gSliceAtom

public export
GSliceSz : Nat
GSliceSz = 5

public export
GSliceFinDecoder : FinDecoder GWExpSlice GSliceSz
GSliceFinDecoder FZ = GSATOM
GSliceFinDecoder (FS FZ) = GSNAT
GSliceFinDecoder (FS (FS FZ)) = GSNATL
GSliceFinDecoder (FS (FS (FS FZ))) = GSEXP
GSliceFinDecoder (FS (FS (FS (FS FZ)))) = GSEXPL

public export
GSliceNatEncoder : NatEncoder GSliceFinDecoder
GSliceNatEncoder GSATOM = (0 ** Refl ** Refl)
GSliceNatEncoder GSNAT =  (1 ** Refl ** Refl)
GSliceNatEncoder GSNATL = (2 ** Refl ** Refl)
GSliceNatEncoder GSEXP = (3 ** Refl ** Refl)
GSliceNatEncoder GSEXPL = (4 ** Refl ** Refl)

public export
GSliceFinDecEncoding : FinDecEncoding GWExpSlice GSliceSz
GSliceFinDecEncoding = NatDecEncoding GSliceFinDecoder GSliceNatEncoder

public export
DecEq GWExpSlice where
  decEq = fdeDecEq GSliceFinDecEncoding

public export
data GWExpNonAtomPos : Type where
  GPNAZ : GWExpNonAtomPos -- zero
  GPNAS : GWExpNonAtomPos -- successor
  GPNAX : GWExpNonAtomPos -- SExp
  GPNANN : GWExpNonAtomPos -- empty list of Nat
  GPNANC : GWExpNonAtomPos -- cons list of Nat
  GPNAXN : GWExpNonAtomPos -- empty list of SExp
  GPNAXC : GWExpNonAtomPos -- cons list of SExp

public export
data GWExpPos : Type where
  GPA : GebAtom -> GWExpPos
  GPNAP : GWExpNonAtomPos -> GWExpPos

public export
GPZ : GWExpPos
GPZ = GPNAP GPNAZ

public export
GPS : GWExpPos
GPS = GPNAP GPNAS

public export
GPX : GWExpPos
GPX = GPNAP GPNAX

public export
GPNN : GWExpPos
GPNN = GPNAP GPNANN

public export
GPNC : GWExpPos
GPNC = GPNAP GPNANC

public export
GPXN : GWExpPos
GPXN = GPNAP GPNAXN

public export
GPXC : GWExpPos
GPXC = GPNAP GPNAXC

public export
gNonAtomPosAtom : GWExpNonAtomPos -> GebAtom
gNonAtomPosAtom GPNAZ = POS_Z
gNonAtomPosAtom GPNAS = POS_S
gNonAtomPosAtom GPNAX = POS_X
gNonAtomPosAtom GPNANN = POS_NN
gNonAtomPosAtom GPNANC = POS_NC
gNonAtomPosAtom GPNAXN = POS_XN
gNonAtomPosAtom GPNAXC = POS_XC

public export
gPosAtom : GWExpPos -> GebAtom
gPosAtom (GPA a) = a
gPosAtom (GPNAP i) = gNonAtomPosAtom i

public export
Show GWExpPos where
  show = show . gPosAtom

public export
GPosSz : Nat
GPosSz = 7

public export
GPosFinDecoder : FinDecoder GWExpNonAtomPos GPosSz
GPosFinDecoder FZ = GPNAZ
GPosFinDecoder (FS FZ) = GPNAS
GPosFinDecoder (FS (FS FZ)) = GPNAX
GPosFinDecoder (FS (FS (FS FZ))) = GPNANN
GPosFinDecoder (FS (FS (FS (FS FZ)))) = GPNANC
GPosFinDecoder (FS (FS (FS (FS (FS FZ))))) = GPNAXN
GPosFinDecoder (FS (FS (FS (FS (FS (FS FZ)))))) = GPNAXC

public export
GPosNatEncoder : NatEncoder GPosFinDecoder
GPosNatEncoder GPNAZ = (0 ** Refl ** Refl)
GPosNatEncoder GPNAS = (1 ** Refl ** Refl)
GPosNatEncoder GPNAX = (2 ** Refl ** Refl)
GPosNatEncoder GPNANN = (3 ** Refl ** Refl)
GPosNatEncoder GPNANC = (4 ** Refl ** Refl)
GPosNatEncoder GPNAXN = (5 ** Refl ** Refl)
GPosNatEncoder GPNAXC = (6 ** Refl ** Refl)

public export
GPosFinDecEncoding : FinDecEncoding GWExpNonAtomPos GPosSz
GPosFinDecEncoding = NatDecEncoding GPosFinDecoder GPosNatEncoder

public export
DecEq GWExpNonAtomPos where
  decEq = fdeDecEq GPosFinDecEncoding

public export
DecEq GWExpPos where
  decEq (GPA a) (GPA a') = case decEq a a' of
    Yes Refl => Yes Refl
    No neq => No $ \Refl => neq Refl
  decEq (GPA _) (GPNAP _) = No $ \eq => case eq of Refl impossible
  decEq (GPNAP _) (GPA _) = No $ \eq => case eq of Refl impossible
  decEq (GPNAP i) (GPNAP i') = case decEq i i' of
    Yes Refl => Yes Refl
    No neq => No $ \Refl => neq Refl

public export
data GWExpDir : Type where
  GDS : GWExpDir
  GDXA : GWExpDir
  GDXNL : GWExpDir
  GDXXL : GWExpDir
  GDNCHD : GWExpDir
  GDNCTL : GWExpDir
  GDXCHD : GWExpDir
  GDXCTL : GWExpDir

public export
gDirAtom : GWExpDir -> GebAtom
gDirAtom GDS = DIR_S
gDirAtom GDXA = DIR_XA
gDirAtom GDXNL = DIR_XNL
gDirAtom GDXXL = DIR_XXL
gDirAtom GDNCHD = DIR_NCHD
gDirAtom GDNCTL = DIR_NCTL
gDirAtom GDXCHD = DIR_XCHD
gDirAtom GDXCTL = DIR_XCTL

public export
Show GWExpDir where
  show = show . gDirAtom

public export
GDirSz : Nat
GDirSz = 8

public export
GDirFinDecoder : FinDecoder GWExpDir GDirSz
GDirFinDecoder FZ = GDS
GDirFinDecoder (FS FZ) = GDXA
GDirFinDecoder (FS (FS FZ)) = GDXNL
GDirFinDecoder (FS (FS (FS FZ))) = GDXXL
GDirFinDecoder (FS (FS (FS (FS FZ)))) = GDNCHD
GDirFinDecoder (FS (FS (FS (FS (FS FZ))))) = GDNCTL
GDirFinDecoder (FS (FS (FS (FS (FS (FS FZ)))))) = GDXCHD
GDirFinDecoder (FS (FS (FS (FS (FS (FS (FS FZ))))))) = GDXCTL

public export
GDirNatEncoder : NatEncoder GDirFinDecoder
GDirNatEncoder GDS = (0 ** Refl ** Refl)
GDirNatEncoder GDXA = (1 ** Refl ** Refl)
GDirNatEncoder GDXNL = (2 ** Refl ** Refl)
GDirNatEncoder GDXXL = (3 ** Refl ** Refl)
GDirNatEncoder GDNCHD = (4 ** Refl ** Refl)
GDirNatEncoder GDNCTL = (5 ** Refl ** Refl)
GDirNatEncoder GDXCHD = (6 ** Refl ** Refl)
GDirNatEncoder GDXCTL = (7 ** Refl ** Refl)

public export
GDirFinDecEncoding : FinDecEncoding GWExpDir GDirSz
GDirFinDecEncoding = NatDecEncoding GDirFinDecoder GDirNatEncoder

public export
DecEq GWExpDir where
  decEq = fdeDecEq GDirFinDecEncoding

public export
gAssign : GWExpDir -> GWExpSlice
gAssign GDS = GSNAT
gAssign GDXA = GSATOM
gAssign GDXNL = GSNATL
gAssign GDXXL = GSEXPL
gAssign GDNCHD = GSNAT
gAssign GDNCTL = GSNATL
gAssign GDXCHD = GSEXP
gAssign GDXCTL = GSEXPL

public export
gDirSlice : GWExpDir -> GWExpPos
gDirSlice GDS = GPS
gDirSlice GDXA = GPX
gDirSlice GDXNL = GPX
gDirSlice GDXXL = GPX
gDirSlice GDNCHD = GPNC
gDirSlice GDNCTL = GPNC
gDirSlice GDXCHD = GPXC
gDirSlice GDXCTL = GPXC

public export
gNonAtomPosSlice : GWExpNonAtomPos -> GWExpSlice
gNonAtomPosSlice GPNAZ = GSNAT
gNonAtomPosSlice GPNAS = GSNAT
gNonAtomPosSlice GPNAX = GSEXP
gNonAtomPosSlice GPNANN = GSNATL
gNonAtomPosSlice GPNANC = GSNATL
gNonAtomPosSlice GPNAXN = GSEXPL
gNonAtomPosSlice GPNAXC = GSEXPL

public export
gPosSlice : GWExpPos -> GWExpSlice
gPosSlice (GPA _) = GSATOM
gPosSlice (GPNAP i) = gNonAtomPosSlice i

public export
GWExpWTF : WTypeEndoFunc GWExpSlice
GWExpWTF = MkWTF GWExpPos GWExpDir gAssign gDirSlice gPosSlice

public export
GWExpSPF : SlicePolyEndoFunc GWExpSlice
GWExpSPF = WTFtoSPF GWExpWTF

public export
GWExpWT : SliceObj GWExpSlice
GWExpWT = SPFMu GWExpSPF

public export
GWExpSigma : Type
GWExpSigma = Sigma {a=GWExpSlice} GWExpWT

public export
GWExpA : Type
GWExpA = GWExpWT GSATOM

public export
GWExpN : Type
GWExpN = GWExpWT GSNAT

public export
GWExpNL : Type
GWExpNL = GWExpWT GSNATL

public export
GWExpX : Type
GWExpX = GWExpWT GSEXP

public export
GWExpXL : Type
GWExpXL = GWExpWT GSEXPL

public export
record GWExpAlg (sa : GWExpSlice -> Type) where
  constructor GAlg
  galgA : GebAtom -> sa GSATOM
  galgZ : sa GSNAT
  galgS : sa GSNAT -> sa GSNAT
  galgNN : sa GSNATL
  galgNC : sa GSNAT -> sa GSNATL -> sa GSNATL
  galgEXP : sa GSATOM -> sa GSNATL -> sa GSEXPL -> sa GSEXP
  galgXN : sa GSEXPL
  galgXC : sa GSEXP -> sa GSEXPL -> sa GSEXPL

public export
GAlgToSPF : {sa : GWExpSlice -> Type} -> GWExpAlg sa -> SPFAlg GWExpSPF sa
GAlgToSPF alg GSATOM (Element0 (GPA a) isl ** d) =
  alg.galgA a
GAlgToSPF alg GSATOM (Element0 (GPNAP GPNAZ) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSATOM (Element0 (GPNAP GPNAS) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSATOM (Element0 (GPNAP GPNAX) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSATOM (Element0 (GPNAP GPNANN) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSATOM (Element0 (GPNAP GPNANC) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSATOM (Element0 (GPNAP GPNAXN) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSATOM (Element0 (GPNAP GPNAXC) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNAT (Element0 (GPA a) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNAT (Element0 (GPNAP GPNAZ) isl ** d) =
  alg.galgZ
GAlgToSPF alg GSNAT (Element0 (GPNAP GPNAS) isl ** d) =
  alg.galgS $ d (Element0 GDS Refl)
GAlgToSPF alg GSNAT (Element0 (GPNAP GPNAX) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNAT (Element0 (GPNAP GPNANN) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNAT (Element0 (GPNAP GPNANC) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNAT (Element0 (GPNAP GPNAXN) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNAT (Element0 (GPNAP GPNAXC) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNATL (Element0 (GPA a) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNATL (Element0 (GPNAP GPNAZ) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNATL (Element0 (GPNAP GPNAS) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNATL (Element0 (GPNAP GPNAX) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNATL (Element0 (GPNAP GPNANN) isl ** d) =
  alg.galgNN
GAlgToSPF alg GSNATL (Element0 (GPNAP GPNANC) isl ** d) =
  alg.galgNC (d $ Element0 GDNCHD Refl) (d $ Element0 GDNCTL Refl)
GAlgToSPF alg GSNATL (Element0 (GPNAP GPNAXN) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNATL (Element0 (GPNAP GPNAXC) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXP (Element0 (GPA a) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXP (Element0 (GPNAP GPNAZ) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXP (Element0 (GPNAP GPNAS) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXP (Element0 (GPNAP GPNAX) isl ** d) =
  alg.galgEXP
    (d $ Element0 GDXA Refl) (d $ Element0 GDXNL Refl) (d $ Element0 GDXXL Refl)
GAlgToSPF alg GSEXP (Element0 (GPNAP GPNANN) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXP (Element0 (GPNAP GPNANC) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXP (Element0 (GPNAP GPNAXN) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXP (Element0 (GPNAP GPNAXC) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXPL (Element0 (GPA a) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXPL (Element0 (GPNAP GPNAZ) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXPL (Element0 (GPNAP GPNAS) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXPL (Element0 (GPNAP GPNAX) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXPL (Element0 (GPNAP GPNANN) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXPL (Element0 (GPNAP GPNANC) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXPL (Element0 (GPNAP GPNAXN) isl ** d) =
  alg.galgXN
GAlgToSPF alg GSEXPL (Element0 (GPNAP GPNAXC) isl ** d) =
  alg.galgXC (d $ Element0 GDXCHD Refl) (d $ Element0 GDXCTL Refl)

public export
gwexpCata : {sa : GWExpSlice -> Type} ->
  GWExpAlg sa -> SliceMorphism {a=GWExpSlice} GWExpWT sa
gwexpCata {sa} alg = spfCata {spf=GWExpSPF} {sa} (GAlgToSPF {sa} alg)

public export
GWExpWTtoGExpAlgSl : SliceObj GWExpSlice
GWExpWTtoGExpAlgSl GSATOM = GebAtom
GWExpWTtoGExpAlgSl GSNAT = Nat
GWExpWTtoGExpAlgSl GSNATL = List Nat
GWExpWTtoGExpAlgSl GSEXP = GExp
GWExpWTtoGExpAlgSl GSEXPL = GList

public export
GWExpWTtoGExpAlg : GWExpAlg GWExpWTtoGExpAlgSl
GWExpWTtoGExpAlg = GAlg id 0 S [] (::) InS [] (::)

public export
gwexpWTtoGExpSl : SliceMorphism {a=GWExpSlice} GWExpWT GWExpWTtoGExpAlgSl
gwexpWTtoGExpSl = gwexpCata GWExpWTtoGExpAlg

public export
gwexpWTtoGExp : GWExpX -> GExp
gwexpWTtoGExp = gwexpWTtoGExpSl GSEXP

public export
Show GWExpX where
  show = show . gwexpWTtoGExp

public export
InGA : GebAtom -> GWExpA
InGA a = InSPFM (GSATOM ** Element0 (GPA a) Refl) $ \(Element0 d dsl) =>
  case d of
    GDS => void $ case dsl of Refl impossible
    GDXA => void $ case dsl of Refl impossible
    GDXNL => void $ case dsl of Refl impossible
    GDXXL => void $ case dsl of Refl impossible
    GDNCHD => void $ case dsl of Refl impossible
    GDNCTL => void $ case dsl of Refl impossible
    GDXCHD => void $ case dsl of Refl impossible
    GDXCTL => void $ case dsl of Refl impossible

public export
InGZ : GWExpN
InGZ = InSPFM (GSNAT ** Element0 GPZ Refl) $ \(Element0 d dsl) =>
  case d of
    GDS => void $ case dsl of Refl impossible
    GDXA => void $ case dsl of Refl impossible
    GDXNL => void $ case dsl of Refl impossible
    GDXXL => void $ case dsl of Refl impossible
    GDNCHD => void $ case dsl of Refl impossible
    GDNCTL => void $ case dsl of Refl impossible
    GDXCHD => void $ case dsl of Refl impossible
    GDXCTL => void $ case dsl of Refl impossible

public export
InGS : GWExpN -> GWExpN
InGS n = InSPFM (GSNAT ** Element0 GPS Refl) $ \(Element0 d dsl) =>
  case d of
    GDS => n
    GDXA => void $ case dsl of Refl impossible
    GDXNL => void $ case dsl of Refl impossible
    GDXXL => void $ case dsl of Refl impossible
    GDNCHD => void $ case dsl of Refl impossible
    GDNCTL => void $ case dsl of Refl impossible
    GDXCHD => void $ case dsl of Refl impossible
    GDXCTL => void $ case dsl of Refl impossible

public export
InGNat : Nat -> GWExpN
InGNat Z = InGZ
InGNat (S n) = InGS (InGNat n)

public export
InGNN : GWExpNL
InGNN = InSPFM (GSNATL ** Element0 GPNN Refl) $ \(Element0 d dsl) =>
  case d of
    GDS => void $ case dsl of Refl impossible
    GDXA => void $ case dsl of Refl impossible
    GDXNL => void $ case dsl of Refl impossible
    GDXXL => void $ case dsl of Refl impossible
    GDNCHD => void $ case dsl of Refl impossible
    GDNCTL => void $ case dsl of Refl impossible
    GDXCHD => void $ case dsl of Refl impossible
    GDXCTL => void $ case dsl of Refl impossible

public export
InGNC : GWExpN -> GWExpNL -> GWExpNL
InGNC n ns = InSPFM (GSNATL ** Element0 GPNC Refl) $ \(Element0 d dsl) =>
  case d of
    GDS => void $ case dsl of Refl impossible
    GDXA => void $ case dsl of Refl impossible
    GDXNL => void $ case dsl of Refl impossible
    GDXXL => void $ case dsl of Refl impossible
    GDNCHD => n
    GDNCTL => ns
    GDXCHD => void $ case dsl of Refl impossible
    GDXCTL => void $ case dsl of Refl impossible

public export
InGNatC : Nat -> GWExpNL -> GWExpNL
InGNatC n ns = InGNC (InGNat n) ns

public export
InGNatList : List Nat -> GWExpNL
InGNatList = foldr InGNatC InGNN

public export
InGXN : GWExpXL
InGXN = InSPFM (GSEXPL ** Element0 GPXN Refl) $ \(Element0 d dsl) =>
  case d of
    GDS => void $ case dsl of Refl impossible
    GDXA => void $ case dsl of Refl impossible
    GDXNL => void $ case dsl of Refl impossible
    GDXXL => void $ case dsl of Refl impossible
    GDNCHD => void $ case dsl of Refl impossible
    GDNCTL => void $ case dsl of Refl impossible
    GDXCHD => void $ case dsl of Refl impossible
    GDXCTL => void $ case dsl of Refl impossible

public export
InGXC : GWExpX -> GWExpXL -> GWExpXL
InGXC x xs = InSPFM (GSEXPL ** Element0 GPXC Refl) $ \(Element0 d dsl) =>
  case d of
    GDS => void $ case dsl of Refl impossible
    GDXA => void $ case dsl of Refl impossible
    GDXNL => void $ case dsl of Refl impossible
    GDXXL => void $ case dsl of Refl impossible
    GDNCHD => void $ case dsl of Refl impossible
    GDNCTL => void $ case dsl of Refl impossible
    GDXCHD => x
    GDXCTL => xs

public export
InGX : GebAtom -> GWExpNL -> GWExpXL -> GWExpX
InGX a ns xs = InSPFM (GSEXP ** Element0 GPX Refl) $ \(Element0 d dsl) =>
  case d of
    GDS => void $ case dsl of Refl impossible
    GDXA => InGA a
    GDXNL => ns
    GDXXL => xs
    GDNCHD => void $ case dsl of Refl impossible
    GDNCTL => void $ case dsl of Refl impossible
    GDXCHD => void $ case dsl of Refl impossible
    GDXCTL => void $ case dsl of Refl impossible

public export
InGNatX : GebAtom -> List Nat -> GWExpXL -> GWExpX
InGNatX a ns = InGX a (InGNatList ns)

public export
InGWExpList : List GWExpX -> GWExpXL
InGWExpList = foldr InGXC InGXN

public export
GWExpToWTAlg : SXLAlg GebAtom GWExpX GWExpXL
GWExpToWTAlg = SXA InGNatX InGXN InGXC

public export
gwexpToWT : GExp -> GWExpX
gwexpToWT = sxCata GWExpToWTAlg

------------------------------------------------------------------------
------------------------------------------------------------------------
---- Geb S-expression as inductive dependent polynomial endofunctor ----
------------------------------------------------------------------------
------------------------------------------------------------------------

-- Equivalent to GExp, but using the inductive representation of
-- dependent polynomial endofunctors, rather than the W-type
-- representation.  This is largely for comparison of the resulting
-- code.

--------------------------
---- Atom endofunctor ----
--------------------------

public export
GAtomF : PolyFunc
GAtomF = PFConstArena GebAtom

public export
GAtomPos : Type
GAtomPos = pfPos GAtomF

public export
GAtomDir : SliceObj GAtomPos
GAtomDir = pfDir {p=GAtomF}

------------------------------------------
---- List (parameterized) endofunctor ----
------------------------------------------

public export
GListPosL : Type
GListPosL = Bool  -- False = nil; True = cons

public export
GListDirL : SliceObj GListPosL
GListDirL False = Void -- nil has no directions
GListDirL True = Bool -- cons has two directions (False = head; True = tail)

public export
GListF : PolyFunc
GListF = (GListPosL ** GListDirL)

public export
GListSlice : Type
GListSlice = Bool  -- False = input PolyFunc; True = list of input PolyFunc

public export
GListLAssign : Sigma {a=GListPosL} GListDirL -> GListSlice
GListLAssign (False ** d) = void d -- nil has no directions
GListLAssign (True ** False) = False -- head is a PolyFunc
GListLAssign (True ** True) = True -- tail is a list

public export
GListLSPF : SlicePolyFunc GListSlice ()
GListLSPF =
  (const GListPosL **
   GListDirL . snd **
   \((() ** i) ** d) => GListLAssign (i ** d))

public export
GListPos : PolyFunc -> SliceObj GListSlice
GListPos p False = pfPos p
GListPos p True = GListPosL

public export
GListDir : Pi {a=PolyFunc} (Slice2Obj {a=GListSlice} . GListPos)
GListDir p False = pfDir {p}
GListDir p True = GListDirL

public export
GListAssign : (p : PolyFunc) -> (sl : GListSlice) -> (i : GListPos p sl) ->
  GListDir p sl i -> GListSlice
GListAssign p False i d = False -- 'p' directions are all in PolyFunc slice
GListAssign p True i d = GListLAssign (i ** d)

public export
GListSPF : PolyFunc -> SlicePolyEndoFunc GListSlice
GListSPF p =
  (GListPos p **
   \(sl ** i) => GListDir p sl i **
   \((sl ** i) ** d) => GListAssign p sl i d)

------------------------------------
---- Natural number endofunctor ----
------------------------------------

public export
GNatF : PolyFunc
GNatF = pfMaybeArena

public export
GNatPos : Type
GNatPos = pfPos GNatF

public export
GNatDir : SliceObj GNatPos
GNatDir = pfDir {p=GNatF}

public export
gNatPosAtom : GNatPos -> GebAtom
gNatPosAtom (Left ()) = POS_S
gNatPosAtom (Right ()) = POS_Z

public export
gNatDirAtom : Sigma {a=GNatPos} GNatDir -> GebAtom
gNatDirAtom ((Left ()) ** ()) = DIR_S
gNatDirAtom ((Right ()) ** v) = void v

------------------------------------------
---- Expression-component endofunctor ----
------------------------------------------

public export
data GExpXDir : Type where
  GDA : GExpXDir
  GDNL : GExpXDir
  GDXL : GExpXDir

-- An expression has only one position, with three directions:  an atom,
-- a natural number list, and an expression list.
public export
GExpF : PolyFunc
GExpF = PFHomArena GExpXDir

public export
GExpPos : Type
GExpPos = pfPos GExpF

public export
GExpDir : SliceObj GExpPos
GExpDir = pfDir {p=GExpF}

public export
GExpPosAtom : GExpPos -> GebAtom
GExpPosAtom () = POS_X

public export
GExpDirAtom : Sigma {a=GExpPos} GExpDir -> GebAtom
GExpDirAtom (() ** GDA) = DIR_XA
GExpDirAtom (() ** GDNL) = DIR_XNL
GExpDirAtom (() ** GDXL) = DIR_XXL

-----------------------------------------
---- Natural number list endofunctor ----
-----------------------------------------

public export
GNatLSPF : SlicePolyEndoFunc Bool
GNatLSPF = GListSPF GNatF

public export
GNatLF : PolyFunc
GNatLF = spfTopf GNatLSPF True

public export
GNatLFPos : Type
GNatLFPos = pfPos GNatLF

public export
GNatLFDir : SliceObj GNatLFPos
GNatLFDir = pfDir {p=GNatLF}

public export
GNatLFAssign : (i : GNatLFPos) -> GNatLFDir i -> GListSlice
GNatLFAssign = GListAssign GNatF True

public export
GNatLFPosAtom : GNatLFPos -> GebAtom
GNatLFPosAtom False = POS_NN
GNatLFPosAtom True = POS_NC

public export
GNatLFDirAtom : Sigma {a=GNatLFPos} GNatLFDir -> GebAtom
GNatLFDirAtom (False ** d) = void d
GNatLFDirAtom (True ** False) = DIR_NCHD
GNatLFDirAtom (True ** True) = DIR_NCTL

-------------------------------------
---- Expression list endofunctor ----
-------------------------------------

public export
GExpLSPF : SlicePolyEndoFunc Bool
GExpLSPF = GListSPF GExpF

public export
GExpLF : PolyFunc
GExpLF = spfTopf GExpLSPF True

public export
GExpLFPos : Type
GExpLFPos = pfPos GExpLF

public export
GExpLFDir : SliceObj GExpLFPos
GExpLFDir = pfDir {p=GExpLF}

public export
GExpLFAssign : (i : GExpLFPos) -> GExpLFDir i -> GListSlice
GExpLFAssign = GListAssign GExpF True

public export
GExpLFPosAtom : GExpLFPos -> GebAtom
GExpLFPosAtom False = POS_XN
GExpLFPosAtom True = POS_XC

public export
GExpLFDirAtom : Sigma {a=GExpLFPos} GExpLFDir -> GebAtom
GExpLFDirAtom (False ** d) = void d
GExpLFDirAtom (True ** False) = DIR_XCHD
GExpLFDirAtom (True ** True) = DIR_XCTL
