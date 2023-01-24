module LanguageDef.GebTopos

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.Atom
import public LanguageDef.ProgFinSet
import public LanguageDef.PolyCat

%default total

public export
FinV : {0 len : Nat} -> Vect len Nat -> Type
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
record RecType (0 nty : Nat) where
  constructor RType
  numCtor : Nat
  ctor : Vect numCtor (Constructor nty)

public export
record TypeFamily (0 nty : Nat) where
  constructor TFamily
  rtype : Vect nty (RecType nty)

public export
InterpTF : {0 nty : Nat} ->
  TypeFamily nty -> (Fin nty -> Type) -> Fin nty -> Type
InterpTF {nty} tf sl ity =
  let ty = index ity tf.rtype in
  (i : Fin ty.numCtor **
   let ct = index i ty.ctor in
   (FinV {len=ct.numConst} ct.cconst,
    HVect {k=ct.numDir} $ map sl ct.cdir))

public export
data MuTF : {0 nty : Nat} -> TypeFamily nty -> Fin nty -> Type where
  InTF : {0 nty : Nat} -> {tf : TypeFamily nty} ->
    (i : Fin nty) -> InterpTF {nty} tf (MuTF tf) i -> MuTF tf i

-----------------------------------------
-----------------------------------------
---- Binary-sexp term representation ----
-----------------------------------------
-----------------------------------------

-------------------------------------
-------------------------------------
---- Initial term representation ----
-------------------------------------
-------------------------------------

-------------------------------------
-------------------------------------
---- Initial type representation ----
-------------------------------------
-------------------------------------

----------------------------------------
----------------------------------------
---- Initial functor representation ----
----------------------------------------
----------------------------------------

public export
MorphSig : SliceObj Type
MorphSig x = SliceObj (x, x)

public export
MorphSPF : Type -> Type
MorphSPF x = DepParamPolyFunc (x, x) (x, x)

public export
MorphMu : {x : Type} -> MorphSPF x -> MorphSig x
MorphMu {x} = SPFMu . SPFFromDPPF
