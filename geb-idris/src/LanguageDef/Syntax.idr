module LanguageDef.Syntax

import Library.IdrisUtils
import Library.IdrisCategories

%default total

public export
record SymSet where
  constructor SS
  slType : Type
  slSize : Nat
  slEnc : FinDecEncoding slType slSize
  slShow : slType -> String

public export
Show SymSet where
  show (SS ty sz enc sh) = let _ = MkShow sh in show (finFToVect (fst enc))

public export
FinSS : Nat -> SymSet
FinSS n = SS (Fin n) n (FinIdDecEncoding n) show

public export
VoidSS : SymSet
VoidSS = FinSS 0

public export
record Namespace where
  constructor NS
  nsLocalSym : SymSet
  nsSubSym : SymSet
  nsSub : Vect nsSubSym.slSize Namespace

public export
FinNS : (nloc : Nat) -> {nsub : Nat} -> Vect nsub Namespace -> Namespace
FinNS nloc {nsub} = NS (FinSS nloc) (FinSS nsub)

public export
VoidNS : Namespace
VoidNS = FinNS 0 []

mutual
  public export
  nsLines : Namespace -> List String
  nsLines (NS ls ss sub) =
    ("loc: " ++ show ls ++ "; sub: " ++ show ss) ::
    map (indent 2) (nsVectLines sub)

  public export
  nsVectLines : {n : Nat} -> Vect n Namespace -> List String
  nsVectLines [] = []
  nsVectLines (ns :: v) = nsLines ns ++ nsVectLines v

public export
Show Namespace where
  show = trim . unlines . nsLines

public export
numSub : Namespace -> Nat
numSub = slSize . nsSubSym

public export
LeafNS : SymSet -> Namespace
LeafNS ss = NS ss VoidSS []

public export
data Subspace : Namespace -> Type where
  This : {ns : Namespace} -> Subspace ns
  Child : {ns : Namespace} ->
    (i : ns.nsSubSym.slType) ->
    Subspace (index (fst (snd ns.nsSubSym.slEnc i)) ns.nsSub) ->
    Subspace ns

public export
(ns : Namespace) => Show (Subspace ns) where
  show {ns} sub = "/" ++ showSub sub where
    showSub : {ns : Namespace} -> Subspace ns -> String
    showSub {ns} This = ""
    showSub {ns} (Child i sub) = slShow ns.nsSubSym i ++ "/" ++ showSub sub

public export
data SAtom :
    (0 numRes, maxNat : Nat) -> (0 res : Type) ->
    (0 decoder : FinDecoder res numRes) ->
    (0 encoder : NatEncoder {a=res} {size=numRes} decoder) ->
    Type where
  SRes :
    (i : res) -> SAtom numRes maxNat res decoder encoder
  SNat :
    (n : Nat) -> {auto 0 ok : IsTrue (n < maxNat)} ->
    SAtom numRes maxNat res decoder encoder

public export
0 saArity :
  {0 numRes, maxNat : Nat} -> {0 res : Type} ->
  {0 decoder : FinDecoder res numRes} ->
  {0 encoder : NatEncoder {a=res} {size=numRes} decoder} ->
  (0 arity : res -> Nat) ->
  SAtom numRes maxNat res decoder encoder -> Nat
saArity arity (SRes i) = arity i
saArity arity (SNat n) = 0

public export
data SExpF :
    (0 numRes, maxNat : Nat) -> (0 res : Type) ->
    (0 decoder : FinDecoder res numRes) ->
    (0 encoder : NatEncoder {a=res} {size=numRes} decoder) ->
    (0 arity : res -> Nat) ->
    Type -> Type where
  SX :
    (a : SAtom numRes maxNat res decoder encoder) ->
    (l : List ty) ->
    {auto 0 ok : IsTrue (length l == saArity arity a)} ->
    SExpF numRes maxNat res decoder encoder arity ty

public export
data SExp :
    (0 numRes, maxNat : Nat) -> (0 res : Type) ->
    (0 decoder : FinDecoder res numRes) ->
    (0 encoder : NatEncoder {a=res} {size=numRes} decoder) ->
    (0 arity : res -> Nat) ->
    Type where
  InSX :
    SExpF numRes maxNat res decoder encoder arity
      (SExp numRes maxNat res decoder encoder arity) ->
    SExp numRes maxNat res decoder encoder arity
