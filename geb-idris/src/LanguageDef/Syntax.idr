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
data BTExpF : Type -> Type -> Type where
  BTA : atom -> BTExpF atom btty
  BTP : btty -> btty -> BTExpF atom btty

public export
data BTExp : Type -> Type where
  InBT : BTExpF atom (BTExp atom) -> BTExp atom

public export
InBTA : atom -> BTExp atom
InBTA = InBT . BTA

public export
InBTP : BTExp atom -> BTExp atom -> BTExp atom
InBTP = InBT .* BTP

public export
BTAlg : Type -> Type -> Type
BTAlg atom a = BTExpF atom a -> a

public export
btCata : BTAlg atom a -> BTExp atom -> a
btCata alg (InBT e) = alg $ case e of
  BTA a => BTA a
  BTP x y => BTP (btCata alg x) (btCata alg y)

public export
BTShowAlg : Show atom => BTAlg atom String
BTShowAlg (BTA a) = show a
BTShowAlg (BTP x y) = "(" ++ x ++ "," ++ y ++ ")"

public export
Show atom => Show (BTExp atom) where
  show = btCata BTShowAlg

public export
data SExpF : Type -> Type -> Type where
  SXF : atom -> List Nat -> List xty -> SExpF atom xty

public export
data SExp : Type -> Type where
  InSX : SExpF atom (SExp atom) -> SExp atom

public export
InS : atom -> List Nat -> List (SExp atom) -> SExp atom
InS a ns xs = InSX $ SXF a ns xs

public export
SList : Type -> Type
SList = List . SExp

public export
SExpAlg : Type -> Type -> Type
SExpAlg atom a = SExpF atom a -> a

mutual
  public export
  sexpCata : SExpAlg atom a -> SExp atom -> a
  sexpCata alg (InSX x) = alg $ case x of
    SXF a ns xs => SXF a ns $ slistCata alg xs

  public export
  slistCata : SExpAlg atom a -> SList atom -> List a
  slistCata alg [] = []
  slistCata alg (x :: xs) = sexpCata alg x :: slistCata alg xs

public export
SExpShowAlg : Show atom => SExpAlg atom String
SExpShowAlg (SXF a ns xs) =
  "(" ++ show a ++ ":" ++ show ns ++ ",[" ++ joinBy "," xs ++ "])"

public export
Show atom => Show (SExp atom) where
  show = sexpCata SExpShowAlg

public export
data SExpToBtAtom : Type -> Type where
  SBAtom : atom -> SExpToBtAtom atom
  SBNil : SExpToBtAtom atom
  SBNat : Nat -> SExpToBtAtom atom

public export
Show atom => Show (SExpToBtAtom atom) where
  show (SBAtom a) = show a
  show SBNil = "[]"
  show (SBNat n) = show n

mutual
  public export
  SExpToBtAlg : SExpAlg atom (BTExp $ SExpToBtAtom atom)
  SExpToBtAlg (SXF a ns xs) =
    InBTP (InBTA $ SBAtom a) $ InBTP (NatListToBtAlg ns) (SListToBtAlg xs)

  public export
  NatListToBtAlg : List Nat -> BTExp (SExpToBtAtom atom)
  NatListToBtAlg [] = InBTA SBNil
  NatListToBtAlg (n :: ns) = InBTP (InBTA $ SBNat n) (NatListToBtAlg ns)

  public export
  SListToBtAlg : List (BTExp $ SExpToBtAtom atom) -> BTExp (SExpToBtAtom atom)
  SListToBtAlg [] = InBTA SBNil
  SListToBtAlg (x :: xs) = InBTP x (SListToBtAlg xs)

public export
sexpToBt : SExp atom -> BTExp $ SExpToBtAtom atom
sexpToBt = sexpCata SExpToBtAlg

mutual
  public export
  btToSexp : BTExp (SExpToBtAtom atom) -> Maybe (SExp atom)
  btToSexp (InBT x) = case x of
    BTA a => case a of
      SBAtom a' => Just $ InS a' [] []
      SBNil => Nothing
      SBNat n => Nothing
    BTP (InBT y) (InBT z) => case y of
      BTA a => case a of
        SBAtom a' => case z of
          BTP y' z' => case (btToNatList y', btToSexpList z') of
            (Just ns, Just xs) => Just $ InS a' ns xs
            _ => Nothing
          _ => Nothing
        _ => Nothing
      BTP y z => Nothing

  public export
  btToNatList : BTExp (SExpToBtAtom atom) -> Maybe (List Nat)
  btToNatList (InBT x) = case x of
    BTA a => case a of
      SBNil => Just []
      _ => Nothing
    BTP y z => case y of
      InBT (BTA (SBNat n)) => case btToNatList z of
        Just ns => Just $ n :: ns
        Nothing => Nothing
      _ => Nothing

  public export
  btToSexpList : BTExp (SExpToBtAtom atom) -> Maybe (List $ SExp atom)
  btToSexpList (InBT x) = case x of
    BTA a => case a of
      SBNil => Just []
      _ => Nothing
    BTP y z => case (btToSexp y, btToSexpList z) of
      (Just x, Just xs) => Just $ x :: xs
      _ => Nothing
