module LanguageDef.TreeCalculus

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.BinTree

%default total

-----------------------
-----------------------
---- Natural trees ----
-----------------------
-----------------------

-------------------------
---- Type definition ----
-------------------------

public export
NatTreeF : Type -> Type
NatTreeF = BinTreeF Unit

public export
natTreeMap : (0 a, b : Type) -> (a -> b) -> NatTreeF a -> NatTreeF b
natTreeMap a b =
  mapSnd {f=Either} {a=Unit} {b=(ProductMonad a)} {d=(ProductMonad b)}
  . mapHom {f=Pair} {a} {b}

public export
ntDeltaF : NaturalTransformation TerminalMonad NatTreeF
ntDeltaF x = Left {a=Unit} {b=(ProductMonad x)}

public export
0 ntDeltaFisNatural :
  NaturalityCondition {f=TerminalMonad} {g=NatTreeF}
    IdrisCategories.terminalMonadMap
    TreeCalculus.natTreeMap
    TreeCalculus.ntDeltaF
ntDeltaFisNatural a b mab () = Refl

public export
δ : {x : Type} -> NatTreeF x
δ {x} = ntDeltaF x ()

public export
ntEdgeF : NaturalTransformation ProductMonad NatTreeF
ntEdgeF x = Right {a=Unit} {b=(ProductMonad x)}

public export
0 ntEdgeFisNatural :
  NaturalityCondition {f=ProductMonad} {g=NatTreeF}
    IdrisCategories.productMonadMap
    TreeCalculus.natTreeMap
    TreeCalculus.ntEdgeF
ntEdgeFisNatural a b mab el = Refl

public export
ε : {x : Type} -> x -> x -> NatTreeF x
ε {x} = ntEdgeF x .* MkPair

public export
Functor NatTreeF where
  map {a} {b} = natTreeMap a b

public export
data NatTree : Type where
  InNT : Algebra NatTreeF NatTree

public export
OutNT : Coalgebra NatTreeF NatTree
OutNT nt = case nt of (InNT ntF) => ntF

public export
0 natTreeOutAfterInId : (ntF : NatTreeF NatTree) -> OutNT (InNT ntF) = ntF
natTreeOutAfterInId ntF = Refl

public export
0 natTreeInAfterOutId : (nt : NatTree) -> InNT (OutNT nt) = nt
natTreeInAfterOutId (InNT ntF) = Refl

public export
Δ : NatTree
Δ = InNT (δ {x=NatTree})

public export
Ε : NatTree -> NatTree -> NatTree
Ε = InNT .* ε {x=NatTree}

public export
Ɩ : NatTree -> NatTree
Ɩ = Ε Δ

public export
TerminalMonadAlg : Type -> Type
TerminalMonadAlg = id {a=Type}

public export
TerminalMonadAlgToAlgebra :
  NaturalTransformation TerminalMonadAlg (Algebra TerminalMonad)
TerminalMonadAlgToAlgebra x = const {a=x} {b=Unit}

public export
TerminalMonadAlgFromAlgebra :
  NaturalTransformation (Algebra TerminalMonad) TerminalMonadAlg
TerminalMonadAlgFromAlgebra x alg = alg ()

public export
TerminalMonadCont : Type -> Type
TerminalMonadCont = flip Cont Void

public export
TerminalMonadAlgToCont :
  NaturalTransformation TerminalMonadAlg TerminalMonadCont
TerminalMonadAlgToCont x = flip $ const {a=(x -> x)} {b=(Void -> x)} $ id {a=x}

public export
TerminalMonadAlgFromCont :
  NaturalTransformation TerminalMonadCont TerminalMonadAlg
TerminalMonadAlgFromCont x cv = cv (voidF x)

public export
ProductMonadAlg : Type -> Type
ProductMonadAlg x = x -> x -> x

public export
ProductMonadAlgToAlgebra :
  NaturalTransformation ProductMonadAlg (Algebra ProductMonad)
ProductMonadAlgToAlgebra x = uncurry {a=x} {b=x} {c=x}

public export
ProductMonadAlgFromAlgebra :
  NaturalTransformation (Algebra ProductMonad) ProductMonadAlg
ProductMonadAlgFromAlgebra x = curry {a=x} {b=x} {c=x}

public export
ProductMonadCont : Type -> Type
ProductMonadCont = flip Cont (Fin 2)

public export
ProductMonadAlgToCont :
  NaturalTransformation ProductMonadAlg ProductMonadCont
ProductMonadAlgToCont x alg el = alg (el FZ) (el $ FS FZ)

public export
ProductMonadAlgFromCont :
  NaturalTransformation ProductMonadCont ProductMonadAlg
ProductMonadAlgFromCont x c2 el1 el2 =
  c2 $ flip (Vect.index {len=2} {elem=x}) [el1, el2]

public export
NatTreeFAlg : Type -> Type
NatTreeFAlg = ProductF TerminalMonadAlg ProductMonadAlg

public export
NatTreeFAlgToAlgebra :
  NaturalTransformation NatTreeFAlg (Algebra NatTreeF)
NatTreeFAlgToAlgebra x alg =
  eitherElim
    (TerminalMonadAlgToAlgebra x (fst alg))
    (ProductMonadAlgToAlgebra x (snd alg))

public export
NatTreeFAlgFromAlgebra :
  NaturalTransformation (Algebra NatTreeF) NatTreeFAlg
NatTreeFAlgFromAlgebra x alg =
  (TerminalMonadAlgFromAlgebra x (alg . Left),
   ProductMonadAlgFromAlgebra x (alg . Right))

public export
natTreeAlgLift : {a, b : Type} -> NatTreeFAlg b -> (a -> b) -> NatTreeF a -> b
natTreeAlgLift {a} {b} alg = (.) (NatTreeFAlgToAlgebra b alg) . natTreeMap a b

public export
natTreeAlgBind : {a : Type} -> (m : Type -> Type) -> Monad m ->
  (NatTreeF a -> m a) -> Algebra NatTreeF (m a)
natTreeAlgBind {a} m isM alg (Left ()) = alg $ Left ()
natTreeAlgBind {a} m isM alg (Right p) =
  map {f=m} Right (sequence {f=m} {t=ProductMonad} p) >>= alg

mutual
  public export
  natTreeCata : {x : Type} -> NatTreeFAlg x -> NatTree -> x
  -- Equivalent to
  --  `natTreeCata {x} alg = natTreeFCata {x} alg . OutNT`
  -- (but Idris wouldn't recognize that as terminating).
  natTreeCata {x} alg (InNT nt) = natTreeFCata {x} alg nt

  public export
  natTreeFCata : {x : Type} -> NatTreeFAlg x -> NatTreeF NatTree -> x
  -- Equivalent to
  --  `natTreeFCata {x} alg =
  --    natTreeAlgLift {a=NatTree} {b=x} alg (natTreeCata {x} alg)`
  -- (but Idris wouldn't recognize that as terminating).
  natTreeFCata {x} alg (Left u_) = fst alg
  natTreeFCata {x} alg (Right p) = natTreePairCata {x} alg p

  public export
  natTreePairCata : {x : Type} -> NatTreeFAlg x -> (NatTree, NatTree) -> x
  -- Equivalent to
  --  `natTreePairCata {x} alg p =
  --    snd alg (natTreeCata {x} alg (fst p)) (natTreeCata {x} alg (snd p))`
  -- (but Idris wouldn't recognize that as terminating).
  natTreePairCata {x} alg (l, r) =
    snd alg (natTreeCata {x} alg l) (natTreeCata {x} alg r)

public export
0 natTreeCataAlt :
  (x : Type) -> (alg : NatTreeFAlg x) -> (nt : NatTree) ->
  natTreeCata {x} alg nt =
    natTreeFCata {x} alg (OutNT nt)
natTreeCataAlt x alg (InNT ntF) = Refl

public export
0 natTreeFCataAlt :
  (x : Type) -> (alg : NatTreeFAlg x) -> (ntF : NatTreeF NatTree) ->
  natTreeFCata {x} alg ntF =
    natTreeAlgLift {a=NatTree} {b=x} alg (natTreeCata {x} alg) ntF
natTreeFCataAlt x alg (Left u_) = Refl
natTreeFCataAlt x alg (Right (l, r)) = Refl

public export
0 natTreePairCataAlt :
  (x : Type) -> (alg : NatTreeFAlg x) -> (p : (NatTree, NatTree)) ->
  natTreePairCata {x} alg p =
    snd alg (natTreeCata {x} alg (fst p)) (natTreeCata {x} alg (snd p))
natTreePairCataAlt x alg (l, r) = Refl

--------------------------------------------------
---- Equivalence with atom-less S-expressions ----
--------------------------------------------------

-- As described at https://treecalcul.us/specification/, `NatTree` as
-- defined above (corresponding to that site's "expression abstract syntax")
-- may also be viewed as the type of unlabeled trees, with varying
-- (arbitrary finite) numbers of children per node.  Here we show that
-- correspondence; that unlabeled tree type may be viewed as a type of
-- atom-or-list S-expressions, but with no atoms (construction always
-- begins with an empty list, corresponding to a leaf node).

public export
data NSExp : Type where
  InNS : Algebra List NSExp

public export
OutRNS : Coalgebra List NSExp
OutRNS (InNS ns) = ns

public export
ד : Algebra List NSExp
ד = InNS . reverse

public export
OutNS : Coalgebra List NSExp
OutNS = reverse . OutRNS

public export
נ : NSExp
נ = ד []

public export
י : NSExp -> NSExp
י ns = ד [ns]

mutual
  public export
  RNSExpToNatTree : NSExp -> NatTree
  RNSExpToNatTree (InNS ts) = ListRNSExpToNatTree ts

  public export
  ListRNSExpToNatTree : List NSExp -> NatTree
  ListRNSExpToNatTree ts = InNT (ListRNSExpToNatTreeF ts)

  public export
  NEListRNSExpToNatTreePair : NSExp -> List NSExp -> (NatTree, NatTree)
  NEListRNSExpToNatTreePair ns ts =
    (ListRNSExpToNatTree ts, RNSExpToNatTree ns)

  public export
  ListRNSExpToNatTreeF : List NSExp -> NatTreeF NatTree
  ListRNSExpToNatTreeF [] =
    ntDeltaF NatTree ()
  ListRNSExpToNatTreeF (t :: ts) =
    ntEdgeF NatTree (NEListRNSExpToNatTreePair t ts)

public export
NSExpToNatTree : NSExp -> NatTree
NSExpToNatTree (InNS ns) = RNSExpToNatTree (ד ns)

public export
ListNSExpToNatTree : List NSExp -> NatTree
ListNSExpToNatTree ns = ListRNSExpToNatTree (reverse ns)

public export
NEListNSExpToNatTreePair : NSExp -> List NSExp -> (NatTree, NatTree)
NEListNSExpToNatTreePair ns ts = (NSExpToNatTree ns, ListNSExpToNatTree ts)

public export
ListNSExpToNatTreeF : List NSExp -> NatTreeF NatTree
ListNSExpToNatTreeF = ListRNSExpToNatTreeF . reverse

mutual
  public export
  NatTreeToRNSExp : NatTree -> NSExp
  NatTreeToRNSExp nt = InNS (NatTreeToListRNSExp nt)

  public export
  NatTreeToListRNSExp : NatTree -> List NSExp
  NatTreeToListRNSExp (InNT ntF) = NatTreeFToListRNSExp ntF

  public export
  NatTreePairToNEListRNSExp : NatTree -> NatTree -> (NSExp, List NSExp)
  NatTreePairToNEListRNSExp (InNT tlF) tr =
    (NatTreeToRNSExp tr, NatTreeFToListRNSExp tlF)

  public export
  NatTreeFToListRNSExp : NatTreeF NatTree -> List NSExp
  NatTreeFToListRNSExp (Left ()) = []
  NatTreeFToListRNSExp (Right (InNT tlF, tr)) =
    NatTreeToRNSExp tr :: NatTreeFToListRNSExp tlF

public export
NatTreeToNSExp : NatTree -> NSExp
NatTreeToNSExp nt with (NatTreeToRNSExp nt)
  NatTreeToNSExp nt | (InNS ns) = ד ns

public export
NatTreeToListNSExp : NatTree -> List NSExp
NatTreeToListNSExp = reverse . NatTreeToListRNSExp

public export
NatTreePairToNEListNSExp : NatTree -> NatTree -> (NSExp, List NSExp)
NatTreePairToNEListNSExp l r = (NatTreeToNSExp l, NatTreeToListNSExp r)

public export
NatTreeFToListNSExp : NatTreeF NatTree -> List NSExp
NatTreeFToListNSExp = reverse . NatTreeFToListRNSExp

mutual
  public export
  0 RNSExpToAfterFromNatTreeId :
    (ns : NSExp) -> NatTreeToRNSExp (RNSExpToNatTree ns) = ns
  RNSExpToAfterFromNatTreeId (InNS []) = Refl
  RNSExpToAfterFromNatTreeId (InNS (t :: ts)) =
    cong InNS
    $ congList
      (RNSExpToAfterFromNatTreeId t)
      (ListRNSExpToAfterFromNatTreeId ts)

  public export
  0 ListRNSExpToAfterFromNatTreeId :
    (ts : List NSExp) -> NatTreeToListRNSExp (ListRNSExpToNatTree ts) = ts
  ListRNSExpToAfterFromNatTreeId [] = Refl
  ListRNSExpToAfterFromNatTreeId (ns :: l) =
    congList
      (RNSExpToAfterFromNatTreeId ns)
      (ListRNSExpToAfterFromNatTreeId l)

  public export
  0 NEListRNSExpToAfterFromNatTreePairId :
    (ns : NSExp) -> (ts : List NSExp) ->
    NatTreePairToNEListRNSExp
      (fst $ NEListRNSExpToNatTreePair ns ts)
      (snd $ NEListRNSExpToNatTreePair ns ts) =
    (ns, ts)
  NEListRNSExpToAfterFromNatTreePairId ns ts =
    pairEqCong
      (RNSExpToAfterFromNatTreeId ns)
      (ListRNSExpToAfterFromNatTreeId ts)

  public export
  0 ListRNSExpToAfterFromNatTreeFId :
    (ts : List NSExp) -> NatTreeFToListRNSExp (ListRNSExpToNatTreeF ts) = ts
  ListRNSExpToAfterFromNatTreeFId [] = Refl
  ListRNSExpToAfterFromNatTreeFId (t :: ts) =
    congList
      (RNSExpToAfterFromNatTreeId t)
      (ListRNSExpToAfterFromNatTreeFId ts)

public export
0 NSExpToAfterFromNatTreeId :
  (ns : NSExp) -> NatTreeToNSExp (NSExpToNatTree ns) = ns
NSExpToAfterFromNatTreeId (InNS ns) =
  rewrite ListRNSExpToAfterFromNatTreeFId (reverse ns) in
  rewrite reverseInvolutive ns in
  Refl

public export
0 ListNSExpToAfterFromNatTreeId :
  (ts : List NSExp) -> NatTreeToListNSExp (ListNSExpToNatTree ts) = ts
ListNSExpToAfterFromNatTreeId ts =
  rewrite ListRNSExpToAfterFromNatTreeFId (reverse ts) in
  rewrite reverseInvolutive ts in
  Refl

public export
0 NEListNSExpToAfterFromNatTreePairId :
  (ns : NSExp) -> (ts : List NSExp) ->
  NatTreePairToNEListNSExp
    (fst $ NEListNSExpToNatTreePair ns ts)
    (snd $ NEListNSExpToNatTreePair ns ts) =
  (ns, ts)
NEListNSExpToAfterFromNatTreePairId (InNS ns) ts =
  rewrite ListRNSExpToAfterFromNatTreeFId (reverse ts) in
  rewrite ListRNSExpToAfterFromNatTreeFId (reverse ns) in
  rewrite reverseInvolutive ts in
  rewrite reverseInvolutive ns in
  Refl

public export
0 ListNSExpToAfterFromNatTreeFId :
  (ts : List NSExp) -> NatTreeFToListNSExp (ListNSExpToNatTreeF ts) = ts
ListNSExpToAfterFromNatTreeFId ts =
  rewrite ListRNSExpToAfterFromNatTreeFId (reverse ts) in
  rewrite reverseInvolutive ts in
  Refl

mutual
  public export
  0 RNSExpFromAfterToNatTreeId :
    (nt : NatTree) -> RNSExpToNatTree (NatTreeToRNSExp nt) = nt
  RNSExpFromAfterToNatTreeId (InNT ntF) =
    rewrite ListRNSExpFromAfterToNatTreeFId ntF in
    Refl

  public export
  0 ListRNSExpFromAfterToNatTreeId :
    (nt : NatTree) ->
    ListRNSExpToNatTree (NatTreeToListRNSExp nt) = nt
  ListRNSExpFromAfterToNatTreeId (InNT ntF) =
    rewrite ListRNSExpFromAfterToNatTreeFId ntF in
    Refl

  public export
  0 NEListRNSExpFromAfterToNatTreePairId :
    (tl, tr : NatTree) ->
    NEListRNSExpToNatTreePair
      (fst $ NatTreePairToNEListRNSExp tl tr)
      (snd $ NatTreePairToNEListRNSExp tl tr) =
    (tl, tr)
  NEListRNSExpFromAfterToNatTreePairId (InNT tlF) (InNT trF) =
    pairEqCong
      (rewrite ListRNSExpFromAfterToNatTreeFId tlF in Refl)
      (rewrite ListRNSExpFromAfterToNatTreeFId trF in Refl)

  public export
  0 ListRNSExpFromAfterToNatTreeFId :
    (ntF : NatTreeF NatTree) ->
    ListRNSExpToNatTreeF (NatTreeFToListRNSExp ntF) = ntF
  ListRNSExpFromAfterToNatTreeFId (Left ()) =
    Refl
  ListRNSExpFromAfterToNatTreeFId (Right (InNT tlF, InNT trF)) =
    cong Right $
      pairEqCong
        (rewrite ListRNSExpFromAfterToNatTreeFId tlF in Refl)
        (rewrite ListRNSExpFromAfterToNatTreeFId trF in Refl)

public export
0 NSExpFromAfterToNatTreeId :
  (nt : NatTree) -> NSExpToNatTree (NatTreeToNSExp nt) = nt
NSExpFromAfterToNatTreeId (InNT ntF) =
  rewrite reverseInvolutive (NatTreeFToListRNSExp ntF) in
  rewrite ListRNSExpFromAfterToNatTreeFId ntF in
  Refl

public export
0 ListNSExpFromAfterToNatTreeId :
  (nt : NatTree) ->
  ListNSExpToNatTree (NatTreeToListNSExp nt) = nt
ListNSExpFromAfterToNatTreeId (InNT ntF) =
  rewrite reverseInvolutive (NatTreeFToListRNSExp ntF) in
  cong InNT $ ListRNSExpFromAfterToNatTreeFId ntF

public export
0 NEListNSExpFromAfterToNatTreePairId :
(tl, tr : NatTree) ->
  NEListNSExpToNatTreePair
    (fst $ NatTreePairToNEListNSExp tl tr)
    (snd $ NatTreePairToNEListNSExp tl tr) =
  (tl, tr)
NEListNSExpFromAfterToNatTreePairId (InNT tlF) (InNT trF) =
  pairEqCong
    (cong InNT $ rewrite reverseInvolutive (NatTreeFToListRNSExp tlF) in
     ListRNSExpFromAfterToNatTreeFId tlF)
    (cong InNT $ rewrite reverseInvolutive (NatTreeFToListRNSExp trF) in
     ListRNSExpFromAfterToNatTreeFId trF)

public export
0 ListNSExpFromAfterToNatTreeFId :
  (ntF : NatTreeF NatTree) ->
  ListNSExpToNatTreeF (NatTreeFToListNSExp ntF) = ntF
ListNSExpFromAfterToNatTreeFId ntF =
  rewrite reverseInvolutive (NatTreeFToListRNSExp ntF) in
  ListRNSExpFromAfterToNatTreeFId ntF

--------------------------------
---- Binary (natural) trees ----
--------------------------------

-- Leaves, stems, and forks in applicative form.

public export
NSleafId : RNSExpToNatTree נ = Δ
NSleafId = Refl

public export
NSstemId : (ns : NSExp) -> RNSExpToNatTree (י ns) = Ɩ (RNSExpToNatTree ns)
NSstemId ns = Refl

public export
NSforkId : (l, r : NSExp) ->
  RNSExpToNatTree (ד [l, r]) = Ε (RNSExpToNatTree (י l)) (RNSExpToNatTree r)
NSforkId l r = Refl

public export
NSgraftId : (l : List NSExp) -> (r : NSExp) ->
  RNSExpToNatTree (ד (l ++ [r])) = Ε (ListNSExpToNatTree l) (RNSExpToNatTree r)
NSgraftId l r = cong InNT $ rewrite sym (revAppend l [r]) in Refl

public export
RNSappId : (f, x : NatTree) ->
  NatTreeToListRNSExp (Ε f x) = NatTreeToRNSExp x :: NatTreeToListRNSExp f
RNSappId (InNT $ Left ()) x = Refl
RNSappId (InNT $ Right (fl, fr)) x = Refl

public export
NSemptyListId : NatTreeToListNSExp Δ = []
NSemptyListId = Refl

public export
NSlistAppId : (ts : List NSExp) -> (ns : NSExp) ->
  NatTreeToListNSExp
    (Ε (ListNSExpToNatTree ts) (RNSExpToNatTree ns)) =
  ts ++ [ns]
NSlistAppId l (InNS r) =
  rewrite (ListRNSExpToAfterFromNatTreeFId $ reverse l) in
  rewrite (ListRNSExpToAfterFromNatTreeFId r) in
  rewrite reverseOntoSpec ([InNS r]) (reverse l) in
  rewrite reverseInvolutive l in
  Refl

public export
NSappListId : (f, x : NatTree) ->
  NatTreeToListNSExp (Ε f x) = NatTreeToListNSExp f ++ [NatTreeToRNSExp x]
NSappListId (InNT $ Left ()) x = Refl
NSappListId (InNT $ Right (fl, fr)) x =
  reverseOntoSpec
    ([NatTreeToRNSExp x])
    (NatTreeFToListRNSExp (Right (fl, fr)))

public export
NSemptyId : NatTreeToRNSExp Δ = נ
NSemptyId = Refl

public export
NSappId : (f, x : NatTree) ->
  NatTreeToRNSExp (Ε f x) = ד (NatTreeToListNSExp f ++ [NatTreeToRNSExp x])
NSappId f x =
  rewrite sym (NSappListId f x) in
  rewrite reverseInvolutive (NatTreeFToListRNSExp (Right (f, x))) in
  Refl

-----------------------
-----------------------
---- Stack machine ----
-----------------------
-----------------------

public export
ntSizeAlg : NatTreeFAlg Nat
ntSizeAlg = (1, (+) . S)

public export
ntSize : NatTree -> Nat
ntSize = natTreeCata ntSizeAlg

public export
ntFSize : NatTreeF NatTree -> Nat
ntFSize = ntSize . InNT

public export
0 ntFSizeNonZero : (ntF : NatTreeF NatTree) -> Not (ntFSize ntF = 0)
ntFSizeNonZero (Left ()) Refl impossible
ntFSizeNonZero (Right (tl, tr)) eq = succNonZero eq

public export
0 ntSizeNonZero : (nt : NatTree) -> Not (ntSize nt = 0)
ntSizeNonZero (InNT ntF) = ntFSizeNonZero ntF

public export
ntlSize : List NatTree -> Nat
ntlSize = foldr {t=List} ((+) . ntSize) 0

public export
NatTreeCataState : Type -> Type
NatTreeCataState x = (Maybe x, List NatTree, NatTreeF NatTree)

public export
ntStateSize : {x : Type} -> NatTreeCataState x -> Nat
ntStateSize {x} (acc_, nts, ntF) = ntFSize ntF + ntlSize nts

public export
ntcAlgApp : {x : Type} -> NatTreeFAlg x -> Maybe x -> x
ntcAlgApp alg Nothing = fst alg
ntcAlgApp alg (Just ex) = snd alg ex $ fst alg

public export
natTreeCataStep : {x : Type} -> NatTreeFAlg x ->
  NatTreeCataState x -> Either (NatTreeCataState x) x
natTreeCataStep {x} alg (acc, [], Left ()) =
  Right (ntcAlgApp alg acc)
natTreeCataStep {x} alg (acc, (nt :: nts), Left ()) =
  Left (Just (ntcAlgApp alg acc), nts, OutNT nt)
natTreeCataStep {x} alg (acc, nts, Right (tl, tr)) =
  Left (acc, tr :: nts, OutNT tl)

public export
natTreeCataStack : {x : Type} -> NatTreeFAlg x -> NatTree -> x
natTreeCataStack {x} alg nt =
  natTreeCataStackInt
    (ntSize nt)
    Nothing
    []
    nt
    (plusZeroRightNeutral $ ntSize nt)
  where

  mutual
    public export
    natTreeCataStackInt : (n : Nat) -> Maybe x ->
      (nts : List NatTree) -> (nt : NatTree) ->
      (0 _ : ntSize nt + ntlSize nts = n) -> x
    natTreeCataStackInt n acc nts (InNT ntF) eq =
      natTreeFCataStackInt n acc nts ntF eq

    public export
    natTreeFCataStackInt : (n : Nat) -> Maybe x ->
      (nts : List NatTree) -> (ntF : NatTreeF NatTree) ->
      (0 _ : ntFSize ntF + ntlSize nts = n) -> x
    natTreeFCataStackInt Z _ _ ntF eq =
      void $ ntFSizeNonZero ntF $ plusZeroLeftZero eq
    natTreeFCataStackInt (S n) acc [] (Left ()) eq =
      let 0 nIsZero : (n = 0) = sym $ injective eq in
      ntcAlgApp alg acc
    natTreeFCataStackInt (S n) acc (nt :: nts) (Left ()) eq =
      natTreeCataStackInt n (Just $ ntcAlgApp alg acc) nts nt (injective eq)
    natTreeFCataStackInt (S n) acc stack (Right (l, r)) eq =
      natTreeCataStackInt n acc (r :: stack) l $
        trans (plusAssociative (ntSize l) (ntSize r) (ntlSize stack)) $
          injective eq

mutual
  public export
  natTreeCataCont : {x : Type} -> (m : Type -> Type) ->
    NatTreeFAlg x -> NatTree -> RKanExt m m x
  -- Equivalent to
  --  `natTreeCataCont {x} m alg = natTreeFCataCont {x} m alg . OutNT`
  -- (but Idris wouldn't recognize that as terminating).
  natTreeCataCont {x} m alg (InNT nt) = natTreeFCataCont {x} m alg nt

  public export
  natTreeFCataCont : {x : Type} -> (m : Type -> Type) -> NatTreeFAlg x ->
    NatTreeF NatTree -> RKanExt m m x
  natTreeFCataCont {x} m alg (Left u_) r k =
    k (fst alg)
  natTreeFCataCont {x} m alg (Right (tl, tr)) r k =
    natTreePairCataCont {x} m alg tl tr r k

  public export
  natTreePairCataCont : {x : Type} -> (m : Type -> Type) -> NatTreeFAlg x ->
    NatTree -> NatTree -> RKanExt m m x
  natTreePairCataCont {x} m alg tl tr r k =
    natTreeCataCont {x} m alg tl r (natTreeCataContR {x} m alg tr r k)

  public export
  natTreeCataContR : {x : Type} -> (m : Type -> Type) -> NatTreeFAlg x ->
    NatTree -> RKanExt m (FunctorExp m x) x
  natTreeCataContR {x} m alg tr r k =
    natTreeCataCont {x} m alg tr r . (.) k . snd alg

---------------------------------------
---------------------------------------
---- Tree calculus data structures ----
---------------------------------------
---------------------------------------

-- The number of core tree-calculus types that we shall define via mutual
-- recursion.
public export
NumTreeCalcStruct : Nat
NumTreeCalcStruct = 3

-- The base object of the slice category over which we shall perform the
-- mutual recursion which defines the core tree-calculus types.
public export
TCSBaseObj : Type
TCSBaseObj = Fin NumTreeCalcStruct

public export
TCSliceObj : Type
TCSliceObj = SliceObj TCSBaseObj

-- The index of the type of natural trees within `TreeCalcStructSl`.
public export
TCS_NT : TCSBaseObj
TCS_NT = FZ

-- The index of the type of binary trees within `TreeCalcStructSl`.
public export
TCS_BT : TCSBaseObj
TCS_BT = FS FZ

-- The index of the type of lists of binary trees within `TreeCalcStructSl`.
public export
TCS_BTL : TCSBaseObj
TCS_BTL = FS $ FS FZ

public export
TreeCalcStructF : TCSliceObj -> TCSliceObj
-- A natural tree is either a leaf or a pair of natural trees.
TreeCalcStructF x FZ =
  Either Unit (ProductMonad $ x TCS_NT)
-- A binary tree is either a leaf, a fork (pair of binary trees), or
-- stem (single binary tree).
TreeCalcStructF x (FS FZ) =
  Either Unit (Either (x TCS_BT) (ProductMonad $ x TCS_BT))
TreeCalcStructF x (FS $ FS FZ) = Either Unit (Pair (x $ TCS_BT) (x $ TCS_BTL))
